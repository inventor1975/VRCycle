-- VR — generic transitive-dependency assertions (project-agnostic meta tooling).
-- Computes, for any declaration, the set of constants it transitively uses (through both its type
-- and its proof/value term), and exposes two build-gating commands:
--
--   #assert_not_depends_on f on g   -- fails to compile if f transitively uses g
--   #assert_depends_on     f on g   -- fails to compile unless f transitively uses g
--
-- This is the engine behind the "differential witness" (a constructive layer is free of a specific
-- classical lemma). Nothing here is tied to any particular theorem — `import` this module and point
-- the commands at any two global constants in scope. Meta/trusted tier, like `#print axioms`: the
-- checker certifies the dependency relation but is not itself kernel-verified.

import Lean

open Lean Elab Command

namespace DependsOn

/-- All constants `start` transitively depends on, through both its type and (for theorems and
definitions) its value/proof term. Tail-recursive worklist closure over the environment. -/
partial def transitiveDeps (env : Environment) (start : Name) : NameSet :=
  go [start] {}
where
  go : List Name → NameSet → NameSet
    | [], acc => acc
    | n :: rest, acc =>
      if acc.contains n then go rest acc
      else
        let used : Array Name :=
          match env.find? n with
          | some ci => ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
          | none => #[]
        go (used.toList ++ rest) (acc.insert n)

end DependsOn

/-- `#assert_not_depends_on f on g` fails the build unless `f` is free of any transitive use of
`g`. Turns a "this layer does not invoke that lemma" claim into a build invariant. -/
elab "#assert_not_depends_on " tgt:ident " on " forb:ident : command => do
  let tgtName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo tgt
  let forbName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo forb
  if (DependsOn.transitiveDeps (← getEnv) tgtName).contains forbName then
    throwError "✗ {tgtName} transitively depends on {forbName}"
  else
    logInfo m!"✓ {tgtName} is free of {forbName}"

/-- `#assert_depends_on f on g` fails the build unless `f` genuinely uses `g` — certifies that a
claimed dependency boundary is real, not vacuous. -/
elab "#assert_depends_on " tgt:ident " on " forb:ident : command => do
  let tgtName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo tgt
  let forbName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo forb
  if (DependsOn.transitiveDeps (← getEnv) tgtName).contains forbName then
    logInfo m!"✓ {tgtName} genuinely depends on {forbName}"
  else
    throwError "✗ {tgtName} does NOT depend on {forbName}"

/-- `#dependency_matrix [f, g, …] vs [m, n, …]` prints, for each target, which of the marker
constants it transitively depends on (`●`) and which it is free of (`·`) — the whole differential
layer table in one command, for citation in a blueprint or paper. -/
elab "#dependency_matrix " "[" tgts:ident,* "]" " vs " "[" marks:ident,* "]" : command => do
  let env ← getEnv
  let markNames ← (marks.getElems.map (·.raw)).toList.mapM fun s =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
  let mut out : String := "dependency matrix (● depends · free):"
  for s in tgts.getElems do
    let tgtName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let deps := DependsOn.transitiveDeps env tgtName
    out := out ++ s!"\n  {tgtName}"
    for m in markNames do
      out := out ++ (if deps.contains m then s!"\n      ● {m}" else s!"\n      · {m}")
  logInfo out


/-- `#axiom_frontier ax in c` prints WHERE an axiom enters the dependency closure of `c`: the constants
that carry `ax` while none of their own dependencies does. `#print axioms` says *that* `propext` is
there; this says *through which lemma* — typically a `simp`-normal form of core (`eq_true`, `false_iff`,
`Int.ofNat_inj._simp_1`) reached by `simp`/`omega`/`decide` inside a proof, which is a tactic choice
and can be rewritten by hand (precedent: `Verify_Choice_standalone.lean`, on `[]`). Added 2026-09-12
when the curator set the bar at the empty list for the whole cycle. -/
elab "#axiom_frontier " ax:ident " in " c:ident : command => do
  let env ← getEnv
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let axName := ax.getId
  let deps (n : Name) : Array Name :=
    match env.find? n with
    | some ci => ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    | none => #[]
  let mut seen : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    for d in deps n do
      if !seen.contains d then stack := d :: stack
  let hasAx (n : Name) : Bool :=
    let (_, s) := ((CollectAxioms.collect n).run env).run {}
    s.axioms.contains axName
  let mut frontier : Array Name := #[]
  for n in seen.toList do
    if n == axName || !hasAx n then continue
    let carried := (deps n).any fun d => d != n && d != axName && hasAx d
    if !carried then frontier := frontier.push n
  let sorted := frontier.qsort (fun a b => a.toString < b.toString)
  logInfo m!"closure of {root}: {seen.size} constants; {axName} enters through {sorted.size}:\n{sorted}"
