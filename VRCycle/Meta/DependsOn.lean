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

/-- `#axiom_census` — axiom census of the cycle: per module, how many constants carry which axiom, and through which
EXTERNAL (non-VRCycle) lemma each axiom first arrives. -/
elab "#axiom_census" : command => do
  let env ← getEnv
  let isOurs (m : Name) : Bool := (m.toString.startsWith "VRCycle.") || m.toString == "VRCycle"
  let axNames : Array Name := #[`propext, `Quot.sound, `Classical.choice, `sorryAx]
  let mut cache : Std.HashMap Name (Array Name) := {}
  let axiomsOf (c : Std.HashMap Name (Array Name)) (n : Name) : Std.HashMap Name (Array Name) × Array Name :=
    match c.get? n with
    | some a => (c, a)
    | none =>
      let (_, s) := ((CollectAxioms.collect n).run env).run {}
      (c.insert n s.axioms, s.axioms)
  let deps (n : Name) : Array Name :=
    match env.find? n with
    | some ci => ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    | none => #[]
  -- module -> (total, per-axiom count, per-axiom entry-lemma counter)
  let mut stats : Std.HashMap Name (Nat × Std.HashMap Name Nat × Std.HashMap Name (Std.HashMap Name Nat)) := {}
  for (n, ci) in env.constants.map₁.toList do
    let some midx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[midx.toNat]!
    if !isOurs m then continue
    if n.isInternal || n.isInternalDetail then continue
    if ci matches .ctorInfo _ | .recInfo _ | .inductInfo _ then continue   -- structural, axiom-free by nature
    let (c1, axs) := axiomsOf cache n
    cache := c1
    let (tot, per, entry) := stats.getD m (0, {}, {})
    let mut per := per; let mut entry := entry
    for a in axNames do
      if axs.contains a then
        per := per.insert a (per.getD a 0 + 1)
        -- external entry lemmas for this axiom: direct deps outside our modules that carry it
        let mut em := entry.getD a {}
        for d in deps n do
          let some didx := env.getModuleIdxFor? d | continue
          if isOurs env.header.moduleNames[didx.toNat]! then continue
          let (c2, dax) := axiomsOf cache d
          cache := c2
          if dax.contains a then em := em.insert d (em.getD d 0 + 1)
        entry := entry.insert a em
    stats := stats.insert m (tot + 1, per, entry)
  let mut lines : Array String := #[]
  for (m, (tot, per, entry)) in stats.toList do
    let p := per.getD `propext 0; let q := per.getD `Quot.sound 0; let ch := per.getD `Classical.choice 0; let so := per.getD `sorryAx 0
    let top (a : Name) : String :=
      let em := (entry.getD a {}).toList.toArray.qsort (fun x y => x.2 > y.2)
      String.intercalate ", " ((em.extract 0 6).toList.map fun (d, k) => s!"{d}×{k}")
    lines := lines.push s!"{m} | total {tot} | propext {p} | Quot.sound {q} | choice {ch} | sorry {so} | propext-entries: {top `propext} | choice-entries: {top `Classical.choice}"
  let sorted := lines.qsort (· < ·)
  logInfo m!"{String.intercalate "\n" sorted.toList}"

/-- `#axiom_offenders_all ax in [M₁, M₂, …]` — every constant of the listed modules that carries `ax`,
with the external (non-VRCycle) lemmas it arrives through and the internal ones it inherits it from.
The worklist for a sweep: an entry `← ext: [eq_self]` is a `simp` call; `[Eq.propIntro]` on `X.mk.injEq`
is an auto-generated lemma (`set_option genInjectivity false`); `[ZFSet.instSetLike]` is a statement about
a mathlib object — a declared limit, not a tactic. Run in a file that imports the modules. -/
elab "#axiom_offenders_all " ax:ident " in " "[" ms:ident,* "]" : command => do
  let env ← getEnv
  let axName := ax.getId
  let mods : Array Name := (ms.getElems.map (·.getId))
  let isOurs (mm : Name) : Bool := mm.toString.startsWith "VRCycle"
  let mut cache : Std.HashMap Name (Array Name) := {}
  let axiomsOfC (c : Std.HashMap Name (Array Name)) (n : Name) : Std.HashMap Name (Array Name) × Array Name :=
    match c.get? n with
    | some a => (c, a)
    | none =>
      let (_, s) := ((CollectAxioms.collect n).run env).run {}
      (c.insert n s.axioms, s.axioms)
  let deps (n : Name) : Array Name :=
    match env.find? n with
    | some ci => ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    | none => #[]
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some midx := env.getModuleIdxFor? n | continue
    if !mods.contains env.header.moduleNames[midx.toNat]! then continue
    if n.isInternal || n.isInternalDetail then continue
    if ci matches .ctorInfo _ | .recInfo _ | .inductInfo _ then continue
    let (c1, axs) := axiomsOfC cache n
    cache := c1
    if !axs.contains axName then continue
    let mut ext : Array String := #[]; let mut intl : Array String := #[]
    for d in deps n do
      let (c2, dax) := axiomsOfC cache d
      cache := c2
      if !dax.contains axName || d == axName then continue
      let some didx := env.getModuleIdxFor? d | continue
      if isOurs env.header.moduleNames[didx.toNat]! then intl := intl.push d.toString else ext := ext.push d.toString
    lines := lines.push s!"{env.header.moduleNames[midx.toNat]!} :: {n}  ← ext: {ext}  int: {intl}"
  logInfo m!"{lines.size} carry {axName}\n{String.intercalate "\n" (lines.qsort (· < ·)).toList}"


