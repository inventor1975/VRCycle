-- VRCycle/SetsOp/Pointed.lean
-- VR-Sets, Brouwer edition — the CHOICE-FREE operational set universe (clean carrier).
-- Self-contained: NO mathlib, NO PFunctor.M.  Built to stay below the choice floor.
--
-- ## Why this file exists (the measured reason)
-- `#print axioms` showed mathlib's `PFunctor.M` substrate is irreducibly Tier-3: not only
-- `OSetZFA.mk` but even the DESTRUCTOR `CoPSet.dest`/`shape`/`children` pull
-- `Classical.choice` — you can BUILD M-elements choice-free (`mk`/`corec` are axiom-free)
-- but you cannot OBSERVE them choice-free.  Since membership and extensionality require
-- observation, an operational set universe ON `CoPSet` cannot be choice-free.  So the
-- operational register is built here FROM SCRATCH, bypassing mathlib entirely.
--
-- ## The carrier — a pointed graph (set = functionality / rule)
-- An operational set is a directed pointed graph `(V, E, pt)`: `E a b` reads "querying the
-- functionality at `b` reveals `a` as a member".  This is exactly the language in which
-- Aczel's AFA is stated (decoration of a graph) — but here NO quotient is taken.
--
-- ## Identity is OPERATIONAL — witnessed bisimulation, not a quotient (doing-not-being)
-- Turning "bisimilar" into a TYPE-level equality (the quotient) is what pulls choice: it
-- Skolemises the bisimulation's existential matches — precisely VR's T→O extraction
-- asymmetry.  So identity stays a RELATION `Equiv` (a setoid), carried with its witness.
-- The universe is representatives + `Equiv`; we never form the quotient.  This is VR's own
-- thesis made into the construction: identity is a performed act, not a given completion.
--
-- ## ZFC and ZFA are NOT choices here (the curator's point, 2026-06-08)
-- Whether a set is well-founded (ZFC) or admits cycles like the Quine atom (ZFA) is a
-- PROPERTY of its graph — `IsGrounded` below — not a global axiom.  VR holds both natively
-- and faces neither Foundation nor Anti-Foundation as a postulate.  ZFC-fragment =
-- grounded sets; ZFA-fragment = all sets.
--
-- ## Axiom profile: MEASURED per object at the bottom (#print axioms).  Target: choice-free.

namespace VRCycle.SetsOp

universe u

/-- An **operational set**: a pointed graph.  `V` its vertices, `E a b` "`a` is revealed
as a member when the functionality at `b` is queried", `pt` the set itself. -/
structure OpSet : Type (u+1) where
  V  : Type u
  E  : V → V → Prop
  pt : V

/-- The member of `x` sitting at vertex `a`: the same graph repointed at `a`. -/
def OpSet.child (x : OpSet.{u}) (a : x.V) : OpSet.{u} := ⟨x.V, x.E, a⟩

-- ============================================================
-- §1.  Witnessed bisimulation = operational identity (no quotient)
-- ============================================================

/-- `R` is a **bisimulation** between `x` and `y`: related vertices reveal matching
members in both directions. -/
def IsBisim (x y : OpSet.{u}) (R : x.V → y.V → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ a', x.E a' a → ∃ b', y.E b' b ∧ R a' b') ∧
    (∀ b', y.E b' b → ∃ a', x.E a' a ∧ R a' b')

/-- **Operational identity**: `x ≈ y` iff some bisimulation relates their points.  This is
strong (AFA-style) extensionality kept as a RELATION — no quotient, hence choice-free. -/
def OpSet.Equiv (x y : OpSet.{u}) : Prop :=
  ∃ R : x.V → y.V → Prop, R x.pt y.pt ∧ IsBisim x y R

theorem OpSet.Equiv.refl (x : OpSet.{u}) : x.Equiv x :=
  ⟨fun a b => a = b, rfl, by
    intro a b hab; subst hab
    exact ⟨fun a' h => ⟨a', h, rfl⟩, fun b' h => ⟨b', h, rfl⟩⟩⟩

theorem OpSet.Equiv.symm {x y : OpSet.{u}} (h : x.Equiv y) : y.Equiv x := by
  obtain ⟨R, hpt, hbi⟩ := h
  refine ⟨fun b a => R a b, hpt, ?_⟩
  intro b a hab
  obtain ⟨fwd, bwd⟩ := hbi a b hab
  exact ⟨bwd, fwd⟩

theorem OpSet.Equiv.trans {x y z : OpSet.{u}}
    (hxy : x.Equiv y) (hyz : y.Equiv z) : x.Equiv z := by
  obtain ⟨R, hRpt, hR⟩ := hxy
  obtain ⟨S, hSpt, hS⟩ := hyz
  refine ⟨fun a c => ∃ b, R a b ∧ S b c, ⟨y.pt, hRpt, hSpt⟩, ?_⟩
  rintro a c ⟨b, hab, hbc⟩
  obtain ⟨Rfwd, Rbwd⟩ := hR a b hab
  obtain ⟨Sfwd, Sbwd⟩ := hS b c hbc
  constructor
  · intro a' ha'
    obtain ⟨b', hb', hRab'⟩ := Rfwd a' ha'
    obtain ⟨c', hc', hSbc'⟩ := Sfwd b' hb'
    exact ⟨c', hc', b', hRab', hSbc'⟩
  · intro c' hc'
    obtain ⟨b', hb', hSbc'⟩ := Sbwd c' hc'
    obtain ⟨a', ha', hRab'⟩ := Rbwd b' hb'
    exact ⟨a', ha', b', hRab', hSbc'⟩

-- ============================================================
-- §2.  Membership
-- ============================================================

/-- `x ∈ y`: some member-vertex of `y` is operationally identical to `x`. -/
def OpSet.Mem (x y : OpSet.{u}) : Prop :=
  ∃ a, y.E a y.pt ∧ x.Equiv (y.child a)

-- ============================================================
-- §3.  ∅, and the Quine atom — both native, distinguished by a PREDICATE
-- ============================================================

/-- The empty operational set: a single point that reveals nothing. -/
def OpSet.empty : OpSet.{u} := ⟨PUnit, fun _ _ => False, PUnit.unit⟩

theorem OpSet.not_mem_empty (x : OpSet.{u}) : ¬ OpSet.Mem x OpSet.empty := by
  rintro ⟨_, h, _⟩; exact h

/-- **Foundation is a PREDICATE, not an axiom.**  `x` is grounded (ZFC-like) iff its point
is accessible under the reveal relation — every membership descent terminates.  VR does not
postulate this; it observes it. -/
def OpSet.IsGrounded (x : OpSet.{u}) : Prop := Acc (fun a b => x.E a b) x.pt

theorem OpSet.empty_isGrounded : OpSet.empty.{u}.IsGrounded :=
  Acc.intro _ (fun _ h => (h).elim)

/-- The **Quine atom** `A = {A}`: one vertex that reveals itself.  A perfectly good
operational set — ZFA-like, NOT grounded.  No Anti-Foundation axiom is invoked; the graph
simply has a cycle. -/
def OpSet.quine : OpSet.{u} := ⟨PUnit, fun _ _ => True, PUnit.unit⟩

theorem OpSet.quine_self_mem : OpSet.Mem OpSet.quine.{u} OpSet.quine.{u} :=
  ⟨PUnit.unit, trivial, OpSet.Equiv.refl _⟩

theorem OpSet.quine_not_grounded : ¬ OpSet.quine.{u}.IsGrounded := by
  -- no point is accessible under the total relation `fun _ _ => True`
  have key : ∀ a : PUnit.{u+1}, Acc (fun _ _ : PUnit.{u+1} => True) a → False := by
    intro a h
    induction h with
    | intro x _ ih => exact ih x trivial
  exact fun h => key _ h

-- CHECKS: no sorry, no admit; self-contained; identity is a setoid (no quotient).

-- Axiom audit (clean carrier) — MEASURED, not claimed
#print axioms OpSet.Equiv.refl
#print axioms OpSet.Equiv.symm
#print axioms OpSet.Equiv.trans
#print axioms OpSet.Mem
#print axioms OpSet.not_mem_empty
#print axioms OpSet.quine_self_mem
#print axioms OpSet.quine_not_grounded

end VRCycle.SetsOp
