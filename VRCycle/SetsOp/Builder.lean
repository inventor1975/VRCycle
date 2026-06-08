-- VRCycle/SetsOp/Builder.lean
-- VR-Sets, Brouwer edition — Stage S2: the operational set-builder.
-- Self-contained continuation of `Pointed.lean`.  Target: axiom-free throughout.
--
-- ## What this file builds
-- The core constructor `OpSet.sup c` — "the set whose members are exactly the `c i`" — as a
-- pointed graph (a new root revealing each component's point), with its membership law
-- `mem_sup : z ∈ sup c ↔ ∃ i, z ≈ c i`.  From it, ∅ / singleton / pair fall out with their
-- membership laws.  All identities are witnessed bisimulations — no quotient, no choice.
--
-- ## Axiom profile: MEASURED at the bottom (#print axioms).  Target: choice-free / axiom-free.

import VRCycle.SetsOp.Pointed

namespace VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  sup — the set whose members are exactly a given family
-- ============================================================

/-- `OpSet.sup c` : the operational set whose members are exactly the `c i`.  A fresh root
(`none`) reveals each component's point (`some ⟨i, (c i).pt⟩`); inside each component the
original reveal-edges are kept (and components never interfere). -/
def OpSet.sup {I : Type u} (c : I → OpSet.{u}) : OpSet.{u} where
  V  := Option (Σ i : I, (c i).V)
  E  := fun a b => match b with
        | none          => ∃ i, a = some ⟨i, (c i).pt⟩
        | some ⟨i, v⟩    => ∃ w, a = some ⟨i, w⟩ ∧ (c i).E w v
  pt := none

/-- Reveal-edges into the root of `sup c`: the members of `sup c` itself. -/
theorem OpSet.sup_E_root {I : Type u} (c : I → OpSet.{u}) (a : (OpSet.sup c).V) :
    (OpSet.sup c).E a (OpSet.sup c).pt ↔ ∃ i, a = some ⟨i, (c i).pt⟩ := Iff.rfl

/-- Reveal-edges inside component `i`. -/
theorem OpSet.sup_E_some {I : Type u} (c : I → OpSet.{u})
    (a : (OpSet.sup c).V) (i : I) (v : (c i).V) :
    (OpSet.sup c).E a (some ⟨i, v⟩) ↔ ∃ w, a = some ⟨i, w⟩ ∧ (c i).E w v := Iff.rfl

/-- The subgraph of `sup c` rooted at component `i`'s point is operationally identical to
`c i`.  Witnessed by `R a v := a = some ⟨i, v⟩`. -/
theorem OpSet.sup_child_equiv {I : Type u} (c : I → OpSet.{u}) (i : I) :
    ((OpSet.sup c).child (some ⟨i, (c i).pt⟩)).Equiv (c i) := by
  refine ⟨fun a v => a = some ⟨i, v⟩, rfl, ?_⟩
  rintro a v rfl
  constructor
  · intro a' ha'
    -- ha' : (sup c).E a' (some ⟨i, v⟩)
    obtain ⟨w, rfl, hw⟩ := (OpSet.sup_E_some c a' i v).1 ha'
    exact ⟨w, hw, rfl⟩
  · intro v' hv'
    exact ⟨some ⟨i, v'⟩, (OpSet.sup_E_some c _ i v).2 ⟨v', rfl, hv'⟩, rfl⟩

/-- **Membership law of `sup`**: `z ∈ sup c ↔ z` is operationally identical to some `c i`. -/
theorem OpSet.mem_sup {I : Type u} (c : I → OpSet.{u}) (z : OpSet.{u}) :
    z.Mem (OpSet.sup c) ↔ ∃ i, z.Equiv (c i) := by
  constructor
  · rintro ⟨a, ha, hz⟩
    obtain ⟨i, rfl⟩ := (OpSet.sup_E_root c a).1 ha
    exact ⟨i, hz.trans (OpSet.sup_child_equiv c i)⟩
  · rintro ⟨i, hz⟩
    exact ⟨some ⟨i, (c i).pt⟩, (OpSet.sup_E_root c _).2 ⟨i, rfl⟩,
           hz.trans (OpSet.sup_child_equiv c i).symm⟩

-- ============================================================
-- §2.  ∅, singleton, pair — all from `sup`, with their membership laws
-- ============================================================

/-- The empty set as the empty `sup`. -/
def OpSet.emptySup : OpSet.{u} := OpSet.sup (fun e : PEmpty.{u+1} => e.elim)

theorem OpSet.not_mem_emptySup (z : OpSet.{u}) : ¬ z.Mem OpSet.emptySup := by
  rw [OpSet.emptySup, OpSet.mem_sup]; rintro ⟨e, _⟩; exact e.elim

/-- Singleton `{a}`. -/
def OpSet.singleton (a : OpSet.{u}) : OpSet.{u} := OpSet.sup (fun _ : PUnit.{u+1} => a)

theorem OpSet.mem_singleton (z a : OpSet.{u}) :
    z.Mem (OpSet.singleton a) ↔ z.Equiv a := by
  rw [OpSet.singleton, OpSet.mem_sup]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩

/-- Unordered pair `{a, b}`.  Indexed by `PUnit ⊕ PUnit` (a two-element type in `Type u`,
so the index lives in the same universe as the sets). -/
def OpSet.pair (a b : OpSet.{u}) : OpSet.{u} :=
  OpSet.sup (Sum.elim (fun _ : PUnit.{u+1} => a) (fun _ : PUnit.{u+1} => b))

theorem OpSet.mem_pair (z a b : OpSet.{u}) :
    z.Mem (OpSet.pair a b) ↔ z.Equiv a ∨ z.Equiv b := by
  rw [OpSet.pair, OpSet.mem_sup]
  constructor
  · rintro ⟨i, h⟩
    cases i with
    | inl _ => exact Or.inl h
    | inr _ => exact Or.inr h
  · rintro (h | h)
    · exact ⟨Sum.inl PUnit.unit, h⟩
    · exact ⟨Sum.inr PUnit.unit, h⟩

-- CHECKS: no sorry, no admit; self-contained; identities are witnessed bisimulations.

-- Axiom audit (Stage S2) — MEASURED
#print axioms OpSet.sup_child_equiv
#print axioms OpSet.mem_sup
#print axioms OpSet.not_mem_emptySup
#print axioms OpSet.mem_singleton
#print axioms OpSet.mem_pair

end VRCycle.SetsOp
