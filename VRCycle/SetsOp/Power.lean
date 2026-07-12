-- VRCycle/SetsOp/Power.lean
-- VR-Sets, Brouwer edition — Stage S7: the operational Power set, choice-free.
--
-- The one ZF⁻ axiom the operational register was still missing (Ext / ∅ / pair / ⋃ /
-- Separation / Replacement / Infinity were already in place).  On the M-type register
-- (`SetsZFA`) power set is irreducibly Tier-3 because every observation goes through
-- `PFunctor.M.dest` (which pulls `Classical.choice`).  Here, on the pointed-graph carrier
-- with identity carried as a witnessed bisimulation (no quotient), it is choice-free.
--
-- A subset of `x` is a vertex-predicate `s : x.V → Prop` selecting which member-vertices to
-- keep — `subsetOf x s`.  The power set is `sup` over ALL such predicates.  The membership
-- law `z ∈ 𝒫 x ↔ z ⊆ x` uses strong extensionality (`ext`) for the `←` direction: given
-- `z ⊆ x`, the selecting predicate is "`a` is a member-vertex whose member lies in `z`".
--
-- Axiom profile: MEASURED at the bottom (#print axioms).  Target: choice-free.

import VRCycle.SetsOp.Extensionality
import VRCycle.SetsOp.Schemas

namespace VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  Subset
-- ============================================================

/-- `x ⊆ y`: every member of `x` is a member of `y`.  A relation on representatives;
respects `≈` on both sides (via `mem_congr` / `mem_congr_left`), like everything here. -/
def OpSet.Subset (x y : OpSet.{u}) : Prop := ∀ z : OpSet.{u}, z.Mem x → z.Mem y

-- ============================================================
-- §2.  The subset of `x` selected by a vertex-predicate
-- ============================================================

/-- `subsetOf x s`: the subset of `x` keeping exactly the member-vertices `a` with `s a`. -/
def OpSet.subsetOf (x : OpSet.{u}) (s : x.V → Prop) : OpSet.{u} :=
  OpSet.sup (fun q : { a : x.V // x.E a x.pt ∧ s a } => x.child q.val)

/-- Membership law of `subsetOf`: a member is a kept member-vertex's member, up to `≈`. -/
theorem OpSet.mem_subsetOf (x : OpSet.{u}) (s : x.V → Prop) (z : OpSet.{u}) :
    z.Mem (OpSet.subsetOf x s) ↔ ∃ a, (x.E a x.pt ∧ s a) ∧ z.Equiv (x.child a) := by
  refine Iff.trans
    (OpSet.mem_sup (fun q : { a : x.V // x.E a x.pt ∧ s a } => x.child q.val) z)
    ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, hsa⟩, hz⟩; exact ⟨a, ⟨ha, hsa⟩, hz⟩
  · rintro ⟨a, ⟨ha, hsa⟩, hz⟩; exact ⟨⟨a, ha, hsa⟩, hz⟩

-- ============================================================
-- §3.  Power set
-- ============================================================

/-- **Power set** `𝒫 x`: the set of all subsets of `x`, indexed by the vertex-predicates
`s : x.V → Prop` (a `Type u`, so the index stays in the sets' universe). -/
def OpSet.powerset (x : OpSet.{u}) : OpSet.{u} :=
  OpSet.sup (fun s : x.V → Prop => OpSet.subsetOf x s)

/-- **Power-set membership law**: `z ∈ 𝒫 x ↔ z ⊆ x`. -/
theorem OpSet.mem_powerset (x z : OpSet.{u}) :
    z.Mem (OpSet.powerset x) ↔ OpSet.Subset z x := by
  refine Iff.trans
    (OpSet.mem_sup (fun s : x.V → Prop => OpSet.subsetOf x s) z) ⟨?_, ?_⟩
  · -- z ≈ subsetOf x s, some s  ⟹  z ⊆ x
    rintro ⟨s, hz⟩ w hw
    have hw' : w.Mem (OpSet.subsetOf x s) := OpSet.mem_congr hz hw
    obtain ⟨a, ⟨ha, _⟩, hwa⟩ := (OpSet.mem_subsetOf x s w).1 hw'
    exact ⟨a, ha, hwa⟩
  · -- z ⊆ x  ⟹  z ≈ subsetOf x s  for  s a := "a is a member-vertex whose member is in z"
    intro hsub
    refine ⟨fun a => x.E a x.pt ∧ (x.child a).Mem z, ?_⟩
    apply OpSet.ext
    intro w
    constructor
    · intro hw
      obtain ⟨a, ha, hwa⟩ := hsub w hw
      exact (OpSet.mem_subsetOf x _ w).2
        ⟨a, ⟨ha, ha, OpSet.mem_congr_left hwa hw⟩, hwa⟩
    · intro hw
      obtain ⟨a, ⟨_, _, hcaz⟩, hwa⟩ := (OpSet.mem_subsetOf x _ w).1 hw
      exact OpSet.mem_congr_left hwa.symm hcaz

-- CHECKS: no sorry, no admit; self-contained; identity stays a witnessed bisimulation.

-- Axiom audit (Stage S7) — MEASURED.  Target: choice-free.
#print axioms OpSet.mem_subsetOf
#print axioms OpSet.mem_powerset

end VRCycle.SetsOp
