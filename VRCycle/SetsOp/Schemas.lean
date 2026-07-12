-- VRCycle/SetsOp/Schemas.lean
-- VR-Sets, Brouwer edition — Stage S6: operational Separation and Replacement.
-- Both fall straight out of `sup`.  The clean ZF membership laws hold for species/functions
-- that RESPECT operational identity `≈` — which any genuine property/function of sets must
-- (a property of a set cannot depend on the particular graph presenting it).  No
-- decidability is required (the subtype index is a Type regardless).  Target: choice-free.

import VRCycle.SetsOp.Closure

namespace VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  Separation:  { z ∈ x | p z }
-- ============================================================

/-- **Separation.**  The subset of `x` carved out by a species `p`: restrict `x`'s
member-vertices to those whose member satisfies `p`. -/
def OpSet.sep (x : OpSet.{u}) (p : OpSet.{u} → Prop) : OpSet.{u} :=
  OpSet.sup (fun q : { a : x.V // x.E a x.pt ∧ p (x.child a) } => x.child q.val)

/-- **Separation membership law**, for a species `p` that respects `≈`:
`z ∈ {z ∈ x | p z} ↔ z ∈ x ∧ p z`. -/
theorem OpSet.mem_sep {x : OpSet.{u}} {p : OpSet.{u} → Prop}
    (hp : ∀ {a b : OpSet.{u}}, a.Equiv b → (p a ↔ p b)) (z : OpSet.{u}) :
    z.Mem (OpSet.sep x p) ↔ z.Mem x ∧ p z := by
  refine Iff.trans
    (OpSet.mem_sup
      (fun q : { a : x.V // x.E a x.pt ∧ p (x.child a) } => x.child q.val) z)
    ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, hpa⟩, hz⟩
    exact ⟨⟨a, ha, hz⟩, (hp hz).2 hpa⟩
  · rintro ⟨⟨a, ha, hz⟩, hpz⟩
    exact ⟨⟨a, ha, (hp hz).1 hpz⟩, hz⟩

-- ============================================================
-- §2.  Replacement:  { F z | z ∈ x }
-- ============================================================

/-- **Replacement.**  The image of `x` under a rule `F`. -/
def OpSet.repl (x : OpSet.{u}) (F : OpSet.{u} → OpSet.{u}) : OpSet.{u} :=
  OpSet.sup (fun q : { a : x.V // x.E a x.pt } => F (x.child q.val))

/-- **Replacement membership law**, for a rule `F` that respects `≈`:
`w ∈ { F z | z ∈ x } ↔ ∃ z ∈ x, w ≈ F z`. -/
theorem OpSet.mem_repl {x : OpSet.{u}} {F : OpSet.{u} → OpSet.{u}}
    (hF : ∀ {a b : OpSet.{u}}, a.Equiv b → (F a).Equiv (F b)) (w : OpSet.{u}) :
    w.Mem (OpSet.repl x F) ↔ ∃ z, z.Mem x ∧ w.Equiv (F z) := by
  refine Iff.trans
    (OpSet.mem_sup (fun q : { a : x.V // x.E a x.pt } => F (x.child q.val)) w)
    ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, hw⟩
    exact ⟨x.child a, ⟨a, ha, OpSet.Equiv.refl _⟩, hw⟩
  · rintro ⟨z, ⟨a, ha, hza⟩, hw⟩
    exact ⟨⟨a, ha⟩, hw.trans (hF hza)⟩

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S6) — MEASURED
#print axioms OpSet.mem_sep
#print axioms OpSet.mem_repl

end VRCycle.SetsOp
