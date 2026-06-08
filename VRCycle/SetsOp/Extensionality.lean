-- VRCycle/SetsOp/Extensionality.lean
-- VR-Sets, Brouwer edition — Stage S3: strong extensionality.
-- The headline theorem justifying `≈` as genuine set equality:
--   operational identity  ⟺  having the same members (up to `≈`).
-- This is the coinductive direction (build a bisimulation from member-matching).  It is
-- the AFA-style STRONG extensionality, kept choice-free by carrying the bisimulation as a
-- witness (no quotient).  Target: axiom-free / choice-free.

import VRCycle.SetsOp.Closure

namespace VRCycle.SetsOp

universe u

/-- **Strong extensionality.**  If `x` and `y` have the same members (each up to `≈`), then
`x ≈ y`.  The bisimulation: relate the two roots, and relate any other pair of vertices
whose rooted subtrees are already operationally identical.  The root step uses the
hypothesis; the subtree step unfolds the witnessing bisimulation and re-wraps it. -/
theorem OpSet.ext {x y : OpSet.{u}} (h : ∀ z : OpSet.{u}, z.Mem x ↔ z.Mem y) : x.Equiv y := by
  refine ⟨fun a b => (a = x.pt ∧ b = y.pt) ∨ (x.child a).Equiv (y.child b),
          Or.inl ⟨rfl, rfl⟩, ?_⟩
  rintro a b (⟨rfl, rfl⟩ | hsub)
  · -- root case
    refine ⟨?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', heq⟩ := (h (x.child a')).1 ⟨a', ha', OpSet.Equiv.refl _⟩
      exact ⟨b', hb', Or.inr heq⟩
    · intro b' hb'
      obtain ⟨a', ha', heq⟩ := (h (y.child b')).2 ⟨b', hb', OpSet.Equiv.refl _⟩
      exact ⟨a', ha', Or.inr heq.symm⟩
  · -- subtree case: x.child a ≈ y.child b, witnessed by R₀
    obtain ⟨R₀, hR₀pt, hR₀⟩ := hsub
    obtain ⟨fwd, bwd⟩ := hR₀ a b hR₀pt
    refine ⟨?_, ?_⟩
    · intro a' ha'
      obtain ⟨b', hb', hR₀'⟩ := fwd a' ha'
      exact ⟨b', hb', Or.inr ⟨R₀, hR₀', hR₀⟩⟩
    · intro b' hb'
      obtain ⟨a', ha', hR₀'⟩ := bwd b' hb'
      exact ⟨a', ha', Or.inr ⟨R₀, hR₀', hR₀⟩⟩

/-- **Operational identity is exactly co-membership.**  `x ≈ y ↔ x` and `y` have the same
members.  (`→` is `mem_congr` both ways; `←` is strong extensionality.)  This is what makes
the witnessed setoid `≈` a faithful equality of operational sets — without ever quotienting. -/
theorem OpSet.equiv_iff_same_mem {x y : OpSet.{u}} :
    x.Equiv y ↔ ∀ z : OpSet.{u}, z.Mem x ↔ z.Mem y :=
  ⟨fun hxy z => ⟨fun hz => OpSet.mem_congr hxy hz, fun hz => OpSet.mem_congr hxy.symm hz⟩,
   OpSet.ext⟩

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S3) — MEASURED
#print axioms OpSet.ext
#print axioms OpSet.equiv_iff_same_mem

end VRCycle.SetsOp
