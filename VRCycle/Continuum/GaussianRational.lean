-- VRCycle/Continuum/GaussianRational.lean
-- Operational ℂ — the Gaussian rationals ℚ[i] over the operational `Qop`, BELOW the choice floor.
--
-- HONEST LABEL (curator's call): this node is for COMPLETENESS of the spectrum ℤ→ℚ→ℝ→ℂ; it
-- INHERITS the operational character of its base `Qop` and does NOT open a new operational boundary.
--   • DecidableEq + total inverse (choice-free) — inherited from `Qop` (decidable zero on ℚ);
--   • NO order / NO trichotomy — but that is a CLASSICAL-ALGEBRA fact (ℂ is not orderable at all),
--     not an operational one.
-- So ℂ confirms operationality is preserved under the degree-2 extension `·[i]`, nothing more.

import VRCycle.Continuum.Rational

namespace VRCycle.Continuum

/-- A Gaussian rational `re + im·i` with `re, im : Qop`. -/
@[ext] structure GaussQ where
  re : Qop
  im : Qop
  deriving DecidableEq

namespace GaussQ

instance : Zero GaussQ := ⟨0, 0⟩
instance : One GaussQ := ⟨1, 0⟩
instance : Add GaussQ := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg GaussQ := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Mul GaussQ := ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] theorem zero_re : (0 : GaussQ).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussQ).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussQ).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussQ).im = 0 := rfl
@[simp] theorem add_re (z w : GaussQ) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : GaussQ) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : GaussQ) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : GaussQ) : (-z).im = -z.im := rfl
@[simp] theorem mul_re (z w : GaussQ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im (z w : GaussQ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

/-- **The Gaussian rationals form a commutative ring**, choice-free, below the floor — inherited
component-wise from `Qop`'s `CommRing` (each law is a `Qop` ring identity, closed by `ring`). -/
instance : CommRing GaussQ where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

end GaussQ

end VRCycle.Continuum

-- Choice-free check (expected [propext, Quot.sound], inherited from Qop)
#print axioms VRCycle.Continuum.GaussQ.instCommRing
