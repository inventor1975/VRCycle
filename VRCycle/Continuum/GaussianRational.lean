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

-- Qop positivity helpers (squares; for `normSq z ≠ 0 ⟸ z ≠ 0`), choice-free via ℤ sign cases.

theorem Qop.mul_self_nonneg (a : Qop) : 0 ≤ a * a := by
  refine Quotient.inductionOn a (fun x => ?_)
  have hsq : (0 : ℤ) ≤ x.num * x.num := by
    rcases Int.lt_or_le x.num 0 with h | h
    · have hp : 0 < (-x.num) * (-x.num) := Int.mul_pos (by omega) (by omega)
      have e : (-x.num) * (-x.num) = x.num * x.num := by ring
      rw [e] at hp; omega
    · exact Int.mul_nonneg h h
  change (0 : ℤ) * (x.den * x.den) ≤ (x.num * x.num) * 1
  omega

theorem Qop.mul_self_pos {a : Qop} (h : a ≠ 0) : 0 < a * a := by
  revert h
  refine Quotient.inductionOn a (fun x h => ?_)
  have hx : x.num ≠ 0 := fun hc => h (Quotient.sound (show PreQ.equiv x (PreQ.ofInt 0) by
    change x.num * 1 = 0 * x.den; rw [hc]; ring))
  have hsq : (0 : ℤ) < x.num * x.num := by
    rcases Int.lt_or_le x.num 0 with hn | hp
    · have hpp : 0 < (-x.num) * (-x.num) := Int.mul_pos (by omega) (by omega)
      have e : (-x.num) * (-x.num) = x.num * x.num := by ring
      rw [e] at hpp; omega
    · exact Int.mul_pos (by omega) (by omega)
  change (0 : ℤ) * (x.den * x.den) < (x.num * x.num) * 1
  omega

theorem Qop.add_pos_of_pos_of_nonneg {A B : Qop} (hA : 0 < A) (hB : 0 ≤ B) : 0 < A + B := by
  revert hA hB
  refine Quotient.inductionOn₂ A B (fun x y hA hB => ?_)
  have hxn : 0 < x.num := by change (0 : ℤ) * x.den < x.num * 1 at hA; omega
  have hyn : 0 ≤ y.num := by change (0 : ℤ) * y.den ≤ y.num * 1 at hB; omega
  have h1 : 0 < x.num * y.den := Int.mul_pos hxn y.den_pos
  have h2 : 0 ≤ y.num * x.den := Int.mul_nonneg hyn (by have := x.den_pos; omega)
  change (0 : ℤ) * (x.den * y.den) < (x.num * y.den + y.num * x.den) * 1
  omega

namespace GaussQ

/-- `|z|² = re² + im² : Qop`. -/
def normSq (z : GaussQ) : Qop := z.re * z.re + z.im * z.im

/-- For a nonzero Gaussian rational the norm is strictly positive (hence nonzero — DECIDABLY, since
`Qop` has `DecidableEq`).  This makes the inverse TOTAL, inherited from `Qop`'s decidable zero. -/
theorem normSq_pos {z : GaussQ} (h : z ≠ 0) : 0 < z.normSq := by
  by_cases hre : z.re = 0
  · by_cases him : z.im = 0
    · exact absurd (by ext <;> simp [hre, him]) h
    · have hp := Qop.add_pos_of_pos_of_nonneg (Qop.mul_self_pos him) (Qop.mul_self_nonneg z.re)
      rwa [add_comm] at hp
  · exact Qop.add_pos_of_pos_of_nonneg (Qop.mul_self_pos hre) (Qop.mul_self_nonneg z.im)

/-- Total reciprocal `z⁻¹ = z̄/|z|²` (and `0⁻¹ = 0` componentwise). -/
def inv (z : GaussQ) : GaussQ := ⟨z.re * (z.normSq)⁻¹, -(z.im * (z.normSq)⁻¹)⟩

instance : Inv GaussQ := ⟨inv⟩

/-- **The Gaussian rationals are a field in CONTENT** — total inverse, `z · z⁻¹ = 1` for `z ≠ 0`,
choice-free `[propext, Quot.sound]`.  Inherited from `Qop` (decidable zero ⇒ total inverse). -/
theorem mul_inv_cancel {z : GaussQ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  have hN : z.normSq ≠ 0 := by
    intro hc
    have hpos := normSq_pos h
    rw [hc] at hpos
    change (0 : ℤ) * 1 < 0 * 1 at hpos
    omega
  have hNN : z.normSq * (z.normSq)⁻¹ = 1 := Qop.mul_inv_cancel z.normSq hN
  ext
  · show z.re * (z.re * (z.normSq)⁻¹) - z.im * -(z.im * (z.normSq)⁻¹) = 1
    have e : z.re * (z.re * (z.normSq)⁻¹) - z.im * -(z.im * (z.normSq)⁻¹)
           = z.normSq * (z.normSq)⁻¹ := by rw [normSq]; ring
    rw [e, hNN]
  · show z.re * -(z.im * (z.normSq)⁻¹) + z.im * (z.re * (z.normSq)⁻¹) = 0
    ring

end GaussQ

end VRCycle.Continuum

-- Choice-free check (expected [propext, Quot.sound], inherited from Qop)
#print axioms VRCycle.Continuum.GaussQ.instCommRing
#print axioms VRCycle.Continuum.GaussQ.mul_inv_cancel
