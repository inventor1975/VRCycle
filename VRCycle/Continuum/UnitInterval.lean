-- VRCycle/Continuum/UnitInterval.lean — the `[0,1]` point named by a branch, as integer pairs.
--
-- Integrity programme, step 1e (2026-09-12).  Until today over Mathlib's `ℤ` with `omega`; now the
-- numerators are VR's own integer pairs and every inequality is a certificate (`int_linarith`) or a
-- `≤ᵢ`-lemma.  `intval α N / 2^N` is the `N`-bit approximation of the point named by `α`; the
-- binary-prefix structure gives the Cauchy bound the real layer needs.  Every theorem on `[]`.
import VRCycle.Continuum.Branch
import VRCycle.Numbers.IntegersOrd

namespace VRCycle.Continuum

open VR VR.Numbers

set_option genInjectivity false

/-- Integer value of a bit. -/
def bitI (b : Bool) : IntExpr := cond b oneI zeroI

theorem bitI_nonneg (b : Bool) : zeroI ≤ᵢ bitI b := by
  cases b
  · exact intLe_refl _
  · exact intLe_of_lt intPos_one

theorem bitI_le_one (b : Bool) : bitI b ≤ᵢ oneI := by
  cases b
  · exact intLe_of_lt intPos_one
  · exact intLe_refl _

/-- The **integer numerator** of the `N`-bit approximation: the binary integer `α₀…α_{N-1}`. -/
def intval (α : Branch) : Nat → IntExpr
  | 0 => zeroI
  | N + 1 => iadd (iadd (intval α N) (intval α N)) (bitI (α N))

theorem intval_succ (α : Branch) (N : Nat) :
    intval α (N + 1) = iadd (iadd (intval α N) (intval α N)) (bitI (α N)) := rfl

/-- The numerator is non-negative: the point is `≥ 0`. -/
theorem intval_nonneg (α : Branch) : ∀ N : Nat, zeroI ≤ᵢ intval α N
  | 0 => intLe_refl _
  | N + 1 => by
      have ih := intval_nonneg α N
      have hb := bitI_nonneg (α N)
      rw [intval_succ]
      int_linarith

/-- The numerator is below `2^N`: the point is `< 1`, so it lies in `[0,1]`. -/
theorem intval_lt_pow (α : Branch) : ∀ N : Nat, intval α N <ᵢ pow2 N
  | 0 => intPos_one
  | N + 1 => by
      have ih := intval_lt_pow α N
      have hb := bitI_le_one (α N)
      have hp := pow2_succ N
      rw [intval_succ]
      int_linarith

/-- One-step monotonicity: the point does not decrease when a bit is read. -/
theorem intval_mono_step (α : Branch) (N : Nat) :
    iadd (intval α N) (intval α N) ≤ᵢ intval α (N + 1) := by
  have hb := bitI_nonneg (α N)
  rw [intval_succ]
  int_linarith

/-- **Binary prefix structure**: `intval α (n+d) = intval α n · 2^d + r` with `0 ≤ r < 2^d`. -/
theorem intval_prefix (α : Branch) (n : Nat) : ∀ d : Nat,
    zeroI ≤ᵢ iadd (intval α (n + d)) (ineg (imul (intval α n) (pow2 d))) ∧
      iadd (intval α (n + d)) (ineg (imul (intval α n) (pow2 d))) <ᵢ pow2 d
  | 0 => by
      rw [pow2_zero]
      have h1 : imul (intval α n) oneI ≈ᵢ intval α n := imul_one _
      have h2 : zeroI <ᵢ oneI := intPos_one
      constructor
      · change zeroI ≤ᵢ iadd (intval α n) (ineg (imul (intval α n) oneI))
        int_linarith
      · change iadd (intval α n) (ineg (imul (intval α n) oneI)) <ᵢ oneI
        int_linarith
  | d + 1 => by
      obtain ⟨ih0, ih1⟩ := intval_prefix α n d
      have hb0 := bitI_nonneg (α (n + d))
      have hb1 := bitI_le_one (α (n + d))
      have hidx : n + (d + 1) = (n + d) + 1 := rfl
      rw [hidx, intval_succ]
      have hQ : imul (intval α n) (pow2 (d + 1))
          ≈ᵢ iadd (imul (intval α n) (pow2 d)) (imul (intval α n) (pow2 d)) :=
        intEq_trans _ _ _ (imul_respects _ _ _ _ (intEq_refl _) (pow2_succ d)) (imul_iadd _ _ _)
      have hP := pow2_succ d
      constructor
      · int_linarith
      · int_linarith

/-- **Cauchy bound for `intval`**: for `n ≤ m`, `0 ≤ intval α m · 2^n − intval α n · 2^m < 2^m`. -/
theorem intval_diff_bound (α : Branch) {n m : Nat} (h : n ≤ m) :
    zeroI ≤ᵢ iadd (imul (intval α m) (pow2 n)) (ineg (imul (intval α n) (pow2 m))) ∧
      iadd (imul (intval α m) (pow2 n)) (ineg (imul (intval α n) (pow2 m))) <ᵢ pow2 m := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  subst hd
  obtain ⟨hp0, hp1⟩ := intval_prefix α n d
  -- the difference is `r · 2^n` with `0 ≤ r < 2^d`; multiply the bounds by `2^n > 0`
  have hpow : pow2 (n + d) ≈ᵢ imul (pow2 d) (pow2 n) :=
    intEq_trans _ _ _ (pow2_add n d) (imul_comm _ _)
  have hpow' : imul (intval α n) (pow2 (n + d)) ≈ᵢ imul (imul (intval α n) (pow2 d)) (pow2 n) :=
    intEq_trans _ _ _ (imul_respects _ _ _ _ (intEq_refl _) hpow) (by int_ring)
  have hr0 := intLe_mul_right (pow2_pos n) hp0
  have hr1 := intLe_mul_right (pow2_pos n) hp1
  constructor
  · int_linarith
  · -- strict: (r + 1)·2^n ≤ 2^d·2^n, and 2^n ≥ 1
    have h1 := one_le_pow2 n
    int_linarith

end VRCycle.Continuum

#print axioms VRCycle.Continuum.intval_lt_pow
#print axioms VRCycle.Continuum.intval_prefix
#print axioms VRCycle.Continuum.intval_diff_bound
