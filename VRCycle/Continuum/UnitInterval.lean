-- VRCycle/Continuum/UnitInterval.lean
-- Operational Continuum (Path 1) — toward operational reals: the operational unit interval.
--
-- STAGE: ℝ-recon (first canoe). SOURCE: PLAN_OPERATIONAL_CONTINUUM.md / martini session.
--
-- ## Goal — and the reef we hit, and the way around it
-- A branch `α : ℕ → Bool` names a point of `[0,1]` by its binary expansion `0.α₀α₁…`.
-- We represent the point OPERATIONALLY and want it BELOW the `Classical.choice` floor that
-- forces mathlib `ℝ`-statements to Tier-3.
--
-- ## Finding CONT-7 (decisive, the reef)
-- mathlib `ℚ` is ENTIRELY Tier-3: even `(2:ℚ)+3`, `(2:ℚ)*3`, `(2:ℚ) ≤ 3` pull
-- `Classical.choice` (the floor is at the ordered-field substrate, not only at `ℝ`).
-- So an "operational `[0,1]`" built over `ℚ` is NO better than mathlib `ℝ` on the tier.
-- BUT `ℤ`/`ℕ` are choice-free (`(2:ℤ)+3` axiom-free, `(2:ℤ)^N` is `[propext]`).
-- The way around: represent the point by its **integer numerator** `intval α N : ℤ` over
-- denominator `2^N`.  Then `[0,1]`-membership is `0 ≤ intval α N ≤ 2^N` over `ℤ` —
-- genuinely choice-free, BELOW the ℚ/ℝ floor.  (Also: `cond`, not `if`; structural
-- recursion, not `Finset.sum` — CONT-6.)

import VRCycle.Continuum.Branch
import Mathlib.Tactic

namespace VRCycle.Continuum

/-- Integer value of a bit: `true ↦ 1`, `false ↦ 0` (via `cond`, over `ℤ`, choice-free). -/
def bitZ (b : Bool) : ℤ := cond b 1 0

theorem bitZ_nonneg (b : Bool) : 0 ≤ bitZ b := by cases b <;> decide

theorem bitZ_le_one (b : Bool) : bitZ b ≤ 1 := by cases b <;> decide

/-- The **integer numerator** of the `N`-bit approximation of the point named by `α`:
the binary integer `α₀…α_{N-1}` (the point itself is `intval α N / 2^N`).  Defined by
structural recursion over `ℤ` — entirely below the ℚ/ℝ `Classical.choice` floor. -/
def intval (α : Branch) : ℕ → ℤ
  | 0 => 0
  | N + 1 => 2 * intval α N + bitZ (α N)

/-- The numerator is nonnegative: the point is `≥ 0`.  Choice-free (`ℤ`, `omega`). -/
theorem intval_nonneg (α : Branch) (N : ℕ) : 0 ≤ intval α N := by
  induction N with
  | zero => simp only [intval]; omega
  | succ N ih =>
      simp only [intval]
      have := bitZ_nonneg (α N)
      omega

/-- The numerator is below `2^N`: the point is `< 1`, so it lies in `[0,1]`.
Choice-free (`ℤ`, `omega`) — the payoff: `[0,1]`-membership below the ℚ/ℝ floor. -/
theorem intval_lt_pow (α : Branch) (N : ℕ) : intval α N < 2 ^ N := by
  induction N with
  | zero => simp only [intval, pow_zero]; omega
  | succ N ih =>
      simp only [intval]
      have hb0 := bitZ_nonneg (α N)
      have hb1 := bitZ_le_one (α N)
      have hp : (2 : ℤ) ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
      omega

/-- One-step monotonicity (cross-multiplied, choice-free): the point does not decrease when a
bit is read.  As a value-inequality, `intval α N / 2^N ≤ intval α (N+1) / 2^(N+1)`. -/
theorem intval_mono_step (α : Branch) (N : ℕ) :
    intval α N * 2 ≤ intval α (N + 1) := by
  simp only [intval]
  have := bitZ_nonneg (α N)
  omega

/-- **Binary prefix structure** (the crux for Cauchyness): for `m = n + d`, the numerator
`intval α (n+d)` equals `intval α n · 2^d` plus a remainder in `[0, 2^d)`.  I.e. the first
`n` bits are a prefix.  Proved by induction on `d`; the product `intval α n · 2^d` is
linearised by `ring` (treated as one atom) so `omega` stays choice-free. -/
theorem intval_prefix (α : Branch) (n d : ℕ) :
    0 ≤ intval α (n + d) - intval α n * 2 ^ d ∧
      intval α (n + d) - intval α n * 2 ^ d < 2 ^ d := by
  induction d with
  | zero =>
      simp only [Nat.add_zero, pow_zero, mul_one]
      constructor <;> omega
  | succ d ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hb0 := bitZ_nonneg (α (n + d))
      have hb1 := bitZ_le_one (α (n + d))
      have hidx : n + (d + 1) = (n + d) + 1 := by omega
      have hrec : intval α ((n + d) + 1) = 2 * intval α (n + d) + bitZ (α (n + d)) := by
        simp only [intval]
      have hQ : intval α n * 2 ^ (d + 1) = 2 * (intval α n * 2 ^ d) := by rw [pow_succ]; ring
      have hP : (2 : ℤ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      rw [hidx, hrec, hQ, hP]
      constructor <;> omega

/-- `0 ≤ (2:ℤ)^n`, choice-free (induction; `pow_pos`/`pow_nonneg` pull `Classical.choice`). -/
theorem two_pow_nonneg (n : ℕ) : (0 : ℤ) ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ m ih => rw [pow_succ]; omega

/-- `0 < (2:ℤ)^n`, choice-free. -/
theorem two_pow_pos (n : ℕ) : (0 : ℤ) < 2 ^ n := by
  induction n with
  | zero => decide
  | succ m ih => rw [pow_succ]; omega

/-- Monotonicity of `2^·` (choice-free; `pow_pos`/`pow_le_pow_right` and `Nat.le.dest`
all pull `Classical.choice`, so: induction on the gap, no destructuring). -/
theorem two_pow_le_add (a e : ℕ) : (2 : ℤ) ^ a ≤ 2 ^ (a + e) := by
  induction e with
  | zero => simp only [Nat.add_zero]; omega
  | succ e ih =>
      have hnn := two_pow_nonneg (a + e)
      rw [show a + (e + 1) = (a + e) + 1 from by omega, pow_succ]
      omega

/-- **Cauchy bound for `intval`** (the bridge from the prefix structure to asymptotic
Cauchyness): for `n ≤ m`, `0 ≤ intval α m · 2^n - intval α n · 2^m < 2^m`.  Via
`intval_prefix` (the difference equals `r · 2^n`, `0 ≤ r < 2^{m-n}`); the products are
bounded by the choice-free `Int.mul_nonneg` / `Int.mul_le_mul_of_nonneg_right`. -/
theorem intval_diff_bound (α : Branch) {n m : ℕ} (h : n ≤ m) :
    0 ≤ intval α m * 2 ^ n - intval α n * 2 ^ m ∧
      intval α m * 2 ^ n - intval α n * 2 ^ m < 2 ^ m := by
  obtain ⟨hp0, hp1⟩ := intval_prefix α n (m - n)
  have hd : n + (m - n) = m := by omega
  rw [hd] at hp0 hp1
  have hpow : (2 : ℤ) ^ m = 2 ^ (m - n) * 2 ^ n := by rw [← pow_add]; congr 1; omega
  have hkey : intval α m * 2 ^ n - intval α n * 2 ^ m
            = (intval α m - intval α n * 2 ^ (m - n)) * 2 ^ n := by rw [hpow]; ring
  rw [hkey]
  have h2n := two_pow_nonneg n
  have h2np := two_pow_pos n
  refine ⟨Int.mul_nonneg hp0 h2n, ?_⟩
  have hle : (intval α m - intval α n * 2 ^ (m - n)) * 2 ^ n ≤ (2 ^ (m - n) - 1) * 2 ^ n :=
    Int.mul_le_mul_of_nonneg_right (by omega) h2n
  have he : ((2 : ℤ) ^ (m - n) - 1) * 2 ^ n = (2 : ℤ) ^ (m - n) * 2 ^ n - 2 ^ n := by ring
  rw [he] at hle
  rw [hpow]
  omega

-- ============================================================
-- Axiom audit — operational [0,1], below the ℚ/ℝ floor
-- ============================================================
-- Must be choice-free: integer arithmetic only.
#print axioms intval
#print axioms intval_nonneg
#print axioms intval_lt_pow
#print axioms intval_mono_step
#print axioms intval_prefix
#print axioms two_pow_le_add
#print axioms intval_diff_bound

end VRCycle.Continuum
