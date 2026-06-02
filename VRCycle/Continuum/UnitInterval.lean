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

/-- `(n:ℤ) ≤ 2^n`, choice-free (induction; avoids the renamed `Nat.lt_two_pow`). -/
theorem nat_le_two_pow (n : ℕ) : (n : ℤ) ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ m ih => rw [pow_succ]; have := two_pow_pos m; omega

/-- Every integer is bounded by a power of two (both sides).  Choice-free.  Used to extract
a magnitude bound for an operational real (prerequisite for multiplication). -/
theorem int_two_pow_bound (z : ℤ) : ∃ B : ℕ, z ≤ 2 ^ B ∧ -(2 ^ B) ≤ z := by
  refine ⟨z.natAbs, ?_, ?_⟩
  · have h1 : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
    have h2 : (z.natAbs : ℤ) ≤ 2 ^ z.natAbs := nat_le_two_pow z.natAbs
    omega
  · have h1 : -z ≤ (z.natAbs : ℤ) := by
      have h := Int.le_natAbs (a := -z); rwa [Int.natAbs_neg] at h
    have h2 : (z.natAbs : ℤ) ≤ 2 ^ z.natAbs := nat_le_two_pow z.natAbs
    omega

/-- Cancel a positive power: `a · 2^N ≤ 2^(E+N) → a ≤ 2^E`.  Choice-free via
`Int.le_of_mul_le_mul_right`. -/
theorem le_of_mul_two_pow {a : ℤ} {E N : ℕ} (h : a * 2 ^ N ≤ 2 ^ (E + N)) : a ≤ 2 ^ E := by
  have e : (2 : ℤ) ^ (E + N) = 2 ^ E * 2 ^ N := by rw [pow_add]
  rw [e] at h
  exact Int.le_of_mul_le_mul_right h (two_pow_pos N)

/-- Lower analogue: `-(2^(E+N)) ≤ a · 2^N → -(2^E) ≤ a`.  Choice-free. -/
theorem neg_le_of_mul_two_pow {a : ℤ} {E N : ℕ} (h : -(2 ^ (E + N)) ≤ a * 2 ^ N) :
    -(2 ^ E) ≤ a := by
  have e : (2 : ℤ) ^ (E + N) = 2 ^ E * 2 ^ N := by rw [pow_add]
  have e2 : -((2 : ℤ) ^ E * 2 ^ N) = (-(2 : ℤ) ^ E) * 2 ^ N := by ring
  rw [e, e2] at h
  exact Int.le_of_mul_le_mul_right h (two_pow_pos N)

/-- Euclidean-division bracket: for `0 < d`, `d·(z.ediv d) ≤ z < d·(z.ediv d) + d`.
The foundation for the floor-division product sequence (multiplication).  Choice-free
(`Int.ediv_add_emod`/`emod_nonneg`/`emod_lt_of_pos` are all `[propext]`; split the `∧`
into separate `omega`s — `omega` on a conjunction pulls choice, CONT-8). -/
theorem int_ediv_bracket (z : ℤ) {d : ℤ} (hd : 0 < d) :
    d * (z.ediv d) ≤ z ∧ z < d * (z.ediv d) + d := by
  have h1 : d * (z.ediv d) + z.emod d = z := Int.mul_ediv_add_emod z d
  have h2 : 0 ≤ z.emod d := Int.emod_nonneg z (by omega)
  have h3 : z.emod d < d := Int.emod_lt_of_pos z hd
  refine ⟨?_, ?_⟩ <;> omega

/-- **Signed product bound**: `|A| ≤ P` and `|C| ≤ Q` give `-(P·Q) ≤ A·C ≤ P·Q`.
Choice-free — by sign cases (`Int.lt_or_le`) using only `Int.mul_*` lemmas (`abs_mul` pulls
`Classical.choice`; so does the general `mul_le_mul`/`mul_zero`). -/
theorem mul_abs_bound {A C P Q : ℤ} (hA1 : -P ≤ A) (hA2 : A ≤ P) (hC1 : -Q ≤ C) (hC2 : C ≤ Q) :
    -(P * Q) ≤ A * C ∧ A * C ≤ P * Q := by
  have hP : 0 ≤ P := by omega
  have hQ : 0 ≤ Q := by omega
  have hPQ : 0 ≤ P * Q := Int.mul_nonneg hP hQ
  rcases Int.lt_or_le 0 A with hA | hA <;> rcases Int.lt_or_le 0 C with hC | hC
  · -- 0 < A, 0 < C
    have hAn : 0 ≤ A := by omega
    have hCn : 0 ≤ C := by omega
    have hu : A * C ≤ P * Q := Int.mul_le_mul hA2 hC2 hCn hP
    have hl : 0 ≤ A * C := Int.mul_nonneg hAn hCn
    exact ⟨by omega, by omega⟩
  · -- 0 < A, C ≤ 0
    have hAn : 0 ≤ A := by omega
    have hnc : 0 ≤ -C := by omega
    have hle : 0 ≤ A * (-C) := Int.mul_nonneg hAn hnc
    have ee : A * (-C) = -(A * C) := by ring
    rw [ee] at hle
    have h1 : A * (-Q) ≤ A * C := Int.mul_le_mul_of_nonneg_left hC1 hAn
    have h2 : A * Q ≤ P * Q := Int.mul_le_mul_of_nonneg_right hA2 hQ
    have e2 : A * (-Q) = -(A * Q) := by ring
    rw [e2] at h1
    exact ⟨by omega, by omega⟩
  · -- A ≤ 0, 0 < C
    have hCn : 0 ≤ C := by omega
    have hna : 0 ≤ -A := by omega
    have hle : 0 ≤ (-A) * C := Int.mul_nonneg hna hCn
    have ee : (-A) * C = -(A * C) := by ring
    rw [ee] at hle
    have h1 : (-P) * C ≤ A * C := Int.mul_le_mul_of_nonneg_right hA1 hCn
    have h2 : P * C ≤ P * Q := Int.mul_le_mul_of_nonneg_left hC2 hP
    have e2 : (-P) * C = -(P * C) := by ring
    rw [e2] at h1
    exact ⟨by omega, by omega⟩
  · -- A ≤ 0, C ≤ 0
    have hna : 0 ≤ -A := by omega
    have hnc : 0 ≤ -C := by omega
    have hl : 0 ≤ (-A) * (-C) := Int.mul_nonneg hna hnc
    have ee : (-A) * (-C) = A * C := by ring
    rw [ee] at hl
    have hu : (-A) * (-C) ≤ P * Q := Int.mul_le_mul (by omega) (by omega) hnc hP
    have ee2 : (-A) * (-C) = A * C := by ring
    rw [ee2] at hu
    exact ⟨by omega, by omega⟩

/-- Bridge: cross-multiplied bounds `D·2^p` within `±2^(E+p)` give the clean `±2^E` bound. -/
theorem abs_le_two_pow_of_mul {D : ℤ} {p E : ℕ}
    (hu : D * 2 ^ p ≤ 2 ^ (E + p)) (hl : -(2 ^ (E + p)) ≤ D * 2 ^ p) :
    -(2 ^ E) ≤ D ∧ D ≤ 2 ^ E :=
  ⟨neg_le_of_mul_two_pow hl, le_of_mul_two_pow hu⟩

/-- Bridge: scaling a magnitude bound by a power.  `|X| ≤ 2^B → |2^n · X| ≤ 2^(n+B)`. -/
theorem two_pow_mul_abs_bound {X : ℤ} {n B : ℕ} (hl : -(2 ^ B) ≤ X) (hu : X ≤ 2 ^ B) :
    -(2 ^ (n + B)) ≤ 2 ^ n * X ∧ 2 ^ n * X ≤ 2 ^ (n + B) := by
  have h := mul_abs_bound (A := (2:ℤ) ^ n) (P := (2:ℤ) ^ n) (C := X) (Q := (2:ℤ) ^ B)
    (by have := two_pow_nonneg n; omega) (by omega) hl hu
  have e : (2 : ℤ) ^ n * 2 ^ B = 2 ^ (n + B) := by rw [pow_add]
  rw [e] at h
  exact h

/-- **Cross identity for the product** (the algebraic backbone of multiplication's
Cauchyness): clearing denominators turns the product Cauchy expression into integers.
Choice-free (`pow_add`, `two_mul`, `ring`). -/
theorem mul_cross_pow (a b : ℤ) (m n : ℕ) :
    2 ^ (m + n) * (a * 2 ^ n - b * 2 ^ m)
      = 2 ^ (2 * n) * (2 ^ m * a) - 2 ^ (2 * m) * (2 ^ n * b) := by
  have e1 : (2 : ℤ) ^ (m + n) = 2 ^ m * 2 ^ n := by rw [pow_add]
  have e2 : (2 : ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  have e3 : (2 : ℤ) ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [e1, e2, e3]; ring

/-- Generic dyadic bound: if `0 ≤ D < 2^m` and `k ≤ n` then `D · 2^k ≤ 2^(m+n)`.
Choice-free (`Int.mul_le_mul_of_nonneg_right`, `pow_add`, `two_pow_le_add`, `omega`). -/
theorem dyadic_bound {D : ℤ} {m n k : ℕ} (h1 : D < 2 ^ m) (hk : k ≤ n) :
    D * 2 ^ k ≤ 2 ^ (m + n) := by
  have hD : D ≤ 2 ^ m - 1 := by omega
  have step1 : D * 2 ^ k ≤ (2 ^ m - 1) * 2 ^ k :=
    Int.mul_le_mul_of_nonneg_right hD (two_pow_nonneg k)
  have step2 : ((2 : ℤ) ^ m - 1) * 2 ^ k = 2 ^ m * 2 ^ k - 2 ^ k := by ring
  have step3 : (2 : ℤ) ^ m * 2 ^ k = 2 ^ (m + k) := by rw [← pow_add]
  have step4 : (2 : ℤ) ^ (m + k) ≤ 2 ^ (m + n) := by
    have h := two_pow_le_add (m + k) (n - k)
    rwa [show (m + k) + (n - k) = m + n from by omega] at h
  have h2k := two_pow_nonneg k
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
#print axioms nat_le_two_pow
#print axioms int_two_pow_bound
#print axioms le_of_mul_two_pow
#print axioms neg_le_of_mul_two_pow
#print axioms int_ediv_bracket
#print axioms mul_cross_pow
#print axioms mul_abs_bound
#print axioms abs_le_two_pow_of_mul
#print axioms two_pow_mul_abs_bound

end VRCycle.Continuum
