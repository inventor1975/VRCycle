-- VRCycle/Continuum/Real.lean
-- Operational Continuum (Path 1) — Operational ℝ, M1: the real type, below the choice floor.
--
-- STAGE: ℝ / M1. SOURCE: PLAN_OPERATIONAL_REAL.md.
--
-- ## Representation (M0, revisited)
-- An operational real is a sequence `seq : ℕ → ℤ` (value `lim seq n / 2^n`) that is
-- **asymptotically Cauchy**: `∀ k, ∃ N, ∀ m,n ≥ N, |seq m·2^n - seq n·2^m|·2^k ≤ 2^(m+n)`
-- — pure `ℤ`, two-sided bounds (no `natAbs`/`ℚ`/`ℝ`).  The `∀k∃N` form is **ring-closed**
-- (a fixed-constant coherence is NOT — it doubles under `+`; see PLAN M0-revisit).
-- This keeps the whole construction BELOW the `Classical.choice` floor.
--
-- ## Milestones: M1 (type + equality) · M2 (order/apartness) · M3 (ring: neg done, +/* next).
-- Every branch's `[0,1]` point (`intval α` from `UnitInterval.lean`) is a `Pre`; the Cauchy
-- proof goes via `intval_prefix`/`intval_diff_bound`/`dyadic_bound`.  All `[propext, Quot.sound]`.

import VRCycle.Continuum.UnitInterval

namespace VRCycle.Continuum

/-- A pre-real: a sequence of integer numerators (`seq n` approximates `value · 2^n`) that
is **asymptotically Cauchy** — for every precision `k`, eventually any two stages agree:
`|seq m · 2^n - seq n · 2^m| · 2^k ≤ 2^(m+n)` (two-sided `ℤ` bounds, no `ℚ`/`natAbs`).
This `∀k∃N` form is **ring-closed** (unlike a fixed-constant coherence — see PLAN M0-revisit). -/
structure Pre where
  /-- The integer numerators; `seq n` approximates `value · 2^n`. -/
  seq : ℕ → ℤ
  /-- Asymptotic Cauchyness: `∀k`, eventually all pairs agree to precision `2^{-k}`. -/
  cauchy : ∀ k : ℕ, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    (seq m * 2 ^ n - seq n * 2 ^ m) * 2 ^ k ≤ 2 ^ (m + n) ∧
      -(2 ^ (m + n)) ≤ (seq m * 2 ^ n - seq n * 2 ^ m) * 2 ^ k

/-- Every branch names a pre-real in `[0,1]`: its `[0,1]` point `intval α` is a dyadic
Cauchy sequence (`2·intval n - intval (n+1) = -bit ∈ {-1,0}`).  Choice-free. -/
def Pre.ofBranch (α : Branch) : Pre where
  seq := intval α
  cauchy := by
    intro k
    refine ⟨k, fun m n hm hn => ?_⟩
    rcases Nat.le_total n m with hnm | hmn
    · -- n ≤ m: the difference is in [0, 2^m); bound it directly.
      obtain ⟨hb0, hb1⟩ := intval_diff_bound α hnm
      have hup := dyadic_bound hb1 hn
      have h0 := Int.mul_nonneg hb0 (two_pow_nonneg k)
      have hge : (0 : ℤ) ≤ 2 ^ (m + n) := two_pow_nonneg _
      exact ⟨by omega, by omega⟩
    · -- m ≤ n: the difference is the negation of one in [0, 2^n).
      obtain ⟨hb0, hb1⟩ := intval_diff_bound α hmn
      have hup := dyadic_bound hb1 hm
      have h0 := Int.mul_nonneg hb0 (two_pow_nonneg k)
      have hcomm : (intval α m * 2 ^ n - intval α n * 2 ^ m) * 2 ^ k
                 = -((intval α n * 2 ^ m - intval α m * 2 ^ n) * 2 ^ k) := by ring
      have hsym : (2 : ℤ) ^ (n + m) = 2 ^ (m + n) := by rw [Nat.add_comm]
      have hge : (0 : ℤ) ≤ 2 ^ (m + n) := two_pow_nonneg _
      rw [hcomm]
      exact ⟨by omega, by omega⟩

-- ============================================================
-- §M1.2  Equality of operational reals (asymptotic agreement)
-- ============================================================

/-- Two pre-reals are **equal** when their values agree to every precision: for each `k`,
eventually `|x.seq n - y.seq n| · 2^k ≤ 2^n` (i.e. `|x_n/2^n - y_n/2^n| ≤ 2^{-k}`).
Two-sided `ℤ` bounds, no `natAbs`; cross-multiplied to avoid `ℚ`. -/
def Pre.equiv (x y : Pre) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (x.seq n - y.seq n) * 2 ^ k ≤ 2 ^ n ∧ -(2 ^ n) ≤ (x.seq n - y.seq n) * 2 ^ k

theorem Pre.equiv_refl (x : Pre) : Pre.equiv x x := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  have hp := two_pow_nonneg n
  have h0 : (x.seq n - x.seq n) * 2 ^ k = 0 := by ring
  rw [h0]
  exact ⟨by omega, by omega⟩

theorem Pre.equiv_symm {x y : Pre} (h : Pre.equiv x y) : Pre.equiv y x := by
  intro k
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have he : (y.seq n - x.seq n) * 2 ^ k = -((x.seq n - y.seq n) * 2 ^ k) := by ring
  rw [he]
  exact ⟨by omega, by omega⟩

theorem Pre.equiv_trans {x y z : Pre} (hxy : Pre.equiv x y) (hyz : Pre.equiv y z) :
    Pre.equiv x z := by
  intro k
  obtain ⟨N1, h1⟩ := hxy (k + 1)
  obtain ⟨N2, h2⟩ := hyz (k + 1)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  obtain ⟨ha1, ha2⟩ := h1 n (by omega)
  obtain ⟨hb1, hb2⟩ := h2 n (by omega)
  have key : 2 * ((x.seq n - z.seq n) * 2 ^ k)
           = (x.seq n - y.seq n) * 2 ^ (k + 1) + (y.seq n - z.seq n) * 2 ^ (k + 1) := by
    rw [pow_succ]; ring
  exact ⟨by omega, by omega⟩

/-- Operational reals form a setoid under asymptotic agreement. -/
instance Pre.setoid : Setoid Pre :=
  ⟨Pre.equiv, ⟨Pre.equiv_refl, Pre.equiv_symm, Pre.equiv_trans⟩⟩

/-- **The operational reals**: pre-reals up to asymptotic agreement.  Entirely over `ℤ`,
below the `ℚ`/`ℝ` `Classical.choice` floor. -/
def Real : Type := Quotient Pre.setoid

/-- The operational real named by a branch (its `[0,1]` point). -/
def Real.ofBranch (α : Branch) : Real := Quotient.mk _ (Pre.ofBranch α)

-- ============================================================
-- §M3  Ring: negation (addition/multiplication next, on the ring-closed Cauchy form)
-- ============================================================

/-- **Negation** of an operational real: flip every numerator.  Asymptotic Cauchyness is
preserved (the Cauchy expression just negates — sign-symmetric).  Choice-free. -/
def Pre.neg (x : Pre) : Pre where
  seq := fun n => - x.seq n
  cauchy := by
    intro k
    obtain ⟨N, hN⟩ := x.cauchy k
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN m n hm hn
    have he : ((-x.seq m) * 2 ^ n - (-x.seq n) * 2 ^ m) * 2 ^ k
            = -((x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k) := by ring
    rw [he]
    exact ⟨by omega, by omega⟩

/-- **Addition** of operational reals: add numerators stage-wise.  Asymptotic Cauchyness is
preserved — the Cauchy expression splits as the sum of `x`'s and `y`'s, and the factor 2 is
absorbed by taking the witnesses at precision `k+1` (the `ring`+`omega` strait technique). -/
def Pre.add (x y : Pre) : Pre where
  seq := fun n => x.seq n + y.seq n
  cauchy := by
    intro k
    obtain ⟨N1, hX⟩ := x.cauchy (k + 1)
    obtain ⟨N2, hY⟩ := y.cauchy (k + 1)
    refine ⟨max N1 N2, fun m n hm hn => ?_⟩
    obtain ⟨hx1, hx2⟩ := hX m n (by omega) (by omega)
    obtain ⟨hy1, hy2⟩ := hY m n (by omega) (by omega)
    have key : 2 * (((x.seq m + y.seq m) * 2 ^ n - (x.seq n + y.seq n) * 2 ^ m) * 2 ^ k)
             = (x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ (k + 1)
             + (y.seq m * 2 ^ n - y.seq n * 2 ^ m) * 2 ^ (k + 1) := by
      rw [pow_succ]; ring
    exact ⟨by omega, by omega⟩

-- ============================================================
-- §M3.2  Lifting negation and addition to `Real` (the quotient)
-- ============================================================

/-- Negation respects equality of reals (congruence). -/
theorem Pre.neg_respects {x₁ x₂ : Pre} (h : Pre.equiv x₁ x₂) :
    Pre.equiv (Pre.neg x₁) (Pre.neg x₂) := by
  intro k
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  simp only [Pre.neg]
  have he : ((-x₁.seq n) - (-x₂.seq n)) * 2 ^ k = -((x₁.seq n - x₂.seq n) * 2 ^ k) := by ring
  rw [he]
  exact ⟨by omega, by omega⟩

/-- Addition respects equality of reals (congruence in both arguments). -/
theorem Pre.add_respects {x₁ x₂ y₁ y₂ : Pre} (hx : Pre.equiv x₁ x₂) (hy : Pre.equiv y₁ y₂) :
    Pre.equiv (Pre.add x₁ y₁) (Pre.add x₂ y₂) := by
  intro k
  obtain ⟨N1, hX⟩ := hx (k + 1)
  obtain ⟨N2, hY⟩ := hy (k + 1)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  obtain ⟨hx1, hx2⟩ := hX n (by omega)
  obtain ⟨hy1, hy2⟩ := hY n (by omega)
  simp only [Pre.add]
  have key : 2 * (((x₁.seq n + y₁.seq n) - (x₂.seq n + y₂.seq n)) * 2 ^ k)
           = (x₁.seq n - x₂.seq n) * 2 ^ (k + 1) + (y₁.seq n - y₂.seq n) * 2 ^ (k + 1) := by
    rw [pow_succ]; ring
  exact ⟨by omega, by omega⟩

/-- Negation on `Real`. -/
def Real.neg : Real → Real :=
  Quotient.lift (fun x => (⟦Pre.neg x⟧ : Real)) (fun _ _ h => Quotient.sound (Pre.neg_respects h))

/-- Addition on `Real`. -/
def Real.add : Real → Real → Real :=
  Quotient.lift₂ (fun x y => (⟦Pre.add x y⟧ : Real))
    (fun _ _ _ _ hx hy => Quotient.sound (Pre.add_respects hx hy))

-- ============================================================
-- §M4  Constants: the integer embedding (gives 0 and 1)
-- ============================================================

/-- The operational real of an integer `z`: numerators `z · 2^n` (value `z`).  The Cauchy
expression is identically `0`, so Cauchyness is trivial.  Choice-free. -/
def Pre.ofInt (z : ℤ) : Pre where
  seq := fun n => z * 2 ^ n
  cauchy := by
    intro k
    refine ⟨0, fun m n _ _ => ?_⟩
    have h0 : (z * 2 ^ m * 2 ^ n - z * 2 ^ n * 2 ^ m) * 2 ^ k = 0 := by ring
    have hge : (0 : ℤ) ≤ 2 ^ (m + n) := two_pow_nonneg _
    rw [h0]
    exact ⟨by omega, by omega⟩

/-- The integer embedding `ℤ → Real`. -/
def Real.ofInt (z : ℤ) : Real := (⟦Pre.ofInt z⟧ : Real)

instance : Zero Real := ⟨Real.ofInt 0⟩
instance : One Real := ⟨Real.ofInt 1⟩
instance : Add Real := ⟨Real.add⟩
instance : Neg Real := ⟨Real.neg⟩

-- ============================================================
-- §M4.2  The additive group structure (all laws reduce to pointwise ℤ equalities)
-- ============================================================

/-- Pre-reals with pointwise-equal numerators are equal reals (the Cauchy expression
vanishes).  The workhorse for the ring laws. -/
theorem Pre.equiv_of_seq {x y : Pre} (h : ∀ n, x.seq n = y.seq n) : Pre.equiv x y := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  have hz : (x.seq n - y.seq n) * 2 ^ k = 0 := by rw [h n]; ring
  have hge := two_pow_nonneg n
  rw [hz]
  exact ⟨by omega, by omega⟩

theorem Real.add_comm (a b : Real) : a + b = b + a := by
  refine Quotient.inductionOn₂ a b (fun x y => Quotient.sound (Pre.equiv_of_seq ?_))
  intro n; simp only [Pre.add]; ring

theorem Real.add_assoc (a b c : Real) : a + b + c = a + (b + c) := by
  refine Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (Pre.equiv_of_seq ?_))
  intro n; simp only [Pre.add]; ring

theorem Real.add_zero (a : Real) : a + 0 = a := by
  refine Quotient.inductionOn a (fun x => Quotient.sound (Pre.equiv_of_seq ?_))
  intro n; simp only [Pre.add, Pre.ofInt]; ring

theorem Real.zero_add (a : Real) : 0 + a = a := by
  refine Quotient.inductionOn a (fun x => Quotient.sound (Pre.equiv_of_seq ?_))
  intro n; simp only [Pre.add, Pre.ofInt]; ring

theorem Real.neg_add_cancel (a : Real) : -a + a = 0 := by
  refine Quotient.inductionOn a (fun x => Quotient.sound (Pre.equiv_of_seq ?_))
  intro n; simp only [Pre.add, Pre.neg, Pre.ofInt]; ring

-- ============================================================
-- §M5.0  Boundedness (Cauchy ⇒ bounded — prerequisite for multiplication)
-- ============================================================

/-- Every operational real is **bounded**: there are `B, N` with `|x.seq m| ≤ 2^(m+B)` for
all `m ≥ N` (i.e. `|value| ≤ 2^B`).  From `cauchy 0` at the anchor `N`, dividing by `2^N`
via the choice-free cancellation `le_of_mul_two_pow`. -/
theorem Pre.bounded (x : Pre) : ∃ (B N : ℕ), ∀ m, N ≤ m →
    x.seq m ≤ 2 ^ (m + B) ∧ -(2 ^ (m + B)) ≤ x.seq m := by
  obtain ⟨N, hN⟩ := x.cauchy 0
  obtain ⟨B0, hu0, hl0⟩ := int_two_pow_bound (x.seq N)
  refine ⟨max B0 N + 1 - N, N, fun m hm => ?_⟩
  obtain ⟨hcu, hcl⟩ := hN m N hm (Nat.le_refl N)
  rw [pow_zero, mul_one] at hcu hcl
  set C := max B0 N + 1 with hCdef
  have hmnn := two_pow_nonneg m
  have emN : (2 : ℤ) ^ (m + N) = 2 ^ N * 2 ^ m := by rw [pow_add]; ring
  -- 2^B0 + 2^N ≤ 2^C
  have hsum : (2 : ℤ) ^ B0 + 2 ^ N ≤ 2 ^ C := by
    have ha : (2 : ℤ) ^ B0 ≤ 2 ^ (max B0 N) := by
      have h := two_pow_le_add B0 (max B0 N - B0)
      rwa [show B0 + (max B0 N - B0) = max B0 N from by omega] at h
    have hb : (2 : ℤ) ^ N ≤ 2 ^ (max B0 N) := by
      have h := two_pow_le_add N (max B0 N - N)
      rwa [show N + (max B0 N - N) = max B0 N from by omega] at h
    have hCe : (2 : ℤ) ^ C = 2 * 2 ^ (max B0 N) := by rw [hCdef, pow_succ]; ring
    omega
  have hexp : m + C = (m + (C - N)) + N := by omega
  refine ⟨?_, ?_⟩
  · -- upper
    have hxNu : x.seq N * 2 ^ m ≤ 2 ^ B0 * 2 ^ m :=
      Int.mul_le_mul_of_nonneg_right hu0 hmnn
    have hringR : ((2:ℤ) ^ B0 + 2 ^ N) * 2 ^ m = 2 ^ B0 * 2 ^ m + 2 ^ N * 2 ^ m := by ring
    have hmul : ((2:ℤ) ^ B0 + 2 ^ N) * 2 ^ m ≤ 2 ^ C * 2 ^ m :=
      Int.mul_le_mul_of_nonneg_right hsum hmnn
    have hprod : (2 : ℤ) ^ (m + C) = 2 ^ C * 2 ^ m := by rw [pow_add]; ring
    have hfin : x.seq m * 2 ^ N ≤ 2 ^ (m + C) := by rw [hprod]; omega
    rw [hexp] at hfin
    exact le_of_mul_two_pow hfin
  · -- lower
    have hxNl : -(2 ^ B0) * 2 ^ m ≤ x.seq N * 2 ^ m :=
      Int.mul_le_mul_of_nonneg_right hl0 hmnn
    have hringR : -(((2:ℤ) ^ B0 + 2 ^ N) * 2 ^ m) = -(2 ^ B0) * 2 ^ m - 2 ^ N * 2 ^ m := by ring
    have hmul : ((2:ℤ) ^ B0 + 2 ^ N) * 2 ^ m ≤ 2 ^ C * 2 ^ m :=
      Int.mul_le_mul_of_nonneg_right hsum hmnn
    have hprod : (2 : ℤ) ^ (m + C) = 2 ^ C * 2 ^ m := by rw [pow_add]; ring
    have hfin : -(2 ^ (m + C)) ≤ x.seq m * 2 ^ N := by rw [hprod]; omega
    rw [hexp] at hfin
    exact neg_le_of_mul_two_pow hfin

/-- **Multiplication** of operational reals: `seq n = (x.seq n · y.seq n) ediv 2^n`.
Cauchyness via the product error analysis (PLAN / memory).  Choice-free. -/
def Pre.mul (x y : Pre) : Pre where
  seq := fun n => (x.seq n * y.seq n).ediv (2 ^ n)
  cauchy := by
    intro k
    obtain ⟨Bx, Nx, hbx⟩ := x.bounded
    obtain ⟨By, Ny, hby⟩ := y.bounded
    obtain ⟨Nxc, hxc⟩ := x.cauchy (k + By + 2)
    obtain ⟨Nyc, hyc⟩ := y.cauchy (k + Bx + 2)
    refine ⟨max (max Nx Ny) (max Nxc Nyc) + (k + Bx + By + 2), fun m n hm hn => ?_⟩
    obtain ⟨hbxm1, hbxm2⟩ := hbx m (by omega)
    obtain ⟨hbyn1, hbyn2⟩ := hby n (by omega)
    -- |x.seq m * 2^n| ≤ 2^(m+n+Bx)
    obtain ⟨hAl, hAu⟩ := mul_abs_bound (A := x.seq m) (P := (2:ℤ) ^ (m + Bx))
      (C := (2:ℤ) ^ n) (Q := (2:ℤ) ^ n) hbxm2 hbxm1 (by have := two_pow_nonneg n; omega) (by omega)
    have hApow : (2:ℤ) ^ (m + Bx) * 2 ^ n = 2 ^ (m + n + Bx) := by rw [← pow_add]; congr 1; omega
    rw [hApow] at hAl hAu
    -- |y.seq n * 2^m| ≤ 2^(m+n+By)
    obtain ⟨hBl, hBu⟩ := mul_abs_bound (A := y.seq n) (P := (2:ℤ) ^ (n + By))
      (C := (2:ℤ) ^ m) (Q := (2:ℤ) ^ m) hbyn2 hbyn1 (by have := two_pow_nonneg m; omega) (by omega)
    have hBpow : (2:ℤ) ^ (n + By) * 2 ^ m = 2 ^ (m + n + By) := by rw [← pow_add]; congr 1; omega
    rw [hBpow] at hBl hBu
    -- x-difference A - A' bound ±2^(m+n-(k+By+2))
    obtain ⟨hdx1, hdx2⟩ := hxc m n (by omega) (by omega)
    have hdxre : (2:ℤ) ^ (m + n) = 2 ^ ((m + n - (k + By + 2)) + (k + By + 2)) := by
      congr 1; omega
    rw [hdxre] at hdx1 hdx2
    obtain ⟨hAA1, hAA2⟩ := abs_le_two_pow_of_mul hdx1 hdx2
    -- y-difference B - B' bound ±2^(m+n-(k+Bx+2))
    obtain ⟨hdy1, hdy2⟩ := hyc m n (by omega) (by omega)
    have hdyre : (2:ℤ) ^ (m + n) = 2 ^ ((m + n - (k + Bx + 2)) + (k + Bx + 2)) := by
      congr 1; omega
    rw [hdyre] at hdy1 hdy2
    obtain ⟨hBB1, hBB2⟩ := abs_le_two_pow_of_mul hdy1 hdy2
    -- product bounds A·(B-B') and B'·(A-A'), each ±2^(2(m+n)-k-2)
    obtain ⟨hP1l, hP1u⟩ := mul_abs_bound (A := x.seq m * 2 ^ n) (P := (2:ℤ) ^ (m + n + Bx))
      (C := y.seq m * 2 ^ n - y.seq n * 2 ^ m) (Q := (2:ℤ) ^ (m + n - (k + Bx + 2)))
      hAl hAu hBB1 hBB2
    have hP1pow : (2:ℤ) ^ (m + n + Bx) * 2 ^ (m + n - (k + Bx + 2))
        = 2 ^ (2 * (m + n) - k - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hP1pow] at hP1l hP1u
    obtain ⟨hP2l, hP2u⟩ := mul_abs_bound (A := y.seq n * 2 ^ m) (P := (2:ℤ) ^ (m + n + By))
      (C := x.seq m * 2 ^ n - x.seq n * 2 ^ m) (Q := (2:ℤ) ^ (m + n - (k + By + 2)))
      hBl hBu hAA1 hAA2
    have hP2pow : (2:ℤ) ^ (m + n + By) * 2 ^ (m + n - (k + By + 2))
        = 2 ^ (2 * (m + n) - k - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hP2pow] at hP2l hP2u
    -- floor brackets (s-terms)
    obtain ⟨hsm0, hsm1⟩ := int_ediv_bracket (x.seq m * y.seq m) (two_pow_pos m)
    obtain ⟨hsn0, hsn1⟩ := int_ediv_bracket (x.seq n * y.seq n) (two_pow_pos n)
    set Pm := (x.seq m * y.seq m).ediv (2 ^ m) with hPmdef
    set Pn := (x.seq n * y.seq n).ediv (2 ^ n) with hPndef
    -- big identity (clear denominators)
    have hID : 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m)
             = 2 ^ (2 * n) * (2 ^ m * Pm) - 2 ^ (2 * m) * (2 ^ n * Pn) := mul_cross_pow Pm Pn m n
    have hMAIN : 2 ^ (2 * n) * (x.seq m * y.seq m) - 2 ^ (2 * m) * (x.seq n * y.seq n)
             = (x.seq m * 2 ^ n) * (y.seq m * 2 ^ n - y.seq n * 2 ^ m)
             + (y.seq n * 2 ^ m) * (x.seq m * 2 ^ n - x.seq n * 2 ^ m) := by
      have e2n : (2:ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
      have e2m : (2:ℤ) ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
      rw [e2n, e2m]; ring
    -- E = 2^(m+n)·D expressed via products and s-terms
    have hE : 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m)
            = (x.seq m * 2 ^ n) * (y.seq m * 2 ^ n - y.seq n * 2 ^ m)
            + (y.seq n * 2 ^ m) * (x.seq m * 2 ^ n - x.seq n * 2 ^ m)
            - 2 ^ (2 * n) * (x.seq m * y.seq m - 2 ^ m * Pm)
            + 2 ^ (2 * m) * (x.seq n * y.seq n - 2 ^ n * Pn) := by
      rw [hID, ← hMAIN]; ring
    have hTnn : (0:ℤ) ≤ 2 ^ (2 * (m + n) - k - 2) := two_pow_nonneg _
    have hSMl : (0:ℤ) ≤ 2 ^ (2 * n) * (x.seq m * y.seq m - 2 ^ m * Pm) :=
      Int.mul_nonneg (two_pow_nonneg _) (by omega)
    have hSMu : 2 ^ (2 * n) * (x.seq m * y.seq m - 2 ^ m * Pm) ≤ 2 ^ (2 * (m + n) - k - 2) := by
      have hb := Int.mul_le_mul_of_nonneg_left
        (by omega : x.seq m * y.seq m - 2 ^ m * Pm ≤ 2 ^ m) (two_pow_nonneg (2 * n))
      have hpw : (2:ℤ) ^ (2 * n) * 2 ^ m = 2 ^ (2 * n + m) := by rw [← pow_add]
      have hpw2 : (2:ℤ) ^ (2 * n + m) ≤ 2 ^ (2 * (m + n) - k - 2) := by
        have h := two_pow_le_add (2 * n + m) (2 * (m + n) - k - 2 - (2 * n + m))
        have heqs : (2 * n + m) + (2 * (m + n) - k - 2 - (2 * n + m))
            = 2 * (m + n) - k - 2 := by omega
        rwa [heqs] at h
      rw [hpw] at hb; omega
    have hSNl : (0:ℤ) ≤ 2 ^ (2 * m) * (x.seq n * y.seq n - 2 ^ n * Pn) :=
      Int.mul_nonneg (two_pow_nonneg _) (by omega)
    have hSNu : 2 ^ (2 * m) * (x.seq n * y.seq n - 2 ^ n * Pn) ≤ 2 ^ (2 * (m + n) - k - 2) := by
      have hb := Int.mul_le_mul_of_nonneg_left
        (by omega : x.seq n * y.seq n - 2 ^ n * Pn ≤ 2 ^ n) (two_pow_nonneg (2 * m))
      have hpw : (2:ℤ) ^ (2 * m) * 2 ^ n = 2 ^ (2 * m + n) := by rw [← pow_add]
      have hpw2 : (2:ℤ) ^ (2 * m + n) ≤ 2 ^ (2 * (m + n) - k - 2) := by
        have h := two_pow_le_add (2 * m + n) (2 * (m + n) - k - 2 - (2 * m + n))
        have heqs : (2 * m + n) + (2 * (m + n) - k - 2 - (2 * m + n))
            = 2 * (m + n) - k - 2 := by omega
        rwa [heqs] at h
      rw [hpw] at hb; omega
    have hT4 : (2:ℤ) ^ (2 * (m + n) - k) = 4 * 2 ^ (2 * (m + n) - k - 2) := by
      set e := 2 * (m + n) - k - 2 with he_def
      have hee : 2 * (m + n) - k = e + 1 + 1 := by omega
      rw [hee, pow_succ, pow_succ]; ring
    have hEu : 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m) ≤ 2 ^ (2 * (m + n) - k) := by
      rw [hE]; omega
    have hEl : -(2 ^ (2 * (m + n) - k)) ≤ 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m) := by
      rw [hE]; omega
    -- cancel 2^(m+n)
    have hpos := two_pow_pos (m + n)
    have h2 : (2:ℤ) ^ (2 * (m + n) - k) * 2 ^ k = 2 ^ (m + n) * 2 ^ (m + n) := by
      rw [← pow_add, show (2 * (m + n) - k) + k = (m + n) + (m + n) from by omega, pow_add]
    refine ⟨?_, ?_⟩
    · have h1 := Int.mul_le_mul_of_nonneg_right hEu (two_pow_nonneg k)
      have hr : 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m) * 2 ^ k
              = 2 ^ (m + n) * ((Pm * 2 ^ n - Pn * 2 ^ m) * 2 ^ k) := by ring
      rw [h2, hr] at h1
      exact Int.le_of_mul_le_mul_left h1 hpos
    · have h1 := Int.mul_le_mul_of_nonneg_right hEl (two_pow_nonneg k)
      have hl : -(2:ℤ) ^ (2 * (m + n) - k) * 2 ^ k = 2 ^ (m + n) * (-(2 ^ (m + n))) := by
        have e : -(2:ℤ) ^ (2 * (m + n) - k) * 2 ^ k = -(2 ^ (2 * (m + n) - k) * 2 ^ k) := by ring
        rw [e, h2]; ring
      have hr : 2 ^ (m + n) * (Pm * 2 ^ n - Pn * 2 ^ m) * 2 ^ k
              = 2 ^ (m + n) * ((Pm * 2 ^ n - Pn * 2 ^ m) * 2 ^ k) := by ring
      rw [hl, hr] at h1
      exact Int.le_of_mul_le_mul_left h1 hpos

/-- Multiplication is commutative (the numerators commute in `ℤ`, so the sequences are
pointwise equal).  Choice-free. -/
theorem Pre.mul_comm (x y : Pre) : Pre.equiv (Pre.mul x y) (Pre.mul y x) := by
  apply Pre.equiv_of_seq
  intro n
  simp only [Pre.mul]
  rw [Int.mul_comm (x.seq n) (y.seq n)]

/-- `x · 1 = x`: the value `1` is `Pre.ofInt 1` (numerators `2^n`), and `(x_n · 2^n) ediv 2^n
= x_n` exactly.  Pointwise equal, hence equal reals.  Choice-free. -/
theorem Pre.mul_one (x : Pre) : Pre.equiv (Pre.mul x (Pre.ofInt 1)) x := by
  apply Pre.equiv_of_seq
  intro n
  simp only [Pre.mul, Pre.ofInt]
  rw [one_mul]
  exact Int.mul_ediv_cancel _ (by have := two_pow_pos n; omega)

/-- `0 · x = 0` — both sides have all-zero numerators (`(0·x_n) ediv 2^n = 0`).  Choice-free. -/
theorem Pre.zero_mul (x : Pre) : Pre.equiv (Pre.mul (Pre.ofInt 0) x) (Pre.ofInt 0) := by
  apply Pre.equiv_of_seq
  intro n
  have h2 : (Pre.ofInt 0).seq n = 0 := by show (0:ℤ) * 2 ^ n = 0; ring
  have h1 : (Pre.mul (Pre.ofInt 0) x).seq n = 0 := by
    show ((Pre.ofInt 0).seq n * x.seq n).ediv (2 ^ n) = 0
    have hz : (Pre.ofInt 0).seq n * x.seq n = 0 := by rw [h2]; ring
    rw [hz]; exact Int.zero_ediv _
  rw [h1, h2]

/-- **Distributivity** `x·(y+z) = x·y + x·z`.  Over `ℤ` the numerators agree exactly
(`x(y+z) = xy+xz`); the only gap is the discreteness of the floor:
`⌊(a+b)/2^n⌋ - ⌊a/2^n⌋ - ⌊b/2^n⌋ ∈ {0,1}` (constant-bounded), proved by three `int_ediv_bracket`
brackets + `Int.lt_of_mul_lt_mul_left` (cannot divide by `2^n` in `omega`).  Choice-free. -/
theorem Pre.mul_add (x y z : Pre) :
    Pre.equiv (Pre.mul x (Pre.add y z)) (Pre.add (Pre.mul x y) (Pre.mul x z)) := by
  intro k
  refine ⟨k, fun n hn => ?_⟩
  simp only [Pre.mul, Pre.add]
  have hsum : x.seq n * (y.seq n + z.seq n) = x.seq n * y.seq n + x.seq n * z.seq n := by ring
  rw [hsum]
  have hdpos : (0:ℤ) < 2 ^ n := two_pow_pos n
  obtain ⟨hqa0, hqa1⟩ := int_ediv_bracket (x.seq n * y.seq n) hdpos
  obtain ⟨hqb0, hqb1⟩ := int_ediv_bracket (x.seq n * z.seq n) hdpos
  obtain ⟨hqab0, hqab1⟩ := int_ediv_bracket (x.seq n * y.seq n + x.seq n * z.seq n) hdpos
  set qa := (x.seq n * y.seq n).ediv (2 ^ n) with hqa
  set qb := (x.seq n * z.seq n).ediv (2 ^ n) with hqb
  set qab := (x.seq n * y.seq n + x.seq n * z.seq n).ediv (2 ^ n) with hqab
  -- qab - qa - qb ∈ {0,1}: divide the bracket inequalities by 2^n via Int.lt_of_mul_lt_mul_left
  have hlt1 : 2 ^ n * qab < 2 ^ n * (qa + qb + 2) := by
    have e : (2:ℤ) ^ n * (qa + qb + 2) = 2 ^ n * qa + 2 ^ n * qb + 2 * 2 ^ n := by ring
    rw [e]; omega
  have hup : qab < qa + qb + 2 := Int.lt_of_mul_lt_mul_left hlt1 (by omega)
  have hlt2 : 2 ^ n * (qa + qb) < 2 ^ n * (qab + 1) := by
    have e1 : (2:ℤ) ^ n * (qa + qb) = 2 ^ n * qa + 2 ^ n * qb := by ring
    have e2 : (2:ℤ) ^ n * (qab + 1) = 2 ^ n * qab + 2 ^ n := by ring
    rw [e1, e2]; omega
  have hlo : qa + qb < qab + 1 := Int.lt_of_mul_lt_mul_left hlt2 (by omega)
  -- the difference qab - (qa+qb) is 0 or 1; scale by 2^k ≤ 2^n
  have hk : (2:ℤ) ^ k ≤ 2 ^ n := by
    have h := two_pow_le_add k (n - k); rwa [show k + (n - k) = n from by omega] at h
  have hkn := two_pow_nonneg k
  have hub : (qab - (qa + qb)) * 2 ^ k ≤ 1 * 2 ^ k :=
    Int.mul_le_mul_of_nonneg_right (by omega) hkn
  have hlb : (0:ℤ) ≤ (qab - (qa + qb)) * 2 ^ k :=
    Int.mul_nonneg (by omega) hkn
  rw [one_mul] at hub
  have hge : (0:ℤ) ≤ 2 ^ n := two_pow_nonneg n
  exact ⟨by omega, by omega⟩

/-- Multiplication respects equality of reals (congruence) — the gateway to `Real.mul`.
Single-index product error analysis: `x₁y₁ - x₂y₂ = y₁(x₁-x₂) + x₂(y₁-y₂)`, bounded by
`Pre.bounded` magnitudes and `hx/hy` differences via `mul_abs_bound`.  Choice-free. -/
theorem Pre.mul_respects {x₁ x₂ y₁ y₂ : Pre} (hx : Pre.equiv x₁ x₂) (hy : Pre.equiv y₁ y₂) :
    Pre.equiv (Pre.mul x₁ y₁) (Pre.mul x₂ y₂) := by
  intro k
  obtain ⟨Bx, Nx, hbx⟩ := x₂.bounded
  obtain ⟨By, Ny, hby⟩ := y₁.bounded
  obtain ⟨Nxc, hxc⟩ := hx (k + By + 2)
  obtain ⟨Nyc, hyc⟩ := hy (k + Bx + 2)
  refine ⟨max (max Nx Ny) (max Nxc Nyc) + (k + Bx + By + 2), fun n hn => ?_⟩
  simp only [Pre.mul]
  obtain ⟨hby1, hby2⟩ := hby n (by omega)
  obtain ⟨hbx1, hbx2⟩ := hbx n (by omega)
  -- x-difference  |x₁ₙ - x₂ₙ| ≤ 2^(n-(k+By+2))
  obtain ⟨hdx1, hdx2⟩ := hxc n (by omega)
  have hdxre : (2:ℤ) ^ n = 2 ^ ((n - (k + By + 2)) + (k + By + 2)) := by congr 1; omega
  rw [hdxre] at hdx1 hdx2
  obtain ⟨hAA1, hAA2⟩ := abs_le_two_pow_of_mul hdx1 hdx2
  -- y-difference  |y₁ₙ - y₂ₙ| ≤ 2^(n-(k+Bx+2))
  obtain ⟨hdy1, hdy2⟩ := hyc n (by omega)
  have hdyre : (2:ℤ) ^ n = 2 ^ ((n - (k + Bx + 2)) + (k + Bx + 2)) := by congr 1; omega
  rw [hdyre] at hdy1 hdy2
  obtain ⟨hBB1, hBB2⟩ := abs_le_two_pow_of_mul hdy1 hdy2
  -- product bounds, each ±2^(2n-k-2)
  obtain ⟨hP1l, hP1u⟩ := mul_abs_bound (A := y₁.seq n) (P := (2:ℤ) ^ (n + By))
    (C := x₁.seq n - x₂.seq n) (Q := (2:ℤ) ^ (n - (k + By + 2))) hby2 hby1 hAA1 hAA2
  have hP1pow : (2:ℤ) ^ (n + By) * 2 ^ (n - (k + By + 2)) = 2 ^ (2 * n - k - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hP1pow] at hP1l hP1u
  obtain ⟨hP2l, hP2u⟩ := mul_abs_bound (A := x₂.seq n) (P := (2:ℤ) ^ (n + Bx))
    (C := y₁.seq n - y₂.seq n) (Q := (2:ℤ) ^ (n - (k + Bx + 2))) hbx2 hbx1 hBB1 hBB2
  have hP2pow : (2:ℤ) ^ (n + Bx) * 2 ^ (n - (k + Bx + 2)) = 2 ^ (2 * n - k - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hP2pow] at hP2l hP2u
  -- floor brackets (s-terms), single index
  obtain ⟨hs1l, hs1u⟩ := int_ediv_bracket (x₁.seq n * y₁.seq n) (two_pow_pos n)
  obtain ⟨hs2l, hs2u⟩ := int_ediv_bracket (x₂.seq n * y₂.seq n) (two_pow_pos n)
  set P1 := (x₁.seq n * y₁.seq n).ediv (2 ^ n) with hP1def
  set P2 := (x₂.seq n * y₂.seq n).ediv (2 ^ n) with hP2def
  -- E = 2^n·(P1-P2) via product decomposition + s-terms
  have hE : 2 ^ n * (P1 - P2)
          = y₁.seq n * (x₁.seq n - x₂.seq n) + x₂.seq n * (y₁.seq n - y₂.seq n)
          - (x₁.seq n * y₁.seq n - 2 ^ n * P1) + (x₂.seq n * y₂.seq n - 2 ^ n * P2) := by
    ring
  -- 2^n ≤ 2^(2n-k-2) (since k+2 ≤ n), and 2^(2n-k) = 4·2^(2n-k-2)
  have h_sle : (2:ℤ) ^ n ≤ 2 ^ (2 * n - k - 2) := by
    have h := two_pow_le_add n (2 * n - k - 2 - n)
    have heqs : n + (2 * n - k - 2 - n) = 2 * n - k - 2 := by omega
    rwa [heqs] at h
  have hTnn : (0:ℤ) ≤ 2 ^ (2 * n - k - 2) := two_pow_nonneg _
  have hT4 : (2:ℤ) ^ (2 * n - k) = 4 * 2 ^ (2 * n - k - 2) := by
    set e := 2 * n - k - 2 with he_def
    have hee : 2 * n - k = e + 1 + 1 := by omega
    rw [hee, pow_succ, pow_succ]; ring
  have hEu : 2 ^ n * (P1 - P2) ≤ 2 ^ (2 * n - k) := by rw [hE]; omega
  have hEl : -(2 ^ (2 * n - k)) ≤ 2 ^ n * (P1 - P2) := by rw [hE]; omega
  -- cancel 2^n
  have hpos := two_pow_pos n
  have h2 : (2:ℤ) ^ (2 * n - k) * 2 ^ k = 2 ^ n * 2 ^ n := by
    rw [← pow_add, show (2 * n - k) + k = n + n from by omega, pow_add]
  refine ⟨?_, ?_⟩
  · have h1 := Int.mul_le_mul_of_nonneg_right hEu (two_pow_nonneg k)
    have hr : 2 ^ n * (P1 - P2) * 2 ^ k = 2 ^ n * ((P1 - P2) * 2 ^ k) := by ring
    rw [h2, hr] at h1
    exact Int.le_of_mul_le_mul_left h1 hpos
  · have h1 := Int.mul_le_mul_of_nonneg_right hEl (two_pow_nonneg k)
    have hl : -(2:ℤ) ^ (2 * n - k) * 2 ^ k = 2 ^ n * (-(2 ^ n)) := by
      have e : -(2:ℤ) ^ (2 * n - k) * 2 ^ k = -(2 ^ (2 * n - k) * 2 ^ k) := by ring
      rw [e, h2]; ring
    have hr : 2 ^ n * (P1 - P2) * 2 ^ k = 2 ^ n * ((P1 - P2) * 2 ^ k) := by ring
    rw [hl, hr] at h1
    exact Int.le_of_mul_le_mul_left h1 hpos

/-- Multiplication on `Real` — well-defined on the quotient via `Pre.mul_respects`. -/
def Real.mul : Real → Real → Real :=
  Quotient.lift₂ (fun x y => (⟦Pre.mul x y⟧ : Real))
    (fun _ _ _ _ hx hy => Quotient.sound (Pre.mul_respects hx hy))

instance : Mul Real := ⟨Real.mul⟩

/-- **The operational reals form an additive commutative group** — choice-free, below the
ℚ/ℝ `Classical.choice` floor. -/
instance : AddCommGroup Real where
  add_assoc := Real.add_assoc
  zero_add := Real.zero_add
  add_zero := Real.add_zero
  neg_add_cancel := Real.neg_add_cancel
  add_comm := Real.add_comm
  nsmul := nsmulRec
  zsmul := zsmulRec

-- ============================================================
-- §M2  Order and apartness (constructive: positive `<`, `∀k`-style `≤`)
-- ============================================================

/-- `x ≤ y`: the difference `x - y` is non-positive up to every precision
(`∀ k`, eventually `(x_n - y_n)·2^k ≤ 2^n`). -/
def Pre.le (x y : Pre) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (x.seq n - y.seq n) * 2 ^ k ≤ 2 ^ n

/-- `x < y`: `y - x` is positive — bounded below by some `2^{-k}` eventually
(`∃ k`, eventually `2^n ≤ (y_n - x_n)·2^k`).  Constructive strict order. -/
def Pre.lt (x y : Pre) : Prop :=
  ∃ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ^ n ≤ (y.seq n - x.seq n) * 2 ^ k

/-- `x # y`: apartness — `x < y` or `y < x` (positive separation). -/
def Pre.apart (x y : Pre) : Prop := Pre.lt x y ∨ Pre.lt y x

theorem Pre.le_refl (x : Pre) : Pre.le x x := by
  intro k
  refine ⟨0, fun n _ => ?_⟩
  have hp := two_pow_nonneg n
  have h0 : (x.seq n - x.seq n) * 2 ^ k = 0 := by ring
  rw [h0]; omega

theorem Pre.le_trans {x y z : Pre} (hxy : Pre.le x y) (hyz : Pre.le y z) : Pre.le x z := by
  intro k
  obtain ⟨N1, h1⟩ := hxy (k + 1)
  obtain ⟨N2, h2⟩ := hyz (k + 1)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have ha := h1 n (by omega)
  have hb := h2 n (by omega)
  have key : 2 * ((x.seq n - z.seq n) * 2 ^ k)
           = (x.seq n - y.seq n) * 2 ^ (k + 1) + (y.seq n - z.seq n) * 2 ^ (k + 1) := by
    rw [pow_succ]; ring
  omega

/-- Apartness is irreflexive: `¬ x # x` (in fact `¬ x < x`). -/
theorem Pre.lt_irrefl (x : Pre) : ¬ Pre.lt x x := by
  rintro ⟨k, N, h⟩
  have hb := h N (Nat.le_refl N)
  have hp := two_pow_pos N
  have h0 : (x.seq N - x.seq N) * 2 ^ k = 0 := by ring
  rw [h0] at hb
  omega

/-- Equal reals are `≤`: `x ≈ y → x ≤ y` (the upper side of the two-sided bound). -/
theorem Pre.equiv_imp_le {x y : Pre} (h : Pre.equiv x y) : Pre.le x y := by
  intro k
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- Antisymmetry: `x ≤ y` and `y ≤ x` give `x ≈ y` (so `≤` orders reals up to equality). -/
theorem Pre.le_antisymm_equiv {x y : Pre} (hxy : Pre.le x y) (hyx : Pre.le y x) :
    Pre.equiv x y := by
  intro k
  obtain ⟨N1, h1⟩ := hxy k
  obtain ⟨N2, h2⟩ := hyx k
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have ha := h1 n (by omega)
  have hb := h2 n (by omega)
  have he : (y.seq n - x.seq n) * 2 ^ k = -((x.seq n - y.seq n) * 2 ^ k) := by ring
  rw [he] at hb
  exact ⟨by omega, by omega⟩

-- ============================================================
-- Axiom audit — operational ℝ, M1 + M2
-- ============================================================
#print axioms Pre.ofBranch
#print axioms Pre.equiv_trans
#print axioms Real.ofBranch
#print axioms Pre.le_refl
#print axioms Pre.le_trans
#print axioms Pre.lt_irrefl
#print axioms Pre.le_antisymm_equiv
#print axioms Pre.neg
#print axioms Pre.add
#print axioms Real.neg
#print axioms Real.add
#print axioms Real.mul
#print axioms Pre.ofInt
#print axioms Real.ofInt
#print axioms Pre.bounded
#print axioms Pre.mul
#print axioms Pre.mul_comm
#print axioms Pre.mul_one
#print axioms Pre.mul_respects
#print axioms Pre.zero_mul
#print axioms Pre.mul_add
#print axioms Real.add_comm
#print axioms Real.add_assoc
#print axioms Real.neg_add_cancel

end VRCycle.Continuum
