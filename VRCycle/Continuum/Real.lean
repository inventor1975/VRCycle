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
  have h2 : (Pre.ofInt 0).seq n = 0 := by change (0:ℤ) * 2 ^ n = 0; ring
  have h1 : (Pre.mul (Pre.ofInt 0) x).seq n = 0 := by
    change ((Pre.ofInt 0).seq n * x.seq n).ediv (2 ^ n) = 0
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

/-- **Associativity** `(x·y)·z = x·(y·z)`.  Both approximate `abc/2^{2n}`; clearing the two
floors, `2^{2n}·(L-R) = a·s₂ - s₁·c + 2^n·(s_R - s_L)` (a `ring` identity in the bracket
remainders).  Each term is bounded by the operands' **magnitudes** (`Pre.bounded`), so the
difference `|L - R| ≤ 2^Bx + 2^Bz + 1` is **constant** — beaten by `2^n` once `n ≥ k+Bx+Bz+2`.
The hard part is purely the constant bound; no vanishing needed.  Choice-free. -/
theorem Pre.mul_assoc (x y z : Pre) :
    Pre.equiv (Pre.mul (Pre.mul x y) z) (Pre.mul x (Pre.mul y z)) := by
  intro k
  obtain ⟨Bx, Nx, hbx⟩ := x.bounded
  obtain ⟨Bz, Nz, hbz⟩ := z.bounded
  refine ⟨max (max Nx Nz) (k + Bx + Bz + 2), fun n hn => ?_⟩
  simp only [Pre.mul]
  obtain ⟨hxu, hxl⟩ := hbx n (by omega)
  obtain ⟨hzu, hzl⟩ := hbz n (by omega)
  have hdpos : (0:ℤ) < 2 ^ n := two_pow_pos n
  -- brackets for the two inner floors, then set
  obtain ⟨hab0, hab1⟩ := int_ediv_bracket (x.seq n * y.seq n) hdpos
  obtain ⟨hbc0, hbc1⟩ := int_ediv_bracket (y.seq n * z.seq n) hdpos
  set qab := (x.seq n * y.seq n).ediv (2 ^ n) with hqabdef
  set qbc := (y.seq n * z.seq n).ediv (2 ^ n) with hqbcdef
  -- brackets for the two outer floors, then set
  obtain ⟨hL0, hL1⟩ := int_ediv_bracket (qab * z.seq n) hdpos
  obtain ⟨hR0, hR1⟩ := int_ediv_bracket (x.seq n * qbc) hdpos
  set L := (qab * z.seq n).ediv (2 ^ n) with hLdef
  set R := (x.seq n * qbc).ediv (2 ^ n) with hRdef
  -- remainder bounds (each in [0,2^n) ⊆ [-2^n,2^n])
  have hge : (0:ℤ) ≤ 2 ^ n := two_pow_nonneg n
  have hC2l : -(2:ℤ) ^ n ≤ y.seq n * z.seq n - 2 ^ n * qbc := by omega
  have hC2u : y.seq n * z.seq n - 2 ^ n * qbc ≤ 2 ^ n := by omega
  have hs1l : -(2:ℤ) ^ n ≤ x.seq n * y.seq n - 2 ^ n * qab := by omega
  have hs1u : x.seq n * y.seq n - 2 ^ n * qab ≤ 2 ^ n := by omega
  have hAl : -(2:ℤ) ^ n ≤ (x.seq n * qbc - 2 ^ n * R) - (qab * z.seq n - 2 ^ n * L) := by omega
  have hAu : (x.seq n * qbc - 2 ^ n * R) - (qab * z.seq n - 2 ^ n * L) ≤ 2 ^ n := by omega
  -- product bounds for the three terms of the identity
  obtain ⟨hT1l, hT1u⟩ := mul_abs_bound (A := x.seq n) (P := (2:ℤ) ^ (n + Bx))
    (C := y.seq n * z.seq n - 2 ^ n * qbc) (Q := (2:ℤ) ^ n) hxl hxu hC2l hC2u
  have hp1 : (2:ℤ) ^ (n + Bx) * 2 ^ n = 2 ^ (2 * n + Bx) := by rw [← pow_add]; congr 1; omega
  rw [hp1] at hT1l hT1u
  obtain ⟨hT2l, hT2u⟩ := mul_abs_bound (A := x.seq n * y.seq n - 2 ^ n * qab) (P := (2:ℤ) ^ n)
    (C := z.seq n) (Q := (2:ℤ) ^ (n + Bz)) hs1l hs1u hzl hzu
  have hp2 : (2:ℤ) ^ n * 2 ^ (n + Bz) = 2 ^ (2 * n + Bz) := by rw [← pow_add]; congr 1; omega
  rw [hp2] at hT2l hT2u
  obtain ⟨hT3l, hT3u⟩ := mul_abs_bound
    (A := (x.seq n * qbc - 2 ^ n * R) - (qab * z.seq n - 2 ^ n * L)) (P := (2:ℤ) ^ n)
    (C := (2:ℤ) ^ n) (Q := (2:ℤ) ^ n) hAl hAu (by omega) (by omega)
  have hp3 : (2:ℤ) ^ n * 2 ^ n = 2 ^ (2 * n) := by rw [← pow_add, two_mul]
  rw [hp3] at hT3l hT3u
  -- the cleared-denominator identity (pure ring in the bracket remainders)
  have hID : 2 ^ n * 2 ^ n * (L - R)
           = x.seq n * (y.seq n * z.seq n - 2 ^ n * qbc)
           - (x.seq n * y.seq n - 2 ^ n * qab) * z.seq n
           + ((x.seq n * qbc - 2 ^ n * R) - (qab * z.seq n - 2 ^ n * L)) * 2 ^ n := by ring
  have hSu : 2 ^ n * 2 ^ n * (L - R) ≤ 2 ^ (2 * n + Bx) + 2 ^ (2 * n + Bz) + 2 ^ (2 * n) := by
    rw [hID]; omega
  have hSl : -(2 ^ (2 * n + Bx) + 2 ^ (2 * n + Bz) + 2 ^ (2 * n)) ≤ 2 ^ n * 2 ^ n * (L - R) := by
    rw [hID]; omega
  -- factor 2^{2n} out of the bound and cancel
  have hRHSeq : (2:ℤ) ^ (2 * n + Bx) + 2 ^ (2 * n + Bz) + 2 ^ (2 * n)
      = 2 ^ n * 2 ^ n * (2 ^ Bx + 2 ^ Bz + 1) := by
    have e1 : (2:ℤ) ^ (2 * n + Bx) = 2 ^ n * 2 ^ n * 2 ^ Bx := by
      rw [show 2 * n + Bx = n + (n + Bx) from by omega, pow_add, pow_add]; ring
    have e2 : (2:ℤ) ^ (2 * n + Bz) = 2 ^ n * 2 ^ n * 2 ^ Bz := by
      rw [show 2 * n + Bz = n + (n + Bz) from by omega, pow_add, pow_add]; ring
    have e3 : (2:ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
    rw [e1, e2, e3]; ring
  have hpos2 : (0:ℤ) < 2 ^ n * 2 ^ n := Int.mul_pos hdpos hdpos
  rw [hRHSeq] at hSu hSl
  have hDu : L - R ≤ 2 ^ Bx + 2 ^ Bz + 1 := Int.le_of_mul_le_mul_left hSu hpos2
  have hDl : -(2 ^ Bx + 2 ^ Bz + 1) ≤ L - R := by
    have h2 : 2 ^ n * 2 ^ n * (-(2 ^ Bx + 2 ^ Bz + 1)) ≤ 2 ^ n * 2 ^ n * (L - R) := by
      have e : (2:ℤ) ^ n * 2 ^ n * (-(2 ^ Bx + 2 ^ Bz + 1))
             = -(2 ^ n * 2 ^ n * (2 ^ Bx + 2 ^ Bz + 1)) := by ring
      rw [e]; exact hSl
    exact Int.le_of_mul_le_mul_left h2 hpos2
  -- the constant bound C := 2^Bx+2^Bz+1 is beaten by 2^n: C·2^k ≤ 2^n
  have hkn := two_pow_nonneg k
  have hCk : ((2:ℤ) ^ Bx + 2 ^ Bz + 1) * 2 ^ k ≤ 2 ^ n := by
    have hCle : (2:ℤ) ^ Bx + 2 ^ Bz + 1 ≤ 2 ^ (Bx + Bz + 2) := by
      have h1 := two_pow_le_add Bx Bz
      have h2 := two_pow_le_add Bz Bx
      have h3 : (2:ℤ) ^ (Bz + Bx) = 2 ^ (Bx + Bz) := by rw [Nat.add_comm]
      have h4 : (2:ℤ) ^ (Bx + Bz + 2) = 4 * 2 ^ (Bx + Bz) := by
        rw [show Bx + Bz + 2 = (Bx + Bz) + 1 + 1 from by omega, pow_succ, pow_succ]; ring
      have h5 : (1:ℤ) ≤ 2 ^ (Bx + Bz) := by have := two_pow_pos (Bx + Bz); omega
      rw [h3] at h2; omega
    have hstep := Int.mul_le_mul_of_nonneg_right hCle hkn
    have hpw : (2:ℤ) ^ (Bx + Bz + 2) * 2 ^ k = 2 ^ (Bx + Bz + 2 + k) := by rw [← pow_add]
    have hpw2 : (2:ℤ) ^ (Bx + Bz + 2 + k) ≤ 2 ^ n := by
      have h := two_pow_le_add (Bx + Bz + 2 + k) (n - (Bx + Bz + 2 + k))
      rwa [show (Bx + Bz + 2 + k) + (n - (Bx + Bz + 2 + k)) = n from by omega] at h
    rw [hpw] at hstep; exact Int.le_trans hstep hpw2
  -- assemble: (L-R)·2^k bounded by ±C·2^k ⊆ ±2^n
  have hDku : (L - R) * 2 ^ k ≤ (2 ^ Bx + 2 ^ Bz + 1) * 2 ^ k :=
    Int.mul_le_mul_of_nonneg_right hDu hkn
  have hDkl : -((2 ^ Bx + 2 ^ Bz + 1) * 2 ^ k) ≤ (L - R) * 2 ^ k := by
    have h := Int.mul_le_mul_of_nonneg_right hDl hkn
    have e : (-(2 ^ Bx + 2 ^ Bz + 1)) * 2 ^ k = -((2 ^ Bx + 2 ^ Bz + 1) * 2 ^ k) := by ring
    rwa [e] at h
  set D2k := (L - R) * 2 ^ k with hD2kdef
  set C2k := (2 ^ Bx + 2 ^ Bz + 1) * 2 ^ k with hC2kdef
  clear_value D2k C2k
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

-- The eight ring laws, lifted from `Pre` to the quotient `Real` (`Quotient.inductionOn` +
-- `Quotient.sound` of the corresponding `Pre` lemma).  Each inherits `[propext, Quot.sound]`.

theorem Real.mul_comm (a b : Real) : a * b = b * a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (Pre.mul_comm x y))

theorem Real.mul_assoc (a b c : Real) : a * b * c = a * (b * c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (Pre.mul_assoc x y z))

theorem Real.mul_one (a : Real) : a * 1 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (Pre.mul_one x))

theorem Real.one_mul (a : Real) : 1 * a = a := by
  rw [Real.mul_comm]; exact Real.mul_one a

theorem Real.left_distrib (a b c : Real) : a * (b + c) = a * b + a * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (Pre.mul_add x y z))

theorem Real.right_distrib (a b c : Real) : (a + b) * c = a * c + b * c := by
  rw [Real.mul_comm, Real.left_distrib, Real.mul_comm c a, Real.mul_comm c b]

theorem Real.zero_mul (a : Real) : 0 * a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (Pre.zero_mul x))

theorem Real.mul_zero (a : Real) : a * 0 = 0 := by
  rw [Real.mul_comm]; exact Real.zero_mul a

/-- **The operational reals form a commutative ring** — `+`, `−`, `×`, `0`, `1` with all ring
laws, choice-free `[propext, Quot.sound]`, entirely below the ℚ/ℝ `Classical.choice` floor.
(`CommRing` subsumes the additive commutative group; no separate `AddCommGroup` instance.) -/
instance : CommRing Real where
  add_assoc := Real.add_assoc
  zero_add := Real.zero_add
  add_zero := Real.add_zero
  neg_add_cancel := Real.neg_add_cancel
  add_comm := Real.add_comm
  mul_assoc := Real.mul_assoc
  one_mul := Real.one_mul
  mul_one := Real.mul_one
  left_distrib := Real.left_distrib
  right_distrib := Real.right_distrib
  zero_mul := Real.zero_mul
  mul_zero := Real.mul_zero
  mul_comm := Real.mul_comm
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

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
-- §M3.inv  Reciprocal — apartness-witnessed (total `Field` is impossible choice-free:
-- `¬(x≈0)` gives no lower-bound modulus on `|x|`; that step is Markov's principle).
-- ============================================================

/-- From a **positivity witness** `2^n ≤ x.seq n · 2^k` (all `n ≥ N`), the numerator is
strictly positive — so it is a valid Euclidean divisor.  Choice-free. -/
theorem Pre.pos_of_lb {x : Pre} {k N : ℕ} (hlb : ∀ n, N ≤ n → 2 ^ n ≤ x.seq n * 2 ^ k)
    {n : ℕ} (hn : N ≤ n) : 0 < x.seq n := by
  have h := hlb n hn
  have h2n := two_pow_pos n
  rcases Int.lt_or_le 0 (x.seq n) with hp | hnp
  · exact hp
  · exfalso
    have hxk := Int.mul_le_mul_of_nonneg_right hnp (two_pow_nonneg k)
    have hz : (0:ℤ) * 2 ^ k = 0 := by ring
    rw [hz] at hxk
    omega

/-- The positivity witness gives a **lower bound** `2^(n-k) ≤ x.seq n` (for `k ≤ n`):
the value is `≥ 2^{-k}`, the apartness modulus that makes the reciprocal Cauchy.  Choice-free. -/
theorem Pre.lb_pow {x : Pre} {k N : ℕ} (hlb : ∀ n, N ≤ n → 2 ^ n ≤ x.seq n * 2 ^ k)
    {n : ℕ} (hn : N ≤ n) (hnk : k ≤ n) : (2:ℤ) ^ (n - k) ≤ x.seq n := by
  have h := hlb n hn
  have e : (2:ℤ) ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  rw [e] at h
  exact Int.le_of_mul_le_mul_right h (two_pow_pos k)

/-- **Reciprocal of a positive operational real** (given an explicit positivity witness
`hlb : 2^n ≤ x.seq n · 2^k`).  `seq n = 2^{2n} ediv x_n` (value `1/value(x)`).  Cauchy because
clearing denominators `x_m x_n·(p_m 2^n − p_n 2^m) = −2^{m+n}·(x's cauchy diff) + floor residuals`,
the cross term shrinks via `x.cauchy`, the residuals via `Pre.bounded`, and `x_m x_n ≥ 2^{m+n−2k}`
(the apartness lower bound) is cancelled.  Choice-free `[propext, Quot.sound]`. -/
def Pre.invPos (x : Pre) (k N : ℕ) (hlb : ∀ n, N ≤ n → 2 ^ n ≤ x.seq n * 2 ^ k) : Pre where
  seq := fun n => ((2:ℤ) ^ (2 * n)).ediv (x.seq n)
  cauchy := by
    intro k'
    obtain ⟨B, Nb, hb⟩ := x.bounded
    obtain ⟨Nc, hc⟩ := x.cauchy (k' + 2 * k + 2)
    refine ⟨max (max N Nb) Nc + (2 * B + 2 * k + k' + 2), fun m n hm hn => ?_⟩
    have hxm : 0 < x.seq m := Pre.pos_of_lb hlb (by omega)
    have hxn : 0 < x.seq n := Pre.pos_of_lb hlb (by omega)
    obtain ⟨hpm0, hpm1⟩ := int_ediv_bracket ((2:ℤ) ^ (2 * m)) hxm
    obtain ⟨hpn0, hpn1⟩ := int_ediv_bracket ((2:ℤ) ^ (2 * n)) hxn
    set pm := ((2:ℤ) ^ (2 * m)).ediv (x.seq m) with hpmdef
    set pn := ((2:ℤ) ^ (2 * n)).ediv (x.seq n) with hpndef
    obtain ⟨hbm_u, hbm_l⟩ := hb m (by omega)
    obtain ⟨hbn_u, hbn_l⟩ := hb n (by omega)
    have hlbm : (2:ℤ) ^ (m - k) ≤ x.seq m := Pre.lb_pow hlb (by omega) (by omega)
    have hlbn : (2:ℤ) ^ (n - k) ≤ x.seq n := Pre.lb_pow hlb (by omega) (by omega)
    obtain ⟨hcu, hcl⟩ := hc m n (by omega) (by omega)
    have hmn_nn : (0:ℤ) ≤ 2 ^ (m + n) := two_pow_nonneg _
    have hn_nn : (0:ℤ) ≤ 2 ^ n := two_pow_nonneg _
    have hm_nn : (0:ℤ) ≤ 2 ^ m := two_pow_nonneg _
    have hk'_nn : (0:ℤ) ≤ 2 ^ k' := two_pow_nonneg _
    -- (1) tight bound on the x-cauchy cross at precision k' (divide out 2^(2k+2))
    have e_pre : (x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ (k' + 2 * k + 2)
               = 2 ^ (2 * k + 2) * ((x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k') := by
      rw [show k' + 2 * k + 2 = k' + (2 * k + 2) from by omega, pow_add]; ring
    have e_rhs : (2:ℤ) ^ (m + n) = 2 ^ (2 * k + 2) * 2 ^ (m + n - (2 * k + 2)) := by
      rw [← pow_add]; congr 1; omega
    rw [e_pre, e_rhs] at hcu hcl
    have hpos2k := two_pow_pos (2 * k + 2)
    have hcross_u : (x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k' ≤ 2 ^ (m + n - (2 * k + 2)) :=
      Int.le_of_mul_le_mul_left hcu hpos2k
    have hcross_l : -(2 ^ (m + n - (2 * k + 2)))
        ≤ (x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k' := by
      have h2 : 2 ^ (2 * k + 2) * (-(2 ^ (m + n - (2 * k + 2))))
              ≤ 2 ^ (2 * k + 2) * ((x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k') := by
        have e : (2:ℤ) ^ (2 * k + 2) * (-(2 ^ (m + n - (2 * k + 2))))
               = -(2 ^ (2 * k + 2) * 2 ^ (m + n - (2 * k + 2))) := by ring
        rw [e]; exact hcl
      exact Int.le_of_mul_le_mul_left h2 hpos2k
    -- (2) the cleared-denominator identity (pure ring) + the cross/pow bridge
    have hID : x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m)
             = (x.seq n * 2 ^ n * 2 ^ (2 * m) - x.seq m * 2 ^ m * 2 ^ (2 * n))
             - (x.seq n * 2 ^ n) * (2 ^ (2 * m) - x.seq m * pm)
             + (x.seq m * 2 ^ m) * (2 ^ (2 * n) - x.seq n * pn) := by ring
    have e1 : (2:ℤ) ^ (m + n) * 2 ^ m = 2 ^ n * 2 ^ (2 * m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e2 : (2:ℤ) ^ (m + n) * 2 ^ n = 2 ^ m * 2 ^ (2 * n) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have hbracket : x.seq n * 2 ^ n * 2 ^ (2 * m) - x.seq m * 2 ^ m * 2 ^ (2 * n)
                  = -(2 ^ (m + n)) * (x.seq m * 2 ^ n - x.seq n * 2 ^ m) := by
      have l1 : x.seq n * 2 ^ n * 2 ^ (2 * m) = x.seq n * (2 ^ n * 2 ^ (2 * m)) := by ring
      have l2 : x.seq m * 2 ^ m * 2 ^ (2 * n) = x.seq m * (2 ^ m * 2 ^ (2 * n)) := by ring
      rw [l1, l2, ← e1, ← e2]; ring
    have hID2 : x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m)
              = -(2 ^ (m + n)) * (x.seq m * 2 ^ n - x.seq n * 2 ^ m)
              - (x.seq n * 2 ^ n) * (2 ^ (2 * m) - x.seq m * pm)
              + (x.seq m * 2 ^ m) * (2 ^ (2 * n) - x.seq n * pn) := by rw [hID, hbracket]
    have hfin : x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k'
              = -(2 ^ (m + n) * ((x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k'))
              - (x.seq n * 2 ^ n) * (2 ^ (2 * m) - x.seq m * pm) * 2 ^ k'
              + (x.seq m * 2 ^ m) * (2 ^ (2 * n) - x.seq n * pn) * 2 ^ k' := by
      rw [hID2]; ring
    -- (3) bound the main (cross) piece by 2^(2(m+n)-2k-2)
    obtain ⟨hE_l, hE_u⟩ := mul_abs_bound (A := (2:ℤ) ^ (m + n)) (P := (2:ℤ) ^ (m + n))
      (C := (x.seq m * 2 ^ n - x.seq n * 2 ^ m) * 2 ^ k') (Q := (2:ℤ) ^ (m + n - (2 * k + 2)))
      (by omega) (by omega) hcross_l hcross_u
    have hEpow : (2:ℤ) ^ (m + n) * 2 ^ (m + n - (2 * k + 2)) = 2 ^ (2 * (m + n) - (2 * k + 2)) := by
      rw [← pow_add]; congr 1; omega
    rw [hEpow] at hE_l hE_u
    -- (4) bound the two floor residuals, each via NESTED mul_abs_bound (triple products)
    obtain ⟨hxn2_l, hxn2_u⟩ := mul_abs_bound (A := x.seq n) (P := (2:ℤ) ^ (n + B))
      (C := (2:ℤ) ^ n) (Q := (2:ℤ) ^ n) hbn_l hbn_u (by omega) (by omega)
    have hxn2pow : (2:ℤ) ^ (n + B) * 2 ^ n = 2 ^ (2 * n + B) := by rw [← pow_add]; congr 1; omega
    rw [hxn2pow] at hxn2_l hxn2_u
    have hrm_l : -(2:ℤ) ^ (m + B) ≤ 2 ^ (2 * m) - x.seq m * pm := by
      have := two_pow_nonneg (m + B); omega
    have hrm_u : (2:ℤ) ^ (2 * m) - x.seq m * pm ≤ 2 ^ (m + B) := by omega
    obtain ⟨hR1_l, hR1_u⟩ := mul_abs_bound (A := x.seq n * 2 ^ n) (P := (2:ℤ) ^ (2 * n + B))
      (C := (2:ℤ) ^ (2 * m) - x.seq m * pm) (Q := (2:ℤ) ^ (m + B)) hxn2_l hxn2_u hrm_l hrm_u
    have hR1pow : (2:ℤ) ^ (2 * n + B) * 2 ^ (m + B) = 2 ^ (m + 2 * n + 2 * B) := by
      rw [← pow_add]; congr 1; omega
    rw [hR1pow] at hR1_l hR1_u
    obtain ⟨hR1k_l, hR1k_u⟩ := mul_abs_bound (A := (x.seq n * 2 ^ n) * (2 ^ (2 * m) - x.seq m * pm))
      (P := (2:ℤ) ^ (m + 2 * n + 2 * B)) (C := (2:ℤ) ^ k') (Q := (2:ℤ) ^ k')
      hR1_l hR1_u (by omega) (by omega)
    have hR1kpow : (2:ℤ) ^ (m + 2 * n + 2 * B) * 2 ^ k' = 2 ^ (m + 2 * n + 2 * B + k') := by
      rw [← pow_add]
    rw [hR1kpow] at hR1k_l hR1k_u
    obtain ⟨hxm2_l, hxm2_u⟩ := mul_abs_bound (A := x.seq m) (P := (2:ℤ) ^ (m + B))
      (C := (2:ℤ) ^ m) (Q := (2:ℤ) ^ m) hbm_l hbm_u (by omega) (by omega)
    have hxm2pow : (2:ℤ) ^ (m + B) * 2 ^ m = 2 ^ (2 * m + B) := by rw [← pow_add]; congr 1; omega
    rw [hxm2pow] at hxm2_l hxm2_u
    have hrn_l : -(2:ℤ) ^ (n + B) ≤ 2 ^ (2 * n) - x.seq n * pn := by
      have := two_pow_nonneg (n + B); omega
    have hrn_u : (2:ℤ) ^ (2 * n) - x.seq n * pn ≤ 2 ^ (n + B) := by omega
    obtain ⟨hR2_l, hR2_u⟩ := mul_abs_bound (A := x.seq m * 2 ^ m) (P := (2:ℤ) ^ (2 * m + B))
      (C := (2:ℤ) ^ (2 * n) - x.seq n * pn) (Q := (2:ℤ) ^ (n + B)) hxm2_l hxm2_u hrn_l hrn_u
    have hR2pow : (2:ℤ) ^ (2 * m + B) * 2 ^ (n + B) = 2 ^ (2 * m + n + 2 * B) := by
      rw [← pow_add]; congr 1; omega
    rw [hR2pow] at hR2_l hR2_u
    obtain ⟨hR2k_l, hR2k_u⟩ := mul_abs_bound (A := (x.seq m * 2 ^ m) * (2 ^ (2 * n) - x.seq n * pn))
      (P := (2:ℤ) ^ (2 * m + n + 2 * B)) (C := (2:ℤ) ^ k') (Q := (2:ℤ) ^ k')
      hR2_l hR2_u (by omega) (by omega)
    have hR2kpow : (2:ℤ) ^ (2 * m + n + 2 * B) * 2 ^ k' = 2 ^ (2 * m + n + 2 * B + k') := by
      rw [← pow_add]
    rw [hR2kpow] at hR2k_l hR2k_u
    -- (5) budget: each residual ≤ 2^(2(m+n)-2k-2); and 2^(2(m+n)-2k) = 4·2^(2(m+n)-2k-2)
    have hbudget1 : (2:ℤ) ^ (m + 2 * n + 2 * B + k') ≤ 2 ^ (2 * (m + n) - (2 * k + 2)) := by
      have h := two_pow_le_add (m + 2 * n + 2 * B + k')
        (2 * (m + n) - (2 * k + 2) - (m + 2 * n + 2 * B + k'))
      rwa [show (m + 2 * n + 2 * B + k') + (2 * (m + n) - (2 * k + 2) - (m + 2 * n + 2 * B + k'))
            = 2 * (m + n) - (2 * k + 2) from by omega] at h
    have hbudget2 : (2:ℤ) ^ (2 * m + n + 2 * B + k') ≤ 2 ^ (2 * (m + n) - (2 * k + 2)) := by
      have h := two_pow_le_add (2 * m + n + 2 * B + k')
        (2 * (m + n) - (2 * k + 2) - (2 * m + n + 2 * B + k'))
      rwa [show (2 * m + n + 2 * B + k') + (2 * (m + n) - (2 * k + 2) - (2 * m + n + 2 * B + k'))
            = 2 * (m + n) - (2 * k + 2) from by omega] at h
    have h4 : (2:ℤ) ^ (2 * (m + n) - 2 * k) = 4 * 2 ^ (2 * (m + n) - (2 * k + 2)) := by
      rw [show 2 * (m + n) - 2 * k = (2 * (m + n) - (2 * k + 2)) + 1 + 1 from by omega,
        pow_succ, pow_succ]; ring
    -- (6) lower bound on the product x_m x_n, and the cancellation
    have hxmn : (0:ℤ) < x.seq m * x.seq n := Int.mul_pos hxm hxn
    have hlbprod0 : (2:ℤ) ^ (m - k) * 2 ^ (n - k) ≤ x.seq m * x.seq n :=
      Int.mul_le_mul hlbm hlbn (two_pow_nonneg _) (by omega)
    have hpprod : (2:ℤ) ^ (m - k) * 2 ^ (n - k) = 2 ^ (m + n - 2 * k) := by
      rw [← pow_add]; congr 1; omega
    rw [hpprod] at hlbprod0
    have hge2 : (2:ℤ) ^ (2 * (m + n) - 2 * k) ≤ x.seq m * x.seq n * 2 ^ (m + n) := by
      have h := Int.mul_le_mul_of_nonneg_right hlbprod0 (two_pow_nonneg (m + n))
      have hp : (2:ℤ) ^ (m + n - 2 * k) * 2 ^ (m + n) = 2 ^ (2 * (m + n) - 2 * k) := by
        rw [← pow_add]; congr 1; omega
      rw [hp] at h; exact h
    refine ⟨?_, ?_⟩
    · -- D · 2^k' ≤ 2^(m+n)
      have hQu : x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k'
               ≤ 2 ^ (2 * (m + n) - 2 * k) := by rw [hfin]; omega
      have hcomb : x.seq m * x.seq n * ((pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k')
                 ≤ x.seq m * x.seq n * 2 ^ (m + n) := by
        have e : x.seq m * x.seq n * ((pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k')
               = x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k' := by ring
        rw [e]; exact Int.le_trans hQu hge2
      exact Int.le_of_mul_le_mul_left hcomb hxmn
    · -- -(2^(m+n)) ≤ D · 2^k'
      have hQl : -(2 ^ (2 * (m + n) - 2 * k))
               ≤ x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k' := by rw [hfin]; omega
      have hcomb : x.seq m * x.seq n * (-(2 ^ (m + n)))
                 ≤ x.seq m * x.seq n * ((pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k') := by
        have e1' : x.seq m * x.seq n * (-(2 ^ (m + n))) = -(x.seq m * x.seq n * 2 ^ (m + n)) := by
          ring
        have e2' : x.seq m * x.seq n * ((pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k')
                 = x.seq m * x.seq n * (pm * 2 ^ n - pn * 2 ^ m) * 2 ^ k' := by ring
        rw [e1', e2']
        have hneg : -(x.seq m * x.seq n * 2 ^ (m + n)) ≤ -(2 ^ (2 * (m + n) - 2 * k)) := by omega
        exact Int.le_trans hneg hQl
      exact Int.le_of_mul_le_mul_left hcomb hxmn

/-- **`x · x⁻¹ = 1`** (with the positivity witness): the reciprocal `Pre.invPos` is a genuine
multiplicative inverse.  Constant-bounded: `t := (x_n·(2^{2n} ediv x_n)) ediv 2^n` satisfies
`0 ≤ 2^n − t ≤ 2^B` (two nested floors lose `< x_n ≤ 2^{n+B}`), so `t → 2^n` and the value
→ `1`.  Choice-free `[propext, Quot.sound]`. -/
theorem Pre.invPos_mul (x : Pre) (k N : ℕ) (hlb : ∀ n, N ≤ n → 2 ^ n ≤ x.seq n * 2 ^ k) :
    Pre.equiv (Pre.mul x (Pre.invPos x k N hlb)) (Pre.ofInt 1) := by
  intro k'
  obtain ⟨B, Nb, hb⟩ := x.bounded
  refine ⟨max N Nb + (B + k' + 2), fun n hn => ?_⟩
  simp only [Pre.mul, Pre.invPos, Pre.ofInt]
  have hxn : 0 < x.seq n := Pre.pos_of_lb hlb (by omega)
  obtain ⟨hbu, hbl⟩ := hb n (by omega)
  obtain ⟨hq0, hq1⟩ := int_ediv_bracket ((2:ℤ) ^ (2 * n)) hxn
  set q := ((2:ℤ) ^ (2 * n)).ediv (x.seq n) with hqdef
  obtain ⟨ht0, ht1⟩ := int_ediv_bracket (x.seq n * q) (two_pow_pos n)
  set t := (x.seq n * q).ediv (2 ^ n) with htdef
  have hpn := two_pow_pos n
  have h2n : (2:ℤ) ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
  have hBpow : (2:ℤ) ^ n * 2 ^ B = 2 ^ (n + B) := by rw [← pow_add]
  -- t ≤ 2^n
  have htu : t ≤ 2 ^ n := by
    have h : 2 ^ n * t ≤ 2 ^ n * 2 ^ n := by
      have hq := hq0; rw [h2n] at hq; exact Int.le_trans ht0 hq
    exact Int.le_of_mul_le_mul_left h hpn
  -- 2^n - t ≤ 2^B
  have htl : 2 ^ n - t ≤ 2 ^ B := by
    have h : 2 ^ n * 2 ^ n < 2 ^ n * (t + 1 + 2 ^ B) := by
      have e : (2:ℤ) ^ n * (t + 1 + 2 ^ B) = 2 ^ n * t + 2 ^ n + 2 ^ (n + B) := by
        rw [← hBpow]; ring
      rw [e, ← h2n]; omega
    have h2 : 2 ^ n < t + 1 + 2 ^ B := Int.lt_of_mul_lt_mul_left h (by omega)
    omega
  have hk' := two_pow_nonneg k'
  have hBk : (2:ℤ) ^ B * 2 ^ k' = 2 ^ (B + k') := by rw [← pow_add]
  have hBkn : (2:ℤ) ^ (B + k') ≤ 2 ^ n := by
    have h := two_pow_le_add (B + k') (n - (B + k'))
    rwa [show (B + k') + (n - (B + k')) = n from by omega] at h
  refine ⟨?_, ?_⟩
  · have hd : t - 1 * 2 ^ n ≤ 0 := by omega
    have hmul := Int.mul_le_mul_of_nonneg_right hd hk'
    have e0 : (0:ℤ) * 2 ^ k' = 0 := by ring
    rw [e0] at hmul
    omega
  · have hh := Int.mul_le_mul_of_nonneg_right htl hk'
    rw [hBk] at hh
    have e : (2 ^ n - t) * 2 ^ k' = -((t - 1 * 2 ^ n) * 2 ^ k') := by ring
    rw [e] at hh
    set D := (t - 1 * 2 ^ n) * 2 ^ k' with hDdef
    clear_value D
    omega

-- (A `Real`-level wrapper `⟦x⟧·⟦x⁻¹⟧ = 1` is straightforward but fights the quotient-instance
-- defeq; the choice-free content lives at the `Pre` level in `Pre.invPos_mul`.  This is the
-- honest "field" below the floor: inverses for apart-from-0 reals; a *total* `Field` is
-- impossible choice-free, since `¬(x≈0)` yields no lower-bound modulus on `|x|` (Markov).)

-- ============================================================
-- §M5  Payoff: the operational reals are a NONTRIVIAL commutative ring
-- ============================================================

/-- **Nontriviality** `(0 : Real) ≠ 1` — a fact about `ℝ` that mathlib can only state Tier-3
(every `ℝ` operation pulls `Classical.choice`), proved here **choice-free below the floor**.
`0` and `1` are apart: their numerators differ by `2^n`, so at precision `k = 1` the lower
agreement bound `-(2^n) ≤ (0_n - 1_n)·2 = -2·2^n` fails (`2·2^n ≤ 2^n` is false). -/
theorem Real.zero_ne_one : (0 : Real) ≠ 1 := by
  intro h
  have he : Pre.equiv (Pre.ofInt 0) (Pre.ofInt 1) := Quotient.exact h
  obtain ⟨N, hN⟩ := he 1
  obtain ⟨_, hlo⟩ := hN N (Nat.le_refl N)
  simp only [Pre.ofInt] at hlo
  have hp := two_pow_pos N
  have e : ((0:ℤ) * 2 ^ N - 1 * 2 ^ N) * 2 ^ 1 = -(2 * 2 ^ N) := by ring
  rw [e] at hlo
  omega

-- ============================================================
-- Axiom audit — operational ℝ, M1 + M2
-- ============================================================
#print axioms Pre.ofBranch
#print axioms Real.zero_ne_one
#print axioms Pre.invPos
#print axioms Pre.invPos_mul
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
#print axioms Real.mul_comm
#print axioms Real.mul_assoc
#print axioms Real.one_mul
#print axioms Real.left_distrib
#print axioms Real.right_distrib
#print axioms Real.zero_mul
#print axioms Pre.ofInt
#print axioms Real.ofInt
#print axioms Pre.bounded
#print axioms Pre.mul
#print axioms Pre.mul_comm
#print axioms Pre.mul_one
#print axioms Pre.mul_respects
#print axioms Pre.zero_mul
#print axioms Pre.mul_add
#print axioms Pre.mul_assoc
#print axioms Real.add_comm
#print axioms Real.add_assoc
#print axioms Real.neg_add_cancel
-- The `CommRing Real` instance carries no choice: a law obtained THROUGH the instance
-- (`_root_.mul_comm`, resolved via `CommRing Real`) is still `[propext, Quot.sound]`.
example (a b : Real) : a * b = b * a := mul_comm a b

end VRCycle.Continuum
