-- VRCycle/Continuum/Real.lean
-- Operational Continuum (Path 1) — Operational ℝ, M1: the real type, below the choice floor.
--
-- STAGE: ℝ / M1. SOURCE: PLAN_OPERATIONAL_REAL.md.
--
-- ## Representation (M0, decided)
-- An operational real is a **dyadic Cauchy sequence** `seq : ℕ → ℤ` (value `lim seq n / 2^n`)
-- with **coherence** `∀ n, -1 ≤ 2·seq n - seq (n+1) ≤ 1` — pure `ℤ`, two-sided bounds (NOT
-- `natAbs`, which makes `omega` pull choice — CONT-8), never mathlib `ℚ`/`ℝ` (CONT-7).
-- This keeps the whole construction BELOW the `Classical.choice` floor.
--
-- ## M1 deliverable + gate
-- The type `Pre`, and the fact that every branch's `[0,1]` point (`intval α` from
-- `UnitInterval.lean`) is a `Pre` — both choice-free.  Riskiest-early gate: the substrate
-- and the coherence proof stay `[propext, Quot.sound]`.

import VRCycle.Continuum.UnitInterval

namespace VRCycle.Continuum

/-- A pre-real: a dyadic Cauchy sequence over `ℤ` (value `lim seq n / 2^n`), with
consecutive **coherence** stated as two-sided `ℤ` bounds (choice-free). -/
structure Pre where
  /-- The integer numerators; `seq n` approximates `value · 2^n`. -/
  seq : ℕ → ℤ
  /-- Consecutive coherence: rescaling stage `n` to `n+1` moves by at most one ulp. -/
  coherent : ∀ n, -1 ≤ 2 * seq n - seq (n + 1) ∧ 2 * seq n - seq (n + 1) ≤ 1

/-- Every branch names a pre-real in `[0,1]`: its `[0,1]` point `intval α` is a dyadic
Cauchy sequence (`2·intval n - intval (n+1) = -bit ∈ {-1,0}`).  Choice-free. -/
def Pre.ofBranch (α : Branch) : Pre where
  seq := intval α
  coherent := by
    intro n
    simp only [intval]
    have hb0 := bitZ_nonneg (α n)
    have hb1 := bitZ_le_one (α n)
    constructor
    · omega
    · omega

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
-- §M3  Ring: negation (addition needs the M0 coherence revisit — see note below)
-- ============================================================

/-- **Negation** of an operational real: flip every numerator.  Coherence `≤ 1` is
preserved (sign flip is symmetric).  Choice-free. -/
def Pre.neg (x : Pre) : Pre where
  seq := fun n => - x.seq n
  coherent := by
    intro n
    obtain ⟨h1, h2⟩ := x.coherent n
    constructor <;> omega

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

end VRCycle.Continuum
