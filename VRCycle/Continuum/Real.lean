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

/-- `0 ≤ (2:ℤ)^n`, choice-free (induction; `pow_pos` pulls `Classical.choice`). -/
theorem two_pow_nonneg (n : ℕ) : (0 : ℤ) ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ m ih => rw [pow_succ]; omega

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
-- Axiom audit — operational ℝ, M1
-- ============================================================
#print axioms Pre.ofBranch
#print axioms Pre.equiv_refl
#print axioms Pre.equiv_symm
#print axioms Pre.equiv_trans
#print axioms Real.ofBranch

end VRCycle.Continuum
