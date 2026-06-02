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
-- Axiom audit — operational ℝ, M1
-- ============================================================
#print axioms Pre.ofBranch

end VRCycle.Continuum
