-- Example E04: Mode B skeleton — template for a new operational audit
-- VRCycle tutorial for Lean developers.
--
-- Import this file as: import VRCycle.Examples.E04_ModeBSkeleton
--
-- ⚠️  THIS FILE CONTAINS INTENTIONAL `sorry` PLACEHOLDERS. ⚠️
-- This is a SKELETON showing the STRUCTURE of a Mode B proof.
-- In a real audit, each `sorry` is replaced by a structural argument.
-- See VRCycle.Apparatus.ModeB (riesz_extension_isModeBOp) for a
-- fully completed Mode B instance.
--
-- WHAT THIS SHOWS:
-- Mode B captures: "a classical operation f yields an operational result
-- PB(f a) whenever the operand a carries both PA a and witness W a."
-- The three steps for a new Mode B audit:
--   Step 1. Identify PA, PB, W, f.
--   Step 2. Prove IsModeBOp PA PB W f (the certificate).
--   Step 3. Lift: use IsModeBOp.lift to get typed operational outputs.
--
-- WITNESS SPECTRUM (from trivial to rich):
--   Trivial:   W = fun _ => True   — VR-Forms transit (S1-A finding)
--   Predicate: W = PA itself       — Mode A as degenerate Mode B
--   Domain:    HasSeparabilityStructure — Hilbert space case (Separability.lean)
--   Explicit:  Factorisable PA PB f — Riesz/Hahn-Banach (ModeB.lean)
--
-- Audience: Lean developers wanting to add a new operational audit.
-- See VR-Apparatus preprint (DOI 10.5281/zenodo.20381417) Section IV.
-- See VRCycle.Audit.HahnBanach for a complete, sorry-free Mode B instance.

import VRCycle.Apparatus.ModeB
import VRCycle.Apparatus.Factorisation

namespace VRCycle.Examples.E04

open VR.Apparatus

-- ============================================================
-- §1. Mode B with trivial witness (W = fun _ => True)
-- ============================================================

-- The simplest case: no enrichment needed beyond PA.
-- VR-Forms transit `translate_implies_realisable` has this shape.
-- Here: if n is even, then n * n is even — no extra witness needed.

theorem evenSquare_isModeBOp :
    IsModeBOp (fun n : ℕ => ∃ k, n = 2 * k)
              (fun n : ℕ => ∃ k, n = 2 * k)
              (fun _ => True)
              (fun n => n * n) :=
  fun n ⟨k, hk⟩ _ => ⟨2 * k * k, by subst hk; ring⟩

-- Lift to typed outputs (no sorry here — fully proved):
def evenSquareLift :
    {n : ℕ // (∃ k, n = 2 * k) ∧ True} →
    {n : ℕ // ∃ k, n = 2 * k} :=
  evenSquare_isModeBOp.lift

-- Computation rule:
example (n : {n : ℕ // (∃ k, n = 2 * k) ∧ True}) :
    (evenSquareLift n).val = n.val * n.val := rfl

-- ============================================================
-- §2. Skeleton: Mode B with non-trivial witness (contains sorry)
-- ============================================================

-- Scenario: a "bounded approximation" function on reals.
-- Stand-in predicates (simplified — not mathematically serious):

-- Source predicate: x has a rational approximation.
def HasRatApprox (x : ℝ) : Prop :=
  ∃ (q : ℚ), |x - q| ≤ 1

-- Target predicate: (x + 1) has a rational approximation.
def HasShiftedApprox (y : ℝ) : Prop :=
  ∃ (q : ℚ), |y - q| ≤ 2

-- Witness: no extra condition needed (trivial W).
-- In a real audit W would encode a domain-specific constraint.

-- ── Step 1: State the Mode B claim ──────────────────────────────────
-- Classical operation: fun x => x + 1 (shift by 1).
-- PA: HasRatApprox.  PB: HasShiftedApprox.  W: fun _ => True.
-- f: fun x => x + 1.
--
-- A REAL AUDIT would construct the approximation explicitly:
-- if |x - q| ≤ 1 then |(x+1) - (q+1)| = |x - q| ≤ 1 ≤ 2.
-- This example uses `sorry` to mark where math arguments go.
theorem shiftByOne_isModeBOp :
    IsModeBOp HasRatApprox HasShiftedApprox (fun _ => True) (· + 1) := by
  intro x ⟨q, hq⟩ _
  -- REAL PROOF: |(x+1) - (q+1)| = |x - q| ≤ 1 ≤ 2.
  -- Use hq and basic real arithmetic.
  exact ⟨q + 1, by sorry⟩
  -- ↑ REPLACE `sorry` with: `push_cast; linarith [hq]` or similar.

-- ── Step 2: Lift to typed outputs ───────────────────────────────────
def shiftLift :
    {x : ℝ // HasRatApprox x ∧ True} →
    {y : ℝ // HasShiftedApprox y} :=
  shiftByOne_isModeBOp.lift

-- Computation rule holds by rfl regardless of sorry in the certificate:
example (x : {x : ℝ // HasRatApprox x ∧ True}) :
    (shiftLift x).val = x.val + 1 := rfl

-- ============================================================
-- §3. Factorisable pattern reference
-- ============================================================

-- For a real audit, `Factorisable PA PB f a` witnesses that there exists
-- a computable function g : A → B agreeing with f at operand a.
-- `operand_determines_operational`: Factorisable → PB (f a).
--
-- Usage pattern:
--   theorem myAudit_isFact (a : T) (ha : PA a) :
--       Factorisable PA PB myOp a :=
--     ⟨myExplicitG, ha, myMatchProof⟩  -- g agrees with myOp at a
--
--   theorem myAudit_isModeBOp : IsModeBOp PA PB W myOp :=
--     IsModeBOp_of_factorisable (fun a ha _ => myAudit_isFact a ha)
--
-- See VRCycle.Audit.HahnBanach for the complete Riesz factorisation.

#check @Factorisable
-- : {A : Type*} → {B : Type*} → (A → Prop) → (B → Prop) → (A → B) → A → Prop

#check @operand_determines_operational
-- : PA a → Factorisable PA PB f a → PB (f a)

-- ============================================================
-- §4. Axiom audit
-- ============================================================

-- Mode B core: axiom-free.
#print axioms IsModeBOp
-- Expected: does not depend on any axioms
#print axioms IsModeBOp.lift
-- Expected: does not depend on any axioms
#print axioms IsModeBOp.lift_val
-- Expected: does not depend on any axioms

-- Fully proved instance (no sorry):
#print axioms evenSquare_isModeBOp
-- Expected: [] or [propext] (omega/ring may use propext)

-- Sorry-containing skeleton: reports sorryAx.
#print axioms shiftByOne_isModeBOp
-- Expected: [sorryAx, propext, Classical.choice, Quot.sound]
-- (sorryAx appears because of the sorry placeholder above)

end VRCycle.Examples.E04
