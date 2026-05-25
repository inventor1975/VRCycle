-- Example E01: Using IsComputableReal
-- VRCycle tutorial for Lean developers.
--
-- Import this file as: import VRCycle.Examples.E01_ComputableReals
--
-- Demonstrates: predicate-wrapping apparatus applied to real numbers.
-- Source: VRCycle.Audit.Computable (VR-Audit, Stage 1).
--
-- WHAT THIS SHOWS:
-- `IsComputableReal` is a Prop-valued predicate on mathlib's `ℝ`.
-- It selects the sub-collection of ℝ that has explicit rational
-- approximations with a modulus of convergence.
--
-- KEY ARCHITECTURAL POINT (wrapping principle):
-- There is NO separate type `ComputableReal`. Instead, `IsComputableReal`
-- is a predicate on the existing mathlib type `ℝ`. This is the
-- VR-Apparatus "predicate-wrapping" pattern (PredicateOperationality).
-- The operational sub-collection is {x : ℝ // IsComputableReal x}.
--
-- Audience: Lean developers already familiar with Lean 4 syntax.
-- See VR-Apparatus preprint (DOI 10.5281/zenodo.20381417) for context.

import VRCycle.Audit.Computable

namespace VRCycle.Examples.E01

open VR.Audit

-- ============================================================
-- §1. Witnessing a specific computable real
-- ============================================================

-- Every rational is computable (library theorem). Implicit arg: the real value.
example (q : ℚ) : IsComputableReal (q : ℝ) :=
  IsComputableReal_rat q

-- Canonical constants:
example : IsComputableReal (0 : ℝ) := IsComputableReal_zero
example : IsComputableReal (1 : ℝ) := IsComputableReal_one

-- Explicit witness for 1/3: constant sequence, exact approximation.
-- Note: use `((1/3 : ℚ) : ℝ)` to cast from ℚ, not `(1 : ℝ) / 3` (ℝ-division).
example : IsComputableReal ((1/3 : ℚ) : ℝ) :=
  ⟨fun _ => 1/3,           -- constant rational approximation
   fun _ => 0,             -- modulus: 0 steps (exact, no approximation error)
   fun n k _ => by simp⟩  -- |(1/3 : ℝ) − (1/3 : ℝ)| = 0 ≤ 1/2^n

-- ============================================================
-- §2. The operational subtype
-- ============================================================

-- The predicate partitions ℝ into the operational sub-collection
-- (computable reals with explicit witnesses) and the rest.
-- Elements carry both value and witness. The def is noncomputable
-- because division in ℝ is noncomputable (even though the value is rational).
noncomputable def oneThird : {x : ℝ // IsComputableReal x} :=
  ⟨((1/3 : ℚ) : ℝ), IsComputableReal_rat (1/3)⟩

#check oneThird.val          -- : ℝ
#check oneThird.property     -- : IsComputableReal oneThird.val

-- ============================================================
-- §3. Mode A closure: operations preserving IsComputableReal
-- ============================================================

-- Negation (implicit x argument — pass only the proof):
example (hx : IsComputableReal x) :
    IsComputableReal (-x) :=
  IsComputableReal_neg hx

-- Addition (implicit x y — pass only proofs):
example (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x + y) :=
  IsComputableReal_add hx hy

-- Subtraction:
example (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x - y) :=
  IsComputableReal_sub hx hy

-- Chaining: (x + y) - z is computable if all three are:
example (hx : IsComputableReal x) (hy : IsComputableReal y) (hz : IsComputableReal z) :
    IsComputableReal ((x + y) - z) :=
  IsComputableReal_sub (IsComputableReal_add hx hy) hz

-- ============================================================
-- §4. Axiom audit
-- ============================================================

-- IsComputableReal inherits [propext, Classical.choice, Quot.sound]
-- through mathlib's ℝ infrastructure (Cauchy sequences, Field ℚ).
-- Classical.choice is expected — this is the standard ceiling.
#print axioms IsComputableReal
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms IsComputableReal_add
-- Expected: [propext, Classical.choice, Quot.sound]

end VRCycle.Examples.E01
