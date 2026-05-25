-- Example E02: Mode A recognition and lifting
-- VRCycle tutorial for Lean developers.
--
-- Import this file as: import VRCycle.Examples.E02_ModeA
--
-- Demonstrates: how to recognise and apply Mode A (closure under operation).
-- Source: VRCycle.Apparatus.ModeA, VRCycle.Apparatus.Instances.
--
-- WHAT THIS SHOWS:
-- Mode A captures: "if f preserves predicate P, then f lifts to the
-- operational subtype {x : T // P x} at zero cost."
-- The closure proof is always trivial (one-liner); the mathematical
-- interest lies in WHICH operations satisfy Mode A for a given (T, P).
--
-- KEY ARCHITECTURAL POINT (productive triviality):
-- `modeA_liftFn hf` produces a function on the operational subtype
-- definitionally — no proof obligation beyond the Mode A certificate hf.
-- The lift computation rule holds by `rfl`.
--
-- Audience: Lean developers already familiar with Lean 4 syntax.
-- See VR-Apparatus preprint (DOI 10.5281/zenodo.20381417) Section III.

import VRCycle.Apparatus.Instances  -- includes ModeA + IsComputableReal instances

namespace VRCycle.Examples.E02

open VR.Apparatus VR.Audit

-- ============================================================
-- §1. Mode A on IsComputableReal: negation (library certificate)
-- ============================================================

-- `isComputableReal_neg_isModeA` (Instances.lean): negation is Mode A
-- for (ℝ, IsComputableReal).
#check isComputableReal_neg_isModeA
-- : PredicateOperationality.IsModeAOp (P := VR.Audit.IsComputableReal) Neg.neg

-- Lift to the operational subtype using the certificate:
def negComputable :
    {x : ℝ // IsComputableReal x} → {x : ℝ // IsComputableReal x} :=
  PredicateOperationality.modeA_liftFn isComputableReal_neg_isModeA

-- Computation rule: `.val` of the lifted application = negation of input.
-- Holds by `rfl` (modeA_lift is @[simp]).
example (x : {r : ℝ // IsComputableReal r}) :
    (negComputable x).val = -x.val :=
  rfl

-- ============================================================
-- §2. Composing Mode A operations
-- ============================================================

-- `IsModeAOp.compose`: if f and g are both Mode A for (T, P),
-- then g ∘ f is also Mode A. Composition is closed. Profile: [].
example : PredicateOperationality.IsModeAOp (P := IsComputableReal) (Neg.neg ∘ Neg.neg) :=
  isComputableReal_neg_isModeA.compose isComputableReal_neg_isModeA

-- ============================================================
-- §3. Defining Mode A for a custom predicate
-- ============================================================

-- Pattern: define P : T → Prop, prove ∀ x, P x → P (f x), done.

-- Custom predicate: IsEven on ℕ.
def IsEven (n : ℕ) : Prop := ∃ k, n = 2 * k

-- Doubling is Mode A for IsEven: ∀ n, IsEven n → IsEven (2 * n).
-- Witness: ⟨n, rfl⟩ — 2*n = 2*n directly. The input proof hx is unused
-- because the doubling result is always even regardless of whether n is even.
theorem double_isModeA :
    @PredicateOperationality.IsModeAOp ℕ IsEven (2 * ·) :=
  fun n _ => ⟨n, rfl⟩

-- Binary addition of two even numbers: if m = 2*j and n = 2*k, then m+n = 2*(j+k).
-- subst rewrites m and n by their values, then ring closes the arithmetic goal.
theorem add_isModeA₂ :
    @PredicateOperationality.IsModeAOp₂ ℕ IsEven (· + ·) := by
  rintro m n ⟨j, hj⟩ ⟨k, hk⟩
  subst hj; subst hk
  exact ⟨j + k, by ring⟩

-- Lift doubling to the operational subtype:
def doubleEven :
    {n : ℕ // IsEven n} → {n : ℕ // IsEven n} :=
  PredicateOperationality.modeA_liftFn double_isModeA

-- Lift binary addition:
def addEven :
    {n : ℕ // IsEven n} → {n : ℕ // IsEven n} → {n : ℕ // IsEven n} :=
  PredicateOperationality.modeA_liftFn₂ add_isModeA₂

-- Computation rules hold by rfl:
example (n : {n : ℕ // IsEven n}) :
    (doubleEven n).val = 2 * n.val := rfl

example (m n : {n : ℕ // IsEven n}) :
    (addEven m n).val = m.val + n.val := rfl

-- ============================================================
-- §4. Axiom audit
-- ============================================================

-- Mode A core infrastructure: axiom-free.
#print axioms PredicateOperationality.IsModeAOp
-- Expected: does not depend on any axioms
#print axioms PredicateOperationality.modeA_liftFn
-- Expected: does not depend on any axioms
#print axioms PredicateOperationality.IsModeAOp.compose
-- Expected: does not depend on any axioms

-- Mode A on IsComputableReal: inherits ℝ ceiling.
#print axioms isComputableReal_neg_isModeA
-- Expected: [propext, Classical.choice, Quot.sound]

-- Mode A on ℕ predicates.
#print axioms double_isModeA
-- Actual: does not depend on any axioms  (witness ⟨n, rfl⟩ requires nothing)
#print axioms add_isModeA₂
-- Actual: [propext]  (ring uses propext for ℕ arithmetic equalities)

end VRCycle.Examples.E02
