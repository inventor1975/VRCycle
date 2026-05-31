-- VR-Apparatus: Wrapping (DOI TBD — v0.1.0)
-- Stage 1: PredicateOperationality — marker class for predicate-wrapping apparatus.
--
-- STAGE: 1 (of 7). SOURCE: PLAN.md Stage 1; CLAUDE.md §Apparatus modes.
--
-- ## Position statement
-- Defines `PredicateOperationality T P` — the marker class for the
-- predicate-wrapping apparatus used throughout VR-Audit.
--
-- ## Design: marker class with no fields (Prop-valued)
-- `PredicateOperationality T P : Prop` is a *declaration* that the pair
-- (T : Type*, P : T → Prop) forms a predicate-wrapping apparatus:
--   - T is the classical type (formal register substrate)
--   - P selects the operational sub-collection (operational register)
--   - Identity mode: AsPoint (objects identified by position in T)
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- The class has no fields. This is intentional and correct:
--
-- Predicate-wrapping *operations* are type-specific:
--   IsComputableReal: closed under +, -, ¬, rat (ℝ-specific)
--   OperationalHilbertSpace: fields are denseSeq, inner_computable (E-specific)
--   OperationalNormableFunctional: fn_computable, norm_computable (functional-specific)
--
-- These cannot be uniformly abstracted into a single class. The mathematical
-- content — closure under operations — lives in:
--   (a) the specific instances (IsComputableReal_add, etc.),
--   (b) Stage 2: Mode A closure theorem with explicit operation parameters.
--
-- Compare: ReferenceOperationality HAS fields (membership, ext) because these
-- ARE uniform across all reference semantics cases. This asymmetry is honest.
--
-- ## Axiom profile
-- PredicateOperationality class itself: [].
-- Instance `PredicateOperationality ℝ IsComputableReal`: [] (Prop marker only).
-- identityNature def: [].

import VRCycle.Apparatus.Identity
import VRCycle.Audit.Computable

namespace VR.Apparatus

-- ============================================================
-- §1. PredicateOperationality class
-- ============================================================

/-- PredicateOperationality T P: marker for predicate-wrapping apparatus.

Declares that the pair (T : Type*, P : T → Prop) forms a predicate-wrapping
apparatus in the VR methodology:
  - T is the classical type (formal register substrate, e.g. ℝ, E : Type*)
  - P selects the operational sub-collection (e.g. IsComputableReal, OperationalHilbertSpace)
  - Identity mode: AsPoint — objects identified by position in T

**Design (marker class)**: `PredicateOperationality T P : Prop` has no fields.
Instances are declarations, not computations. The mathematical content is in
the specific instances and in Stage 2 (Mode A closure theorem).

**Asymmetry with ReferenceOperationality**: `ReferenceOperationality` has
substantive fields (`membership`, `ext`) because membership and extensionality
are uniform across all reference semantics cases. `PredicateOperationality`
operations (add, neg, inner product, ...) are type-specific — not uniform.
This asymmetry is intentional, not an oversight.

**Instance use pattern**: theorems can take `[PredicateOperationality T P]`
as hypothesis to indicate they operate within a predicate-wrapping context.
Stage 2 will use this in the Mode A closure theorem.

## Axiom profile: [] (Prop class, no fields) -/
class PredicateOperationality (T : Type*) (P : T → Prop) : Prop

-- ============================================================
-- §2. Identity nature
-- ============================================================

/-- The identity nature of every predicate-wrapping apparatus is AsPoint.

Objects in a predicate-wrapping apparatus are identified by their position
in the classical type T. The predicate P then certifies operational status.
This is always AsPoint — the definition of the predicate-wrapping mode.

## Axiom profile: [] -/
def PredicateOperationality.identityNature
    {T : Type*} {P : T → Prop} [PredicateOperationality T P] :
    IdentityNature :=
  .AsPoint

-- ============================================================
-- §3. Test instance: IsComputableReal over ℝ
-- ============================================================

/-- IsComputableReal is a predicate-wrapping apparatus over ℝ.

The classical type is ℝ (mathlib's `Real`); the operational predicate is
`IsComputableReal` (VR-Audit Stage 1, Computable.lean):

  `IsComputableReal x := ∃ (alg : ℕ → ℚ) (mod : ℕ → ℕ),
     ∀ n k, mod n ≤ k → |(alg k : ℝ) - x| ≤ 1/2^n`

Objects `x : ℝ` are identified as real numbers (AsPoint). The predicate
certifies that x has explicit rational approximations with modulus.

This instance has no content beyond the declaration. The substantive
apparatus (closure under +, -, ¬, rat) is in VRCycle.Audit.Computable.

## Axiom profile: [] (marker instance, Prop) -/
instance : PredicateOperationality ℝ VR.Audit.IsComputableReal := ⟨⟩

-- ============================================================
-- §4. Verification
-- ============================================================

/-- The identity nature of the IsComputableReal apparatus is AsPoint. -/
example : @PredicateOperationality.identityNature ℝ VR.Audit.IsComputableReal _ =
    IdentityNature.AsPoint := rfl

-- ============================================================
-- Axiom audit — Stage 1, Wrapping.lean
-- ============================================================
-- STAGE: 1. SOURCE: PLAN.md Stage 1.
-- LEAN OBJECTS (1 class, 1 def, 1 instance):
--   PredicateOperationality (class, Prop, 0 fields)
--   PredicateOperationality.identityNature (def)
--   instance PredicateOperationality ℝ IsComputableReal
-- AXIOM AUDIT: expected [] for all objects in this file.
--   The marker class and its instance introduce no proof obligations.
--   identityNature returns a constructor — no axioms.
-- CHECKS: no sorry, no admit.

#print axioms PredicateOperationality
#print axioms PredicateOperationality.identityNature

end VR.Apparatus
