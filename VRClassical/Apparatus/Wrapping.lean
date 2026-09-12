-- VRClassical/Apparatus/Wrapping.lean — classical instances of the predicate-wrapping apparatus
-- (split out of VRCycle/Apparatus/Wrapping.lean on 2026-09-12: the class stays in the VR core on
-- `[]`; the instance over Mathlib's ℝ lives here).

import VR.Apparatus.Wrapping
import VRClassical.Audit.Computable

namespace VR.Apparatus

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

end VR.Apparatus
