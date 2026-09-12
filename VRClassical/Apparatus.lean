-- VRClassical/Apparatus.lean — classical-register / bridge modules of Apparatus (see VRClassical.lean).

import VRCycle.Apparatus
import VRClassical.Apparatus.Instances
import VRClassical.Apparatus.QuotientBridge
import VRClassical.Apparatus.Separability
import VRClassical.Apparatus.Numbers
import VRClassical.Apparatus.Wrapping
import VRClassical.Apparatus.Reference
import VRClassical.Apparatus.ModeA
import VRClassical.Apparatus.ModeB
import VRClassical.Apparatus.Factorisation
import VRClassical.Apparatus.InterMorphism

namespace VR.Apparatus

-- Cross-apparatus verification (moved from VRCycle/Apparatus.lean, 2026-09-12).

/-- The predicate-wrapping apparatus (IsComputableReal) has AsPoint identity. -/
example : @PredicateOperationality.identityNature ℝ VR.Audit.IsComputableReal _ =
    IdentityNature.AsPoint := rfl

/-- The reference semantics apparatus (OSetZFA) has AsReference identity. -/
example : @ReferenceOperationality.identityNature
    VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid instRefOpCoPSet =
    IdentityNature.AsReference := rfl

-- Tier 4 spot check: [propext, Classical.choice, Quot.sound] (concrete Mode B)
-- Tier 4: [propext, Classical.choice, Quot.sound] (representative: concrete Mode B)
#print axioms riesz_extension_isModeBOp
-- Expected: 'VR.Apparatus.riesz_extension_isModeBOp' depends on axioms:
--           [propext, Classical.choice, Quot.sound]


-- Tier 2: [Quot.sound] (representative: IAM lift — NEW tier in v1.0.0)
#print axioms InterApparatusMorphism.lift_mk
-- Expected: 'VR.Apparatus.InterApparatusMorphism.lift_mk' depends on axioms: [Quot.sound]


end VR.Apparatus
