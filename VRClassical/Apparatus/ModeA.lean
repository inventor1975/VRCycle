-- VRClassical/Apparatus/ModeA.lean — classical Mode A instances (ℝ/IsComputableReal, OSetZFA)
-- (split out of VRCycle/Apparatus/ModeA.lean on 2026-09-12: the Mode A definitions stay in the VR
-- core on `[]`; the instances over Mathlib's ℝ and over CoPSet live here).

import VR.Apparatus.ModeA
import VRClassical.Apparatus.Wrapping
import VRClassical.Apparatus.Reference
import VRClassical.SetsZFA.API

namespace VR.Apparatus

-- ============================================================
-- §3. Concrete instances
-- ============================================================

/-- Addition on ℝ is a Mode A binary operation for the IsComputableReal apparatus.

**Certificate**: IsComputableReal_add (VR-Audit Stage 1):
if x, y : ℝ have explicit rational approximations with moduli, so does x + y.

**Named-argument form** `(P := VR.Audit.IsComputableReal)`: T = ℝ is inferred
from P : ℝ → Prop; `[PredicateOperationality ℝ IsComputableReal]` is found
from the instance in Wrapping.lean.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from IsComputableReal_add (standard ceiling). -/
theorem isComputableReal_add_isModeA :
    PredicateOperationality.IsModeAOp₂ (P := VR.Audit.IsComputableReal) (· + ·) :=
  fun _ _ hx hy => VR.Audit.IsComputableReal_add hx hy

-- Case 2: OSetZFA.singleton is IsModeAOp for CoPSet reference semantics.

/-- Representative-level singleton map: sends CoPSet a to the OSetZFA singleton
containing OSetZFA.mk a.

**noncomputable**: OSetZFA.singleton uses Quotient.liftOn with classical CoPSet
infrastructure. -/
private noncomputable def osetZFA_singleton_rep :
    VR.SetsZFA.CoPSet → VR.SetsZFA.OSetZFA :=
  fun a => VR.SetsZFA.OSetZFA.singleton (VR.SetsZFA.OSetZFA.mk a)

/-- The singleton map is Mode A for the CoPSet reference semantics apparatus.

**Certificate**: a ≈ b → OSetZFA.sound gives OSetZFA.mk a = OSetZFA.mk b;
then congrArg OSetZFA.singleton concludes.

No access to the private `singleton_congr` needed: well-definedness of
OSetZFA.singleton is recovered via OSetZFA.sound + congrArg.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  OSetZFA.sound uses Quot.sound; CoPSet infra (PFunctor.M) uses Classical.choice. -/
theorem osetZFA_singleton_isModeA :
    @ReferenceOperationality.IsModeAOp
      VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid
      osetZFA_singleton_rep :=
  fun _ _ hab =>
    congrArg VR.SetsZFA.OSetZFA.singleton (VR.SetsZFA.OSetZFA.sound hab)

-- ============================================================
-- §4. Verification examples
-- ============================================================

-- Binary lift computation rule: rfl.
example (x y : {r : ℝ // VR.Audit.IsComputableReal r}) :
    (PredicateOperationality.modeA_liftFn₂ isComputableReal_add_isModeA x y).val =
    x.val + y.val :=
  rfl

-- Composition: double negation is Mode A.
example : PredicateOperationality.IsModeAOp
    (P := VR.Audit.IsComputableReal) (fun x => -(-(x))) :=
  PredicateOperationality.IsModeAOp.compose
    (fun _ hx => VR.Audit.IsComputableReal_neg hx)
    (fun _ hx => VR.Audit.IsComputableReal_neg hx)

#print axioms isComputableReal_add_isModeA
#print axioms osetZFA_singleton_isModeA

end VR.Apparatus
