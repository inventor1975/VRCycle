-- VRClassical/Apparatus/Reference.lean — classical instance of the reference apparatus (OSetZFA)
-- (split out of VRCycle/Apparatus/Reference.lean on 2026-09-12: the class stays in the VR core on
-- `[]`; the instance over CoPSet/PFunctor.M lives here).

import VRCycle.Apparatus.Reference
import VRClassical.SetsZFA.Membership

namespace VR.Apparatus

-- ============================================================
-- §4. Main instance: OSetZFA
-- ============================================================

-- Technical notes on Q2 (implicit/explicit matching for OSetZFA.ext):
--
-- OSetZFA.ext signature:
--   theorem OSetZFA.ext {x y : OSetZFA} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y
-- Class field expects:
--   ∀ x y : Quotient s, (∀ z, membership z x ↔ membership z y) → x = y
--
-- After membership := OSetZFA.Mem and s := CoPSet.instSetoid:
--   membership z x   = OSetZFA.Mem z x   = (z ∈ x)  [via instMembership]
--   Quotient s       = OSetZFA            [definitional]
--
-- Field becomes:
--   ∀ x y : OSetZFA, (∀ z : OSetZFA, z ∈ x ↔ z ∈ y) → x = y
-- which matches OSetZFA.ext (with explicit x y via wrapper lambda).
--
-- Q2 RESULT: `ext := fun x y h => OSetZFA.ext h` works directly.
-- No `show`/`change` needed. Lean sees through the definitional equalities.
--
-- Axiom note: instRefOpCoPSet carries [propext, Classical.choice, Quot.sound].
-- Classical.choice enters transitively through CoPSet = PFunctor.M CoPSetFunctor
-- (mathlib's M-type construction uses Classical.choice in termination proofs).
-- This is the standard ceiling for all VR-Sets-ZFA work. Acceptable.

/-- OSetZFA is a reference semantics apparatus over CoPSet.

Pre-set type:    CoPSet (coinductive trees, PFunctor.M CoPSetFunctor).
Setoid:          CoPSet.instSetoid (extensional cobisimulation, Cobisimulation.lean).
Quotient:        OSetZFA = Quotient CoPSet.instSetoid (ZFA set universe).
Membership:      OSetZFA.Mem (lifted from CoPSet.mem via liftOn₂, Membership.lean).
Extensionality:  OSetZFA.ext (bisimulation argument, Membership.lean).

This apparatus underlies VR-Sets-ZFA: AFA holds in OSetZFA as a theorem.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  propext:         from OSetZFA.ext → CoPSet.mem_congr → propext.
  Classical.choice: from CoPSet = PFunctor.M (mathlib M-type infrastructure).
  Quot.sound:      from OSetZFA.Mem (liftOn₂) and OSetZFA.ext (Quotient.sound).
  Within standard ceiling [propext, Classical.choice, Quot.sound]. ✓ -/
instance instRefOpCoPSet :
    @ReferenceOperationality
      VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid where
  membership := VR.SetsZFA.OSetZFA.Mem
  ext := fun x y h => @VR.SetsZFA.OSetZFA.ext x y h

-- ============================================================
-- §5. Verification (Reference.lean scope)
-- ============================================================

-- Local verification examples — cross-apparatus comparison lives in Apparatus.lean
-- (which imports both Wrapping.lean and Reference.lean).

/-- The identity nature of the OSetZFA apparatus is AsReference. -/
example : @ReferenceOperationality.identityNature
    VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid instRefOpCoPSet =
    IdentityNature.AsReference := rfl

/-- The two IdentityNature constructors are distinct. -/
example : IdentityNature.AsReference ≠ IdentityNature.AsPoint := by decide

#print axioms instRefOpCoPSet

end VR.Apparatus
