-- VRClassical/Apparatus/InterMorphism.lean — the ZFC→ZFA embedding as an inter-apparatus morphism
-- (split out of VRCycle/Apparatus/InterMorphism.lean and Composition.lean on 2026-09-12: the IAM
-- definitions, lifts and laws stay in the VR core on `[]`; the PSet/CoPSet instance lives here).

import VRCycle.Apparatus.Composition
import VRClassical.Apparatus.QuotientBridge
import VRClassical.Apparatus.Reference
import VRClassical.SetsZFA.API

namespace VR.Apparatus

-- ============================================================
-- §5. Canonical instance: ZFC → ZFA representative embedding
-- ============================================================

/-- The ZFC→ZFA representative embedding `embedPSet : PSet → CoPSet` is an
inter-apparatus morphism from the ZFC apparatus `(PSet, PSet.setoid)` to the
ZFA apparatus `(CoPSet, CoPSet.instSetoid)`.

**Condition**: `PSet.Equiv x y → CoPSet.Equiv (embedPSet x) (embedPSet y)`.

**Proof**: `embedPSet_congr` from VR-Sets-ZFA Embedding.lean (Stage 3 of that work).
The bisimulation argument establishing forward faithfulness of the embedding
is precisely the IAM certificate. `fun x y hxy => VR.SetsZFA.embedPSet_congr hxy`.

**Apparatus reading**:
  Source: `(PSet, PSet.setoid)` — ZFC reference apparatus (instRefOpPSet, Instances.lean).
  Target: `(CoPSet, CoPSet.instSetoid)` — ZFA reference apparatus (instRefOpCoPSet, Reference.lean).

**Methodological re-reading of v0.1.0**:
  `embedPSet_congr_modeA_pattern` (Instances.lean, Group D) stated the same congruence
  as a direct theorem, without the IAM wrapper. The v0.1.0 observation that this was
  "the cross-apparatus Mode A pattern" is now formalised: it IS an IAM certificate.
  Stage 5 (v0.1.0) identified the gap; Stage 2 (v1.0.0) fills it.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from CoPSet.instSetoid/OSetZFA infrastructure:
  PFunctor.M (coinductive M-type) pulls Classical.choice.
  Quot.sound: quotient reasoning. propext: standard ceiling. -/
theorem embedPSet_isInterApparatus :
    @InterApparatusMorphism PSet VR.SetsZFA.CoPSet
      PSet.setoid VR.SetsZFA.CoPSet.instSetoid
      VR.SetsZFA.embedPSet :=
  fun _ _ hxy => VR.SetsZFA.embedPSet_congr hxy

-- ============================================================
-- §6. embedOSet as inter-apparatus lift
-- ============================================================

/-- The ZFC→ZFA quotient embedding `embedOSet : ZFSet → OSetZFA` equals the
lift of the inter-apparatus morphism `embedPSet`.

`embedOSet = embedPSet_isInterApparatus.lift`

**Proof**: for any representative `p : PSet`:
  - LHS: `embedOSet ⟦p⟧ = OSetZFA.mk (embedPSet p)` (by `embedOSet_mk`, `rfl`).
  - RHS: `embedPSet_isInterApparatus.lift ⟦p⟧ = Quotient.mk CoPSet.instSetoid (embedPSet p)`
    (by `lift_mk`, `rfl`). And `OSetZFA.mk = Quotient.mk CoPSet.instSetoid` definitionally.
Both sides are `rfl` at representatives; `Quotient.inductionOn` discharges the quotient.

**Architectural content**:
  VR-Sets-ZFA's `embedOSet` was constructed via `Quotient.lift` with `embedPSet_congr`
  as the well-definedness proof (Embedding.lean §5). The IAM framework re-reads this:
    `embedOSet` = the categorical lift of the IAM `embedPSet`.
  The v0.1.0 construction IS the v1.0.0 IAM lift — the framework retroactively
  formalises the existing embedding in apparatus terms.

**Type note**:
  `ZFSet = Quotient PSet.setoid` (mathlib definition, definitional equality).
  `OSetZFA = Quotient CoPSet.instSetoid` (VR-Sets-ZFA definition, definitional equality).
  Both sides have type `Quotient PSet.setoid → Quotient CoPSet.instSetoid`
  (= `ZFSet → OSetZFA`). No coercion needed.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from `embedPSet_isInterApparatus` (CoPSet infrastructure). -/
theorem embedOSet_eq_interApparatus_lift :
    VR.SetsZFA.embedOSet = embedPSet_isInterApparatus.lift := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

-- ============================================================
-- §7. Verification examples
-- ============================================================

-- Identity map is always an IAM (reflexivity of ≈).
example {Q : Type*} [s : Setoid Q] :
    @InterApparatusMorphism Q Q s s id :=
  fun _ _ h => h

-- Composition: identity ∘ embedPSet = embedPSet, certified as IAM.
example : @InterApparatusMorphism PSet VR.SetsZFA.CoPSet
    PSet.setoid VR.SetsZFA.CoPSet.instSetoid (id ∘ VR.SetsZFA.embedPSet) :=
  embedPSet_isInterApparatus.compose (fun _ _ h => h)

-- lift_mk computation: lift at a PSet representative.
example (p : PSet) :
    embedPSet_isInterApparatus.lift (Quotient.mk PSet.setoid p) =
    Quotient.mk VR.SetsZFA.CoPSet.instSetoid (VR.SetsZFA.embedPSet p) :=
  rfl

-- IsModeAOp_of_interApparatus: identity IAM → Mode A map fun q => ⟦q⟧.
example {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.IsModeAOp (fun q => Quotient.mk s q) :=
  IsModeAOp_of_interApparatus (fun _ _ h => h)

-- ============================================================
-- Cross-level example (from Composition.lean §5)
-- ============================================================

-- Cross-level B1: embedPSet_isInterApparatus + IsModeAOp_quotientMk.
-- Well-definedness for composing embedPSet (IAM) with Quotient.mk CoPSet.instSetoid (Mode A).
example :
    ∀ a b : PSet, a ≈ b →
      (Quotient.mk VR.SetsZFA.CoPSet.instSetoid ∘ VR.SetsZFA.embedPSet) a =
      (Quotient.mk VR.SetsZFA.CoPSet.instSetoid ∘ VR.SetsZFA.embedPSet) b :=
  interApparatus_comp_modeA_wd embedPSet_isInterApparatus
    ReferenceOperationality.IsModeAOp_quotientMk

#print axioms embedPSet_isInterApparatus
#print axioms embedOSet_eq_interApparatus_lift

end VR.Apparatus
