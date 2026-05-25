-- VR-Apparatus: module index (DOI TBD — v0.1.0)
-- Lean 4 formalisation of the VR-Apparatus methodological apparatus.
--
-- STAGES COMPLETE: 1, 2, 3, 5 (Stage 4 merged into Stage 1; Stage 6 = this polish).
-- TOTAL: 35 public objects, 1501 lines across 6 implementation files.
--
-- ============================================================
-- ## Architecture overview
-- ============================================================
--
-- VR-Apparatus formalises the **methodological apparatus** used implicitly
-- in the six prior VR cycle works (VR, VR-Numbers, VR-Sets, VR-Forms,
-- VR-Audit, VR-Sets-ZFA). Two apparatus modes, two transit modes.
--
-- ### Two apparatus modes (Finding B, PLAN.md)
--
-- **Predicate-wrapping** (VRCycle.Apparatus.Wrapping):
--   Objects identified by position in a classical type T.
--   Predicate P : T → Prop selects the operational sub-collection.
--   Identity: AsPoint. Examples: IsComputableReal on ℝ.
--   Class: PredicateOperationality (marker, no fields — operations type-specific).
--
-- **Reference semantics** (VRCycle.Apparatus.Reference):
--   Objects identified by position in a membership graph.
--   Pre-set type Q with setoid [s : Setoid Q]; quotient Quotient s is the
--   operational type. Identity: AsReference.
--   Examples: OSetZFA (Quotient CoPSet.instSetoid), ZFSet (Quotient PSet.setoid).
--   Class: ReferenceOperationality (two fields: membership, ext — uniform across cases).
--
-- ### Two transit modes (Finding A, PLAN.md)
--
-- **Mode A — guaranteed transit** (VRCycle.Apparatus.ModeA):
--   If operation f stays within the operational register (f preserves P, or f
--   respects ≈), extraction is free. Certificate → lifted function.
--   Predicate-wrapping: IsModeAOp P f → modeA_liftFn : {x // P x} → {x // P x}.
--   Reference semantics: IsModeAOp f → modeA_liftFn : Quotient s → Quotient s.
--   Apparatus-structure-independent: no [PredicateOperationality] or
--   [ReferenceOperationality] needed in the signature.
--
-- **Mode B — conditional transit** (VRCycle.Apparatus.ModeB):
--   Classically-constructed operation f is operationally evaluable on
--   operationally-enriched operands. Operationality flows FROM the operand
--   THROUGH the classical operation to the result.
--   IsModeBOp PA PB W f: ∀ a, PA a → W a → PB (f a).
--   Mode A is the special case W = fun _ => True.
--   Concrete instance: VR-Audit-1 Riesz extension (Hahn-Banach on Hilbert).
--
-- ### Identity nature (VRCycle.Apparatus.Identity)
--   IdentityNature: AsPoint | AsReference.
--   Usage indicator (not type property): the same Lean type may be used
--   as AsPoint in one context, AsReference in another.
--
-- ============================================================
-- ## Known limitation — v0.1.0 scope
-- ============================================================
--
-- **Endomorphisms only in ReferenceOperationality.IsModeAOp** (Finding Stage5-A):
-- ReferenceOperationality.IsModeAOp handles operations f : Q → Quotient s
-- where the target quotient is the SAME as the source setoid's quotient.
-- This is an ENDOMORPHISM condition.
--
-- Cross-apparatus HETEROMORPHISMS — maps from one reference apparatus to another
-- (e.g., embedPSet : PSet → CoPSet, inducing ZFSet → OSetZFA) — are NOT directly
-- expressible via IsModeAOp. They are handled as direct congruence theorems
-- (see embedPSet_congr_modeA_pattern in Apparatus.Instances).
--
-- Future apparatus version may introduce a cross-apparatus morphism concept.
-- This is the identified scope boundary for v0.1.0.
--
-- ============================================================
-- ## Comprehensive axiom audit — all 35 public objects
-- ============================================================
--
-- Profile key:
--   [] = axiom-free
--   [P,Q] = [propext, Quot.sound]
--   [P,C,Q] = [propext, Classical.choice, Quot.sound]  (standard ceiling)
--
-- Identity.lean (2 objects):
--   IdentityNature                              []
--   IdentityNature.AsPoint_ne_AsReference       []
--
-- Wrapping.lean (3 objects):
--   PredicateOperationality                     []
--   PredicateOperationality.identityNature      []
--   (instance : PredicateOperationality ℝ _)   []
--
-- Reference.lean (3 objects):
--   ReferenceOperationality                     []
--   ReferenceOperationality.identityNature      []
--   instRefOpCoPSet                             [P,C,Q]  ← CoPSet/PFunctor.M infra
--
-- ModeA.lean (13 objects):
--   PredicateOperationality.IsModeAOp           []
--   PredicateOperationality.IsModeAOp₂          []
--   PredicateOperationality.modeA_liftFn        []
--   PredicateOperationality.modeA_lift  @[simp] []
--   PredicateOperationality.modeA_liftFn₂       []
--   PredicateOperationality.modeA_lift₂ @[simp] []
--   PredicateOperationality.IsModeAOp.compose   []
--   ReferenceOperationality.IsModeAOp           []
--   ReferenceOperationality.modeA_liftFn        []
--   ReferenceOperationality.modeA_lift  @[simp] []
--   ReferenceOperationality.IsModeAOp.compose   []
--   isComputableReal_add_isModeA                [P,C,Q]
--   osetZFA_singleton_isModeA                   [P,C,Q]
--
-- ModeB.lean (9 objects):
--   IsModeBOp                                   []
--   IsModeBOp.lift                              []
--   IsModeBOp.lift_val              @[simp]     []
--   PredicateOperationality.IsModeAOp_iff_IsModeBOp  []
--   PredicateOperationality.IsModeAOp.toModeBOp      []
--   IsModeBOp.compose                           []
--   riesz_extension_map                         [P,C,Q]
--   riesz_extension_isModeBOp                   [P,C,Q]
--   riesz_mode_b_lift                           [P,C,Q]
--
-- Instances.lean (5 objects):
--   isComputableReal_neg_isModeA                [P,C,Q]
--   isComputableReal_sub_isModeA                [P,C,Q]
--   instRefOpPSet                               [P,Q]    ← ZFC, no Classical.choice
--   osetZFA_empty_isModeA                       [P,C,Q]
--   embedPSet_congr_modeA_pattern               [P,C,Q]
--
-- TOTALS:
--   Axiom-free []:         24 objects (69%)
--   Sub-ceiling [P,Q]:      1 object  (3%)   — instRefOpPSet (ZFC apparatus)
--   Standard ceiling [P,C,Q]: 10 objects (28%)
--   Total: 35 objects.
--
-- The high proportion of axiom-free infrastructure (24/35) reflects
-- the constructive nature of the apparatus framework. Classical machinery
-- enters only through concrete instances (Riesz, CoPSet, IsComputableReal).
--
-- Asymmetry note: instRefOpPSet [P,Q] < instRefOpCoPSet [P,C,Q].
-- PSet (inductive) vs CoPSet (coinductive/M-type) — foundational asymmetry
-- between ZFC (well-founded) and ZFA (admits non-well-founded sets) manifests
-- in axiom profiles. ZFC apparatus is axiomatically lighter.
--
-- ============================================================
-- ## Stage contents
-- ============================================================
--
-- Stage 1: IdentityNature, PredicateOperationality, ReferenceOperationality
--          (VRCycle.Apparatus.Identity, Wrapping, Reference)
-- Stage 2: Mode A closure theorem for both apparatus modes
--          (VRCycle.Apparatus.ModeA)
-- Stage 3: Mode B schema — conditional operational extraction
--          (VRCycle.Apparatus.ModeB)
-- Stage 4: Apparatus split (SKIPPED — merged into Stage 1)
-- Stage 5: Instance enrichment — additional apparatus instances from VR cycle
--          (VRCycle.Apparatus.Instances)
-- Stage 6: API polish — @[simp] additions, module documentation (this file)

import VRCycle.Apparatus.Identity
import VRCycle.Apparatus.Wrapping
import VRCycle.Apparatus.Reference
import VRCycle.Apparatus.ModeA
import VRCycle.Apparatus.ModeB
import VRCycle.Apparatus.Instances

-- ============================================================
-- Cross-apparatus verification (requires both Wrapping + Reference)
-- ============================================================

-- These examples require IsComputableReal (from Wrapping) and
-- OSetZFA (from Reference), so they live here in the module index.

namespace VR.Apparatus

/-- The predicate-wrapping apparatus (IsComputableReal) has AsPoint identity. -/
example : @PredicateOperationality.identityNature ℝ VR.Audit.IsComputableReal _ =
    IdentityNature.AsPoint := rfl

/-- The reference semantics apparatus (OSetZFA) has AsReference identity. -/
example : @ReferenceOperationality.identityNature
    VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid instRefOpCoPSet =
    IdentityNature.AsReference := rfl

/-- The two apparatus modes are categorically distinct. -/
example : IdentityNature.AsPoint ≠ IdentityNature.AsReference := by decide

-- ============================================================
-- Spot-check axiom audit (Stage 6) — one from each profile tier
-- ============================================================

section SpotCheckAxioms

-- Tier 1: axiom-free (representative: Mode B infrastructure)
#print axioms IsModeBOp.lift_val
-- Expected: 'VR.Apparatus.IsModeBOp.lift_val' does not depend on any axioms

-- Tier 2: sub-ceiling (the single sub-ceiling object)
#print axioms instRefOpPSet
-- Expected: 'VR.Apparatus.instRefOpPSet' depends on axioms: [propext, Quot.sound]

-- Tier 3: standard ceiling (representative: concrete Mode B instance)
#print axioms riesz_extension_isModeBOp
-- Expected: [propext, Classical.choice, Quot.sound]

end SpotCheckAxioms

end VR.Apparatus
