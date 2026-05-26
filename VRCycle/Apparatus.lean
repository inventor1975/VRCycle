-- VR-Apparatus: module index (DOI TBD — v1.0.0)
-- Lean 4 formalisation of the VR-Apparatus methodological apparatus.
--
-- v0.1.0: 35 public objects, 1655 lines across 6 implementation files.
-- v1.0.0: 68 public objects, 3430 lines across 12 implementation files.
--         33 new objects across 6 new files. Zero sorry. Zero warnings.
--
-- ============================================================
-- ## Architecture overview — v1.0.0
-- ============================================================
--
-- VR-Apparatus formalises the **methodological apparatus** used implicitly
-- in the six prior VR cycle works (VR, VR-Numbers, VR-Sets, VR-Forms,
-- VR-Audit, VR-Sets-ZFA). Two apparatus modes, two transit modes.
--
-- ### Two apparatus modes
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
-- ### Four morphism levels — v1.0.0 architectural picture
--
-- Level 1 (Predicate Mode A): f : T → T preserving P : T → Prop.
--   PredicateOperationality.IsModeAOp.
--   Subtype lifting: {x // P x} → {x // P x}.
--
-- Level 2 (Reference Mode A): f : Q → Quotient s respecting setoid s.
--   ReferenceOperationality.IsModeAOp (endomorphism condition).
--   Quotient lifting: Quotient s → Quotient s.
--
-- Level 3 (InterApparatusMorphism): f : Q1 → Q2 respecting s1 → s2.
--   Representative-level (not quotient-level). Cross-apparatus morphisms.
--   Canonical example: PSet.ofNat : (ℕ, =) → (PSet, PSet.Equiv).
--
-- Level 4 (Mode B): ∀ a, PA a → W a → PB (f a). Predicate transit.
--   Canonical example: Riesz extension (Hahn-Banach on Hilbert).
--   VR-Forms canonical example: translate_pi → isRealisable (W = True).
--
-- ### Two parallel tracks (Finding S3-A)
--
-- The four levels form TWO structurally distinct tracks with no natural bridge:
--
-- PREDICATE TRACK (Levels 1 + 4):
--   Level 1 (Predicate Mode A) ↔ Level 4 (Mode B) via IsModeAOp_iff_IsModeBOp.
--   Predicate → Predicate transit. W witnesses operand enrichment.
--   Identity: IsModeAOp_id (Level 1), IsModeBOp_id (Level 4).
--
-- REFERENCE TRACK (Levels 2 + 3):
--   Level 3 (IAM, same setoid) → Level 2 (Ref Mode A) via IsModeAOp_of_interApparatus.
--   Cross-apparatus composition: interApparatus_comp_modeA_wd.
--   Identity: IsModeAOp_quotientMk (Level 2), id_isInterApparatus (Level 3).
--
-- Cross-track non-composability (structural): Mode B (predicate) cannot naturally
-- compose with IAM (setoid), nor with Reference Mode A (quotient endomorphism).
-- The type system enforces this separation. See Composition.lean §4.
--
-- ### Architectural layers — v1.0.0 Tier structure
--
-- Tier 1 — Apparatus instances:
--   PredicateOperationality, ReferenceOperationality (Identity, Wrapping, Reference).
--
-- Tier 2 — Domain structures:
--   HasSeparabilityStructure — separability as formal apparatus hypothesis (Separability).
--
-- Tier 3 — Morphism levels:
--   Mode A (intra-instance endomorphisms) — ModeA.
--   InterApparatusMorphism (between instances, Level 3) — InterMorphism.
--   Mode B with Factorisable witness (predicate transit) — ModeB + Factorisation.
--
-- Tier 4 — Compositional algebra:
--   Identity elements + cross-level composition rules — Composition.
--
-- Tier 5 — Instances and integration:
--   Concrete apparatus instances from VR cycle — Instances.
--   Numbers as hybrid apparatus subjects — Numbers.
--   VR-Forms integration (transit as Mode B) — FormsIntegration.
--
-- ============================================================
-- ## Findings catalog — twelve v1.0.0 methodological findings
-- ============================================================
--
-- These findings emerged during implementation, not from pre-planning.
-- All are formally documented in their respective stage files.
-- This catalog is the preprint reference.
--
-- FINDING S4-A (Factorisation): Operand-not-operation theorem.
--   The witness W in IsModeBOp is Factorisable PA PB f a — existence of a
--   computable function g matching f on the specific operand. Operationality
--   of result determined by operand, not by classical operation. W is not
--   about f globally; it localises to the specific a.
--
-- FINDING S4-B (Factorisation): Factorisable as computability condition.
--   Factorisable witnesses are computability-like conditions: existence of
--   g : {x // PA x} → {x // PB x} matching f on operand a. Mode B with
--   Factorisable is strictly stronger than IsModeBOp (every Factorisable
--   gives Mode B; converse requires Axiom of Choice in general).
--
-- FINDING S6-A (Separability): Separability as apparatus hypothesis.
--   HasSeparabilityStructure T provides, via separability_provides_factorisable,
--   a Factorisable witness for the Riesz extension. Domain-specific structure
--   flows into the apparatus as a formal hypothesis, not a classical axiom.
--   This is the Tier 2 → Tier 3 connection in the architectural layer picture.
--
-- FINDING S2-A (InterMorphism): Layered structure, type-system enforced.
--   Mode A (quotient level) and IAM (representative level) are DISTINCT layers.
--   IAM f : Q1 → Q2 respecting setoids CANNOT be directly read as a Mode A
--   operation on Quotient s1. IsModeAOp_of_interApparatus is a ONE-WAY bridge
--   (same-setoid IAM → Level 2 Mode A), not a setoid isomorphism.
--
-- FINDING S2-B (InterMorphism): New axiom sub-ceiling [Quot.sound].
--   IAM lift infrastructure uses only Quot.sound — between axiom-free and
--   [propext, Quot.sound] in strength. This is a new sub-sub-ceiling tier absent
--   from v0.1.0. IAM lift needs Quotient.sound to identify quotient elements;
--   it does NOT need propext (no iff-to-eq reasoning) or Classical.choice.
--
-- FINDING S3-A (Composition): Two parallel tracks, no natural bridge.
--   The apparatus framework has two structurally distinct architectures
--   (predicate track + reference track) that do not naturally compose
--   cross-track. This is not an oversight — it reflects the genuine
--   structural asymmetry between predicate-selecting and setoid-quotienting.
--   Headline architectural observation for the preprint.
--
-- FINDING S3-B (Composition): IsModeAOp endomorphism constraint, type-enforced.
--   ReferenceOperationality.IsModeAOp requires f : Q → Quotient s where the
--   target quotient is the SAME setoid as the source. Cross-apparatus
--   composition (s1 ≠ s2) cannot use IsModeAOp; interApparatus_comp_modeA_wd
--   states the raw Prop directly. The type system makes this constraint explicit.
--
-- FINDING S3-C (Composition): Productive triviality as mathematical content.
--   Identity elements for all four morphism levels are proved by trivially-simple
--   proofs (fun _ hx => hx, fun _ _ hab => Quotient.sound hab, etc.). The
--   accumulation of 8 such instances across Stages 2-3 IS the content — it
--   demonstrates the apparatus framework is closed under identity. Simplicity
--   of proof is not weakness but witness to the framework's coherence.
--
-- FINDING S5-A (Numbers): Lens applicability depends on natural structure.
--   Multi-lens capability is STRUCTURED, not uniform: ℝ with IsComputableReal
--   is natural (predicate lens); ℝ with Cauchy reference lens is artificial
--   (Cauchy sequences carry no natural membership relation). ℕ with von Neumann
--   ordinals is natural (reference lens; ordinals ARE sets with membership).
--   Apparatus framework does not force uniform applicability — honesty wins.
--
-- FINDING S5-B (Numbers): Axiom asymmetry between apparatus tracks.
--   Analysis track (ℝ, Cauchy): even trivially-proved objects inherit standard
--   ceiling [propext, Classical.choice, Quot.sound] through type elaboration of
--   Field ℚ / IsAbsoluteValue / LinearOrder infrastructure. Set-theory track
--   (ℕ, PSet, ZFC): axiom-free throughout. Mirrors v0.1.0 Finding B-B
--   (ZFC axiomatically lighter than ZFA). Systematic pattern.
--
-- FINDING S1-A (FormsIntegration): Generic Register abstraction unnecessary.
--   Planned Stage 1 deliverable was a generic Register structure + DirectionalMorphism
--   typeclass. Reconnaissance showed: (a) VR-Forms already has `Register` (inductive
--   | ontological | formal); (b) DirectionalMorphism type-mismatches transit (predicate
--   implication ≠ morphism between setoid types); (c) translate_implies_realisable IS
--   IsModeBOp with W = True. The v0.1.0 Mode B schema already captures VR-Forms transit.
--   Stage 1 = recognition that the apparatus framework suffices without extension.
--
-- FINDING S1-B (FormsIntegration): Three-way identity nature contrast.
--   VR-Forms apparatus anatomy: instPredicateOpTranslatePi (AsPoint, specific predicate) +
--   instPredicateOpFormalTerm (AsPoint, existential predicate) + instRefOpPSet (AsReference,
--   ontological register). Two predicate-wrapping for the formal register; one reference-
--   semantics for the operational register. Transit (Mode B) connects the two AsPoint
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- ontological levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--   instances. The ontological apparatus is the target universe.
--
-- ============================================================
-- ## Known limitations — v1.0.0 scope
-- ============================================================
--
-- LIMITATION 1 (carried from v0.1.0): Endomorphisms only in Ref IsModeAOp.
--   ReferenceOperationality.IsModeAOp handles f : Q → Quotient s where target
--   is the SAME setoid's quotient. Heteromorphisms (PSet → CoPSet, inducing
--   ZFSet → OSetZFA) are handled as direct congruence theorems, not via IsModeAOp.
--   Resolved at Level 3 (InterApparatusMorphism) — but IAM is representative-level,
--   not quotient-level. A cross-apparatus quotient morphism concept remains future work.
--
-- LIMITATION 2 (new in v1.0.0): Cross-track non-composability.
--   Mode B (predicate track, Level 4) and IAM (reference track, Level 3) cannot
--   be composed without additional structure (a predicate tracking setoid classes).
--   The three structural non-composabilities are documented in Composition.lean §4.
--   This is a genuine architectural boundary, not an implementation gap.
--
-- LIMITATION 3 (new in v1.0.0): Artificial reference lens for ℝ.
--   Cauchy abs = Quotient CauSeq.equiv is the reference carrier for reals, bridged
--   to ℝ by Real.equivCauchy. But Cauchy sequences carry no natural membership
--   relation — ReferenceOperationality instance for CauSeq ℚ abs is artificial.
--   Documented in Numbers.lean §1 with explicit non-construction rationale.
--
-- ============================================================
-- ## Comprehensive axiom audit — all 68 public objects
-- ============================================================
--
-- Profile key:
--   []    = axiom-free
--   [Q]   = [Quot.sound]                                  ← NEW TIER in v1.0.0
--   [P,Q] = [propext, Quot.sound]
--   [P,C,Q] = [propext, Classical.choice, Quot.sound]    (standard ceiling)
--
-- ── v0.1.0 objects (35) ──────────────────────────────────────────────────────
--
-- Identity.lean (2 objects):
--   IdentityNature                                        []
--   IdentityNature.AsPoint_ne_AsReference                 []
--
-- Wrapping.lean (3 objects):
--   PredicateOperationality                               []
--   PredicateOperationality.identityNature                []
--   (instance : PredicateOperationality ℝ _)             []
--
-- Reference.lean (3 objects):
--   ReferenceOperationality                               []
--   ReferenceOperationality.identityNature                []
--   instRefOpCoPSet                                       [P,C,Q]  ← CoPSet/M-type
--
-- ModeA.lean (13 objects):
--   PredicateOperationality.IsModeAOp                     []
--   PredicateOperationality.IsModeAOp₂                   []
--   PredicateOperationality.modeA_liftFn                  []
--   PredicateOperationality.modeA_lift          @[simp]   []
--   PredicateOperationality.modeA_liftFn₂                []
--   PredicateOperationality.modeA_lift₂         @[simp]  []
--   PredicateOperationality.IsModeAOp.compose             []
--   ReferenceOperationality.IsModeAOp                     []
--   ReferenceOperationality.modeA_liftFn                  []
--   ReferenceOperationality.modeA_lift          @[simp]   []
--   ReferenceOperationality.IsModeAOp.compose             []
--   isComputableReal_add_isModeA                          [P,C,Q]
--   osetZFA_singleton_isModeA                             [P,C,Q]
--
-- ModeB.lean (9 objects):
--   IsModeBOp                                             []
--   IsModeBOp.lift                                        []
--   IsModeBOp.lift_val                          @[simp]   []
--   PredicateOperationality.IsModeAOp_iff_IsModeBOp       []
--   PredicateOperationality.IsModeAOp.toModeBOp           []
--   IsModeBOp.compose                                     []
--   riesz_extension_map                                   [P,C,Q]
--   riesz_extension_isModeBOp                             [P,C,Q]
--   riesz_mode_b_lift                                     [P,C,Q]
--
-- Instances.lean (5 objects):
--   isComputableReal_neg_isModeA                          [P,C,Q]
--   isComputableReal_sub_isModeA                          [P,C,Q]
--   instRefOpPSet                                         [P,Q]  ← ZFC, no Classical.choice
--   osetZFA_empty_isModeA                                 [P,C,Q]
--   embedPSet_congr_modeA_pattern                         [P,C,Q]
--
-- ── v1.0.0 new objects (33) ──────────────────────────────────────────────────
--
-- Factorisation.lean (8 objects):
--   Factorisable                                          []
--   operand_determines_operational                        []
--   factorisable_implies_isModeBOp                        []
--   IsModeBOp_of_factorisable                             []
--   Factorisable.lift                                     []
--   Factorisable.lift_val                       @[simp]   []
--   riesz_extension_factorisable                          [P,C,Q]
--   riesz_extension_isModeBOp'                            [P,C,Q]
--
-- Separability.lean (3 objects):
--   HasSeparabilityStructure                              []
--   instHasSepStructOfOpHilbert                           [P,C,Q]
--   separability_provides_factorisable                    []
--
-- InterMorphism.lean (8 objects):
--   InterApparatusMorphism                                []
--   InterApparatusMorphism.lift                           [Q]   ← sub-sub-ceiling
--   InterApparatusMorphism.lift_mk              @[simp]   [Q]   ← sub-sub-ceiling
--   IsModeAOp_of_interApparatus                           [Q]   ← sub-sub-ceiling
--   InterApparatusMorphism.compose                        []
--   InterApparatusMorphism.lift_compose                   [Q]   ← sub-sub-ceiling
--   embedPSet_isInterApparatus                            [P,C,Q]
--   embedOSet_eq_interApparatus_lift                      [P,C,Q]
--
-- Composition.lean (7 objects):
--   PredicateOperationality.IsModeAOp_id                  []
--   ReferenceOperationality.IsModeAOp_quotientMk          [Q]   ← sub-sub-ceiling
--   ReferenceOperationality.modeA_liftFn_quotientMk_eq_id [Q]   ← sub-sub-ceiling
--   InterApparatusMorphism.id_isInterApparatus             []
--   IsModeBOp_id                                           []
--   interApparatus_comp_modeA_wd                           []
--   modeA_liftFn_comp_interApparatus                       [Q]   ← sub-sub-ceiling
--
-- Numbers.lean (4 objects):
--   cauchy_abs_isQuotient                                 [P,C,Q]  ← type elab
--   real_cauchy_bridge                                    [P,C,Q]  ← type elab
--   natEqSetoid                                           []
--   nat_vonNeumann_isInterApparatus                       []
--
-- FormsIntegration.lean (3 objects):
--   instPredicateOpFormalTerm                             [P,Q]
--   instPredicateOpTranslatePi                            [P,Q]
--   vr_forms_transit_isModeBOp                            [P,Q]
--
-- ── TOTALS ───────────────────────────────────────────────────────────────────
--
-- Profile                                  v0.1.0  v1.0.0 new  Total    %
-- []  axiom-free                              24        16       40    59%
-- [Q] = [Quot.sound]                           0         7        7    10%
-- [P,Q] = [propext, Quot.sound]                1         3        4     6%
-- [P,C,Q] (standard ceiling)                 10         7       17    25%
-- TOTAL                                       35        33       68
--
-- The [Q] sub-sub-ceiling tier is NEW in v1.0.0: IAM lift infrastructure uses
-- Quot.sound (to identify quotient representatives) but not propext (no iff-to-eq)
-- or Classical.choice. This is an axiom-profile refinement absent from v0.1.0.
--
-- Asymmetry notes:
-- instRefOpPSet [P,Q] < instRefOpCoPSet [P,C,Q] — ZFC (inductive) lighter than ZFA (M-type).
-- FormsIntegration [P,Q] — VR-Forms avoids Classical.choice throughout.
-- Numbers analysis objects [P,C,Q] — type elaboration of Field ℚ pulls ceiling.
--
-- ============================================================
-- ## Stage contents — complete
-- ============================================================
--
-- v0.1.0 (stages 1-6, order 1 → 5, then Stage 6 = polish):
-- Stage 1: IdentityNature, PredicateOperationality, ReferenceOperationality
--          (VRCycle.Apparatus.Identity, Wrapping, Reference)
-- Stage 2: Mode A closure theorem for both apparatus modes (VRCycle.Apparatus.ModeA)
-- Stage 3: Mode B schema — conditional operational extraction (VRCycle.Apparatus.ModeB)
-- Stage 4: Apparatus split (SKIPPED — merged into Stage 1)
-- Stage 5: Instance enrichment — additional apparatus instances (VRCycle.Apparatus.Instances)
-- Stage 6: API polish — @[simp] additions, module documentation (this file)
--
-- v1.0.0 (six pieces, order 4 → 6 → 2 → 3 → 5 → 1):
-- Stage 4: Operand-not-operation theorem — Factorisable (VRCycle.Apparatus.Factorisation)
-- Stage 6: Separability as formal hypothesis — HasSeparabilityStructure (VRCycle.Apparatus.Separability)
-- Stage 2: Cross-apparatus morphisms — InterApparatusMorphism (VRCycle.Apparatus.InterMorphism)
-- Stage 3: Compositional algebra — identity elements, cross-level composition (VRCycle.Apparatus.Composition)
-- Stage 5: Numbers as hybrid apparatus subjects — lens applicability (VRCycle.Apparatus.Numbers)
-- Stage 1: VR-Forms integration — transit as Mode B (VRCycle.Apparatus.FormsIntegration)
-- Polish: @[simp] audit (no new additions), comprehensive module doc (this file)

import VRCycle.Apparatus.Identity
import VRCycle.Apparatus.Wrapping
import VRCycle.Apparatus.Reference
import VRCycle.Apparatus.ModeA
import VRCycle.Apparatus.ModeB
import VRCycle.Apparatus.Instances
import VRCycle.Apparatus.Factorisation
import VRCycle.Apparatus.Separability
import VRCycle.Apparatus.InterMorphism
import VRCycle.Apparatus.Composition
import VRCycle.Apparatus.Numbers
import VRCycle.Apparatus.FormsIntegration

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
-- Spot-check axiom audit (Polish) — one representative per tier
-- ============================================================

section SpotCheckAxioms

-- Tier 1: axiom-free [] (representative: Mode B infrastructure)
#print axioms IsModeBOp.lift_val
-- Expected: 'VR.Apparatus.IsModeBOp.lift_val' does not depend on any axioms

-- Tier 2: [Quot.sound] (representative: IAM lift — NEW tier in v1.0.0)
#print axioms InterApparatusMorphism.lift_mk
-- Expected: 'VR.Apparatus.InterApparatusMorphism.lift_mk' depends on axioms: [Quot.sound]

-- Tier 3: [propext, Quot.sound] (representative: VR-Forms integration)
#print axioms instPredicateOpFormalTerm
-- Expected: 'VR.Apparatus.instPredicateOpFormalTerm' depends on axioms: [propext, Quot.sound]

-- Tier 4: [propext, Classical.choice, Quot.sound] (representative: concrete Mode B)
#print axioms riesz_extension_isModeBOp
-- Expected: 'VR.Apparatus.riesz_extension_isModeBOp' depends on axioms:
--           [propext, Classical.choice, Quot.sound]

end SpotCheckAxioms

end VR.Apparatus
