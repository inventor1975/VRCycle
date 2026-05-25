-- VR-Apparatus: FormsIntegration (DOI TBD — v1.0.0)
-- Stage 1: VR-Forms integration — apparatus re-reading of the two-register system.
--
-- STAGE: 1 (of 6). ORDER: 4 → 6 → 2 → 3 → 5 → 1 (final stage). SOURCE: CLAUDE.md §v1.0.0 piece (1).
--
-- ## Filename note
-- This file was planned as `Register.lean`. Renamed to `FormsIntegration.lean` after
-- reconnaissance: VR-Forms already has a type named `Register` (Language.lean, line 65):
--   `inductive Register where | ontological | formal`
-- Using `Register.lean` for an apparatus concept with the same name would cause confusion.
-- The planned "generic apparatus Register structure" is dropped (see §3).
--
-- ## Finding S1-A: Generic Register abstraction unnecessary
--
-- Original Stage 1 plan: generic `Register` (structure carrying apparatus instances) +
-- `DirectionalMorphism` (IAM with asymmetry). Reconnaissance of VR-Forms files reveals:
--
-- (1) VR-Forms `Register` inductive (Language.lean) is a two-constructor EXISTING type:
--     `| ontological | formal`. This is a MODE-OF-CONSIDERATION marker, not an apparatus
--     concept. Conflating with planned apparatus Register = category error. Dropped.
--
-- (2) `DirectionalMorphism` as planned ("IAM extended with asymmetry") does NOT fit VR-Forms
--     transit. IAM is a morphism between quotient types (f : Q1 → Q2 respecting setoids).
--     VR-Forms transit (`translate_implies_realisable`) is a logical implication between two
--     predicates on the SAME type `FormalTerm`. Different structure entirely. Dropped.
--
-- (3) KEY FINDING: `translate_implies_realisable` IS already Mode B.
--     `IsModeBOp PA PB W f : ∀ a, PA a → W a → PB (f a)` with
--       PA = translate_pi, PB = isRealisable, W = fun _ => True, f = id
--     reduces to `∀ t, translate_pi t → isRealisable t` = `translate_implies_realisable`.
--     The Mode B schema from v0.1.0 already captures VR-Forms transit.
--     No new abstraction needed. Stage 1 = recognition, not new framework.
--
-- ## Finding S1-B: Three-way identity nature contrast
--
-- VR-Forms two-register system, read through apparatus lens, reveals:
--   (a) Formal specific apparatus (FormalTerm, translate_pi):    AsPoint  [instPredicateOpTranslatePi]
--   (b) Formal existential apparatus (FormalTerm, isRealisable): AsPoint  [instPredicateOpFormalTerm]
--   (c) Ontological reference apparatus (PSet, instRefOpPSet):   AsReference [Instances.lean]
--
-- Two AsPoint (predicate-wrapping) apparatus instances for the formal register.
-- One AsReference (reference semantics) apparatus instance for the ontological register.
-- The transit (vr_forms_transit_isModeBOp) connects (a) to (b): specific → existential.
-- The ontological apparatus (c) is the target universe: realisability says (b) has
-- an operational correlate in (c).
--
-- This three-way contrast is the complete apparatus anatomy of VR-Forms.
--
-- ## VR-Forms implicit apparatus structure (reconnaissance)
--
-- VR-Forms (Language + Realisability + Transit) implicitly uses:
--   FormalTerm : Type           — shallow embedding: (description : String, register : Register)
--   translate_pi : FormalTerm → Prop  — specific predicate (naming concrete VR-Sets objects)
--   isRealisable : FormalTerm → Prop  — existential predicate (∃ s : OSet, P(s))
--   translate_implies_realisable      — transit: translate_pi t → isRealisable t
--   OSet = ZFSet = Quotient PSet.setoid — the ontological universe (instRefOpPSet apparatus)
--
-- Stage 1 makes the apparatus structure EXPLICIT by instantiating the apparatus classes.
--
-- ## Lean content (3 public objects + 2 examples)
-- §1. Predicate apparatus marker instances:
--   A1. instPredicateOpFormalTerm   — (FormalTerm, isRealisable) is predicate-wrapping apparatus.
--   A2. instPredicateOpTranslatePi  — (FormalTerm, translate_pi) is predicate-wrapping apparatus.
-- §2. VR-Forms transit as Mode B:
--   B1. vr_forms_transit_isModeBOp  — translate_implies_realisable IS IsModeBOp.
-- Examples (non-public):
--   OQ-A: identityNature = AsPoint for instPredicateOpFormalTerm.
--   OQ-B: three-way identity nature contrast (comment block, see above).
--
-- ## Axiom profile
-- All three objects: [propext, Quot.sound].
-- Inherited from VR-Forms predicates (translate_pi, isRealisable) via VR-Sets/ZFSet
-- infrastructure (propext for iff-reasoning on OSet, Quot.sound for ZFSet quotient).
-- No Classical.choice: VR-Forms avoids classical reasoning throughout.
-- Parallel to all VR-Forms Transit.lean objects [propext, Quot.sound].
--
-- ## Scope discipline
-- - No modifications to VR-Forms files (Language, Realisability, Transit, Bridge, Examples).
-- - No re-derivation of VR-Forms theorems.
-- - Stage 1 reads VR-Forms through apparatus lens; does not rewrite it.
-- - Apparatus.lean updated to import this file.

import VRCycle.Apparatus.Numbers
import VRCycle.Forms.Transit

namespace VR.Apparatus

open VR.Forms

-- ============================================================
-- §1. Predicate apparatus marker instances for FormalTerm
-- ============================================================

-- VR-Forms uses FormalTerm as the carrier for TWO predicate apparatus instances:
-- one for the existential realisability predicate, one for the specific translate_pi predicate.
-- Both are predicate-wrapping apparatus with AsPoint identity nature.

/-- **A1**: `(FormalTerm, isRealisable)` is a predicate-wrapping apparatus.

`isRealisable : FormalTerm → Prop` selects the sub-collection of operationally realisable
formal terms within the formal register. This is the existential predicate apparatus:
  `isRealisable ⌜"∅"⌝ = ∃ s : OSet, ∀ x, x ∉ s`
  `isRealisable ⌜"omega_OSet"⌝ = ∃ s : OSet, ∅ ∈ s ∧ …`
  `isRealisable ⌜t⌝ = False`  (for non-realisable terms)

The predicate `isRealisable` plays the same role for `FormalTerm` that `IsComputableReal`
plays for `ℝ`: it selects the operationally meaningful sub-collection within the full type.

## Identity nature: AsPoint (Finding S1-B)
The formal register treats formal terms as POINTS (named syntactic objects in a string-indexed
space). The `AsPoint` identity nature reflects this: formal terms are identified by their
description string and register marker, not by membership structure. This contrasts with
the ontological apparatus (`instRefOpPSet`, Instances.lean) which is `AsReference`.

## Axiom profile: [propext, Quot.sound]
PredicateOperationality is a marker class (no fields); its axioms are determined by the
type elaboration context. `isRealisable` depends on VR-Sets ZFSet machinery ([propext, Quot.sound]).
Classical.choice is NOT used in VR-Forms (DecidableEq FormalTerm avoids classical reasoning). -/
instance instPredicateOpFormalTerm : PredicateOperationality FormalTerm isRealisable := ⟨⟩

/-- The identity nature of the formal realisability apparatus is AsPoint. -/
example : @PredicateOperationality.identityNature
    FormalTerm isRealisable instPredicateOpFormalTerm =
    IdentityNature.AsPoint := rfl

/-- **A2**: `(FormalTerm, translate_pi)` is a predicate-wrapping apparatus.

`translate_pi : FormalTerm → Prop` is the SPECIFIC predicate apparatus: it selects formal
terms by the definite operational predicate referencing concrete VR-Sets objects by name:
  `translate_pi ⌜"∅"⌝ = ∀ x : OSet, x ∉ osetEmpty`         (names `osetEmpty`)
  `translate_pi ⌜"omega_OSet"⌝ = ∅ ∈ omega_OSet ∧ …`       (names `omega_OSet`)
  `translate_pi ⌜t⌝ = False`  (for terms without named VR-Sets correlate)

Contrast with A1 (`isRealisable`): the specific predicate (`translate_pi`) implies the
existential predicate (`isRealisable`) — this is the content of B1 below. The converse
does NOT hold (from ∃ s, ∀ x, x ∉ s one cannot recover ∀ x, x ∉ osetEmpty).

The specific-predicate apparatus `(FormalTerm, translate_pi)` is the STRICTER of the two:
`{t : FormalTerm // translate_pi t} ⊆ {t : FormalTerm // isRealisable t}` (subtype sense). -/
instance instPredicateOpTranslatePi : PredicateOperationality FormalTerm translate_pi := ⟨⟩

-- ============================================================
-- §2. VR-Forms transit as Mode B (Finding S1-A)
-- ============================================================

-- The key apparatus re-reading of VR-Forms:
-- `translate_implies_realisable : ∀ t, translate_pi t → isRealisable t` (Transit.lean)
-- IS `IsModeBOp translate_pi isRealisable (fun _ => True) id`.
--
-- Mode B schema:  `IsModeBOp PA PB W f : ∀ a, PA a → W a → PB (f a)`
-- Instantiation:  PA = translate_pi, PB = isRealisable, W = fun _ => True, f = id
-- Reduces to:     `∀ t, translate_pi t → True → isRealisable (id t)`
--               = `∀ t, translate_pi t → isRealisable t`
--               = `translate_implies_realisable`
--
-- The trivial witness W = fun _ => True means: no additional operational enrichment
-- of the operand is needed — the specific predicate (translate_pi) is sufficient on its own.
-- Compare: Riesz extension is Mode B with nontrivial W (operand must be subspace element).
-- VR-Forms transit is Mode B with trivial W = degenerate Mode B = Mode A at the subtype level.
--
-- Methodological observation: the v0.1.0 Mode B schema was discovered from Riesz extension;
-- it also captures VR-Forms transit with trivial witness. Apparatus framework is NOT tailored
-- to the Riesz case — it is broad enough to include the formal-register transit pattern.

/-- **B1**: The VR-Forms transit pattern reads as a Mode B operation.

`translate_implies_realisable` (VR-Forms Transit.lean) is `IsModeBOp` with:
  - Source predicate: `translate_pi` (the specific apparatus)
  - Target predicate: `isRealisable` (the existential apparatus)
  - Witness: `fun _ => True` (no additional enrichment needed)
  - Map: `id` (formal terms map to themselves)

**Finding S1-A**: The Mode B schema from v0.1.0 already captures VR-Forms transit.
No new abstraction (`DirectionalMorphism`, generic `Register`) is needed. Stage 1 is
a RECOGNITION that the apparatus framework already covers VR-Forms through Mode B.

**Two-layer structure** (Transit.lean Methodological Observation 4):
- `translate_pi t` is the SPECIFIC layer (naming `osetEmpty`, `omega_OSet`, `osetPair`)
- `isRealisable t` is the EXISTENTIAL layer (`∃ s, P(s)` without naming the witness)
- `vr_forms_transit_isModeBOp` connects them: specific → existential via Mode B
- The converse fails: Mode B is NOT symmetric (existential does not recover specific).

## Axiom profile: [propext, Quot.sound]
Inherited from `translate_implies_realisable` (Transit.lean: [propext, Quot.sound]).
No Classical.choice: VR-Forms uses DecidableEq FormalTerm throughout. -/
theorem vr_forms_transit_isModeBOp :
    IsModeBOp translate_pi isRealisable (fun _ => True) id :=
  fun t h _ => translate_implies_realisable t h

-- ============================================================
-- §3. Dropped abstractions — explicit scope documentation
-- ============================================================

-- **Generic Register structure**: DROPPED.
-- Planned: `structure ApparatusRegister where` (collection of apparatus instances).
-- Reason dropped:
-- (a) Name collision: VR-Forms has `inductive Register where | ontological | formal`
--     (Language.lean, line 65). The name «Register» in apparatus context would conflict.
-- (b) VR-Forms is NOT a generic Register — it has exactly two specific apparatus instances
--     (formal: instPredicateOpTranslatePi/instPredicateOpFormalTerm; ontological: instRefOpPSet).
--     Generic structure adds no mathematical content beyond this specific reading.
-- (c) Lean's typeclass system already provides the "collection of apparatus instances" concept
--     implicitly: instantiating PredicateOperationality or ReferenceOperationality IS the
--     apparatus declaration. No wrapper structure needed.

-- **DirectionalMorphism typeclass**: DROPPED.
-- Planned: `DirectionalMorphism` extending InterApparatusMorphism with asymmetry.
-- Reason dropped:
-- (a) Type mismatch: IAM is a morphism between QUOTIENT TYPES (f : Q1 → Q2 respecting setoids).
--     VR-Forms transit is an implication between PREDICATES on the same type FormalTerm.
-- (b) The asymmetry in VR-Forms transit is predicate asymmetry (translate_pi → isRealisable,
--     not the converse), not morphism asymmetry (one-way between apparatus types).
-- (c) Mode B already captures this: `IsModeBOp` is the right abstraction for predicate-to-predicate
--     transit with optional witness enrichment. See B1 above.
-- Future work: if cross-apparatus ASYMMETRIC morphisms are needed (v1.1.0?), a DirectionalMorphism
-- typeclass could be developed. The current v1.0.0 scope does not require it.

-- ============================================================
-- Axiom audit (Stage 1 — 3 public objects)
-- ============================================================

section AxiomAudit

-- A1: marker instance; axioms from type elaboration of isRealisable (ZFSet).
#print axioms instPredicateOpFormalTerm
-- Verified: [propext, Quot.sound]

-- A2: marker instance; axioms from type elaboration of translate_pi (ZFSet).
#print axioms instPredicateOpTranslatePi
-- Verified: [propext, Quot.sound]

-- B1: translate_implies_realisable inherits [propext, Quot.sound].
#print axioms vr_forms_transit_isModeBOp
-- Verified: [propext, Quot.sound]

end AxiomAudit

end VR.Apparatus
