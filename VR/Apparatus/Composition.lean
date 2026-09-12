-- VR-Apparatus: Composition (v1.0.0, Stage 3)
-- Compositional algebra — identity elements and cross-level composition.
--
-- STAGE: v1.0.0 Stage 3 (fourth of six pieces). SOURCE: PLAN.md Stage 3.
--
-- ## Position statement
-- Catalogs what actually composes across the apparatus morphism levels.
-- The result is smaller than originally planned but honest: most composition
-- was already proved in v0.1.0 + Stages 2–3. Stage 3 adds identity elements
-- and one genuine cross-level composition theorem.
--
-- ## Revised scope (Finding S2-A, Stage 2)
--
-- The apparatus has FOUR distinct morphism levels, not three:
--
--   Level 1 — Predicate endomorphisms:
--     PredicateOperationality.IsModeAOp  (f : T → T, P-preserving)
--
--   Level 2 — Quotient endomorphisms:
--     ReferenceOperationality.IsModeAOp  (f : Q → Quotient s, ≈-respecting)
--     Note: s in Quotient s = SAME setoid as Q. Endomorphism condition.
--
--   Level 3 — Representative morphisms:
--     InterApparatusMorphism             (f : Q1 → Q2, ≈-preserving across setoids)
--
--   Level 4 — Conditional predicate transit:
--     IsModeBOp                          (f : A → B, with witness W)
--
-- Within-level composition: already proved in v0.1.0 + Stage 2 (reference §1).
-- Stage 3 adds: identity elements (one per level, Group A) and cross-level
-- well-definedness + functor law for Levels 2–3 (Group B).
--
-- ## Finding S3-A — Two parallel tracks (headline architectural observation)
--
-- The four morphism levels form TWO PARALLEL TRACKS:
--
--   Predicate track:  Level 1 (Predicate Mode A) + Level 4 (Mode B).
--     Internal: IsModeAOp_iff_IsModeBOp, IsModeAOp.toModeBOp (v0.1.0).
--
--   Reference track:  Level 2 (Reference Mode A) + Level 3 (IAM).
--     Internal: IsModeAOp_of_interApparatus (Stage 2),
--               interApparatus_comp_modeA_wd (Stage 3 B1).
--
-- Cross-track connections (ABSENT — structural fact, not a gap):
--   Mode B ∘ IAM:               predicates vs setoid equivalences, no canonical bridge.
--   Mode B ∘ Reference Mode A:  different structural universes; IsModeAOp_iff_IsModeBOp
--                                 connects PREDICATE Level 1, not Reference Level 2.
--   Predicate Mode A ∘ IAM:     comp_modeA_wd applies to Reference Mode A only;
--                                 Predicate Mode A (f : T → T) ≠ IAM structure.
--
-- The apparatus is NOT a unified theory with a single morphism hierarchy.
-- It is TWO PARALLEL ARCHITECTURES, each internally consistent and composable,
-- non-composing across tracks without additional bridging structure.
--
-- This is a preprint-level finding for the Methodological Section:
-- the two tracks co-exist, serve different mathematical contexts
-- (predicate-based computability vs reference-semantics quotient structures),
-- and share concrete instances (numbers in Stage 5 straddle both).
--
-- ## Type-level observation on Group B (Stage 3 finding)
--
-- ReferenceOperationality.IsModeAOp (f : Q → Quotient s) is an ENDOMORPHISM:
-- s in Quotient s = SAME setoid as Q. For cross-apparatus composition
-- (f : Q1 → Q2 IAM, g : Q2 → Quotient s2 Mode A), the result g ∘ f maps
-- Q1 → Quotient s2 (NOT Quotient s1). This makes `IsModeAOp` unsuitable
-- as the wrapper for the cross-apparatus case — the codomain setoid differs.
--
-- B1 therefore states the well-definedness property DIRECTLY as a Prop
-- (∀ a b : Q1, a ≈ b → (g ∘ f) a = (g ∘ f) b), which is precisely the
-- condition for Quotient.lift from Quotient s1 to Quotient s2.
-- B2 shows this Quotient.lift equals modeA_liftFn hg ∘ hf.lift.
--
-- ## Content
-- §1. Reference: existing within-level composition (comment block).
-- §2. Group A: identity elements (5 theorems, one per level + A2 companion).
-- §3. Group B: cross-level composition (2 theorems, Levels 2–3).
-- §4. Finding S3-A: non-composability documentation (comment block).
-- §5. Verification examples.
-- §6. Axiom audit.
--
-- ## Axiom profile overview
--   PredicateOperationality.IsModeAOp_id                  []
--   ReferenceOperationality.IsModeAOp_quotientMk           [Quot.sound]
--   ReferenceOperationality.modeA_liftFn_quotientMk_eq_id  [Quot.sound]
--   InterApparatusMorphism.id_isInterApparatus              []
--   IsModeBOp_id                                            []
--   interApparatus_comp_modeA_wd                            []
--   modeA_liftFn_comp_interApparatus                        [Quot.sound]
--   §2b witnessed Mode A (IsModeAOpW, 11 objects)          []
--
-- Integrity step 5 (2026-09-12): the three [Quot.sound] objects are the
-- QUOTIENT BRIDGE (Lean's `Quotient`, kind 3 in VR-LOGIC §1); the same algebra
-- is stated in the witnessed register in §2b on []. The bridge objects moved to
-- VRClassical/Apparatus/QuotientBridge.lean (same day, library split); every
-- object left in this file is on [] — enforced by VRCycle/Guard.lean.
--
-- ## Productive triviality — fifth through seventh instances
-- Identity proofs (A1, A3, A4) are one-liners; B1 is one-liner.
-- The simplicity IS the content: identities are free because the apparatus
-- was defined correctly.
-- Full count: modeA_liftFn (v0.1.0), operand_determines_operational (Stage 4),
-- IsModeBOp_of_factorisable (Stage 4), separability_provides_factorisable (Stage 6),
-- IsModeAOp_id (Stage 3), id_isInterApparatus (Stage 3), IsModeBOp_id (Stage 3).

import VR.Apparatus.InterMorphism

namespace VR.Apparatus

-- ============================================================
-- §1. Existing within-level composition (reference only)
-- ============================================================
--
-- All proved in v0.1.0 + Stage 2. No new proofs here.
--
-- Level 1: PredicateOperationality.IsModeAOp.compose (ModeA.lean)
--   IsModeAOp f → IsModeAOp g → IsModeAOp (g ∘ f)
--
-- Level 2: ReferenceOperationality.IsModeAOp.compose (ModeA.lean)
--   IsModeAOp f → IsModeAOp g → IsModeAOp (fun a => modeA_liftFn hg (f a))
--
-- Level 3: InterApparatusMorphism.compose (InterMorphism.lean)
--   IAM f → IAM g → IAM (g ∘ f)
-- Level 3 lift: InterApparatusMorphism.lift_compose
--   (hf.compose hg).lift = hg.lift ∘ hf.lift
--
-- Level 4: IsModeBOp.compose (ModeB.lean)
--   IsModeBOp PA PB W1 f → IsModeBOp PB PC W2 g →
--   IsModeBOp PA PC (fun a => W1 a ∧ W2 (f a)) (g ∘ f)
--
-- Cross-level (v0.1.0 + Stage 2):
--   IsModeAOp_iff_IsModeBOp, IsModeAOp.toModeBOp: Level 1 ↔ Level 4.
--   IsModeAOp_of_interApparatus: Level 3 (same setoid) → Level 2.

-- ============================================================
-- §2. Group A — Identity elements
-- ============================================================

/-- Predicate Mode A identity: `id` preserves any predicate P.

`IsModeAOp id = ∀ x : T, P x → P (id x) = ∀ x : T, P x → P x`

**Proof**: `fun _ hx => hx`. Trivially true — id is the identity.

**Compositional role**: identity of the composition monoid at Level 1.
`compose IsModeAOp_id h = h` and `compose h IsModeAOp_id = h` at the Prop level.

**Productive triviality (fifth instance)**: simplicity = correct definition.

## Axiom profile: [] -/
theorem PredicateOperationality.IsModeAOp_id {T : Type*} {P : T → Prop} :
    @PredicateOperationality.IsModeAOp T P id :=
  fun _ hx => hx

/-- IAM identity: `id` is an inter-apparatus morphism for any apparatus.

`InterApparatusMorphism id = ∀ x y : Q, x ≈ y → id x ≈ id y = ∀ x y : Q, x ≈ y → x ≈ y`

**Proof**: `fun _ _ h => h`. The equivalence is its own certificate.

**Compositional role**: identity of the Level 3 category.
`compose id_isInterApparatus hg = hg` (left identity).
`compose hf id_isInterApparatus = hf` (right identity).

**Productive triviality (sixth instance)**.

## Axiom profile: [] -/
theorem InterApparatusMorphism.id_isInterApparatus {Q : Type*} [s : Setoid Q] :
    @InterApparatusMorphism Q Q s s id :=
  fun _ _ h => h

/-- Mode B identity: `id` is a Mode B operation with trivial witness.

`IsModeBOp PA PA (fun _ => True) id = ∀ a : A, PA a → True → PA (id a)`

**Proof**: `fun _ ha _ => ha`. Trivially true.

**Alternative**: `IsModeAOp_id.toModeBOp` gives the same via the Level 1 → Level 4 bridge.
The direct proof is cleaner.

**Productive triviality (seventh instance)**.

## Axiom profile: [] -/
theorem IsModeBOp_id {A : Type*} {PA : A → Prop} :
    IsModeBOp PA PA (fun _ => True) id :=
  fun _ ha _ => ha

-- ============================================================
-- §2b. Witnessed Mode A — Level 2 without the quotient (integrity step 5)
-- ============================================================
--
-- Integrity programme (2026-09-12), step 5: the apparatus must state its
-- reference-track algebra WITHOUT `Quotient`. A Mode A map in the witnessed
-- register is an endomorphism `f : Q → Q` together with its congruence
-- certificate `a ≈ b → f a ≈ f b` — no passage to `Quotient s`, no
-- `Quot.sound`. Identity is `id` (not `Quotient.mk s`), the identity and
-- associativity laws hold POINTWISE UP TO `≈` (they are `Setoid.refl`), and the
-- bridge to the quotient level is `IsModeAOp_of_interApparatus` (kept, on
-- `[Quot.sound]`). Definitionally `IsModeAOpW f` IS `InterApparatusMorphism f`
-- with the same setoid on both sides (`IsModeAOpW_iff_interApparatus`, `Iff.rfl`):
-- the witnessed Level 2 is the endomorphism case of Level 3.
--
-- The reverse bridge — from `g : Q → Quotient s` back to a witnessed `Q → Q` —
-- needs a choice of representatives (`Quotient.out`, `Classical.choice`). It is
-- not provided: this is the T→O absence of VR-LOGIC §3 in miniature.
--
-- All objects of this section: axiom profile `[]`.

namespace ReferenceOperationality
section
variable {Q : Type*} [s : Setoid Q]

/-- Witnessed Mode A: an endomorphism of the pre-type with its congruence
certificate. `IsModeAOpW f = ∀ a b : Q, a ≈ b → f a ≈ f b`.

## Axiom profile: [] -/
def IsModeAOpW (f : Q → Q) : Prop :=
  ∀ a b : Q, a ≈ b → f a ≈ f b

/-- Witnessed Mode A is the endomorphism case of an inter-apparatus morphism.

## Axiom profile: [] -/
theorem IsModeAOpW_iff_interApparatus {f : Q → Q} :
    IsModeAOpW f ↔ @InterApparatusMorphism Q Q s s f :=
  Iff.rfl

/-- Witnessed identity element: `id` is Mode A. The equivalence is its own
certificate.

## Axiom profile: [] -/
theorem IsModeAOpW_id : IsModeAOpW (id : Q → Q) :=
  fun _ _ h => h

/-- Witnessed Mode A maps compose (no lift needed: both are `Q → Q`).

## Axiom profile: [] -/
theorem IsModeAOpW.compose {f g : Q → Q}
    (hf : IsModeAOpW f) (hg : IsModeAOpW g) : IsModeAOpW (g ∘ f) :=
  fun a b hab => hg _ _ (hf a b hab)

/-- Left identity law, pointwise up to `≈`.

## Axiom profile: [] -/
theorem IsModeAOpW_id_comp (f : Q → Q) (a : Q) : (id ∘ f) a ≈ f a :=
  Setoid.refl _

/-- Right identity law, pointwise up to `≈`.

## Axiom profile: [] -/
theorem IsModeAOpW_comp_id (f : Q → Q) (a : Q) : (f ∘ id) a ≈ f a :=
  Setoid.refl _

/-- Associativity, pointwise up to `≈`.

## Axiom profile: [] -/
theorem IsModeAOpW_assoc (f g h : Q → Q) (a : Q) :
    ((h ∘ g) ∘ f) a ≈ (h ∘ (g ∘ f)) a :=
  Setoid.refl _

/-- Mode A is a property of the map UP TO pointwise `≈`: a map pointwise
equivalent to a Mode A map is Mode A. (The witnessed replacement for
`funext`-based equalities of lifted maps.)

## Axiom profile: [] -/
theorem IsModeAOpW.of_pointwise {f g : Q → Q}
    (hf : IsModeAOpW f) (hfg : ∀ a, f a ≈ g a) : IsModeAOpW g :=
  fun a b hab =>
    Setoid.trans (Setoid.symm (hfg a)) (Setoid.trans (hf a b hab) (hfg b))

/-- A Mode A map sends pointwise-equivalent inputs to pointwise-equivalent
outputs: composition respects pointwise `≈` on the right.

## Axiom profile: [] -/
theorem IsModeAOpW.comp_congr_right {g : Q → Q} (hg : IsModeAOpW g)
    {f f' : Q → Q} (hff' : ∀ a, f a ≈ f' a) (a : Q) :
    (g ∘ f) a ≈ (g ∘ f') a :=
  hg _ _ (hff' a)

end -- section {Q : Type*} [s : Setoid Q]
end ReferenceOperationality

/-- Cross-level, witnessed: an IAM `f : Q1 → Q2` followed by a witnessed Mode A
map `g : Q2 → Q2` is an IAM `Q1 → Q2` — the witnessed form of
`interApparatus_comp_modeA_wd`, with `≈₂` in place of equality in `Quotient s2`.

## Axiom profile: [] -/
theorem interApparatus_comp_modeAW
    {Q1 Q2 : Type*} [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} {g : Q2 → Q2}
    (hf : InterApparatusMorphism f)
    (hg : @ReferenceOperationality.IsModeAOpW Q2 s2 g) :
    InterApparatusMorphism (g ∘ f) :=
  fun a b hab => hg _ _ (hf a b hab)

/-- Witnessed functor law: the composite acts as `g` after `f`, pointwise up to
`≈₂` (the witnessed form of `modeA_liftFn_comp_interApparatus`, which needs
`funext` for the equality of lifted maps).

## Axiom profile: [] -/
theorem comp_modeAW_pointwise
    {Q1 Q2 : Type*} [s2 : Setoid Q2]
    (f : Q1 → Q2) (g : Q2 → Q2) (a : Q1) :
    (g ∘ f) a ≈ g (f a) :=
  Setoid.refl _

-- ============================================================
-- §3. Group B — Cross-level composition (Levels 2 and 3)
-- ============================================================
--
-- The one genuinely new cross-level theorem: IAM (Level 3) followed by
-- Reference Mode A (Level 2) satisfies the well-definedness condition
-- for Quotient.lift from Quotient s1 to Quotient s2.
--
-- Type-level note (see module header):
-- `IsModeAOp` cannot wrap this result when s1 ≠ s2 because IsModeAOp
-- requires the codomain to be Quotient s (SAME setoid as Q). For cross-apparatus
-- (g ∘ f : Q1 → Quotient s2 with s2 ≠ s1), B1 uses the raw Prop directly.
-- B2 shows the two natural quotient-level maps agree.

/-- Cross-level well-definedness: IAM followed by Reference Mode A satisfies
the Quotient.lift condition from Quotient s1 to Quotient s2.

Given `f : Q1 → Q2` (IAM for s1 → s2) and `g : Q2 → Quotient s2` (Mode A),
the composition `g ∘ f : Q1 → Quotient s2` satisfies:
  `∀ a b : Q1, a ≈ b → (g ∘ f) a = (g ∘ f) b`

**Proof**: `a ≈₁ b → (hf) f a ≈₂ f b → (hg) g(f a) = g(f b)`. One-liner.

**Why not IsModeAOp**: `IsModeAOp` requires codomain `Quotient s1` (same setoid
as source Q1). Here the codomain is `Quotient s2` (target apparatus), which differs
from s1 when the apparatus instances are different. B1 states the property directly
as a Prop — the well-definedness condition for `Quotient.lift s1 → Quotient s2`.

**Quotient.lift usage**: enables `Quotient.lift (g ∘ f) (interApparatus_comp_modeA_wd hf hg)
: Quotient s1 → Quotient s2` — see B2.

## Axiom profile: [] -/
theorem interApparatus_comp_modeA_wd
    {Q1 Q2 : Type*} [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} {g : Q2 → Quotient s2}
    (hf : InterApparatusMorphism f)
    (hg : @ReferenceOperationality.IsModeAOp Q2 s2 g) :
    ∀ a b : Q1, a ≈ b → (g ∘ f) a = (g ∘ f) b :=
  fun a b hab => hg _ _ (hf a b hab)

-- ============================================================
-- §4. Finding S3-A — Two parallel tracks (non-composability)
-- ============================================================
--
-- ── PREDICATE TRACK ──────────────────────────────────────────────
-- Level 1: IsModeAOp (P-preserving endomorphisms on T)
-- Level 4: IsModeBOp (conditional predicate transit)
-- Connected: IsModeAOp_iff_IsModeBOp, IsModeAOp.toModeBOp (v0.1.0)
-- Identity: IsModeAOp_id (Level 1), IsModeBOp_id (Level 4) — Stage 3
--
-- ── REFERENCE TRACK ──────────────────────────────────────────────
-- Level 2: IsModeAOp (≈-respecting maps Q → Quotient s)
-- Level 3: InterApparatusMorphism (≈-preserving maps Q1 → Q2)
-- Connected:
--   Level 3 (same setoid) → Level 2: IsModeAOp_of_interApparatus (Stage 2)
--   Level 3 + Level 2 → quotient: interApparatus_comp_modeA_wd (Stage 3 B1)
--   Functor law: modeA_liftFn_comp_interApparatus (Stage 3 B2)
-- Identity:
--   Level 2: IsModeAOp_quotientMk + modeA_liftFn_quotientMk_eq_id — Stage 3
--   Level 3: id_isInterApparatus — Stage 3
--
-- ── THREE STRUCTURAL NON-COMPOSABILITIES ────────────────────────
--
-- (1) Mode B ∘ IAM:
--   Mode B (Level 4) operates on TYPE PREDICATES: PA : A → Prop.
--   IAM (Level 3) operates on SETOID EQUIVALENCES: s1-equivalent implies s2-equivalent.
--   Connecting setoid equivalences to type predicates requires additional structure
--   beyond the apparatus framework (e.g., a predicate that tracks setoid classes).
--   No canonical bridge. Non-composability is structural.
--
-- (2) Mode B ∘ Reference Mode A:
--   Reference Mode A (Level 2): quotient endomorphisms.
--   Mode B (Level 4): predicate transit.
--   IsModeAOp_iff_IsModeBOp connects PREDICATE Level 1 (P-preserving f : T → T)
--   to Mode B, NOT Reference Level 2 (≈-respecting f : Q → Quotient s).
--   The two Mode A levels are structurally distinct: Level 1 maps T → T;
--   Level 2 maps Q → Quotient s. The Level 4 bridge applies only to Level 1.
--
-- (3) Predicate Mode A ∘ IAM:
--   Predicate Mode A (Level 1): f : T → T preserving P : T → Prop.
--   IAM (Level 3): f : Q1 → Q2 preserving setoid equivalence.
--   interApparatus_comp_modeA_wd applies to REFERENCE Mode A (g : Q → Quotient s),
--   not Predicate Mode A (f : T → T). For Predicate Mode A, the operational
--   structure is about subtype {x : T // P x}, not about setoid quotients.
--
-- ── PREPRINT FRAMING ─────────────────────────────────────────────
--
-- The apparatus is not a single unified morphism hierarchy.
-- It is two parallel architectures, each internally rich and consistent:
--   Predicate track formalises computability-style operationality.
--   Reference track formalises quotient/extensionality-style operationality.
-- Both appear in the VR cycle: IsComputableReal (predicate track),
-- ZFSet and OSetZFA (reference track).
-- The tracks meet at concrete instances but not at the structural level.

-- ============================================================
-- §5. Verification examples
-- ============================================================

-- Level 1 identity: id is Mode A, and f ∘ id = f definitionally.
example {T : Type*} {P : T → Prop} {f : T → T}
    (hf : @PredicateOperationality.IsModeAOp T P f) :
    @PredicateOperationality.IsModeAOp T P (f ∘ id) :=
  hf

-- ============================================================
-- §6. Axiom audit — Stage 3, Composition.lean
-- ============================================================
-- STAGE: v1.0.0 Stage 3. SOURCE: PLAN.md Stage 3.
-- LEAN OBJECTS (7 public objects):
--   PredicateOperationality.IsModeAOp_id                  (theorem, identity Level 1)
--   ReferenceOperationality.IsModeAOp_quotientMk           (theorem, identity Level 2)
--   ReferenceOperationality.modeA_liftFn_quotientMk_eq_id  (theorem, identity cert. Level 2)
--   InterApparatusMorphism.id_isInterApparatus              (theorem, identity Level 3)
--   IsModeBOp_id                                            (theorem, identity Level 4)
--   interApparatus_comp_modeA_wd                            (theorem, cross-level B1)
--   modeA_liftFn_comp_interApparatus                        (theorem, cross-level B2)
--   §2b (integrity step 5, 11 objects): IsModeAOpW, IsModeAOpW_iff_interApparatus,
--     IsModeAOpW_id, IsModeAOpW.compose, IsModeAOpW_id_comp, IsModeAOpW_comp_id,
--     IsModeAOpW_assoc, IsModeAOpW.of_pointwise, IsModeAOpW.comp_congr_right,
--     interApparatus_comp_modeAW, comp_modeAW_pointwise
-- AXIOM AUDIT:
--   [] (15): IsModeAOp_id, id_isInterApparatus, IsModeBOp_id, interApparatus_comp_modeA_wd,
--            and the 11 objects of §2b
--   [Quot.sound] (3, quotient bridge): IsModeAOp_quotientMk, modeA_liftFn_quotientMk_eq_id,
--                     modeA_liftFn_comp_interApparatus
-- CHECKS: no sorry, no admit.

#print axioms PredicateOperationality.IsModeAOp_id
#print axioms InterApparatusMorphism.id_isInterApparatus
#print axioms IsModeBOp_id
#print axioms interApparatus_comp_modeA_wd
#print axioms ReferenceOperationality.IsModeAOpW_id
#print axioms ReferenceOperationality.IsModeAOpW.compose
#print axioms ReferenceOperationality.IsModeAOpW.of_pointwise
#print axioms interApparatus_comp_modeAW
#print axioms comp_modeAW_pointwise

end VR.Apparatus
