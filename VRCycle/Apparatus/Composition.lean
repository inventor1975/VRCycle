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
--
-- 4 objects axiom-free []; 3 objects sub-ceiling [Quot.sound].
-- No propext, no Classical.choice. Pure quotient-algebraic composition.
--
-- ## Productive triviality — fifth through seventh instances
-- Identity proofs (A1, A3, A4) are one-liners; B1 is one-liner.
-- The simplicity IS the content: identities are free because the apparatus
-- was defined correctly.
-- Full count: modeA_liftFn (v0.1.0), operand_determines_operational (Stage 4),
-- IsModeBOp_of_factorisable (Stage 4), separability_provides_factorisable (Stage 6),
-- IsModeAOp_id (Stage 3), id_isInterApparatus (Stage 3), IsModeBOp_id (Stage 3).

import VRCycle.Apparatus.InterMorphism

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

/-- Reference Mode A identity: `Quotient.mk s` is a Mode A map for `(Q, s)`.

`IsModeAOp (Quotient.mk s) = ∀ a b : Q, a ≈ b → Quotient.mk s a = Quotient.mk s b`

**Proof**: `fun a b hab => Quotient.sound hab`. Equivalent representatives give
equal quotient elements — Quotient.sound exactly.

**Compositional role**: identity element of the Level 2 composition monoid.
Unlike Levels 1, 3, 4 where `id` is the identity, Level 2's identity element
is `Quotient.mk s` (type: Q → Quotient s, not Q → Q), because Level 2 maps
are Q → Quotient s, not endomorphisms on Q. The lifted identity is `id` on
Quotient s (see `modeA_liftFn_quotientMk_eq_id`).

## Axiom profile: [Quot.sound] -/
theorem ReferenceOperationality.IsModeAOp_quotientMk {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.IsModeAOp (Quotient.mk s) :=
  fun _ _ hab => Quotient.sound hab

/-- The Mode A lift of `Quotient.mk s` is the identity on `Quotient s`.

`modeA_liftFn IsModeAOp_quotientMk = id`

**Proof**: `modeA_liftFn IsModeAOp_quotientMk ⟦a⟧ = Quotient.mk s a = ⟦a⟧`.
`rfl` at representative level; `Quotient.inductionOn` discharges the quotient.

**Identity certificate**: completes the Level 2 identity element story.
`IsModeAOp_quotientMk`: "Quotient.mk s is Mode A."
`modeA_liftFn_quotientMk_eq_id`: "its lift is the identity function on Quotient s."

## Axiom profile: [Quot.sound] -/
theorem ReferenceOperationality.modeA_liftFn_quotientMk_eq_id
    {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.modeA_liftFn
      (@ReferenceOperationality.IsModeAOp_quotientMk Q s) = id := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

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

/-- Functor law: Mode A lift ∘ IAM lift = direct Quotient.lift of composition.

`modeA_liftFn hg ∘ hf.lift = Quotient.lift (g ∘ f) (interApparatus_comp_modeA_wd hf hg)`

**Proof**: for representative `a : Q1`:
  - LHS: `(modeA_liftFn hg ∘ hf.lift) ⟦a⟧ = modeA_liftFn hg ⟦f a⟧ = g(f a)`.
  - RHS: `Quotient.lift (g ∘ f) _ ⟦a⟧ = (g ∘ f) a = g(f a)`.
Both reduce to `g(f a)` definitionally. `rfl` closes; `Quotient.inductionOn` discharges.

**Two functor laws in the reference track**:
  Level 3 ∘ Level 3 at quotient: `lift_compose` (Stage 2).
  Level 3 + Level 2 at quotient: `modeA_liftFn_comp_interApparatus` (Stage 3 B2).
Together: quotient-level maps respect both within-level and cross-level composition.

**Parallel to**: `InterApparatusMorphism.lift_compose` from Stage 2 (which is the
IAM ∘ IAM version of this functor law).

## Axiom profile: [Quot.sound]
  Quotient.inductionOn uses Quot.sound. -/
theorem modeA_liftFn_comp_interApparatus
    {Q1 Q2 : Type*} [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} {g : Q2 → Quotient s2}
    (hf : InterApparatusMorphism f)
    (hg : @ReferenceOperationality.IsModeAOp Q2 s2 g) :
    ReferenceOperationality.modeA_liftFn hg ∘ hf.lift =
    Quotient.lift (g ∘ f) (interApparatus_comp_modeA_wd hf hg) := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

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

-- Level 2 identity: the lift of IsModeAOp_quotientMk is id on Quotient.
example {Q : Type*} [s : Setoid Q] (q : Quotient s) :
    ReferenceOperationality.modeA_liftFn
      (@ReferenceOperationality.IsModeAOp_quotientMk Q s) q = q := by
  simp [ReferenceOperationality.modeA_liftFn_quotientMk_eq_id]

-- Level 3 identity: lift of id_isInterApparatus is id on the quotient.
example {Q : Type*} [s : Setoid Q] :
    (@InterApparatusMorphism.id_isInterApparatus Q s).lift = id := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

-- Cross-level B1: embedPSet_isInterApparatus + IsModeAOp_quotientMk.
-- Well-definedness for composing embedPSet (IAM) with Quotient.mk CoPSet.instSetoid (Mode A).
example :
    ∀ a b : PSet, a ≈ b →
      (Quotient.mk VR.SetsZFA.CoPSet.instSetoid ∘ VR.SetsZFA.embedPSet) a =
      (Quotient.mk VR.SetsZFA.CoPSet.instSetoid ∘ VR.SetsZFA.embedPSet) b :=
  interApparatus_comp_modeA_wd embedPSet_isInterApparatus
    ReferenceOperationality.IsModeAOp_quotientMk

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
-- AXIOM AUDIT:
--   [] (4): IsModeAOp_id, id_isInterApparatus, IsModeBOp_id, interApparatus_comp_modeA_wd
--   [Quot.sound] (3): IsModeAOp_quotientMk, modeA_liftFn_quotientMk_eq_id,
--                     modeA_liftFn_comp_interApparatus
-- CHECKS: no sorry, no admit.

#print axioms PredicateOperationality.IsModeAOp_id
#print axioms ReferenceOperationality.IsModeAOp_quotientMk
#print axioms ReferenceOperationality.modeA_liftFn_quotientMk_eq_id
#print axioms InterApparatusMorphism.id_isInterApparatus
#print axioms IsModeBOp_id
#print axioms interApparatus_comp_modeA_wd
#print axioms modeA_liftFn_comp_interApparatus

end VR.Apparatus
