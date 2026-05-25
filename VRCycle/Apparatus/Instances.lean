-- VR-Apparatus: Instances (DOI TBD — v0.1.0)
-- Stage 5: Instance enrichment — additional apparatus instances from VR cycle.
--
-- STAGE: 5 (of 7). SOURCE: PLAN.md Stage 5; CLAUDE.md §Finding A, §Finding B.
--
-- ## Position statement
-- Expands apparatus test coverage beyond the two «founding examples»
-- (isComputableReal_add_isModeA, osetZFA_singleton_isModeA from Stage 2).
-- Re-derives existing VR instances as explicit apparatus objects.
-- No new mathematical content — pure apparatus packaging of existing VR material.
--
-- ## Instance groups
--
-- Group A (PredicateOperationality, Mode A):
--   A1. isComputableReal_neg_isModeA   — unary Mode A, wraps IsComputableReal_neg.
--   A2. isComputableReal_sub_isModeA   — binary Mode A, wraps IsComputableReal_sub.
--
-- Group B (ReferenceOperationality, ZFSet apparatus):
--   B1. instRefOpPSet                  — @ReferenceOperationality PSet PSet.setoid.
--       Second reference apparatus instance. Completes pair: OSet (ZFC) and
--       OSetZFA (ZFA) both explicit apparatus instances. Parallel to instRefOpCoPSet.
--       Actual axiom profile: [propext, Quot.sound] — Classical.choice NOT needed.
--       (Cleaner than instRefOpCoPSet which pulls Classical.choice from CoPSet/PFunctor.M.)
--
-- Group C (ReferenceOperationality, Mode A lower bound):
--   C1. osetZFA_empty_isModeA          — constant map to OSetZFA.empty is Mode A.
--       Demonstrates lower bound: constant maps are always Mode A.
--
-- Group D (cross-apparatus congruence — structural finding):
--   D1. embedPSet_congr_modeA_pattern  — congruence property of ZFC→ZFA embedding.
--       ARCHITECTURAL FINDING: ReferenceOperationality.IsModeAOp requires
--       f : Q → Quotient s (SAME setoid). Cross-apparatus maps (Q₁ → Quotient s₂)
--       are NOT directly expressible with IsModeAOp. The ZFC→ZFA embedding is a
--       heteromorphism (PSet → OSetZFA, two different quotients), not an endomorphism.
--       D1 states the congruence directly, as the cross-apparatus generalisation
--       of the Mode A pattern. This distinction requires separate treatment.
--       See §4 for full discussion.
--
-- ## Cross-instance structural finding (Stage 5)
-- Two reference apparatus instances (instRefOpPSet, instRefOpCoPSet) are connected
-- through the cross-apparatus congruence D1. The apparatus framework:
--   - Handles endomorphisms cleanly (IsModeAOp, f : Q → Quotient s, same setoid).
--   - Handles heteromorphisms (cross-apparatus maps) via direct congruence statement.
-- The distinction endomorphism vs heteromorphism is a Stage 5 finding with
-- implications for the preprint architecture section.
--
-- ## Import chain
-- VRCycle.Apparatus.ModeB → ModeA → SetsZFA.API → SetsZFA.Examples
--   → SetsZFA.Embedding (embedPSet, embedPSet_congr)
--   → Mathlib.SetTheory.ZFC.Basic (PSet, PSet.setoid, ZFSet, ZFSet.ext)
-- No additional imports needed.
--
-- ## Axiom profile
-- A1, A2:  [propext, Classical.choice, Quot.sound] (inherited from IsComputableReal).
-- B1:      [propext, Quot.sound] — cleaner than instRefOpCoPSet (no Classical.choice).
--          ZFSet.ext → propext; ZFSet/PSet quotient operations → Quot.sound.
--          Classical.choice NOT used: PSet is inductive (no PFunctor.M/M-type infra).
-- C1:      [propext, Classical.choice, Quot.sound] (OSetZFA.empty in statement).
--   Note: proof is `fun _ _ _ => rfl` (axiom-free proof term), but OSetZFA.empty
--   appears in statement → axioms propagate. Risk 4 from plan confirmed.
-- D1:      [propext, Classical.choice, Quot.sound] (OSetZFA.sound, CoPSet infra).
-- B1_rfl:  [] (identityNature rfl verification, no external dependencies).

import VRCycle.Apparatus.ModeB

namespace VR.Apparatus

-- ============================================================
-- §1. Group A — Additional PredicateOperationality Mode A instances
-- ============================================================

-- These wrap existing VR-Audit-1 theorems as explicit Mode A certificates.
-- Parallel structure to isComputableReal_add_isModeA from Stage 2.

/-- Negation on ℝ is a Mode A unary operation for the IsComputableReal apparatus.

**Certificate**: IsComputableReal_neg (VR-Audit Stage 1):
if x : ℝ has explicit rational approximations with moduli, so does -x.

This is the unary parallel to the binary `isComputableReal_add_isModeA`.
The predicate-wrapping apparatus (ℝ, IsComputableReal) is closed under negation.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from IsComputableReal_neg (standard ceiling). -/
theorem isComputableReal_neg_isModeA :
    PredicateOperationality.IsModeAOp (P := VR.Audit.IsComputableReal) Neg.neg :=
  fun _ hx => VR.Audit.IsComputableReal_neg hx

/-- Subtraction on ℝ is a Mode A binary operation for the IsComputableReal apparatus.

**Certificate**: IsComputableReal_sub (VR-Audit Stage 1):
if x, y : ℝ have explicit rational approximations with moduli, so does x - y.
Proof in VR-Audit: x - y = x + (-y), combining add and neg certificates.

The predicate-wrapping apparatus (ℝ, IsComputableReal) is closed under subtraction.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from IsComputableReal_sub (standard ceiling). -/
theorem isComputableReal_sub_isModeA :
    PredicateOperationality.IsModeAOp₂ (P := VR.Audit.IsComputableReal) (· - ·) :=
  fun _ _ hx hy => VR.Audit.IsComputableReal_sub hx hy

-- ============================================================
-- §2. Group B — ReferenceOperationality instance for ZFSet (OSet)
-- ============================================================

-- instRefOpPSet: second reference apparatus instance.
-- Parallel to instRefOpCoPSet in Reference.lean.
--
-- Technical notes:
--
-- ZFSet.ext signature (mathlib, Mathlib.SetTheory.ZFC.Basic line 190):
--   @[ext] lemma ZFSet.ext {x y : ZFSet} : (∀ z : ZFSet, z ∈ x ↔ z ∈ y) → x = y
--   x, y are implicit section variables. Wrapper: `fun _ _ h => ZFSet.ext h`.
--   Note: `fun x y h => ZFSet.ext h` produces unused variable warnings (x, y bound
--   explicitly but not used in body — ZFSet.ext infers them from h's type).
--   Fix: `fun _ _ h => ZFSet.ext h`. Lean infers {x y} from h : ∀ z, z ∈ x ↔ z ∈ y.
--
-- PSet.setoid (mathlib, Mathlib.SetTheory.ZFC.PSet line 112):
--   instance setoid : Setoid PSet
--   Accessible as PSet.setoid.
--
-- ZFSet = Quotient PSet.setoid (mathlib line 49 — definitional equality).
-- membership field type: Quotient PSet.setoid → Quotient PSet.setoid → Prop
--   = ZFSet → ZFSet → Prop  (by definitional equality)
--
-- ZFSet membership: the standard (· ∈ ·) via ZFSet.instMembership.
--
-- Axiom comparison with instRefOpCoPSet:
--   instRefOpCoPSet: [propext, Classical.choice, Quot.sound]
--   instRefOpPSet:   [propext, Quot.sound]   ← Classical.choice NOT needed
-- CoPSet = PFunctor.M CoPSetFunctor pulls Classical.choice transitively (M-type infra).
-- PSet is an inductive type — no M-type, no Classical.choice.
-- This is a meaningful asymmetry between the two reference apparatus instances.

/-- ZFSet (OSet) is a reference semantics apparatus over PSet.

Pre-set type:    PSet (inductive trees, Mathlib.SetTheory.ZFC.PSet).
Setoid:          PSet.setoid (PSet.Equiv, mutual inductive bisimulation).
Quotient:        ZFSet = Quotient PSet.setoid (ZFC set universe).
Membership:      (· ∈ ·) on ZFSet (via ZFSet.instMembership).
Extensionality:  ZFSet.ext.

This is the **second** reference apparatus instance. Together with
instRefOpCoPSet (OSetZFA), it establishes that both ZFC and ZFA set
universes in the VR cycle are explicit reference semantics apparatuses.

**Parallel structure** to instRefOpCoPSet (Reference.lean):
  Pre-sets: PSet  ↔  CoPSet
  Setoid:   PSet.setoid  ↔  CoPSet.instSetoid
  Quotient: ZFSet  ↔  OSetZFA
  Mem:      (· ∈ ·)  ↔  OSetZFA.Mem
  Ext:      ZFSet.ext  ↔  OSetZFA.ext

**Axiom profile asymmetry** (Stage 5 finding):
instRefOpPSet: [propext, Quot.sound] — Classical.choice NOT needed.
instRefOpCoPSet: [propext, Classical.choice, Quot.sound].
The difference reflects PSet (inductive, no M-type) vs CoPSet (coinductive,
PFunctor.M pulls Classical.choice). The ZFC apparatus is axiomatically lighter.

## Axiom profile: [propext, Quot.sound] -/
instance instRefOpPSet : @ReferenceOperationality PSet PSet.setoid where
  membership := (· ∈ · : ZFSet → ZFSet → Prop)
  ext := fun _ _ h => ZFSet.ext h

-- Verification: ZFSet apparatus has AsReference identity.
example : @ReferenceOperationality.identityNature PSet PSet.setoid instRefOpPSet =
    IdentityNature.AsReference := rfl

-- ============================================================
-- §3. Group C — Constant map as Mode A (lower bound demonstration)
-- ============================================================

/-- The constant map to OSetZFA.empty is Mode A for the CoPSet reference apparatus.

**Proof**: `fun _ _ _ => rfl` — a constant map trivially respects any equivalence.

**Methodological content**: this is the **lower bound** for Mode A:
  Every constant map `fun _ => c` is Mode A: `a ≈ b → c = c` needs no hypothesis.
  Mode A requires equivalence-preservation (a ≈ b → f a = f b), trivially true
  for constant maps without any hypothesis on the output.

**Contrast with singleton map** (osetZFA_singleton_isModeA in ModeA.lean):
  The singleton map requires `OSetZFA.sound` to establish equality of the outputs.
  The constant map needs no argument at all.

**Predicted axiom profile** (Risk 4 from Stage 5 plan, confirmed):
  Proof is `rfl` (axiom-free proof term), but OSetZFA.empty appears in the
  theorem STATEMENT. The rfl proof expands to `@Eq.refl OSetZFA OSetZFA.empty`,
  referencing OSetZFA.empty. Lean 4's `#print axioms` traces definitions in the
  proof term → axioms propagate from OSetZFA.empty.
  Actual profile: [propext, Classical.choice, Quot.sound].

## Axiom profile: [propext, Classical.choice, Quot.sound]
  (from OSetZFA.empty in the statement, despite rfl proof) -/
theorem osetZFA_empty_isModeA :
    @ReferenceOperationality.IsModeAOp
      VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid
      (fun _ => VR.SetsZFA.OSetZFA.empty) :=
  fun _ _ _ => rfl

-- ============================================================
-- §4. Group D — ZFC→ZFA cross-apparatus congruence (Stage 5 finding)
-- ============================================================

-- KEY ARCHITECTURAL FINDING (Stage 5):
-- ReferenceOperationality.IsModeAOp requires f : Q → Quotient s — the SAME setoid.
-- The ZFC→ZFA embedding is a CROSS-APPARATUS heteromorphism:
--   embedPSet : PSet → CoPSet          (representative-level, two different types)
--   fun p => OSetZFA.mk (embedPSet p)  (maps PSet → OSetZFA = Quotient CoPSet.instSetoid)
-- The codomain OSetZFA = Quotient CoPSet.instSetoid ≠ ZFSet = Quotient PSet.setoid.
-- Therefore @ReferenceOperationality.IsModeAOp PSet PSet.setoid (fun p => OSetZFA.mk ...)
-- FAILS to typecheck: Lean expects f : PSet → ZFSet (= Quotient PSet.setoid),
-- not f : PSet → OSetZFA (= Quotient CoPSet.instSetoid).
--
-- ENDOMORPHISM vs HETEROMORPHISM:
-- IsModeAOp handles ENDOMORPHISMS: f maps Q-representatives to the Q-quotient.
--   Stage 2 instances: osetZFA_singleton_rep : CoPSet → OSetZFA (= Quotient CoPSet.instSetoid)
--   IsModeAOp for CoPSet.instSetoid ✓
-- The ZFC→ZFA embedding is a HETEROMORPHISM: PSet → OSetZFA (two different quotient types).
--   @ReferenceOperationality.IsModeAOp PSet PSet.setoid f requires f : PSet → ZFSet ✗
--
-- CONSEQUENCE: A generalised cross-apparatus congruence concept is needed for heteromorphisms.
-- The current framework covers apparatus endomorphisms cleanly; heteromorphisms require
-- a new concept (potential Stage 6 extension or preprint discussion).
--
-- D1 states the congruence directly, as the cross-apparatus generalisation of Mode A:
--   ∀ p q : PSet, PSet.Equiv p q → OSetZFA.mk (embedPSet p) = OSetZFA.mk (embedPSet q)
-- This IS the Mode A pattern — but with source setoid PSet.setoid and
-- target quotient OSetZFA (Quotient CoPSet.instSetoid), two different structures.

/-- The ZFC→ZFA representative map satisfies the cross-apparatus congruence condition.

**Statement**: `∀ p q : PSet, PSet.Equiv p q → OSetZFA.mk (embedPSet p) = OSetZFA.mk (embedPSet q)`

**Proof**:
  `embedPSet_congr hpq : CoPSet.Equiv (embedPSet p) (embedPSet q)` (Stage 6)
  `OSetZFA.sound (embedPSet_congr hpq) : OSetZFA.mk (embedPSet p) = OSetZFA.mk (embedPSet q)`

**This is the Mode A pattern** — congruence condition for `Quotient.lift` — but applied
heterogeneously:
  Source: PSet with setoid PSet.setoid (PSet.Equiv)
  Target: OSetZFA = Quotient CoPSet.instSetoid (OSetZFA equality)
Two different quotient structures. This is a cross-apparatus congruence.

**Architectural finding** (Stage 5):
`ReferenceOperationality.IsModeAOp` handles ENDOMORPHISMS (f : Q → Quotient s, same setoid).
The ZFC→ZFA embedding is a HETEROMORPHISM (PSet → OSetZFA, two distinct quotients).
IsModeAOp does not typecheck for this case — the cross-apparatus heteromorphism
requires a separate concept.

**Relationship to embedOSet** (VR-Sets-ZFA Stage 6):
  `embedOSet = Quotient.lift (fun p => OSetZFA.mk (embedPSet p)) (embedPSet_congr_modeA_pattern)`
  This theorem IS the well-definedness proof for `embedOSet`: it enables the Quotient.lift.

**Implication for preprint**: the apparatus framework captures:
  - Intra-apparatus endomorphisms: IsModeAOp (Stage 2, Stage 5 instances).
  - Cross-apparatus heteromorphisms: direct congruence (this theorem).
A unified concept would cover both. Stage 5 identifies the gap; addressing it
is potential future work.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  OSetZFA.sound: Quot.sound.
  CoPSet.instSetoid/OSetZFA infrastructure: Classical.choice (PFunctor.M).
  propext: standard ceiling. -/
theorem embedPSet_congr_modeA_pattern :
    ∀ p q : PSet, PSet.Equiv p q →
      VR.SetsZFA.OSetZFA.mk (VR.SetsZFA.embedPSet p) =
      VR.SetsZFA.OSetZFA.mk (VR.SetsZFA.embedPSet q) :=
  fun _ _ hpq =>
    VR.SetsZFA.OSetZFA.sound (VR.SetsZFA.embedPSet_congr hpq)

-- ============================================================
-- §5. Cross-instance observations
-- ============================================================

-- Observation 1: instRefOpPSet is cleaner than instRefOpCoPSet.
-- PSet (inductive): [propext, Quot.sound].
-- CoPSet (coinductive/M-type): [propext, Classical.choice, Quot.sound].
-- The inductive foundation of ZFC requires fewer axioms than the coinductive ZFA.

-- Observation 2: embedPSet_congr_modeA_pattern is the well-definedness proof for embedOSet.
-- VR-Sets-ZFA Stage 6 proves:
--   embedOSet := Quotient.lift (fun p => OSetZFA.mk (embedPSet p)) (...)
-- where the (...) is exactly the content of embedPSet_congr_modeA_pattern.
-- The apparatus framework re-reads this as the cross-apparatus Mode A condition.

-- Verification: modeA_liftFn for osetZFA_empty_isModeA.
-- Demonstrates the Mode A lifting machinery on the constant map instance.
example (a : VR.SetsZFA.OSetZFA) :
    ReferenceOperationality.modeA_liftFn osetZFA_empty_isModeA a =
    VR.SetsZFA.OSetZFA.empty := by
  revert a
  apply Quotient.ind
  intro x
  rfl

-- ============================================================
-- Axiom audit — Stage 5, Instances.lean
-- ============================================================
-- STAGE: 5. SOURCE: PLAN.md Stage 5.
-- LEAN OBJECTS (6 public objects):
--   isComputableReal_neg_isModeA       (theorem, Group A, unary Mode A)
--   isComputableReal_sub_isModeA       (theorem, Group A, binary Mode A)
--   instRefOpPSet                      (instance, Group B, ZFSet reference apparatus)
--   osetZFA_empty_isModeA              (theorem, Group C, constant map Mode A)
--   embedPSet_congr_modeA_pattern      (theorem, Group D, cross-apparatus congruence)
-- AXIOM AUDIT:
--   A1: [propext, Classical.choice, Quot.sound] (IsComputableReal_neg inheritance).
--   A2: [propext, Classical.choice, Quot.sound] (IsComputableReal_sub inheritance).
--   B1: [propext, Quot.sound] — Classical.choice ABSENT. Axiom finding Stage 5.
--   C1: [propext, Classical.choice, Quot.sound] — Risk 4 confirmed: rfl proof but
--       OSetZFA.empty in statement pulls axioms.
--   D1: [propext, Classical.choice, Quot.sound] (OSetZFA.sound + CoPSet infra).
-- CHECKS: no sorry, no admit.

#print axioms isComputableReal_neg_isModeA
#print axioms isComputableReal_sub_isModeA
#print axioms instRefOpPSet
#print axioms osetZFA_empty_isModeA
#print axioms embedPSet_congr_modeA_pattern

end VR.Apparatus
