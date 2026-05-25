-- VR-Apparatus: ModeB (DOI TBD — v0.1.0)
-- Stage 3: Mode B schema — conditional operational extraction.
--
-- STAGE: 3 (of 7). SOURCE: PLAN.md Stage 3; CLAUDE.md §Finding A.
--
-- ## Position statement
-- Formalises Finding A (Mode B, conditional): when a classical operation is applied
-- to an operationally-enriched operand, the result can still be extractably operational.
--
-- ## Mode B refined framing (reconnaissance finding, Stage 3)
-- The original framing «classical theorem implies operational conclusion» is INCORRECT
-- for VR-Audit-1. HahnBanachOperational_Hilbert does NOT derive the operational
-- result from a classical Hahn-Banach premise. Instead:
--
--   1. Riesz constructs ξ ∈ M classically (using Classical.choice via toDual).
--   2. g = innerSL ℝ (ξ : E) is defined directly from ξ.
--   3. Operationality of g at denseSeq n flows back to f:
--      g(denseSeq n) = f(P_M(denseSeq n)) — finite factorisation through f.
--
-- Correct framing: **classically-constructed operation is operationally evaluable
-- on operationally-enriched operand**. The operation (Riesz extension) is classical;
-- the operand (OperationalNormableFunctional f) carries operational content;
-- the operation routes operationality through.
--
-- This is the «operand-not-operation» insight in precise form: operationality flows
-- FROM the operand THROUGH the classical operation to the result.
--
-- ## IsModeBOp definition
-- `IsModeBOp PA PB W f`: f maps (PA ∧ W)-elements to PB-elements.
--
-- Parameters:
--   PA : A → Prop   — operational predicate on the OPERAND type A
--   PB : B → Prop   — operational predicate on the RESULT type B
--   W  : A → Prop   — WITNESS condition on the operand (why extraction works)
--   f  : A → B      — the (possibly classical) operation
--
-- Mode A is the special case W = trivially satisfied:
--   IsModeAOp P f = IsModeBOp P P (fun _ => True) f
--
-- Mode B adds the witness W:
--   IsModeAOp fails for f globally → but IsModeBOp holds for operands satisfying W.
-- W captures WHY the operation is locally operational. For VR-Audit-1:
--   W = implicit [OperationalHilbertSpace E] typeclass (separability witness).
--
-- ## Apparatus-independence (parallel to Stage 2 finding)
-- IsModeBOp does NOT require [PredicateOperationality] or [ReferenceOperationality].
-- The definition is purely about predicates PA, PB, W and the function f.
-- The apparatus context is expressed by the VR.Apparatus namespace.
-- Mode B, like Mode A, is apparatus-structure-independent.
--
-- ## Typeclass-level vs term-level witness (VR-Audit-1 finding)
-- For the Hilbert Mode B instance, W = fun _ => True (trivial at term level).
-- The actual separability witness ([OperationalHilbertSpace E]) lives at the
-- TYPECLASS level, not as a term-level predicate on the operand.
-- This is «Outcome β» (abstract clean, concrete typeclass-dependent):
-- IsModeBOp formalises cleanly; concrete instances may need typeclass-level W.
-- Two sub-forms of Mode B:
--   Mode B-term:     W : A → Prop (term-level witness, used in IsModeBOp)
--   Mode B-typeclass: witness expressed via [Typeclass A] (Hilbert case)
-- This distinction is a Stage 3 finding for the preprint.
--
-- ## Axiom profile
-- IsModeBOp (def): [].
-- IsModeBOp.lift (def): [].
-- IsModeAOp_iff_IsModeBOp (theorem): [].
-- IsModeBOp.compose (theorem): [].
-- riesz_extension_map (noncomputable def): [propext, Classical.choice, Quot.sound].
-- riesz_extension_isModeBOp (theorem): [propext, Classical.choice, Quot.sound].

import VRCycle.Apparatus.ModeA
import VRCycle.Audit.HahnBanach

namespace VR.Apparatus

-- ============================================================
-- §1. IsModeBOp — the Mode B condition
-- ============================================================

/-- `IsModeBOp PA PB W f`: f is a Mode B operation mapping
(PA ∧ W)-enriched elements of A to PB-operational elements of B.

**Parameters**:
  PA : A → Prop  — operational predicate on the operand.
  PB : B → Prop  — operational predicate on the result.
  W  : A → Prop  — witness condition: WHY extraction is possible for this operand.
  f  : A → B     — the operation (may use classical machinery).

**Semantics**: for every a : A with PA a and W a, the result f a satisfies PB.

**Mode B refined framing** (Stage 3 reconnaissance finding):
  Mode B is NOT «classical_stmt → operational_stmt».
  Mode B IS: classically-constructed f is operationally evaluable on PA ∧ W operands.
  The witness W captures the additional structure (separability, Riesz factorisation)
  that makes the operand amenable to operational extraction.

**Apparatus-independence**: no [PredicateOperationality] or [ReferenceOperationality]
in the signature. Mode B, like Mode A, is apparatus-structure-independent.

**Mode A as special case**: IsModeAOp P f = IsModeBOp P P (fun _ => True) f.
See IsModeAOp_iff_IsModeBOp.

## Axiom profile: [] -/
def IsModeBOp {A B : Type*} (PA : A → Prop) (PB : B → Prop) (W : A → Prop) (f : A → B) : Prop :=
  ∀ a : A, PA a → W a → PB (f a)

-- ============================================================
-- §2. IsModeBOp.lift — the lifting theorem
-- ============================================================

/-- Mode B lift: given `IsModeBOp PA PB W f`, lift f to a function from
{a : A // PA a ∧ W a} to {b : B // PB b}.

This is the Mode B analogue of `PredicateOperationality.modeA_liftFn`:
  Mode A: {a : A // PA a} → {b : B // PB b}       (W trivially satisfied)
  Mode B: {a : A // PA a ∧ W a} → {b : B // PB b} (W explicitly required)

The additional witness condition W in the domain Subtype reflects that Mode B
requires enriched operands to guarantee operational results.

## Axiom profile: [] -/
def IsModeBOp.lift {A B : Type*} {PA : A → Prop} {PB : B → Prop} {W : A → Prop} {f : A → B}
    (hf : IsModeBOp PA PB W f) :
    {a : A // PA a ∧ W a} → {b : B // PB b} :=
  fun a => ⟨f a.val, hf a.val a.property.1 a.property.2⟩

/-- Computation rule: `(IsModeBOp.lift hf a).val = f a.val`.

**Proof**: rfl (definitional unfolding of Subtype). **@[simp]**: reduces
`.val` of a Mode B lifted application to the underlying function. Loop-safe.

## Axiom profile: [] -/
@[simp]
theorem IsModeBOp.lift_val {A B : Type*} {PA : A → Prop} {PB : B → Prop} {W : A → Prop}
    {f : A → B} (hf : IsModeBOp PA PB W f) (a : {a : A // PA a ∧ W a}) :
    (hf.lift a).val = f a.val :=
  rfl

-- ============================================================
-- §3. Mode A as special case of Mode B
-- ============================================================

/-- Mode A is the special case of Mode B with trivial witness W = fun _ => True.

`IsModeAOp P f ↔ IsModeBOp P P (fun _ => True) f`

**Interpretation**: Mode A = globally Mode B (witness always satisfied).
Mode B = locally Mode A (witness satisfied only for enriched operands).

**Structural relationship**: Mode B strictly generalises Mode A.
Every Mode A operation is Mode B; the converse fails when W is non-trivial.

**Note on predicate-wrapping Mode A**: uses `@IsModeAOp T P f` (3 explicit args)
because the auto-generated signature has no [PredicateOperationality T P] instance
(the body ∀ x, P x → P (f x) doesn't use it). See Stage 2 finding Stage2-D.

## Axiom profile: [] -/
theorem PredicateOperationality.IsModeAOp_iff_IsModeBOp
    {T : Type*} {P : T → Prop} {f : T → T} :
    @PredicateOperationality.IsModeAOp T P f ↔ IsModeBOp P P (fun _ => True) f :=
  ⟨fun h a ha _ => h a ha, fun h a ha => h a ha trivial⟩

/-- Mode A is Mode B with trivial witness (forward direction).

A Mode A certificate `hf : IsModeAOp f` gives a Mode B certificate for the same f
with W = fun _ => True.

## Axiom profile: [] -/
theorem PredicateOperationality.IsModeAOp.toModeBOp
    {T : Type*} {P : T → Prop} {f : T → T}
    (hf : @PredicateOperationality.IsModeAOp T P f) :
    IsModeBOp P P (fun _ => True) f :=
  IsModeAOp_iff_IsModeBOp.mp hf

-- ============================================================
-- §4. IsModeBOp.compose — composition theorem
-- ============================================================

/-- Mode B operations compose.

If f : A → B is Mode B (PA, PB, WA) and g : B → C is Mode B (PB, PC, WB),
then g ∘ f : A → C is Mode B with combined witness `fun a => WA a ∧ WB (f a)`.

**Combined witness interpretation**: to guarantee PC (g (f a)), we need:
  - WA a: the operand a satisfies its witness → PB (f a) via hf.
  - WB (f a): the intermediate f a satisfies the witness for g → PC (g (f a)) via hg.
The combined witness records BOTH conditions.

**Categorical structure**: Mode B maps compose. The witness condition accumulates —
composition requires more enrichment on the operand than either factor alone.
Contrast with Mode A: `IsModeAOp.compose` has trivial witnesses throughout.

## Axiom profile: [] -/
theorem IsModeBOp.compose {A B C : Type*}
    {PA : A → Prop} {PB : B → Prop} {PC : C → Prop}
    {WA : A → Prop} {WB : B → Prop}
    {f : A → B} {g : B → C}
    (hf : IsModeBOp PA PB WA f) (hg : IsModeBOp PB PC WB g) :
    IsModeBOp PA PC (fun a => WA a ∧ WB (f a)) (g ∘ f) :=
  fun a ha hw => hg (f a) (hf a ha hw.1) hw.2

-- ============================================================
-- §5. Concrete instance: VR-Audit-1 Hilbert Mode B
-- ============================================================

-- The Riesz extension is a Mode B operation.
-- This is the ACID TEST for the Mode B schema.
--
-- SETUP:
--   A = OperationalNormableFunctional E M    (operational functionals on subspace M)
--   B = E →L[ℝ] ℝ                           (classical CLMs on the ambient space E)
--   PA = fun _ => True                       (all OperationalNormableFunctionals are OK)
--   PB = fun g => (∀ n, IsComputableReal (g (denseSeq n))) ∧ IsComputableReal g.opNorm
--   W  = fun _ => True                       (witness is typeclass-level, see §5 doc)
--   f  = riesz_extension_map                 (the Riesz extension: f ↦ innerSL ℝ ξ)
--
-- WITNESS STRUCTURE (Stage 3 finding):
-- W = fun _ => True at the TERM level. The actual separability witness
-- ([OperationalHilbertSpace E].denseSeq) lives at the TYPECLASS level.
-- This is «Mode B-typeclass»: witness expressed via [OperationalHilbertSpace E],
-- not as a term-level predicate on OperationalNormableFunctional.
-- The formal IsModeBOp is satisfied with W = True because the witness
-- is already present in the typeclass context.
--
-- HOW OPERATIONALITY FLOWS (the Mode B factorisation):
--   g(denseSeq n) = ⟨denseSeq n, ξ⟩ = f(P_M(denseSeq n))
--   Operationality of f (operand) routes through to g (result) via Riesz.
--
-- OUTCOME: α (clean). VR-Audit-1 fits IsModeBOp with W = True. ✓

/-- The Riesz extension map: extracts the classical CLM g : E →L[ℝ] ℝ
provided by HahnBanachOperational_Hilbert for a given operational functional f.

**noncomputable**: uses Classical.choice via HahnBanachOperational_Hilbert
(Riesz representation requires CompleteSpace and InnerProductSpace.toDual).

This is the MODE B OPERATION: it takes an operational input f and returns
a classical g whose operationality is inherited from f. -/
noncomputable def riesz_extension_map {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E}
    (f : VR.Audit.OperationalNormableFunctional E M) : E →L[ℝ] ℝ :=
  (VR.Audit.HahnBanachOperational_Hilbert f).choose

/-- The Riesz extension map is a Mode B operation for the IsComputableReal apparatus.

**IsModeBOp** instance with:
  PA = fun _ => True  (all OperationalNormableFunctionals)
  PB = fun g => (∀ n, IsComputableReal (g (denseSeq n))) ∧ IsComputableReal g.opNorm
  W  = fun _ => True  (witness = [OperationalHilbertSpace E] typeclass, not term-level)

**Proof**: direct from HahnBanachOperational_Hilbert.choose_spec:
  `.1` gives ∀ n, IsComputableReal (g (denseSeq n))
  `.2.1` gives IsComputableReal g.opNorm

**Mode B refined framing** confirmed: the Riesz extension is NOT globally
Mode A (not every functional has computable denseSeq values), but IS Mode B
for OperationalNormableFunctional operands (whose operational content routes
through the Riesz factorisation g(denseSeq n) = f(P_M(denseSeq n))).

**Outcome classification**: α (clean VR-Audit-1 instance). IsModeBOp formalises
the Riesz extension pattern without forced type gymnastics.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Classical.choice: from HahnBanachOperational_Hilbert (Riesz, toDual, CompleteSpace).
  propext, Quot.sound: standard ceiling from mathlib. -/
theorem riesz_extension_isModeBOp {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E} :
    IsModeBOp
      (A := VR.Audit.OperationalNormableFunctional E M)
      (B := E →L[ℝ] ℝ)
      (PA := fun _ => True)
      (PB := fun g =>
        (∀ n : ℕ, VR.Audit.IsComputableReal
          (g (VR.Audit.OperationalHilbertSpace.denseSeq (E := E) n))) ∧
        VR.Audit.IsComputableReal g.opNorm)
      (W := fun _ => True)
      riesz_extension_map :=
  fun f _ _ =>
    let hspec := (VR.Audit.HahnBanachOperational_Hilbert f).choose_spec
    ⟨hspec.1, hspec.2.1⟩

-- ============================================================
-- §6. Mode B lift applied to the Riesz instance
-- ============================================================

-- Using the Riesz Mode B certificate to produce an operational subtype element.
-- This shows the machinery working end-to-end.

private def riesz_PB {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E] : (E →L[ℝ] ℝ) → Prop :=
  fun g =>
    (∀ n : ℕ, VR.Audit.IsComputableReal
      (g (VR.Audit.OperationalHilbertSpace.denseSeq (E := E) n))) ∧
    VR.Audit.IsComputableReal g.opNorm

/-- The Riesz extension lift: given an operational functional f, produce
an element {g : E →L[ℝ] ℝ // g is computable on denseSeq ∧ norm computable}
via the Mode B lifting mechanism.

This demonstrates Mode B machinery working end-to-end:
  OperationalNormableFunctional E M ⊃ {f // True ∧ True}
  → via IsModeBOp.lift (riesz_extension_isModeBOp)
  → {g : E →L[ℝ] ℝ // computable on denseSeq ∧ norm computable}

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from riesz_extension_isModeBOp. -/
noncomputable def riesz_mode_b_lift {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E} :
    {_f : VR.Audit.OperationalNormableFunctional E M // True ∧ True} →
    {g : E →L[ℝ] ℝ // riesz_PB g} :=
  riesz_extension_isModeBOp.lift

-- ============================================================
-- §7. Verification: Mode A → Mode B
-- ============================================================

-- Verify that IsModeAOp.toModeBOp works on a concrete example.
-- IsComputableReal_neg is Mode A → Mode B via toModeBOp.

example : IsModeBOp (PA := VR.Audit.IsComputableReal) (PB := VR.Audit.IsComputableReal)
    (W := fun _ => True) (fun x : ℝ => -x) :=
  PredicateOperationality.IsModeAOp.toModeBOp (fun _ hx => VR.Audit.IsComputableReal_neg hx)

-- ============================================================
-- Axiom audit — Stage 3, ModeB.lean
-- ============================================================
-- STAGE: 3. SOURCE: PLAN.md Stage 3.
-- LEAN OBJECTS:
--   IsModeBOp                       (def, Prop)
--   IsModeBOp.lift                  (def)
--   IsModeBOp.lift_val              (theorem, rfl)
--   PredicateOperationality.IsModeAOp_iff_IsModeBOp (theorem, iff)
--   PredicateOperationality.IsModeAOp.toModeBOp     (theorem)
--   IsModeBOp.compose               (theorem)
--   riesz_extension_map             (noncomputable def, VR-Audit-1 concrete)
--   riesz_extension_isModeBOp       (theorem, VR-Audit-1 concrete)
--   riesz_mode_b_lift               (noncomputable def, end-to-end demo)
-- AXIOM AUDIT:
--   abstract infrastructure: [].
--   VR-Audit-1 concrete: [propext, Classical.choice, Quot.sound].
-- CHECKS: no sorry, no admit.

#print axioms IsModeBOp
#print axioms IsModeBOp.lift
#print axioms IsModeBOp.lift_val
#print axioms PredicateOperationality.IsModeAOp_iff_IsModeBOp
#print axioms PredicateOperationality.IsModeAOp.toModeBOp
#print axioms IsModeBOp.compose
#print axioms riesz_extension_map
#print axioms riesz_extension_isModeBOp
#print axioms riesz_mode_b_lift

end VR.Apparatus
