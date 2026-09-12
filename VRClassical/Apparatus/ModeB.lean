-- VRClassical/Apparatus/ModeB.lean — the Riesz-extension Mode B instance (VR-Audit-1, Hilbert)
-- (split out of VRCycle/Apparatus/ModeB.lean on 2026-09-12: the Mode B definitions stay in the VR
-- core on `[]`; the Hilbert-space instance over Mathlib lives here).

import VRCycle.Apparatus.ModeB
import VRClassical.Apparatus.Wrapping
import VRClassical.Audit.HahnBanach

namespace VR.Apparatus

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

#print axioms riesz_extension_map
#print axioms riesz_extension_isModeBOp
#print axioms riesz_mode_b_lift

end VR.Apparatus
