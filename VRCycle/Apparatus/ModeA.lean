-- VR-Apparatus: ModeA (DOI TBD — v0.1.0)
-- Stage 2: Mode A closure theorem for both apparatus modes.
--
-- STAGE: 2 (of 7). SOURCE: PLAN.md Stage 2; CLAUDE.md §Finding A.
--
-- ## Position statement
-- Formalises Finding A (Mode A, sufficient condition): if an operation stays
-- within VR's operational register, it lifts freely to the operational type.
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- ontological levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- Two apparatus modes, two parallel theorems:
--
--   (A) Predicate-wrapping: f : T → T preserves P iff it lifts to {x : T // P x}.
--       Lifting = Subtype.mk — definitionally trivial.
--       "Productively trivial": the theorem's simplicity IS its content.
--
--   (B) Reference semantics: f : Q → Quotient s respects ≈ iff it lifts
--       to Quotient s → Quotient s via Quotient.lift.
--
-- ## Lean 4 structural note (section variable and @-form)
-- IsModeAOp and IsModeAOp₂ do not use [PredicateOperationality T P] in
-- their bodies (the definition is purely ∀ x, P x → P (f x)). Lean 4
-- therefore does NOT add the typeclass instance to their auto-generated
-- signatures. Consequence: the instance must NOT appear in @-form calls
-- (i.e., @IsModeAOp T P f, not @IsModeAOp T P _ f).
--
-- The apparatus context is expressed structurally (namespace) rather than
-- through the [PredicateOperationality T P] parameter. This parallels the
-- reference semantics case where [ReferenceOperationality Q] is also absent
-- from IsModeAOp's signature (the definition only needs [Setoid Q]).
--
-- This is a methodological finding: Mode A is apparatus-structure-independent.
-- The lifting mechanism (Subtype.mk / Quotient.lift) is purely about the
-- predicate/relation — not the full apparatus class.
--
-- ## Composition (Opus Stage 2 addition)
-- Mode A operations form a composition-closed family:
--   Predicate-wrapping:  IsModeAOp f → IsModeAOp g → IsModeAOp (g ∘ f)
--   Reference semantics: IsModeAOp f → IsModeAOp g →
--                        IsModeAOp (fun a => modeA_liftFn hg (f a))
-- Both reflect that Mode A maps form a category.
--
-- ## Concrete instances
-- Case 1 (predicate-wrapping, binary):
--   isComputableReal_add_isModeA: (· + ·) is IsModeAOp₂ for IsComputableReal.
-- Case 2 (reference semantics):
--   osetZFA_singleton_isModeA: the singleton map is IsModeAOp for CoPSet.
--
-- ## Axiom profile
-- IsModeAOp, IsModeAOp₂, modeA_liftFn*, modeA_lift*:  [].
-- IsModeAOp.compose (both modes):                       [].
-- isComputableReal_add_isModeA:  [propext, Classical.choice, Quot.sound].
-- osetZFA_singleton_isModeA:     [propext, Classical.choice, Quot.sound].

import VRCycle.Apparatus.Wrapping
import VRCycle.Apparatus.Reference
import VRCycle.SetsZFA.API

namespace VR.Apparatus

-- ============================================================
-- §1. Predicate-wrapping Mode A
-- ============================================================

namespace PredicateOperationality

-- Note: section variable uses {T} {P} WITHOUT [PredicateOperationality T P].
-- Reason: IsModeAOp, IsModeAOp₂ bodies do not use the instance, so Lean
-- would not add it to their signatures. Using @-form calls requires knowing
-- exactly which arguments are in the signature. See module header note.

section
variable {T : Type*} {P : T → Prop}

/-- A unary operation f : T → T is Mode A for the predicate-wrapping apparatus
(T, P) if it preserves the operational predicate P.

**Mode A** (Finding A): f stays in the operational register ↔ it lifts to
`{x : T // P x}` at zero cost (lifting = Subtype.mk, definitionally trivial).

**Apparatus-independence of IsModeAOp**: this definition does not require the
[PredicateOperationality T P] instance — it is a property of (P, f) alone.
The apparatus context is expressed by the `PredicateOperationality` namespace.

## Axiom profile: [] -/
def IsModeAOp (f : T → T) : Prop :=
  ∀ x : T, P x → P (f x)

/-- A binary operation f : T → T → T is Mode A for (T, P) if it preserves P.

## Axiom profile: [] -/
def IsModeAOp₂ (f : T → T → T) : Prop :=
  ∀ x y : T, P x → P y → P (f x y)

/-- Mode A unary lift: certificate hf : IsModeAOp f lifts to a function on the
operational subtype `{x : T // P x}`.

**Productively trivial**: the lift IS Subtype.mk. Staying in the register = free.

**@-form note**: `@IsModeAOp T P f` (3 args: T, P, f) because IsModeAOp's
auto-generated signature has no instance argument.

## Axiom profile: [] -/
def modeA_liftFn {f : T → T} (hf : @IsModeAOp T P f) :
    {x : T // P x} → {x : T // P x} :=
  fun x => ⟨f x.val, hf x.val x.property⟩

/-- Computation rule: (modeA_liftFn hf x).val = f x.val.

**Proof**: rfl. **@[simp]**: allows simp to reduce `.val` of a lifted function
application to the underlying function. Loop-safe: rewrites `modeA_liftFn _ _`
to `f _`, strictly reducing structure.

## Axiom profile: [] -/
@[simp]
theorem modeA_lift {f : T → T} (hf : @IsModeAOp T P f) (x : {x : T // P x}) :
    (modeA_liftFn hf x).val = f x.val :=
  rfl

/-- Mode A binary lift: certificate hf : IsModeAOp₂ f lifts to a binary function
on the operational subtype.

## Axiom profile: [] -/
def modeA_liftFn₂ {f : T → T → T} (hf : @IsModeAOp₂ T P f) :
    {x : T // P x} → {x : T // P x} → {x : T // P x} :=
  fun x y => ⟨f x.val y.val, hf x.val y.val x.property y.property⟩

/-- Computation rule: (modeA_liftFn₂ hf x y).val = f x.val y.val.

**Proof**: rfl. **@[simp]**: reduces binary lifted applications. Loop-safe.

## Axiom profile: [] -/
@[simp]
theorem modeA_lift₂ {f : T → T → T} (hf : @IsModeAOp₂ T P f)
    (x y : {x : T // P x}) :
    (modeA_liftFn₂ hf x y).val = f x.val y.val :=
  rfl

/-- Mode A unary operations compose.

If f and g are both Mode A for (T, P), then g ∘ f is also Mode A.

**Proof**: P x → P (f x) → P (g (f x)). One-liner: `fun x hx => hg (f x) (hf x hx)`.

**Categorical**: Mode A endomorphisms of (T, P) compose — they form a category.

## Axiom profile: [] -/
theorem IsModeAOp.compose {f g : T → T}
    (hf : @IsModeAOp T P f) (hg : @IsModeAOp T P g) :
    @IsModeAOp T P (g ∘ f) :=
  fun x hx => hg (f x) (hf x hx)

end -- section {T : Type*} {P : T → Prop}
end PredicateOperationality

-- ============================================================
-- §2. Reference semantics Mode A
-- ============================================================

namespace ReferenceOperationality

section
variable {Q : Type*} [s : Setoid Q]

/-- A map f : Q → Quotient s is Mode A for the reference semantics apparatus if
it respects the equivalence: equivalent representatives give equal quotient values.
This is the well-definedness condition for Quotient.lift.

**Parallel structure**:
  - Predicate-wrapping: f preserves P → lifts to {x : T // P x} via Subtype.mk
  - Reference semantics: f respects ≈ → lifts to Quotient s via Quotient.lift

**Apparatus-independence**: [ReferenceOperationality Q] is not in the signature
(the definition only needs [Setoid Q] via the ≈ notation). The apparatus context
is expressed by the `ReferenceOperationality` namespace.

## Axiom profile: [] -/
def IsModeAOp (f : Q → Quotient s) : Prop :=
  ∀ a b : Q, a ≈ b → f a = f b

/-- Mode A quotient lift: a Mode A certificate lifts f : Q → Quotient s to
a well-defined map Quotient s → Quotient s via Quotient.lift.

**noncomputable**: marked for safety in the OSetZFA context. The definition
uses only the primitive Quotient.lift (axiom-free).

## Axiom profile: [] -/
noncomputable def modeA_liftFn {f : Q → Quotient s} (hf : IsModeAOp f) :
    Quotient s → Quotient s :=
  Quotient.lift f hf

/-- Computation rule: modeA_liftFn hf ⟦a⟧ = f a.

**Proof**: rfl (Quotient.lift_mk is definitional). **@[simp]**: reduces
quotient-lifted applications at representative level. Loop-safe: rewrites
`modeA_liftFn _ ⟦_⟧` to `f _`.

## Axiom profile: [] -/
@[simp]
theorem modeA_lift {f : Q → Quotient s} (hf : IsModeAOp f) (a : Q) :
    modeA_liftFn hf (Quotient.mk s a) = f a :=
  rfl

/-- Mode A operations compose (reference semantics).

If f and g are both Mode A, then `fun a => modeA_liftFn hg (f a)` is Mode A.

**Categorical**: this is composition of the lifted maps on the quotient:
  F = modeA_liftFn hf, G = modeA_liftFn hg, then G ∘ F = modeA_liftFn (compose).

**Asymmetry with predicate-wrapping**: uses `modeA_liftFn hg ∘ f` rather than
`g ∘ f` because f's output is Quotient s (not Q). Genuine structural difference.

## Axiom profile: [] -/
theorem IsModeAOp.compose {f g : Q → Quotient s}
    (hf : IsModeAOp f) (hg : IsModeAOp g) :
    IsModeAOp (fun a => modeA_liftFn hg (f a)) :=
  fun a b hab => congrArg (modeA_liftFn hg) (hf a b hab)

end -- section {Q : Type*} [s : Setoid Q]
end ReferenceOperationality

-- ============================================================
-- §3. Concrete instances
-- ============================================================

/-- Addition on ℝ is a Mode A binary operation for the IsComputableReal apparatus.

**Certificate**: IsComputableReal_add (VR-Audit Stage 1):
if x, y : ℝ have explicit rational approximations with moduli, so does x + y.

**Named-argument form** `(P := VR.Audit.IsComputableReal)`: T = ℝ is inferred
from P : ℝ → Prop; `[PredicateOperationality ℝ IsComputableReal]` is found
from the instance in Wrapping.lean.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from IsComputableReal_add (standard ceiling). -/
theorem isComputableReal_add_isModeA :
    PredicateOperationality.IsModeAOp₂ (P := VR.Audit.IsComputableReal) (· + ·) :=
  fun _ _ hx hy => VR.Audit.IsComputableReal_add hx hy

-- Case 2: OSetZFA.singleton is IsModeAOp for CoPSet reference semantics.

/-- Representative-level singleton map: sends CoPSet a to the OSetZFA singleton
containing OSetZFA.mk a.

**noncomputable**: OSetZFA.singleton uses Quotient.liftOn with classical CoPSet
infrastructure. -/
private noncomputable def osetZFA_singleton_rep :
    VR.SetsZFA.CoPSet → VR.SetsZFA.OSetZFA :=
  fun a => VR.SetsZFA.OSetZFA.singleton (VR.SetsZFA.OSetZFA.mk a)

/-- The singleton map is Mode A for the CoPSet reference semantics apparatus.

**Certificate**: a ≈ b → OSetZFA.sound gives OSetZFA.mk a = OSetZFA.mk b;
then congrArg OSetZFA.singleton concludes.

No access to the private `singleton_congr` needed: well-definedness of
OSetZFA.singleton is recovered via OSetZFA.sound + congrArg.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  OSetZFA.sound uses Quot.sound; CoPSet infra (PFunctor.M) uses Classical.choice. -/
theorem osetZFA_singleton_isModeA :
    @ReferenceOperationality.IsModeAOp
      VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid
      osetZFA_singleton_rep :=
  fun _ _ hab =>
    congrArg VR.SetsZFA.OSetZFA.singleton (VR.SetsZFA.OSetZFA.sound hab)

-- ============================================================
-- §4. Verification examples
-- ============================================================

-- Binary lift computation rule: rfl.
example (x y : {r : ℝ // VR.Audit.IsComputableReal r}) :
    (PredicateOperationality.modeA_liftFn₂ isComputableReal_add_isModeA x y).val =
    x.val + y.val :=
  rfl

-- Composition: double negation is Mode A.
example : PredicateOperationality.IsModeAOp
    (P := VR.Audit.IsComputableReal) (fun x => -(-(x))) :=
  PredicateOperationality.IsModeAOp.compose
    (fun _ hx => VR.Audit.IsComputableReal_neg hx)
    (fun _ hx => VR.Audit.IsComputableReal_neg hx)

-- ============================================================
-- Axiom audit — Stage 2, ModeA.lean
-- ============================================================
-- STAGE: 2. SOURCE: PLAN.md Stage 2.
-- LEAN OBJECTS:
--   PredicateOperationality.IsModeAOp     (def, Prop, unary)
--   PredicateOperationality.IsModeAOp₂    (def, Prop, binary)
--   PredicateOperationality.modeA_liftFn  (def, Subtype → Subtype)
--   PredicateOperationality.modeA_lift    (theorem, rfl)
--   PredicateOperationality.modeA_liftFn₂ (def, Subtype → Subtype → Subtype)
--   PredicateOperationality.modeA_lift₂   (theorem, rfl)
--   PredicateOperationality.IsModeAOp.compose (theorem)
--   ReferenceOperationality.IsModeAOp     (def, Prop)
--   ReferenceOperationality.modeA_liftFn  (noncomputable def, Quotient.lift)
--   ReferenceOperationality.modeA_lift    (theorem, rfl)
--   ReferenceOperationality.IsModeAOp.compose (theorem)
--   isComputableReal_add_isModeA          (theorem, Case 1)
--   osetZFA_singleton_isModeA             (theorem, Case 2)
-- AXIOM AUDIT: infrastructure [], concrete instances [propext, Classical.choice, Quot.sound].

#print axioms PredicateOperationality.IsModeAOp
#print axioms PredicateOperationality.IsModeAOp₂
#print axioms PredicateOperationality.modeA_liftFn
#print axioms PredicateOperationality.modeA_lift
#print axioms PredicateOperationality.modeA_liftFn₂
#print axioms PredicateOperationality.modeA_lift₂
#print axioms PredicateOperationality.IsModeAOp.compose
#print axioms ReferenceOperationality.IsModeAOp
#print axioms ReferenceOperationality.modeA_liftFn
#print axioms ReferenceOperationality.modeA_lift
#print axioms ReferenceOperationality.IsModeAOp.compose
#print axioms isComputableReal_add_isModeA
#print axioms osetZFA_singleton_isModeA

end VR.Apparatus
