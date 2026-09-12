-- VR-Apparatus: Factorisation (v1.0.0, Stage 4)
-- Operand-not-operation theorem — Factorisable as canonical Mode B witness.
--
-- STAGE: v1.0.0 Stage 4 (first of six pieces). SOURCE: PLAN.md Stage 4.
--
-- ## Position statement
-- Formalises the «operand-not-operation» insight documented in ModeB.lean §5:
-- operationality of the result f a is determined by the operand a,
-- not by the operation f.
--
-- The witness W in IsModeBOp PA PB W f can be taken as `Factorisable PA PB f`:
-- there exists an operational function g : A → B that agrees with f on the
-- specific operand a. This makes the structural reason for Mode B explicit,
-- rather than leaving W = fun _ => True.
--
-- ## Spectrum-of-witnesses finding (Stage 4)
-- IsModeBOp admits a spectrum of witnesses for the same operation f:
--
--   Minimal:   W = fun _ => True
--              Works when operationality is certified directly (e.g., via
--              HahnBanachOperational_Hilbert.choose_spec). No structural account.
--
--   Canonical: W = Factorisable PA PB f
--              Explicit structural reason: an operational g agrees with f on a.
--              Self-witnessing (g = f) is valid when f is already globally Mode B.
--
--   Mixed:     any W implying Factorisable (factorisable_implies_isModeBOp)
--              W need only certify existence of g, not name it.
--
-- Neither witness supersedes the other. The spectrum is a feature:
-- apparatus structure permits progressively more informative certificates
-- without breaking Mode B. Both v0.1.0 (W = True) and v1.0.0 (W = Factorisable)
-- Riesz instances are valid and coexist — see §5 comparison.
--
-- ## Relationship to v0.1.0
-- ModeB.lean is NOT modified. riesz_extension_isModeBOp (W = True) stays.
-- New: riesz_extension_isModeBOp' (W = Factorisable) added here.
--
-- ## Import chain
-- Factorisation.lean → ModeB.lean → ModeA.lean → Wrapping, Reference, Identity
-- → VR.Audit.HahnBanach (for the Riesz concrete instance)
--
-- ## Axiom profile overview
--   Factorisable                          []
--   operand_determines_operational        []
--   factorisable_implies_isModeBOp        []
--   IsModeBOp_of_factorisable             []
--   Factorisable.lift                     []
--   Factorisable.lift_val                 []
--   (riesz_extension_factorisable, riesz_extension_isModeBOp' — in VRClassical/Apparatus/Factorisation.lean)

import VR.Apparatus.ModeB

namespace VR.Apparatus

-- ============================================================
-- §1. Factorisable — the operand-not-operation witness
-- ============================================================

/-- `Factorisable PA PB f a`: there exists an operational function g : A → B
that (1) preserves PB on all PA-elements, and (2) agrees with f on operand a.

This formalises the «operand-not-operation» insight:
operationality of the result f a is determined by the operand a (via g),
not by whether f is globally operational.

**Design decisions**:
- `f a = g a` (not `∀ x, f x = g x`): operand-specific, not global.
  This is the structural content of «operand determines operationality»:
  only the behaviour of f at the specific operand a matters.
- `∀ x : A, PA x → PB (g x)`: g is operational on all PA-elements.
  The witness g must be a globally operational function, not just locally.
- g unrestricted: g may equal f (self-witness) or differ structurally.
  Self-witnessing (g = f) is valid and common when f is already globally
  Mode B — in that case f witnesses its own Factorisability at every operand.

**Typing**: `Factorisable PA PB f : A → Prop` — a predicate on A.
This fits exactly as W : A → Prop in IsModeBOp PA PB W f.

**Relationship to IsModeBOp**:
- `W := Factorisable PA PB f` gives IsModeBOp via IsModeBOp_of_factorisable.
- Any W implying Factorisable gives IsModeBOp via factorisable_implies_isModeBOp.
- See §3 for both connections.

## Axiom profile: [] -/
def Factorisable {A B : Type _} (PA : A → Prop) (PB : B → Prop)
    (f : A → B) (a : A) : Prop :=
  ∃ g : A → B, (∀ x : A, PA x → PB (g x)) ∧ f a = g a

-- ============================================================
-- §2. operand_determines_operational — the core theorem
-- ============================================================

/-- If f factorises through an operational function g on operand a,
and a is PA-operational, then f a is PB-operational.

**Statement**: `PA a → Factorisable PA PB f a → PB (f a)`.

**Productive triviality** (cf. Mode A modeA_liftFn in ModeA.lean):
The proof is 3 lines — obtain g, rewrite f a = g a, apply g's preservation.
Simplicity is the content: operand structure routes operationality through f.

**Why this matters** (the operand-not-operation principle):
- f itself need not be globally operational.
- The existence of any g that agrees with f at a and is globally operational
  is sufficient to conclude PB (f a).
- Mode B generalises Mode A: Mode A says «f preserves P»;
  Mode B (via Factorisable) says «f locally agrees with some function that does».

**Proof sketch**:
  obtain ⟨g, hg_preserves, hfa_eq⟩ := hfact   -- extract the Factorisable witness
  rw [hfa_eq]                                   -- replace f a with g a
  exact hg_preserves a ha                        -- g is operational at a

## Axiom profile: [] -/
theorem operand_determines_operational {A B : Type _}
    {PA : A → Prop} {PB : B → Prop}
    (f : A → B) (a : A) (ha : PA a)
    (hfact : Factorisable PA PB f a) : PB (f a) := by
  obtain ⟨g, hg_preserves, hfa_eq⟩ := hfact
  rw [hfa_eq]
  exact hg_preserves a ha

-- ============================================================
-- §3. Connection to IsModeBOp — spectrum of witnesses
-- ============================================================

/-- Any witness W implying Factorisable PA PB f makes f a Mode B operation.

**General form**: if W a → Factorisable PA PB f a for all a, then
`IsModeBOp PA PB W f` holds — W is a sufficient Mode B witness.

**Consequence — spectrum of witnesses**:
- W = fun _ => True: need W a → Factorisable PA PB f a, i.e., a separate
  argument that f is Factorisable (like riesz_extension_factorisable).
- W = Factorisable PA PB f: hw = id, gives IsModeBOp_of_factorisable.
- W = any stronger condition: hw forgets extra structure.

**Usage pattern**: provide a function hw : ∀ a, W a → Factorisable PA PB f a
to transport any witness into the Factorisable framework.

## Axiom profile: [] -/
theorem factorisable_implies_isModeBOp {A B : Type _}
    {PA : A → Prop} {PB : B → Prop} {f : A → B} {W : A → Prop}
    (hw : ∀ a : A, W a → Factorisable PA PB f a) :
    IsModeBOp PA PB W f :=
  fun a ha hwa => operand_determines_operational f a ha (hw a hwa)

/-- W = Factorisable PA PB f is itself a sufficient Mode B witness for f.

**Self-applying case**: factorisable_implies_isModeBOp with hw = id.
When W = Factorisable PA PB f, the witness IS the Factorisable certificate itself.

**Position in witness spectrum**:
- IsModeBOp_of_factorisable uses W = Factorisable (canonical, informative).
- riesz_extension_isModeBOp (ModeB.lean) uses W = True (minimal).
Both are valid; the spectrum is a feature of the apparatus, not a defect.

**Not uniqueness**: Factorisable is canonical in the sense of being the
structurally minimal explanation of why Mode B holds, but it is not the
only valid witness. The apparatus admits all W implying Factorisable.

## Axiom profile: [] -/
theorem IsModeBOp_of_factorisable {A B : Type _}
    {PA : A → Prop} {PB : B → Prop} {f : A → B} :
    IsModeBOp PA PB (Factorisable PA PB f) f :=
  factorisable_implies_isModeBOp (fun _ hfact => hfact)

-- ============================================================
-- §4. Factorisable.lift — end-to-end machinery with canonical witness
-- ============================================================

/-- Factorisable lift: extract an operational output from an operand that
carries both PA-operationality and a Factorisable certificate.

This is `IsModeBOp.lift` instantiated at `IsModeBOp_of_factorisable`.
It demonstrates the full Mode B pipeline with canonical witness W = Factorisable.

**Parallel structure across modes**:
  Mode A:               {a : A // PA a}                   → {b : B // PB b}
  Mode B (W = True):    {a : A // PA a ∧ True}            → {b : B // PB b}
  Mode B (Factorise):   {a : A // PA a ∧ Factorisable PA PB f a} → {b : B // PB b}

The Factorisable lift is strictly more general than Mode A (requires operand
certificate) and strictly more structured than W = True (names the structural reason).

## Axiom profile: [] -/
def Factorisable.lift {A B : Type _} {PA : A → Prop} {PB : B → Prop} {f : A → B} :
    {a : A // PA a ∧ Factorisable PA PB f a} → {b : B // PB b} :=
  IsModeBOp_of_factorisable.lift

/-- Computation rule: (Factorisable.lift a).val = f a.val.

**Proof**: rfl — unfolds through IsModeBOp.lift (itself definitional via Subtype.mk).
**@[simp]**: reduces `.val` of a Factorisable-lifted application. Loop-safe.

## Axiom profile: [] -/
@[simp]
theorem Factorisable.lift_val {A B : Type _} {PA : A → Prop} {PB : B → Prop} {f : A → B}
    (a : {a : A // PA a ∧ Factorisable PA PB f a}) :
    (Factorisable.lift (f := f) a).val = f a.val :=
  rfl

-- ============================================================
-- Axiom audit — v1.0.0 Stage 4, Factorisation.lean
-- ============================================================
-- STAGE: v1.0.0 Stage 4. SOURCE: PLAN.md Stage 4.
-- LEAN OBJECTS (8 public objects):
--   Factorisable                          (def, Prop)
--   operand_determines_operational        (theorem)
--   factorisable_implies_isModeBOp        (theorem)
--   IsModeBOp_of_factorisable             (theorem)
--   Factorisable.lift                     (def)
--   Factorisable.lift_val     @[simp]     (theorem, rfl)
--   riesz_extension_factorisable          (theorem, Riesz concrete)
--   riesz_extension_isModeBOp'            (theorem, Riesz concrete)
-- AXIOM AUDIT:
--   infrastructure []: Factorisable, operand_determines_operational,
--     factorisable_implies_isModeBOp, IsModeBOp_of_factorisable,
--     Factorisable.lift, Factorisable.lift_val.
--   standard ceiling [P,C,Q]: riesz_extension_factorisable,
--     riesz_extension_isModeBOp'.
-- CHECKS: no sorry, no admit.

#print axioms Factorisable
#print axioms operand_determines_operational
#print axioms factorisable_implies_isModeBOp
#print axioms IsModeBOp_of_factorisable
#print axioms Factorisable.lift
#print axioms Factorisable.lift_val

end VR.Apparatus
