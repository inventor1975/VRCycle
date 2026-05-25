-- VR-Apparatus: Separability (v1.0.0, Stage 6)
-- HasSeparabilityStructure — Tier 2 domain structure for analysis apparatus.
--
-- STAGE: v1.0.0 Stage 6 (second of six pieces). SOURCE: PLAN.md Stage 6.
--
-- ## Position statement
-- Introduces `HasSeparabilityStructure T`: a minimal typeclass capturing separability
-- as a Tier 2 domain structure in the apparatus layered architecture.
--
-- **Architectural decomposition of OperationalHilbertSpace** (Stage 6 finding):
-- OperationalHilbertSpace E has three fields:
--   (1) denseSeq : ℕ → E              \
--   (2) denseSeq_dense : DenseRange     }  = HasSeparabilityStructure E  (Tier 2)
--   (3) inner_computable               }  = apparatus-specific content   (Tier 1)
-- Stage 6 separates fields (1)–(2) into HasSeparabilityStructure. The Hilbert
-- class is NOT refactored — the decomposition is established via an instance (§2).
-- This makes the layered architecture from CLAUDE.md explicit in Lean.
--
-- **Scope boundary**: HasSeparabilityStructure requires [TopologicalSpace T].
-- Analysis types (ℝ, Hilbert spaces): HasSeparabilityStructure ✓
-- Reference semantics (OSet, OSetZFA, ZFSet): HasSeparabilityStructure ✗
-- See §3 for the full boundary discussion.
--
-- **Connection to Stage 4 (Factorisable)**:
-- `separability_provides_factorisable` (§4) bridges the two stages:
-- HasSeparabilityStructure names the evaluation points at which Factorisable holds.
-- Without HasSeparabilityStructure, these points have no canonical apparatus name.
--
-- **Critical finding — two levels of Factorisable** (§5):
-- Stage 4: Factorisable at OPERAND LEVEL (functional f as operand of riesz_extension_map)
-- Stage 6: Factorisable at EVALUATION-POINT LEVEL (denseSeq n as operand of extended map)
-- Mode B admits recursive application of Factorisable at multiple architectural levels.
--
-- ## Axiom profile overview
--   HasSeparabilityStructure               []
--   instHasSepStructOfOpHilbert            [propext, Classical.choice, Quot.sound]
--   separability_provides_factorisable     []

import VRCycle.Apparatus.Factorisation

namespace VR.Apparatus

-- ============================================================
-- §1. HasSeparabilityStructure — the Tier 2 domain structure
-- ============================================================

/-- `HasSeparabilityStructure T`: topological type T carries an explicit separable structure.

A separable structure consists of:
  1. `denseSeq : ℕ → T` — an explicit dense sequence (separability witness).
  2. `denseSeq_dense : DenseRange denseSeq` — its range is dense in T.

**Architectural role — Tier 2 domain structure**:
HasSeparabilityStructure sits above Tier 1 apparatus instances (PredicateOperationality,
ReferenceOperationality) as a domain prerequisite. Analysis apparatus instances
(OperationalHilbertSpace) use separability implicitly; Stage 6 makes it explicit.

The Tier 2 concept is: «what does T need to provide for analysis Mode B to work?»
Answer: a dense sequence with named points. HasSeparabilityStructure encodes this
precisely, without bundling apparatus-specific content (inner products, norms, etc.).

**Minimal**: exactly two fields — the minimum separability content for the apparatus
bridge (§4). No algebraic or metric structure is bundled here. This is intentional:
separability is a topological concept, independent of the apparatus content.

**`[TopologicalSpace T]` as class argument, not `extends`**:
`DenseRange denseSeq` requires a topology on T. Using `[TopologicalSpace T]` as a
class argument (not `extends`) avoids diamond problems with mathlib's topology
hierarchy. Standard mathlib pattern for topology-dependent classes.

**Scope boundary** (§3): analysis types with TopologicalSpace instances qualify.
Reference semantics apparatus (OSet, OSetZFA, ZFSet) is NOT in scope.

**Connection to Factorisable** (Stage 4):
`separability_provides_factorisable` (§4) uses `HasSeparabilityStructure.denseSeq`
to name the evaluation points at which Factorisable holds. The dense sequence bridges
separability (Tier 2 domain structure) and Mode B (apparatus transit mechanism).

## Axiom profile: [] (pure Prop class, two fields, no axioms introduced) -/
class HasSeparabilityStructure (T : Type*) [TopologicalSpace T] where
  /-- An explicit dense sequence in T (separability witness). -/
  denseSeq : ℕ → T
  /-- The dense sequence has dense range: closure (range denseSeq) = univ.
  This is what makes `denseSeq` a genuine separability witness — without this,
  any sequence would qualify. The density property is required for mathematical
  honesty, even though `separability_provides_factorisable` (§4) uses only the
  sequence, not this property, in its proof. -/
  denseSeq_dense : DenseRange denseSeq

-- ============================================================
-- §2. Instance: OperationalHilbertSpace E → HasSeparabilityStructure E
-- ============================================================

/-- Every operational Hilbert space has a separability structure.

**Architectural decomposition of OperationalHilbertSpace** (Stage 6 headline finding):
The three fields of OperationalHilbertSpace E split along Tier 2 / Tier 1 lines:

  Tier 2 (domain structure = HasSeparabilityStructure):
    denseSeq : ℕ → E              — explicit dense sequence
    denseSeq_dense : DenseRange   — density of that sequence

  Tier 1 apparatus-specific content:
    inner_computable              — InnerProductSpace-dependent operational content

This instance makes the decomposition Lean-visible:
  OperationalHilbertSpace E = HasSeparabilityStructure E + inner_computable.

**No refactoring of OperationalHilbertSpace**: v0.1.0 VR-Audit code is untouched.
The decomposition is established via this instance, not by modifying the class.
Both the old class and the new Tier 2 view coexist — another spectrum phenomenon.

**Consequence**: for any `[OperationalHilbertSpace E]`, `instHasSepStructOfOpHilbert`
synthesizes `[HasSeparabilityStructure E]` automatically, with
`HasSeparabilityStructure.denseSeq (T := E) = OperationalHilbertSpace.denseSeq`.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from [OperationalHilbertSpace E] (instOperationalHilbertSpaceReal for ℝ,
  etc.). OperationalHilbertSpace.denseSeq_dense uses classical density proofs. -/
instance instHasSepStructOfOpHilbert {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E] :
    HasSeparabilityStructure E where
  denseSeq := VR.Audit.OperationalHilbertSpace.denseSeq
  denseSeq_dense := VR.Audit.OperationalHilbertSpace.denseSeq_dense

-- Verification: ℝ automatically has HasSeparabilityStructure via instance synthesis.
-- instOperationalHilbertSpaceReal → instHasSepStructOfOpHilbert → HasSeparabilityStructure ℝ.
-- No explicit instHasSepStructReal needed — automatic.
noncomputable example : HasSeparabilityStructure ℝ := inferInstance

-- The denseSeq for ℝ (from HasSeparabilityStructure) is the rational enumeration
-- from instOperationalHilbertSpaceReal. Computation rule holds by rfl:
-- HasSeparabilityStructure.denseSeq (T := ℝ) n
--   = instHasSepStructOfOpHilbert.denseSeq n
--   = OperationalHilbertSpace.denseSeq (E := ℝ) n
--   = (Denumerable.ofNat ℚ n : ℝ)   [by instOperationalHilbertSpaceReal.denseSeq def]
example (n : ℕ) :
    HasSeparabilityStructure.denseSeq (T := ℝ) n = (Denumerable.ofNat ℚ n : ℝ) := rfl

-- ============================================================
-- §3. Scope boundary — explicit architectural constraint
-- ============================================================
--
-- ## HasSeparabilityStructure is analysis-only: the honest boundary
--
-- **Analysis types: HasSeparabilityStructure ✓**
--   ℝ, Hilbert spaces, L², ℓ² — normed spaces with DenseRange for a rational sequence.
--   Any [OperationalHilbertSpace E] gives HasSeparabilityStructure E via §2.
--
-- **Reference semantics apparatus: HasSeparabilityStructure ✗**
--   OSet = ZFSet = Quotient PSet.setoid:
--     Has a discrete TopologicalSpace instance in mathlib.
--     But the apparatus-relevant dense sequence concept does not apply in the
--     analysis sense: discrete topology on ZFSet has no non-trivial dense sequences
--     (every singleton is closed in discrete topology).
--   OSetZFA = Quotient CoPSet.instSetoid: same observation.
--   Reference semantics Mode B uses different witnesses (predicate structure,
--   not dense sequences). Forcing HasSeparabilityStructure here would be dishonest.
--
-- **Generic T without canonical topology: HasSeparabilityStructure ✗**
--   If T has no [TopologicalSpace T] instance, HasSeparabilityStructure T
--   cannot be stated (DenseRange is undefined). This is correct behavior.
--
-- ## Architectural message: apparatus boundaries are domain-specific
--
-- Tier 2 domain structures are NOT universal:
--   HasSeparabilityStructure: for analysis apparatus (predicate-wrapping over ℝ, E).
--   Reference semantics: no separability Tier 2 — witnesses are structural (setoid-based).
--   Future: arithmetic Tier 2 (computability witnesses for number theory) — distinct.
--
-- This modularity is a FEATURE, not a limitation. The apparatus framework does not
-- impose a single Tier 2 on all domains. Each domain contributes its own Tier 2
-- structures when relevant. Mode B witnesses remain domain-specific.
--
-- ## Preprint content (scope boundary observation)
-- The honest boundary between HasSeparabilityStructure and reference semantics
-- demonstrates that the apparatus framework is modular: one may add or omit Tier 2
-- structures independently of Tier 1. This is the architectural flexibility
-- of the «layered» design — the tiers are independent. ∎

-- ============================================================
-- §4. Bridge theorem: separability provides Factorisable evaluation points
-- ============================================================

/-- Given a HasSeparabilityStructure, if f and g agree on all dense sequence points
and g is globally operational, then f is Factorisable at each dense sequence point.

**Statement**:
  [HasSeparabilityStructure T]
  + hg_op   : ∀ x : T, PA x → PB (g x)          (g globally operational)
  + hg_agree: ∀ n : ℕ, f (denseSeq n) = g (denseSeq n)  (agreement at dense points)
  → Factorisable PA PB f (denseSeq n)              (for each specific n)

**Role of HasSeparabilityStructure**:
The dense sequence `denseSeq : ℕ → T` provides the canonical evaluation points at
which Factorisable holds. Without HasSeparabilityStructure, these points would have
no canonical name in the apparatus framework — the caller would need to provide them
as explicit arguments. HasSeparabilityStructure makes the evaluation-point structure
a typeclass, automatically available for any separable T.

**Role of denseSeq_dense** (not used in proof):
`DenseRange denseSeq` is a field of HasSeparabilityStructure but is NOT used in
this proof. Its role is mathematical: it ensures `denseSeq` is a genuine separability
witness, not an arbitrary sequence. The Factorisable derivation is about specific
points (not density), but the class requires density for mathematical honesty.

**Productive triviality** — fourth instance in the apparatus:
  modeA_liftFn (ModeA.lean):                Mode A lifting is free.
  operand_determines_operational:            Operand structure routes through.
  IsModeBOp_of_factorisable:                Factorisable implies Mode B.
  separability_provides_factorisable (here): Separability names evaluation points.
Each proof is minimal; the content is in the conceptual identification.

**Two-level Factorisable position**:
This theorem operates at EVALUATION-POINT level (Level B, §5):
  - T plays the role of the OPERAND TYPE at evaluation-point level.
  - denseSeq n is the SPECIFIC OPERAND (evaluation point).
  - f is the OPERATION applied to evaluation points.
Compare to Stage 4's Level A: A = OperationalNormableFunctional E M,
  riesz_extension_map is the OPERATION, functional f is the OPERAND.
Same concept (Factorisable), different architectural level.

## Axiom profile: []
  Pure propositional logic: the proof is ⟨g, hg_op, hg_agree n⟩.
  No analysis, no Classical.choice, no propext. -/
theorem separability_provides_factorisable {T B : Type*}
    [TopologicalSpace T] [HasSeparabilityStructure T]
    {PA : T → Prop} {PB : B → Prop}
    {f g : T → B}
    (hg_op : ∀ x : T, PA x → PB (g x))
    (hg_agree : ∀ n : ℕ,
      f (HasSeparabilityStructure.denseSeq n) = g (HasSeparabilityStructure.denseSeq n))
    (n : ℕ) :
    Factorisable PA PB f (HasSeparabilityStructure.denseSeq n) :=
  ⟨g, hg_op, hg_agree n⟩

-- ============================================================
-- §5. Two levels of Factorisable — headline finding Stage 6
-- ============================================================
--
-- ## Finding S6-A: Mode B admits Factorisable at multiple architectural levels
--
-- Stage 4 established Factorisable at the OPERAND LEVEL (Level A, riesz case).
-- Stage 6 reveals Factorisable at the EVALUATION-POINT LEVEL (Level B, general).
-- These are distinct applications of the SAME Factorisable concept at different tiers.
--
-- ── Level A: Operand level (Stage 4, riesz_extension_factorisable) ────────────
--
--   Setting:
--     A = OperationalNormableFunctional E M  (operand type = functional space)
--     B = E →L[ℝ] ℝ                         (result type = classical CLMs)
--     f = riesz_extension_map : A → B        (the MODE B OPERATION)
--     a = some functional in A               (the OPERAND = the functional itself)
--
--   Statement: Factorisable (PA := fun _ => True) riesz_PB riesz_extension_map (a : A)
--
--   Witness g = riesz_extension_map (self-witnessing):
--     (1) ∀ x : A, True → riesz_PB (riesz_extension_map x) [from HahnBanachOperational_Hilbert]
--     (2) riesz_extension_map a = riesz_extension_map a     [rfl]
--
--   Content: «Is riesz_extension_map a Mode B operation?» — YES, because it is
--   globally operational (self-witnesses Factorisable at every functional operand).
--
-- ── Level B: Evaluation-point level (Stage 6, general principle) ─────────────
--
--   Setting:
--     T = E (ambient Hilbert space, with HasSeparabilityStructure E)
--     B = ℝ (real numbers)
--     For a FIXED functional f₀ : OperationalNormableFunctional E M:
--     f = fun e => riesz_extension_map f₀ e : E → ℝ   (view extended CLM as function of e)
--     a = denseSeq n : E                                (OPERAND = evaluation point in E)
--
--   Statement:
--     Factorisable (PA := fun _ => True) IsComputableReal
--       (fun e => riesz_extension_map f₀ e) (HasSeparabilityStructure.denseSeq n)
--
--   Natural witness g = fun e => f₀.toFun (M.toSubmodule.orthogonalProjection e):
--     (1) ∀ e : E, True → IsComputableReal (f₀.toFun (P_M e))
--         [from fn_computable_everywhere f₀ (P_M e), since P_M e : M.toSubmodule]
--     (2) riesz_extension_map f₀ (denseSeq n) = f₀.toFun (P_M (denseSeq n))
--         [by hchain from HahnBanach.lean §II Part 1:
--           riesz_extension_map f₀ (denseSeq n)
--           = ⟨ξ, denseSeq n⟩_E                    [by definition of innerSL ℝ ξ]
--           = ⟨ξ, P_M(denseSeq n)⟩_K               [inner_orthogonalProjection_eq_of_mem_left]
--           = f₀.toFun (P_M(denseSeq n))            [Riesz property hξ]
--         ]
--
--   Content: «Is riesz_extension_map f₀ operational at evaluation point denseSeq n?» — YES,
--   because the projection witness g routes operationality through orthogonal projection.
--
--   Level B Lean proof status — DEFERRED:
--   Proving hchain outside HahnBanach.lean requires significant inner product computation
--   (re-deriving the orthogonal projection identity). The architectural observation is
--   complete and the general theorem (separability_provides_factorisable) states the
--   principle. Full Level B Riesz formalisation is future work.
--
-- ── Architectural distinction ─────────────────────────────────────────────────
--
--   Level A: Factorisable at the INPUT DOMAIN of the Mode B operation.
--            Captures: «why is this operation Mode B?»
--            Answer: it self-witnesses via Factorisable at every functional operand.
--
--   Level B: Factorisable at the EVALUATION POINTS of the MODE B RESULT.
--            Captures: «why is the result operational at specific points?»
--            Answer: orthogonal projection routes operationality to the dense sequence.
--
--   Both levels correspond to legitimate apparatus questions.
--   HasSeparabilityStructure (this stage) enables Level B:
--   it names the evaluation points (denseSeq n ∈ E) where Factorisable holds.
--
-- ── Structural richness of Mode B ────────────────────────────────────────────
--
--   Mode B via Factorisable applies at multiple architectural levels without
--   requiring a meta-framework. The apparatus is SELF-REFERENTIAL at two levels:
--
--   Level A: Factorisable at the apparatus INSTANCE boundary (functional ↔ CLM).
--   Level B: Factorisable at the DOMAIN STRUCTURE boundary (HasSeparabilityStructure).
--
--   The same concept (Factorisable) handles both levels. This is STRUCTURAL RICHNESS,
--   not redundancy: each level addresses a different apparatus question, with the
--   same answer (∃ g, global-operational ∧ local-agreement).
--
-- ── Consequence for preprint ─────────────────────────────────────────────────
--
--   Section on Mode B in the preprint should note:
--   (a) Factorisable is parametric over the «operand type» — it applies to any Type*.
--   (b) In the Riesz case, the operand type can be chosen at Level A (functional space)
--       or Level B (ambient Hilbert space). The two choices yield different apparatus
--       questions and different witnesses, but the same formal Factorisable structure.
--   (c) HasSeparabilityStructure enables Level B by providing canonical operands
--       (denseSeq n). Without Tier 2, Level B has no canonical operand.
--   This is the «recursive» application of Mode B, now documented formally.

-- ============================================================
-- Axiom audit — v1.0.0 Stage 6, Separability.lean
-- ============================================================
-- STAGE: v1.0.0 Stage 6. SOURCE: PLAN.md Stage 6.
-- LEAN OBJECTS (3 public objects):
--   HasSeparabilityStructure               (class, Prop, 2 fields)
--   instHasSepStructOfOpHilbert            (instance)
--   separability_provides_factorisable     (theorem, bridge, axiom-free)
-- AXIOM AUDIT:
--   HasSeparabilityStructure:              []
--   instHasSepStructOfOpHilbert:           [propext, Classical.choice, Quot.sound]
--   separability_provides_factorisable:    []
-- CHECKS: no sorry, no admit.

#print axioms HasSeparabilityStructure
#print axioms instHasSepStructOfOpHilbert
#print axioms separability_provides_factorisable

end VR.Apparatus
