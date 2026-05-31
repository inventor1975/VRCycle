-- VR-Audit: Hilbert.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 2: OperationalHilbertSpace typeclass.
--
-- STAGE: 2 (of 7). SOURCE: PLAN.md Stage 2; CLAUDE.md wrapping principle.
--         Follows VRCycle.Audit.Computable (Stage 1).
--
-- ## Position statement
-- Stage 2 of VR-Audit cycle. Defines `OperationalHilbertSpace` typeclass —
-- the central architectural construct of the cycle from which all subsequent
-- stages (Stages 3–7) are built.
--
-- ## Wrapping principle in action
-- Per CLAUDE.md, this is wrapping over mathlib's classical
-- `InnerProductSpace ℝ E`. No new type of "computable Hilbert space" is
-- introduced. Instead, three operational restrictions are layered on top of
-- mathlib's existing `InnerProductSpace ℝ E`:
--
--   (a) an explicit dense sequence (separability witness),
--   (b) classical density of its range (`DenseRange`),
--   (c) `IsComputableReal` predicates on inner products of dense sequence pairs.
--
-- Formal register   = mathlib's `InnerProductSpace ℝ E` (unrestricted).
-- Operational register = `OperationalHilbertSpace E` (three added fields).
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- ## Why exactly three fields
-- Three fields are the minimum sufficient for Stage 5 (Hahn-Banach via Riesz):
--
-- * `denseSeq` and `denseSeq_dense`: a computable separable structure is
--   needed to name the vectors that appear in the Riesz representation
--   witness.  The classical approximation property (any element is a limit
--   of the sequence) does not add an operational field here; it follows from
--   density + completeness.
--
-- * `inner_computable`: needed to verify that the Riesz image of an
--   operational functional is again operational (Stage 5 transit).
--
-- DOES NOT include:
-- * Pointwise computability of `denseSeq` elements themselves — not required
--   for the main theorem; only computability of pairwise inner products is
--   needed. (If needed in a future stage, it can be added then.)
-- * Completeness modulus — classical `CompleteSpace E` from mathlib suffices.
--   Operational outputs are obtained via locatedness (Stage 3), not via an
--   explicit completeness witness. Per the wrapping principle (CLAUDE.md),
--   we do not replace classical `CompleteSpace` with a constructive version.
--
-- ## Methodological Observation 2
-- (informs eventual preprint §VI-equivalent)
--
-- The field `inner_computable : ∀ m n, IsComputableReal (@inner ℝ E _ (denseSeq m) (denseSeq n))`
-- is the precise embodiment of the wrapping principle at the Hilbert space level:
-- we do not define a new "computable inner product" type; we **select**, from
-- the classical `@inner ℝ E _` values provided by mathlib's `InnerProductSpace ℝ E`,
-- those pairs for which the result is computable. The operational register
-- (inner products of basis elements) lives **inside** the formal register
-- (full classical `InnerProductSpace ℝ E`). This is a working pattern for
-- VR-Audit: any classical structure with values in ℝ can be wrapped
-- operationally by adding `IsComputableReal` predicates on selected outputs.
--
-- ## Connection to Stage 3+
-- Stage 3 will introduce `OperationalLocatedSubspace E [OperationalHilbertSpace E]`,
-- capturing the operational analogue of closed subspace (locatedness replaces
-- classical closedness). Stage 5 invokes `InnerProductSpace.toDual` (Riesz
-- representation) over `OperationalHilbertSpace E` to obtain the operational
-- Hahn-Banach extension.
--
-- ## Lean 4 notation workaround
-- The notation `⟪·, ·⟫_ℝ` (from `open scoped RealInnerProductSpace`) does
-- NOT parse inside `class where` field type declarations. The subscript `_ℝ`
-- is misinterpreted by the parser. Workaround: use `@inner ℝ E _` explicitly
-- in field types. The notation can still be used freely outside class blocks
-- (proofs, theorems, etc.).
--
-- ## What this file does
-- DEFINES:
--   class OperationalHilbertSpace (E : Type*) ... where ...
-- PROVES (canonical instance):
--   instOperationalHilbertSpaceReal : OperationalHilbertSpace ℝ
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound]
-- Classical.choice enters via mathlib's ℝ (Cauchy completeness).
-- This is the expected and acceptable ceiling for the entire VR-Audit cycle.

import VRCycle.Audit.Computable
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

namespace VR.Audit

-- ============================================================
-- §I. OperationalHilbertSpace typeclass
-- ============================================================

/-- `OperationalHilbertSpace E`: operational Hilbert space structure on `E`.

An operational Hilbert space is a classical Hilbert space `E` (meaning
`InnerProductSpace ℝ E` and `CompleteSpace E` from mathlib) equipped with
three additional operational fields that make it "computable":

1. `denseSeq : ℕ → E` — an explicit dense sequence (separability witness).
2. `denseSeq_dense : DenseRange denseSeq` — its range is dense in `E`.
3. `inner_computable : ∀ m n, IsComputableReal (⟨denseSeq m, denseSeq n⟩)` —
   the inner products of dense sequence elements are computable reals.

## Design choices

- **Class, not Structure**: we need typeclass synthesis for multiple types
  (ℝ, ℓ², L²(μ), ...) in later stages. Using `class` allows automatic
  instance resolution: `[OperationalHilbertSpace E]` in Stage 3+.

- **`[InnerProductSpace ℝ E]` as implicit argument, not `extends`**:
  avoids duplication issues with mathlib's own hierarchy. The classical
  inner product structure is a prerequisite, not a component of the class.

- **No completeness modulus field**: classical `[CompleteSpace E]` suffices
  per the wrapping principle. Operational content comes from `inner_computable`
  and locatedness (Stage 3), not from explicit completeness witnesses.

- **No pointwise computability of `denseSeq k`**: not required for Stage 5;
  only pairwise inner products need to be computable.

## Lean 4 workaround: `@inner ℝ E _` in field types
The notation `⟪·, ·⟫_ℝ` does NOT parse inside `class where` blocks.
The subscript `_ℝ` is misinterpreted by the Lean 4 parser ("Invalid field:
Type expected"). Use `@inner ℝ E _` (explicit arguments) in field type
declarations. The notation works normally outside class blocks.

## Source
Wrapping principle: CLAUDE.md. Operational Hilbert spaces: Pour-El &
Richards 1989, §2.1 (computable Banach spaces); adapted here to Hilbert
setting via `InnerProductSpace.toDual` (Riesz representation).

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
class OperationalHilbertSpace (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- An explicit computable dense sequence in `E` (separability witness). -/
  denseSeq : ℕ → E
  /-- The dense sequence has dense range: `closure (range denseSeq) = univ`. -/
  denseSeq_dense : DenseRange denseSeq
  /-- Inner products of dense sequence pairs are computable reals.
  Note: `@inner ℝ E _` is used explicitly (not `⟪·, ·⟫_ℝ`) because
  the `⟪·, ·⟫_ℝ` notation does not parse inside `class where` blocks
  in Lean 4 — see file-level comment §Lean 4 workaround. -/
  inner_computable : ∀ m n : ℕ,
    IsComputableReal (@inner ℝ E _ (denseSeq m) (denseSeq n))

-- ============================================================
-- §II. Canonical ℝ instance
-- ============================================================

/-- `ℝ` is an operational Hilbert space (1-dimensional case).

## Dense sequence
Rationals enumerated by `Denumerable.ofNat ℚ : ℕ → ℚ`, cast to ℝ.
This is surjective onto ℚ (via `(Denumerable.eqv ℚ).symm.surjective`)
and ℚ is dense in ℝ (via `Rat.denseRange_cast`).

## DenseRange proof
`DenseRange.comp` composes dense ranges:
  `Rat.denseRange_cast : DenseRange (Rat.cast : ℚ → ℝ)`
  `(Denumerable.eqv ℚ).symm.surjective.denseRange : DenseRange (Denumerable.ofNat ℚ)`
  `Rat.continuous_coe_real : Continuous (Rat.cast : ℚ → ℝ)`

## Inner product proof
On ℝ, the canonical inner product satisfies:
  `@inner ℝ ℝ _ x y = y * starRingEnd ℝ x = y * x`
  [by `RCLike.inner_apply`; `starRingEnd ℝ = id` by default simp]
  `= x * y` [by `mul_comm`]

For rational casts: `(q : ℝ) * (r : ℝ) = ((q * r : ℚ) : ℝ)` by `push_cast; ring`,
then `IsComputableReal_rat` closes the goal.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
noncomputable instance instOperationalHilbertSpaceReal : OperationalHilbertSpace ℝ where
  denseSeq := fun n => (Denumerable.ofNat ℚ n : ℝ)
  denseSeq_dense :=
    -- Rat.denseRange_cast.comp : DenseRange g → DenseRange f → Continuous g →
    --                             DenseRange (g ∘ f)
    -- g = Rat.cast : ℚ → ℝ,  f = Denumerable.ofNat ℚ : ℕ → ℚ
    Rat.denseRange_cast.comp
      (Denumerable.eqv ℚ).symm.surjective.denseRange
      Rat.continuous_coe_real
  inner_computable := fun m n => by
    -- Step 1: @inner ℝ ℝ _ (q : ℝ) (r : ℝ) = (r : ℝ) * starRingEnd ℝ (q : ℝ)
    --         by RCLike.inner_apply (which is rfl for RCLike.innerProductSpace)
    -- Step 2: = (r : ℝ) * (q : ℝ)   [starRingEnd ℝ = id, by default simp]
    -- Step 3: = ((r * q : ℚ) : ℝ)   [by push_cast; ring]
    -- Step 4: IsComputableReal ((r * q : ℚ) : ℝ)   [by IsComputableReal_rat]
    have heq : @inner ℝ ℝ _ (Denumerable.ofNat ℚ m : ℝ) (Denumerable.ofNat ℚ n : ℝ) =
               ((Denumerable.ofNat ℚ n * Denumerable.ofNat ℚ m : ℚ) : ℝ) :=
      calc @inner ℝ ℝ _ (Denumerable.ofNat ℚ m : ℝ) (Denumerable.ofNat ℚ n : ℝ)
            -- RCLike.inner_apply: @inner ℝ ℝ _ x y = y * starRingEnd ℝ x
            = (Denumerable.ofNat ℚ n : ℝ) * starRingEnd ℝ (Denumerable.ofNat ℚ m : ℝ) :=
                RCLike.inner_apply _ _
            -- starRingEnd ℝ = id (default simp; in ℝ, star = id)
          _ = (Denumerable.ofNat ℚ n : ℝ) * (Denumerable.ofNat ℚ m : ℝ) := by simp
            -- rational casts compose: (r : ℝ) * (q : ℝ) = ((r * q : ℚ) : ℝ)
          _ = ((Denumerable.ofNat ℚ n * Denumerable.ofNat ℚ m : ℚ) : ℝ) := by push_cast; ring
    rw [heq]
    exact IsComputableReal_rat _

-- ============================================================
-- Axiom audit — Stage 2
-- ============================================================
-- STAGE: 2. SOURCE: PLAN.md Stage 2; CLAUDE.md wrapping principle.
-- LEAN OBJECTS (2 public):
--   class: OperationalHilbertSpace
--   instance: instOperationalHilbertSpaceReal
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound] for all.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms OperationalHilbertSpace
#print axioms instOperationalHilbertSpaceReal

end VR.Audit
