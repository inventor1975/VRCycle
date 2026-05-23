-- VR-Audit: Subspace.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 3: OperationalLocatedSubspace structure.
--
-- STAGE: 3 (of 7). SOURCE: PLAN.md Stage 3; CLAUDE.md wrapping principle.
--         Follows VRCycle.Audit.Hilbert (Stage 2).
--
-- ## Position statement
-- Stage 3 of VR-Audit cycle. Defines `OperationalLocatedSubspace` — the
-- operational analogue of a closed subspace of a Hilbert space. Replaces
-- classical closedness with locatedness: computable distance from the
-- enclosing dense sequence to the subspace. This is the minimal operational
-- structure needed to make orthogonal projection computable in Stage 5.
--
-- ## Wrapping principle in action
-- Per CLAUDE.md, wrapping over mathlib's `ClosedSubmodule ℝ E`. No new type
-- of "computable closed subspace" is introduced. Instead, three additional
-- operational restrictions are layered on top of `ClosedSubmodule ℝ E`:
--
--   (a) `denseSubSeq : ℕ → E` — an explicit dense sequence within M,
--   (b) `denseSubSeq_dense_in` — its density within M,
--   (c) `dist_computable` — computability of infDist from the enclosing
--       dense sequence to M (locatedness on the ambient denseSeq).
--
-- Formal register   = mathlib's `ClosedSubmodule ℝ E` (unrestricted).
-- Operational register = `OperationalLocatedSubspace E` (three added fields).
--
-- ## Why this formulation of locatedness (Methodological Observation 3)
-- The locatedness predicate `dist_computable` is formulated only over points
-- of `OperationalHilbertSpace.denseSeq`, not over arbitrary `x : E`. This is
-- principled, not opportunistic: operational predicates apply to operational
-- objects (those carrying explicit witnesses), not to arbitrary elements of
-- the enclosing classical structure. Arbitrary `x : E` lives entirely in the
-- formal register; it has no operational tag. Demanding computability on
-- arbitrary points would conflate the registers. This formulation is sufficient
-- for Stage 5 because orthogonal projection in the main theorem is applied
-- precisely to points of `denseSeq`. The pattern — operational predicates only
-- over operational witnesses — generalises to all future VR-Audit work.
--
-- ## Why orthogonal projection comes for free
-- `HasOrthogonalProjection` (the mathlib typeclass for orthogonal projection)
-- is inherited from `ClosedSubmodule` via the instance:
--
--   `instance (K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection`
--
-- Since `OperationalLocatedSubspace` extends `ClosedSubmodule ℝ E`, for any
-- `M : OperationalLocatedSubspace E`, the instance `M.toSubmodule.HasOrthogonalProjection`
-- is resolved by `inferInstance`. No additional field is needed. The operationality
-- of the projection on operational witnesses is established in Stage 5 via locatedness.
--
-- ## Methodological Observation 3 (locatedness formulation)
-- The locatedness predicate `dist_computable` is formulated only over points
-- of `OperationalHilbertSpace.denseSeq`, not over arbitrary `x : E`. This is
-- principled, not opportunistic: operational predicates apply to operational
-- objects (those carrying explicit witnesses), not to arbitrary elements of
-- the enclosing classical structure. Arbitrary `x : E` lives entirely in the
-- formal register; it has no operational tag. Demanding computability on
-- arbitrary points would conflate the registers. This formulation is sufficient
-- for Stage 5 because orthogonal projection in the main theorem is applied
-- precisely to points of `denseSeq`. The pattern — operational predicates only
-- over operational witnesses — generalises to all future VR-Audit work.
--
-- ## Methodological Observation 4 (Specker boundary explicitly avoided)
-- The orthogonal projection construction produces `orthogonalProjection M v`
-- as a single element of M, not as a limit of a bounded monotone computable
-- sequence. The Specker obstruction (1949) applies to the latter, not the
-- former. Our transit through Riesz representation in Stage 5 uses this
-- directly: the Riesz vector x₀ is constructed as a projection, not as a
-- supremum. The locatedness condition (computable infDist on dense sequence
-- points) ensures the projection inherits computability. This is the structural
-- reason why VR-Audit Hahn-Banach-via-Riesz is clean where general Banach
-- Hahn-Banach would not be.
--
-- ## What this file does
-- DEFINES:
--   structure: OperationalLocatedSubspace
-- PROVES (canonical instance):
--   topOperationalLocatedSubspace : OperationalLocatedSubspace ℝ
--     (trivial sanity check: ⊤ subspace = whole space; denseSubSeq = ambient denseSeq)
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound]
-- Inherited from mathlib's ℝ (Cauchy completeness) and ClosedSubmodule.
-- This is the expected and acceptable ceiling for the entire VR-Audit cycle.

import VRCycle.Audit.Hilbert
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

namespace VR.Audit

-- ============================================================
-- §I. OperationalLocatedSubspace structure
-- ============================================================

/-- `OperationalLocatedSubspace E`: operational closed subspace of an operational
Hilbert space `E`.

An operational located subspace is a classical closed submodule
`ClosedSubmodule ℝ E` (from mathlib) equipped with four additional operational
fields that make it "located" and computably separable:

1. `denseSubSeq : ℕ → E` — an explicit dense sequence within M.
2. `denseSubSeq_mem` — all terms lie in the underlying submodule.
3. `denseSubSeq_dense_in` — the sequence is dense within M: every element of M
   is arbitrarily well approximated by some term.
4. `dist_computable` — locatedness: for every element of the ambient dense
   sequence, the infimal distance to M is a computable real.

## Design choices

- **Structure, not Class**: multiple subspaces may live in the same `E`;
  a `structure` bundles data for a specific subspace, whereas `class` is
  for typeclass synthesis over a type. Cf. `OperationalHilbertSpace` (class).

- **`extends ClosedSubmodule ℝ E`**: bundles mathlib's `Submodule ℝ E` and
  `IsClosed` together. Gives `HasOrthogonalProjection` for free via the
  mathlib instance `(K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection`.

- **Locatedness on `denseSeq` only**: `dist_computable` ranges over
  `OperationalHilbertSpace.denseSeq m`, not over arbitrary `x : E`.
  See Methodological Observation 3 (file-level comment): operational predicates
  apply to operational objects. Sufficient for Stage 5.

- **No `HasOrthogonalProjection` field**: inherited automatically from
  `ClosedSubmodule`; see file-level comment §Why orthogonal projection comes
  for free.

## Lean 4 constructor note
`ClosedSubmodule ℝ E` is constructed as `⟨submodule, isClosed_proof⟩`
(anonymous angle-bracket constructor). The named syntax
`{ toSubmodule := ..., toCloseds := ... }` does NOT work: both parent structures
`Submodule R M` and `Closeds M` share the `carrier : Set M` field, and the
`toCloseds` field name conflicts. Use the positional constructor instead.

## Source
Locatedness: Bishop-Bridges 1985 §7 (located subsets); Pour-El & Richards 1989
§4 (computable subspaces). Wrapping principle: CLAUDE.md. Specker boundary:
Specker 1949; see Methodological Observation 4 (file-level comment).

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
structure OperationalLocatedSubspace (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E] extends ClosedSubmodule ℝ E where
  /-- Explicit dense sequence in M (separability witness for the subspace). -/
  denseSubSeq : ℕ → E
  /-- All terms of `denseSubSeq` lie in the underlying submodule. -/
  denseSubSeq_mem : ∀ n, denseSubSeq n ∈ toSubmodule
  /-- `denseSubSeq` is dense within M: every element of M is arbitrarily
  well approximated by some term of `denseSubSeq`. -/
  denseSubSeq_dense_in : ∀ x ∈ (toSubmodule : Set E), ∀ ε > 0,
    ∃ n, dist x (denseSubSeq n) < ε
  /-- Locatedness: the infimal distance from each point of the ambient
  dense sequence to M is a computable real.

  Per Methodological Observation 3: the predicate ranges over
  `OperationalHilbertSpace.denseSeq m` (operational witnesses), not over
  arbitrary `x : E` (formal register). This is principled, not a shortcut. -/
  dist_computable : ∀ m : ℕ,
    IsComputableReal (Metric.infDist
      (OperationalHilbertSpace.denseSeq (E := E) m)
      (toSubmodule : Set E))

-- ============================================================
-- §II. HasOrthogonalProjection: automatic via inferInstance
-- ============================================================
-- Per §I design choice: for any M : OperationalLocatedSubspace E,
-- M.toSubmodule.HasOrthogonalProjection is resolved by inferInstance.
-- This is not proved explicitly here; Stage 5 uses it directly.
-- The instance chain:
--   M extends ClosedSubmodule ℝ E
--   → instance (K : ClosedSubmodule 𝕜 E) [CompleteSpace E] : K.HasOrthogonalProjection
--   → M.toSubmodule.HasOrthogonalProjection ✓

-- ============================================================
-- §III. Canonical ⊤ instance for ℝ (trivial sanity check)
-- ============================================================

/-- `OperationalLocatedSubspace ℝ` for the whole space `⊤`.

## Design
- `ClosedSubmodule` part: `⊤ : Submodule ℝ ℝ` with `isClosed_univ`.
- `denseSubSeq` = ambient `denseSeq` (rationals enumerated by `Denumerable`).
- Density within ⊤ follows from `DenseRange denseSeq` on ℝ.
- `infDist (denseSeq m) ⊤ = 0` since `denseSeq m ∈ ⊤`; `IsComputableReal_zero` closes.

## Purpose
Sanity check that the structure is non-vacuous and the four fields are
consistently satisfied in the simplest case. Not used in Stage 5.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
noncomputable def topOperationalLocatedSubspace : OperationalLocatedSubspace ℝ where
  -- ClosedSubmodule part: top submodule (= whole space ℝ).
  -- Constructor: ⟨submodule, isClosed_proof⟩ (positional, not named fields).
  toClosedSubmodule := ⟨⊤, isClosed_univ⟩
  denseSubSeq       := OperationalHilbertSpace.denseSeq (E := ℝ)
  denseSubSeq_mem   := fun _ => Submodule.mem_top
  denseSubSeq_dense_in := by
    -- ⊤ = univ, so density within ⊤ is exactly DenseRange denseSeq.
    intro x _hx ε hε
    have hd := OperationalHilbertSpace.denseSeq_dense (E := ℝ)
    rw [Metric.denseRange_iff] at hd
    exact hd x ε hε
  dist_computable := fun m => by
    -- infDist (denseSeq m) ⊤ = 0 because denseSeq m ∈ ⊤ (= whole space).
    have hzero : Metric.infDist (OperationalHilbertSpace.denseSeq (E := ℝ) m)
                 ((⊤ : Submodule ℝ ℝ) : Set ℝ) = 0 :=
      Metric.infDist_zero_of_mem Submodule.mem_top
    rw [hzero]
    exact IsComputableReal_zero

-- ============================================================
-- Axiom audit — Stage 3
-- ============================================================
-- STAGE: 3. SOURCE: PLAN.md Stage 3; CLAUDE.md wrapping principle.
-- LEAN OBJECTS (2 public):
--   structure: OperationalLocatedSubspace
--   def:       topOperationalLocatedSubspace
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound] for all.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms OperationalLocatedSubspace
#print axioms topOperationalLocatedSubspace

end VR.Audit
