-- VR-Audit: Example.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 6: Concrete OperationalHilbertSpace instance — EuclideanSpace ℝ (Fin n).
--
-- STAGE: 6 (of 7). SOURCE: PLAN.md Stage 6; CLAUDE.md wrapping principle.
--         Follows VRCycle.Audit.HahnBanach (Stage 5).
--
-- ## Position statement
-- Stage 6 of VR-Audit cycle. Provides the first concrete non-trivial instance
-- of `OperationalHilbertSpace`: n-dimensional Euclidean space ℝⁿ for any n : ℕ.
-- This demonstrates non-vacuity of operationality: the main theorem
-- (Stage 5) applies to at least one concrete, mathematically natural space.
--
-- ## Scope decision: ℝⁿ only, ℓ² deferred
-- EuclideanSpace ℝ (Fin n) = PiLp 2 (fun _ : Fin n => ℝ) is the natural
-- first example: finite-dimensional, explicitly constructible dense sequence,
-- inner products are finite sums (hence obviously computable). The infinite-
-- dimensional case ℓ² = lp (fun _ : ℕ => ℝ) 2 is deferred: denseSeq requires
-- a Finsupp-based enumeration and inner_computable requires tsum convergence
-- arguments, adding substantial complexity without additional methodological
-- content. The ℓ² case is noted as future work.
--
-- ## Construction overview
-- `denseSeq k := WithLp.toLp 2 (fun i => ((Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℝ))`
-- This enumerates (via `decode : ℕ → Option (Fin n → ℚ)`) all rational vectors,
-- embedded as real vectors via `WithLp.toLp 2`. Density follows by:
-- (1) `Encodable.surjective_decode_getD` enumerates all `Fin n → ℚ`;
-- (2) `DenseRange.piMap` lifts coordinate-wise density of ℚ ↪ ℝ to `Fin n → ℝ`;
-- (3) `PiLp.homeomorph` transfers density from `Fin n → ℝ` (product topology) to
--     `EuclideanSpace ℝ (Fin n)` (Euclidean = L² topology, homeomorphic to product
--     for finite-dimensional spaces).
-- `inner_computable`: `PiLp.inner_apply` reduces `⟪denseSeq m, denseSeq k⟫` to
-- `∑ i : Fin n, ⟪..., ...⟫_ℝ`, then `RCLike.inner_apply` reduces each summand
-- to a product; `conj = id` on ℝ (TrivialStar). The finite sum of rational
-- products is rational, hence computable by `IsComputableReal_rat`.
--
-- ## Wrapping principle in action
-- No new type is introduced. `OperationalHilbertSpace` is layered on top of
-- mathlib's existing `EuclideanSpace / InnerProductSpace ℝ (EuclideanSpace ℝ (Fin n))`.
-- The three fields (`denseSeq`, `denseSeq_dense`, `inner_computable`) are witnesses;
-- the underlying classical structure (`InnerProductSpace ℝ E`, `CompleteSpace E`) is
-- provided entirely by mathlib and remains unrestricted.
--
-- ## Methodological Observation 10 (non-vacuity of operationality)
-- Stage 5 establishes `HahnBanachOperational_Hilbert` for any `OperationalHilbertSpace`.
-- Stage 6 confirms operationality is non-vacuous: for every n : ℕ, `ℝⁿ` satisfies the
-- three operational requirements with explicit witnesses. This is the standard VR-Audit
-- pattern: main theorem in full generality, then at least one explicit instance to show
-- operationality is inhabited. The instance also serves as a sanity check that the
-- operational requirements are achievable without exotic mathematics.
--
-- ## Connection to main theorem
-- For any n : ℕ, `HahnBanachOperational_Hilbert` specialises (via
-- `instOperationalHilbertSpaceEuclidean`) to: any operational normable functional on
-- an operational located subspace of `EuclideanSpace ℝ (Fin n)` extends to an
-- operational normable functional on all of `EuclideanSpace ℝ (Fin n)` with the same
-- norm. The extension is given by the Riesz representation vector (Stage 5, Path B).
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound]
-- Inherited from mathlib's ℝ and EuclideanSpace. Encodable instances for Fin n → ℚ
-- require Classical.choice for the Encodable.fintypeArrow instance. No new axioms.

import VRCycle.Audit.HahnBanach
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Encodable.Pi
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic

namespace VR.Audit

open scoped RealInnerProductSpace

-- ============================================================
-- §I. instOperationalHilbertSpaceEuclidean
-- ============================================================

/-- `EuclideanSpace ℝ (Fin n)` is an `OperationalHilbertSpace` for every `n : ℕ`.

## Dense sequence
`denseSeq k = WithLp.toLp 2 (fun i => ((Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℝ))`

`Encodable.fintypeArrowOfEncodable` provides `Encodable (Fin n → ℚ)` (since `Fin n` is
`Fintype` and `ℚ` is `Encodable`). `Encodable.surjective_decode_getD` then enumerates
all rational vectors surjectively, giving a countable dense subset.

## Density proof (three-step DenseRange.comp chain)
1. `Encodable.surjective_decode_getD (Fin n → ℚ) 0` is surjective (hence dense range).
2. `DenseRange.piMap` lifts the dense range of `Rat.cast : ℚ → ℝ` to
   `Pi.map Rat.cast : (Fin n → ℚ) → (Fin n → ℝ)` (product topology on `Fin n → ℝ`).
3. `PiLp.homeomorph 2 (fun _ : Fin n => ℝ)` is a homeomorphism
   `EuclideanSpace ℝ (Fin n) ≃ₜ (Fin n → ℝ)`. Its inverse transfers density from
   `Fin n → ℝ` (product topology) to `EuclideanSpace ℝ (Fin n)` (L² topology).

## Inner product computability
`PiLp.inner_apply : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ := rfl`
`RCLike.inner_apply : ⟪a, b⟫_ℝ = b * conj a`; for `a b : ℝ`, `conj = id` (TrivialStar).
The result is a finite sum of rational products cast to ℝ. `IsComputableReal_rat` closes.

## Technical Note: `ring` vs `mul_comm` on ℝ inner products
For ℝ as base field, `@inner ℝ ℝ _ x y = y * x` **by definition** through
`RCLike.toInnerProductSpaceReal` (the default instance on ℝ) — note the argument
order: y first, x second. When proving `⟪m_i, k_i⟫_ℝ = m_i * k_i` after unfolding
`PiLp.inner_apply` and `push_cast`, the tactic `ring` fails: it treats `⟪·, ·⟫`
as an opaque atom and cannot unfold it. The fix is `exact mul_comm _ _`, which
bridges the `k_i * m_i = m_i * k_i` argument-order reversal after definitional
reduction. This pattern applies to any future proof that must bridge between the
`⟪·,·⟫` notation and arithmetic expressions on ℝ.

## Methodological Observation 10: non-vacuity of operationality (see file header).

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
noncomputable instance instOperationalHilbertSpaceEuclidean (n : ℕ) :
    OperationalHilbertSpace (EuclideanSpace ℝ (Fin n)) where

  -- Dense sequence: rational vectors (Fin n → ℚ), enumerated via Encodable,
  -- embedded into EuclideanSpace ℝ (Fin n) = PiLp 2 (fun _ : Fin n => ℝ) via WithLp.toLp 2.
  denseSeq := fun k =>
    WithLp.toLp 2 (fun i : Fin n =>
      ((Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℝ))

  -- DenseRange: three-step chain via DenseRange.comp and PiLp.homeomorph.
  denseSeq_dense := by
    -- Step 1: surjective enumeration of all Fin n → ℚ.
    -- `Encodable.fintypeArrowOfEncodable` provides `[Encodable (Fin n → ℚ)]` automatically.
    have h_enum : DenseRange (fun k : ℕ =>
        (Encodable.decode (α := Fin n → ℚ) k).getD 0) :=
      (Encodable.surjective_decode_getD (Fin n → ℚ) 0).denseRange
    -- Step 2: coordinate-wise density of ℚ in ℝ lifts to Pi.map Rat.cast.
    -- `DenseRange.piMap` uses `Rat.denseRange_cast` at each coordinate.
    have h_cast : DenseRange (Pi.map (fun (_ : Fin n) => (Rat.cast : ℚ → ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    -- Step 3: compose steps 1 and 2 to get density in Fin n → ℝ (product topology).
    -- Continuity of Pi.map Rat.cast: `Continuous.piMap` with `Rat.continuous_coe_real`.
    have h_prod : DenseRange (fun k : ℕ =>
        Pi.map (fun (_ : Fin n) => (Rat.cast : ℚ → ℝ))
          ((Encodable.decode (α := Fin n → ℚ) k).getD 0)) :=
      h_cast.comp h_enum (Continuous.piMap fun _ => Rat.continuous_coe_real)
    -- Step 4: transfer density from Fin n → ℝ (product topology) to EuclideanSpace ℝ (Fin n)
    -- via the inverse of the homeomorphism PiLp.homeomorph 2 (fun _ : Fin n => ℝ).
    -- Inverse = WithLp.toLp 2 (continuous by continuous_toLp).
    -- Pi.map Rat.cast q i = (q i : ℝ) definitionally, so the functions coincide.
    exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.surjective.denseRange.comp
        h_prod (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.continuous

  -- Inner product computability: reduces to a finite sum of rational products.
  inner_computable := fun m k => by
    -- First, make the denseSeq field explicit (it equals WithLp.toLp 2 (fun i => ...)).
    change IsComputableReal (@inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (WithLp.toLp 2 (fun i : Fin n =>
        ((Encodable.decode (α := Fin n → ℚ) m).getD 0 i : ℝ)))
      (WithLp.toLp 2 (fun i : Fin n =>
        ((Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℝ))))
    -- Prove the inner product equals a rational sum.
    have heq : @inner ℝ (EuclideanSpace ℝ (Fin n)) _
        (WithLp.toLp 2 (fun i : Fin n =>
          ((Encodable.decode (α := Fin n → ℚ) m).getD 0 i : ℝ)))
        (WithLp.toLp 2 (fun i : Fin n =>
          ((Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℝ))) =
        ((∑ i : Fin n,
          (Encodable.decode (α := Fin n → ℚ) m).getD 0 i *
          (Encodable.decode (α := Fin n → ℚ) k).getD 0 i : ℚ) : ℝ) := by
      -- PiLp.inner_apply (rfl): ⟪x, y⟫_ℝ = ∑ i, ⟪x i, y i⟫_ℝ. After this, the
      -- inner product on ℝ is definitionally y * x (from RCLike.innerProductSpace and
      -- TrivialStar ℝ), so the sum has the form ∑ i, (decode k).getD 0 i * (decode m).getD 0 i.
      simp only [PiLp.inner_apply]
      -- Push the ℚ → ℝ cast through the sum and products.
      push_cast
      -- The summands differ only by commutativity: (k i) * (m i) vs (m i) * (k i).
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    rw [heq]
    exact IsComputableReal_rat _

-- ============================================================
-- Axiom audit — Stage 6
-- ============================================================
-- STAGE: 6. SOURCE: PLAN.md Stage 6; CLAUDE.md wrapping principle.
-- LEAN OBJECTS (1 public):
--   instance: instOperationalHilbertSpaceEuclidean
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound].
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms instOperationalHilbertSpaceEuclidean

end VR.Audit
