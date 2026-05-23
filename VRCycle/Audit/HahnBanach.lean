-- VR-Audit: HahnBanach.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 5: Main theorem — HahnBanachOperational_Hilbert.
--
-- STAGE: 5 (of 7). SOURCE: PLAN.md Stage 5; CLAUDE.md transit pattern.
--         Follows VRCycle.Audit.Functional (Stage 4).
--
-- ## Position statement (Stage 5: central theorem of the VR-Audit cycle)
-- This file proves `HahnBanachOperational_Hilbert`: every operational
-- normable functional on an operational located subspace of an operational
-- Hilbert space extends to an operational normable functional on the whole
-- space with the same norm.  This is the operational Hahn-Banach theorem
-- for Hilbert spaces, proved by the Riesz representation route.
--
-- ## Why Path B (Riesz) and not Path A (classical Hahn-Banach)
-- The classical Hahn-Banach extension theorem (mathlib:
-- `Mathlib.Analysis.NormedSpace.HahnBanach.Extension`) produces an extension
-- as a classical existence result — it gives no constructive witness for the
-- extension's values, only an abstract CLM.  Applying it would satisfy the
-- formal register but leave the operational register empty: there would be
-- no computable witness for g(denseSeq n).
--
-- Path B (Riesz representation) instead:
--   (1) Represents f as an inner product via Riesz: f(v) = ⟪ξ, v⟫_M.
--   (2) Extends to g(w) := ⟪ξ, w⟫_E for all w : E — a concrete map.
--   (3) Operationality of g on denseSeq n follows by an explicit computation
--       through orthogonal projection (locatedness of Stage 3).
--   (4) The norm equality g.opNorm = f.toFun.opNorm is proved directly by
--       Cauchy-Schwarz (upper) and inner product evaluation (lower).
-- The Riesz route is the unique structure that makes the transit clean.
--
-- ## Architecture: six steps of the proof
-- Let K = M.toSubmodule : Submodule ℝ E.
-- Step 1. Riesz vector: ξ := (InnerProductSpace.toDual ℝ K).symm f.toFun : K.
--         Key: ⟪ξ, v⟫_K = f.toFun v for all v : K  (by toDual_symm_apply).
-- Step 2. Extension: g := innerSL ℝ (ξ : E) : E →L[ℝ] ℝ.
--         g w = ⟪(ξ:E), w⟫_E for all w : E.
-- Step 3. Extension property: g (x:E) = f.toFun x for x : K.
--         Via Submodule.coe_inner: ⟪(ξ:E), (x:E)⟫_E = ⟪ξ, x⟫_K = f.toFun x.
-- Step 4. Operationality of g on denseSeq n:
--         g(denseSeq n) = ⟪(ξ:E), denseSeq n⟫_E
--                       = ⟪ξ, K.orthogonalProjection(denseSeq n)⟫_K
--                           [inner_orthogonalProjection_eq_of_mem_left]
--                       = f.toFun (K.orthogonalProjection(denseSeq n))
--                           [hξ]
--         IsComputableReal by fn_computable_everywhere (Stage 4).
-- Step 5. Norm equality: g.opNorm = ‖(ξ:E)‖ (by innerSL_apply_norm).
--         f.toFun.opNorm = ‖(ξ:E)‖ by le_antisymm:
--           upper ≤ ‖(ξ:E)‖: Cauchy-Schwarz (abs_real_inner_le_norm).
--           lower ≥ ‖(ξ:E)‖: evaluate f.toFun.le_opNorm at ξ, use ⟪ξ,ξ⟫=‖ξ‖².
-- Step 6. norm_computable: rw [h_norm_eq]; exact f.norm_computable.
--
-- ## Methodological Observation 6 (transit pattern for Hilbert Hahn-Banach)
-- The transit pattern in this stage has a richer structure than the standard
-- "apply classical lemma, prove output operational" schema.  The classical
-- object (the extended functional) is built entirely from operational data:
--   - ξ is the Riesz vector of f (classical Riesz applied to operational f),
--   - g := innerSL ℝ (ξ:E) is defined concretely from ξ.
-- The operational content of g at denseSeq n is derived not from g's definition
-- directly but from the factorisation g(x) = f(P_M(x)) (Steps 2–4), where P_M
-- is orthogonal projection.  This factorisation is the operational heart of the
-- transit: it rewrites the output of the classical construction in terms of a
-- known operational object (f applied to a computable input).  The Riesz map is
-- the unique structure that enables this factorisation.
--
-- ## Methodological Observation 7 (Norm synthesis gap: propagation to Stage 5)
-- In Stage 4 we observed that the `Norm (↥M.toSubmodule →L[ℝ] ℝ)` instance
-- does not synthesize at declaration/goal-elaboration time.  In Stage 5 this
-- propagates: we cannot write ‖f.toFun‖ in a goal or `have` type annotation.
-- Workaround: use f.toFun.opNorm throughout, and use `show` or definitional
-- `change` to pass to `‖·‖`-based lemmas (e.g. opNorm_le_bound, innerSL_apply_norm)
-- inside tactic proof bodies where elaboration context is richer.  The gap is
-- structural (universe/instance unification) and expected in wrapping-style
-- formalisations where the ambient type carries multiple unification paths.
--
-- ## Specker boundary: explicitly avoided (see also Methodological Observation 4)
-- The Specker obstruction (1949) applies to suprema of bounded monotone
-- computable sequences.  Our construction avoids it:
--   - ξ is a single vector (not a limit): Riesz gives ξ concretely.
--   - g(denseSeq n) = f(P_M(denseSeq n)): a finite-step computation.
--   - The norm is ‖(ξ:E)‖: a single real, not a supremum.
-- The locatedness condition (Stage 3) enables orthogonal projection to be
-- applied operationally; without it the factorisation in Step 4 would not hold.
--
-- ## What this file does
-- PROVES (1 public theorem):
--   HahnBanachOperational_Hilbert : ∀ f : OperationalNormableFunctional E M,
--     ∃ g : E →L[ℝ] ℝ,
--       (∀ n, IsComputableReal (g (denseSeq n))) ∧
--       IsComputableReal g.opNorm ∧
--       (∀ x : M.toSubmodule, g (x:E) = f.toFun x) ∧
--       g.opNorm = f.toFun.opNorm
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound]
-- Classical.choice is expected (Riesz uses CompleteSpace, toDual uses it).
-- propext and Quot.sound are inherited from mathlib's ℝ.
-- No new axioms beyond mathlib's standard ceiling.

import VRCycle.Audit.Functional
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

namespace VR.Audit

-- ============================================================
-- §I. Main theorem: HahnBanachOperational_Hilbert
-- ============================================================

/-- **Operational Hahn-Banach for Hilbert Spaces** (v1.4-vr-audit-hb-hilbert, Stage 5).

Every operational normable functional `f` on an operational located subspace
`M` of an operational Hilbert space `E` extends to an operational normable
functional `g : E →L[ℝ] ℝ` on the whole space with the same operator norm.

## Statement (Form A — existential)
Given:
- `E : Type*` with `OperationalHilbertSpace E` (Stage 2),
- `M : OperationalLocatedSubspace E` (Stage 3),
- `f : OperationalNormableFunctional E M` (Stage 4).

Produces:
- `g : E →L[ℝ] ℝ` (classical CLM on E),
- `∀ n, IsComputableReal (g (denseSeq n))` — g computable on ambient dense sequence,
- `IsComputableReal g.opNorm` — g normable,
- `∀ x : M.toSubmodule, g (x:E) = f.toFun x` — g extends f,
- `g.opNorm = f.toFun.opNorm` — norm preservation.

## Proof method
Riesz representation (Path B): the Riesz vector ξ ∈ M represents f, and
g := innerSL ℝ (ξ:E) extends it to E. Operationality follows via the
factorisation g(x) = f(P_M(x)) where P_M is orthogonal projection.
See file-level comment §Architecture for the six-step proof.

## Specker boundary
The Specker obstruction (1949) does not apply: g(denseSeq n) = f(P_M(denseSeq n))
is a finite-step computation, not a limit of a computable sequence. See
Methodological Observation 4 in Subspace.lean and the file-level comment above.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem HahnBanachOperational_Hilbert {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    {M : OperationalLocatedSubspace E}
    (f : OperationalNormableFunctional E M) :
    ∃ g : E →L[ℝ] ℝ,
      (∀ n : ℕ, IsComputableReal (g (OperationalHilbertSpace.denseSeq (E := E) n))) ∧
      IsComputableReal g.opNorm ∧
      (∀ x : M.toSubmodule, g (x : E) = f.toFun x) ∧
      g.opNorm = f.toFun.opNorm := by
  -- §1. CompleteSpace for K = M.toSubmodule (needed for toDual and hK_proj).
  -- letI (transparent) makes it findable by tactic-level instance synthesis
  -- (contrast: haveI is opaque and may not propagate into term-mode let).
  -- Two Lean 4 obstacles overcome here:
  -- (a) ⟪⟫_ℝ notation fails in ∃-binder scope of type annotations; use inner ℝ.
  -- (b) term-mode `let ξ := toDual.symm` doesn't see outer haveI/letI;
  --     pass hK_complete EXPLICITLY via @toDual to bypass instance search.
  letI hK_complete : CompleteSpace (↥M.toSubmodule) := by
    letI := M.toClosedSubmodule.isClosed'
    exact inferInstance
  -- §2. HasOrthogonalProjection (global ClosedSubmodule instance; needs CompleteSpace).
  haveI hK_proj : M.toSubmodule.HasOrthogonalProjection := inferInstance
  -- §3. Riesz vector ξ ∈ K via Fréchet-Riesz.
  -- Use tactic-mode `have` (not term-mode) so that letI hK_complete is found
  -- by typeclass synthesis inside `exact`. The @-form with explicit hK_complete
  -- fails because toDual's universe/instance arg ordering differs from Lean's
  -- implicit arg count. In tactic mode, `hK_complete` is a local instance,
  -- so `InnerProductSpace.toDual ℝ _` synthesizes it automatically.
  -- hξ uses `inner ℝ` (function form) not ⟪⟫_ℝ (fails in ∃-binder scope).
  have riesz_exists : ∃ ξ : M.toSubmodule, ∀ v : M.toSubmodule,
      inner ℝ ξ v = f.toFun v := by
    -- Pass hK_complete explicitly via @ to bypass instance synthesis for CompleteSpace.
    -- Instance synthesis reduces ↥M.toSubmodule to ↥↑M.toClosedSubmodule (via
    -- OperationalLocatedSubspace.toSubmodule reducible def), and hK_complete is
    -- stored under the unreduced form, so synthesis fails. @ avoids the lookup.
    exact ⟨(@InnerProductSpace.toDual ℝ (↥M.toSubmodule) _ _ _ hK_complete).symm f.toFun,
           fun v => @InnerProductSpace.toDual_symm_apply ℝ (↥M.toSubmodule) _ _ _ hK_complete
                      v f.toFun⟩
  obtain ⟨ξ, hξ⟩ := riesz_exists
  -- §4. Extension: g := innerSL ℝ (ξ:E).
  -- g w = ⟪(ξ:E), w⟫_E for all w : E (innerSL_apply_apply is definitionally rfl).
  let g : E →L[ℝ] ℝ := innerSL ℝ (ξ : E)
  -- §5. Norm equality: g.opNorm = f.toFun.opNorm (both equal ‖(ξ:E)‖).
  have h_norm_eq : g.opNorm = f.toFun.opNorm := by
    -- Step A: g.opNorm = ‖(ξ:E)‖.
    -- innerSL_apply_norm takes TWO explicit args (field 𝕜 and vector x).
    have hg : g.opNorm = ‖(ξ : E)‖ := by
      change ‖(innerSL ℝ (ξ : E))‖ = ‖(ξ : E)‖
      exact innerSL_apply_norm _ _
    -- Step B: f.toFun.opNorm = ‖(ξ:E)‖ by le_antisymm.
    have hf : f.toFun.opNorm = ‖(ξ : E)‖ := by
      apply le_antisymm
      · -- Upper: |f v| ≤ ‖(ξ:E)‖ * ‖v‖ via Cauchy-Schwarz.
        -- hξ v : inner ℝ ξ v = f.toFun v; rw [← hξ v] would fail (inner ℝ form
        -- vs ⟪⟫_ℝ syntactic mismatch); use `have hfv` to introduce then rewrite.
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro v
        have hfv : f.toFun v = inner ℝ ξ v := (hξ v).symm
        -- congr_arg norm bypasses CLM coercion opacity inside ‖·‖ (simp/rw can't rewrite there).
        calc ‖f.toFun v‖
            = ‖inner ℝ ξ v‖     := congr_arg norm hfv
          _ = |inner ℝ ξ v|     := Real.norm_eq_abs _
          _ ≤ ‖ξ‖ * ‖v‖         := abs_real_inner_le_norm ξ v
          _ = ‖(ξ : E)‖ * ‖v‖   := by rw [Submodule.coe_norm]
      · -- Lower: use le_opNorm at ξ, inner ξ ξ = ‖ξ‖².
        by_cases hξ0 : ξ = 0
        · simp only [hξ0, Submodule.coe_zero, norm_zero]
          exact ContinuousLinearMap.opNorm_nonneg _
        · have hpos : 0 < ‖(ξ : E)‖ := by
            have h := norm_pos_iff.mpr hξ0
            rwa [Submodule.coe_norm] at h
          have hle := f.toFun.le_opNorm ξ
          -- f.toFun ξ = inner ℝ ξ ξ: introduce via have to avoid rw mismatch.
          -- f.toFun ξ = inner ℝ ξ ξ = ‖(ξ:E)‖^2
          -- Use simp only (not rw) to handle CLM application coercions inside ‖·‖.
          have hfxi : f.toFun ξ = ‖(ξ : E)‖ ^ 2 := by
            have step1 : f.toFun ξ = inner ℝ ξ ξ := (hξ ξ).symm
            rw [step1, real_inner_self_eq_norm_sq, Submodule.coe_norm]
          -- ‖f.toFun ξ‖ = ‖(ξ:E)‖^2 (non-negative)
          have hnrm : ‖f.toFun ξ‖ = ‖(ξ : E)‖ ^ 2 :=
            calc ‖f.toFun ξ‖
                = ‖(‖(ξ : E)‖ ^ 2 : ℝ)‖  := congr_arg norm hfxi
              _ = |‖(ξ : E)‖ ^ 2|         := Real.norm_eq_abs _
              _ = ‖(ξ : E)‖ ^ 2           := abs_of_nonneg (sq_nonneg _)
          -- Chain: ‖(ξ:E)‖^2 ≤ f.toFun.opNorm * ‖(ξ:E)‖
          have hle2 : ‖(ξ : E)‖ ^ 2 ≤ f.toFun.opNorm * ‖(ξ : E)‖ := by
            calc ‖(ξ : E)‖ ^ 2 = ‖f.toFun ξ‖               := hnrm.symm
              _ ≤ f.toFun.opNorm * ‖ξ‖                      := hle
              _ = f.toFun.opNorm * ‖(ξ : E)‖                := by rw [Submodule.coe_norm]
          rw [pow_two] at hle2
          exact le_of_mul_le_mul_right hle2 hpos
    exact hg.trans hf.symm
  -- §6. Produce the witness ⟨g, ...⟩ with four components.
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  -- ── Part 1: g computable on denseSeq n ──────────────────────────────────
  · intro n
    -- g(denseSeq n) = ⟪(ξ:E), denseSeq n⟫ = ⟪ξ, K.proj(denseSeq n)⟫
    --              = inner ℝ ξ (proj(denseSeq n)) = f.toFun(proj(denseSeq n))
    -- inner_orthogonalProjection_eq_of_mem_left ξ v :
    --   inner ℝ ξ (K.proj v) = inner ℝ ↑ξ v
    -- So .symm : inner ℝ ↑ξ v = inner ℝ ξ (K.proj v).
    -- 3-step calc: g → inner ℝ ↑ξ v → inner ℝ ξ (K.proj v) → f (K.proj v).
    -- No Submodule.coe_inner needed.
    have hchain : g (OperationalHilbertSpace.denseSeq (E := E) n) =
        f.toFun (M.toSubmodule.orthogonalProjection
          (OperationalHilbertSpace.denseSeq (E := E) n)) :=
      calc g (OperationalHilbertSpace.denseSeq (E := E) n)
          = inner ℝ (ξ : E) (OperationalHilbertSpace.denseSeq (E := E) n) := rfl
        _ = inner ℝ ξ (M.toSubmodule.orthogonalProjection
              (OperationalHilbertSpace.denseSeq (E := E) n)) :=
            (Submodule.inner_orthogonalProjection_eq_of_mem_left ξ
              (OperationalHilbertSpace.denseSeq (E := E) n)).symm
        _ = f.toFun (M.toSubmodule.orthogonalProjection
              (OperationalHilbertSpace.denseSeq (E := E) n)) := hξ _
    rw [hchain]
    exact fn_computable_everywhere f _
  -- ── Part 2: g.opNorm is a computable real ───────────────────────────────
  · rw [h_norm_eq]; exact f.norm_computable
  -- ── Part 3: g extends f ──────────────────────────────────────────────────
  · intro x
    -- calc avoids rw-direction ambiguity: (coe_inner ...).symm goes ambient → submodule.
    calc g (x : E)
        = inner ℝ (ξ : E) (x : E) := rfl
      _ = inner ℝ ξ x := (Submodule.coe_inner M.toSubmodule ξ x).symm
      _ = f.toFun x := hξ x
  -- ── Part 4: norm equality ────────────────────────────────────────────────
  · exact h_norm_eq

-- ============================================================
-- Axiom audit — Stage 5
-- ============================================================
-- STAGE: 5. SOURCE: PLAN.md Stage 5; CLAUDE.md transit pattern.
-- LEAN OBJECTS (1 public):
--   theorem: HahnBanachOperational_Hilbert
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound] for all.
-- Classical.choice is expected: toDual uses CompleteSpace; fn_computable_everywhere
-- uses Classical.choose; ℝ's Cauchy completeness uses it.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms HahnBanachOperational_Hilbert

end VR.Audit
