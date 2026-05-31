-- VR-Audit: Functional.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 4: OperationalNormableFunctional structure.
--
-- STAGE: 4 (of 7). SOURCE: PLAN.md Stage 4; CLAUDE.md wrapping principle.
--         Follows VRCycle.Audit.Subspace (Stage 3).
--
-- ## Position statement
-- Stage 4 of VR-Audit cycle. Defines `OperationalNormableFunctional` — the
-- operational analogue of a bounded linear functional on a located subspace.
-- Equips the classical bounded functional `M.toSubmodule →L[ℝ] ℝ` with two
-- computability witnesses:
--   (a) values on the dense sequence of M are computable reals,
--   (b) the operator norm is a computable real (= "normable" in Ishihara's sense).
--
-- ## Wrapping principle in action
-- Per CLAUDE.md, wrapping over mathlib's `ContinuousLinearMap` (abbrev `→L[ℝ]`).
-- No new type of "computable functional" is introduced. Instead, two operational
-- predicates are layered on top of `M.toSubmodule →L[ℝ] ℝ`:
--   (a) `fn_computable_on_dense : ∀ n, IsComputableReal (toFun ⟨denseSubSeq n, _⟩)`
--   (b) `norm_computable : IsComputableReal toFun.opNorm`
--
-- Formal register   = mathlib's `M.toSubmodule →L[ℝ] ℝ` (unrestricted).
-- Operational register = `OperationalNormableFunctional E M` (two added fields).
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- ## Bounded ≠ normable (Methodological Observation 5)
-- In classical mathematics, every bounded linear functional has a well-defined
-- norm ‖f‖ ∈ ℝ. In computable analysis (Ishihara 1989), "bounded" (∃ C, ∀ x,
-- |f(x)| ≤ C‖x‖) and "normable" (the exact infimum sup|f(x)|/‖x‖ is a
-- computable real) are distinct: a functional can be bounded without its norm
-- being computable. Our `norm_computable` field precisely captures normability,
-- not mere boundedness. This is the correct operational analogue for the
-- norm-preservation clause of Hahn-Banach: F.norm = f.norm in Stage 5
-- requires both norms to be computable. Imposing normability here (not just
-- boundedness) is what makes the norm-preservation clause of the operational
-- Hahn-Banach theorem expressible and provable.
--
-- ## Technical Note: Norm instance synthesis gap
-- For `f : M.toSubmodule →L[ℝ] ℝ` where `M : OperationalLocatedSubspace E`,
-- the `Norm (M.toSubmodule →L[ℝ] ℝ)` instance does NOT synthesize when `‖f‖`
-- is written explicitly in structure field type declarations or term-level
-- goals (mathlib infrastructure gap: `ContinuousLinearMap.hasOpNorm` instance
-- does not discharge in this context at declaration time). Workaround: use
-- `f.opNorm` (direct field access on `ContinuousLinearMap`), which is
-- definitionally equal to `‖f‖` via `ContinuousLinearMap.norm_def`.
-- This workaround is internal to Stage 4; in proof bodies, `le_opNorm` works
-- and `f.opNorm` appears correctly in hypotheses.
--
-- ## fn_computable_everywhere
-- From the two fields, all values `f.toFun x` for `x : M.toSubmodule` are
-- computable, not just values on the dense sequence. Proof: for each x,
-- density gives a sequence of dense approximations y_k → x; continuity
-- (f.le_opNorm) bounds |f(x) - f(y_k)|; fn_computable_on_dense gives
-- rational approximations for f(y_k); triangle inequality combines them.
-- Witnesses are constructed via Classical.choose (Prop-valued, axiom ceiling
-- [propext, Classical.choice, Quot.sound] respected).
--
-- ## topOperationalLocatedSubspace instance
-- The zero functional on `topOperationalLocatedSubspace` (⊤ subspace of ℝ)
-- satisfies both fields trivially: f(v) = 0, opNorm = 0, both computable by
-- IsComputableReal_zero.
--
-- ## What this file does
-- DEFINES:
--   structure: OperationalNormableFunctional
-- PROVES:
--   theorem: fn_computable_everywhere
--   def: zeroOperationalNormableFunctional
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound]
-- Classical.choice enters via density (Classical.choose for dense approximation)
-- and fn_computable_on_dense witnesses. Expected and acceptable.

import VRCycle.Audit.Subspace
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

namespace VR.Audit

-- ============================================================
-- §I. OperationalNormableFunctional structure
-- ============================================================

/-- `OperationalNormableFunctional E M`: operational normable functional on M.

A classical continuous linear functional `M.toSubmodule →L[ℝ] ℝ` equipped
with two operational fields making it normable in Ishihara's sense:

1. `fn_computable_on_dense`: values on M's dense sequence are computable reals.
2. `norm_computable`: the operator norm is a computable real (normability).

## Technical note: `toFun.opNorm` vs `‖toFun‖`
The field `norm_computable` uses `toFun.opNorm` instead of `‖toFun‖`.
The `Norm (M.toSubmodule →L[ℝ] ℝ)` instance does not synthesize at structure
declaration time (mathlib gap). `toFun.opNorm` is definitionally equal to
`‖toFun‖` (by `ContinuousLinearMap.norm_def`) and is accepted by the elaborator.

## Source
Normability: Ishihara 1989 "Continuity properties in constructive mathematics",
J. Symbolic Logic 54(4):1365–1370. Wrapping: CLAUDE.md.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
structure OperationalNormableFunctional (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    (M : OperationalLocatedSubspace E) where
  /-- Classical continuous linear functional on M.toSubmodule. -/
  toFun : M.toSubmodule →L[ℝ] ℝ
  /-- Values of toFun on M's dense sequence are computable reals.
  Element subtype: ⟨M.denseSubSeq n, M.denseSubSeq_mem n⟩ : ↥M.toSubmodule. -/
  fn_computable_on_dense : ∀ n : ℕ,
    IsComputableReal (toFun ⟨M.denseSubSeq n, M.denseSubSeq_mem n⟩)
  /-- Operator norm of toFun is a computable real (normability condition).
  Uses toFun.opNorm (not ‖toFun‖): see Technical Note in file header.
  This is the "normable" condition (Ishihara 1989). -/
  norm_computable : IsComputableReal toFun.opNorm

#print axioms OperationalNormableFunctional

-- ============================================================
-- §II. fn_computable_everywhere
-- ============================================================

/-- Every value of an operational normable functional is a computable real.

## Proof outline
Given `x : M.toSubmodule` and `f : OperationalNormableFunctional E M`:
For each index `k : ℕ`:
1. Density of `M.denseSubSeq` in `M` gives `y_k : M.toSubmodule` with
   `dist (x : E) (y_k : E) < 1 / (2^(k+2) * (‖f.toFun‖ + 1))`.
2. `fn_computable_on_dense` gives a rational `q_k` with
   `|q_k - f(y_k)| ≤ 1/2^(k+2)`.
3. Continuity: `|f(x) - f(y_k)| ≤ ‖f.toFun‖ * dist(x, y_k) < 1/2^(k+2)`.
4. Triangle: `|q_k - f(x)| < 1/2^(k+1)`.
Then for `k ≥ n`, `1/2^(k+1) ≤ 1/2^n`, giving the modulus `mod n := n`.

Witnesses use `Classical.choose` (Prop-valued, axiom ceiling respected).

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem fn_computable_everywhere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    {M : OperationalLocatedSubspace E}
    (f : OperationalNormableFunctional E M)
    (x : M.toSubmodule) : IsComputableReal (f.toFun x) := by
  -- C = operator norm; used to calibrate the density ε
  set C := f.toFun.opNorm with hC_def
  have hC_nn : 0 ≤ C := f.toFun.opNorm_nonneg
  -- For each k, density gives m_k with dist(x, denseSubSeq m_k) < 1/(2^(k+2)*(C+1))
  have hdens : ∀ k : ℕ, ∃ m : ℕ,
      dist (x : E) (M.denseSubSeq m) < 1 / (2 ^ (k + 2) * (C + 1)) := fun k =>
    M.denseSubSeq_dense_in (x : E) x.2 _ (by positivity)
  -- Choose the dense index for each k
  let ι : ℕ → ℕ := fun k => Classical.choose (hdens k)
  have hι : ∀ k, dist (x : E) (M.denseSubSeq (ι k)) < 1 / (2 ^ (k + 2) * (C + 1)) :=
    fun k => Classical.choose_spec (hdens k)
  -- For each k, ∃ q : ℚ, |(q : ℝ) - f.toFun x| < 1/2^(k+1)
  have hkey : ∀ k : ℕ, ∃ q : ℚ, |(q : ℝ) - f.toFun x| < 1 / 2 ^ (k + 1) := by
    intro k
    -- Set y_k = ⟨denseSubSeq (ι k), ...⟩ as element of M.toSubmodule
    set y : M.toSubmodule := ⟨M.denseSubSeq (ι k), M.denseSubSeq_mem (ι k)⟩
    -- Step 1: get rational approximation q_k of f(y_k) at precision 1/2^(k+2)
    obtain ⟨algk, modk, halgk⟩ := f.fn_computable_on_dense (ι k)
    -- q_k = algk(modk(k+2)) is (k+2)-close to f(y_k)
    set q := algk (modk (k + 2)) with hq_def
    have h1 : |(q : ℝ) - f.toFun y| ≤ 1 / 2 ^ (k + 2) :=
      halgk (k + 2) _ le_rfl
    -- Step 2: continuity bound |f(x) - f(y_k)| ≤ C * dist(x, y_k)
    have h2 : |f.toFun x - f.toFun y| ≤ C * dist (x : E) (M.denseSubSeq (ι k)) := by
      rw [show f.toFun x - f.toFun y = f.toFun (x - y) from (map_sub f.toFun x y).symm]
      rw [← Real.norm_eq_abs]
      have hle : ‖f.toFun (x - y)‖ ≤ f.toFun.opNorm * ‖x - y‖ := f.toFun.le_opNorm (x - y)
      have hnorm : ‖x - y‖ = dist (x : E) (M.denseSubSeq (ι k)) := by
        rw [Submodule.coe_norm, Submodule.coe_sub, dist_eq_norm]
      linarith [hnorm ▸ hle]
    -- Step 3: C * dist < 1/2^(k+2) by density choice
    have h3 : C * dist (x : E) (M.denseSubSeq (ι k)) < 1 / 2 ^ (k + 2) := by
      have hC1 : (0 : ℝ) < C + 1 := by linarith
      have h2k2 : (0 : ℝ) < 2 ^ (k + 2) := by positivity
      have hprod : (0 : ℝ) < 2 ^ (k + 2) * (C + 1) := mul_pos h2k2 hC1
      have hd' : dist (x : E) (M.denseSubSeq (ι k)) * (2 ^ (k + 2) * (C + 1)) < 1 :=
        (lt_div_iff₀ hprod).mp (hι k)
      rw [lt_div_iff₀ h2k2]
      nlinarith [dist_nonneg (α := E) (x := (x : E)) (y := M.denseSubSeq (ι k)),
                 mul_nonneg (dist_nonneg (α := E) (x := (x : E)) (y := M.denseSubSeq (ι k)))
                            (le_of_lt h2k2)]
    -- Step 4: triangle inequality gives |q - f(x)| < 1/2^(k+1)
    use q
    have htri : |(q : ℝ) - f.toFun x|
        ≤ |(q : ℝ) - f.toFun y| + |f.toFun x - f.toFun y| := by
      have : |(q : ℝ) - f.toFun x|
          = |(q : ℝ) - f.toFun y + (f.toFun y - f.toFun x)| := by ring_nf
      rw [this]
      have hadd := abs_add_le ((q : ℝ) - f.toFun y) (f.toFun y - f.toFun x)
      have hswap : |f.toFun y - f.toFun x| = |f.toFun x - f.toFun y| := abs_sub_comm _ _
      linarith
    have hsum : (1 : ℝ) / 2 ^ (k + 2) + 1 / 2 ^ (k + 2) = 1 / 2 ^ (k + 1) := by
      have : (2 : ℝ) ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
      rw [this]; ring
    linarith [htri, h1, h2, h3]
  -- Build IsComputableReal witnesses from hkey
  -- alg k = the rational q_k from hkey k
  -- mod n = n: for k ≥ n, |alg k - f(x)| < 1/2^(k+1) ≤ 1/2^n
  refine ⟨fun k => Classical.choose (hkey k), fun n => n, ?_⟩
  intro n k hnk
  have hq := Classical.choose_spec (hkey k)
  -- hq : |(alg k : ℝ) - f.toFun x| < 1/2^(k+1)
  -- 1/2^(k+1) ≤ 1/2^n since n ≤ k (so n ≤ k+1)
  have hpow : (1 : ℝ) / 2 ^ (k + 1) ≤ 1 / 2 ^ n := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) (Nat.le_succ_of_le hnk)
  linarith [hq, hpow]

#print axioms fn_computable_everywhere

-- ============================================================
-- §III. Zero functional instance (trivial sanity check)
-- ============================================================

/-- Zero functional on `topOperationalLocatedSubspace` (⊤ subspace of ℝ).

## Fields
- `toFun = 0`: zero CLM.
- `fn_computable_on_dense`: `(0)(denseSubSeq n) = 0`, `IsComputableReal_zero` closes.
- `norm_computable`: `(0).opNorm = 0` by `ContinuousLinearMap.opNorm_zero`;
  `IsComputableReal_zero` closes.

## Purpose
Sanity check: the structure is non-vacuous. Used in Stage 5 tests.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
noncomputable def zeroOperationalNormableFunctional :
    OperationalNormableFunctional ℝ topOperationalLocatedSubspace where
  toFun := 0
  fn_computable_on_dense := fun _ => by
    simp only [ContinuousLinearMap.zero_apply]
    exact IsComputableReal_zero
  norm_computable := by
    have h : (0 : topOperationalLocatedSubspace.toSubmodule →L[ℝ] ℝ).opNorm = 0 :=
      ContinuousLinearMap.opNorm_zero
    rw [h]
    exact IsComputableReal_zero

#print axioms zeroOperationalNormableFunctional

-- ============================================================
-- Axiom audit — Stage 4
-- ============================================================
-- STAGE: 4. SOURCE: PLAN.md Stage 4; CLAUDE.md wrapping principle.
-- LEAN OBJECTS (3 public):
--   structure: OperationalNormableFunctional
--   theorem:   fn_computable_everywhere
--   def:       zeroOperationalNormableFunctional
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound] for all.
-- CHECKS: no sorry, no admit; lake build passes.

end VR.Audit
