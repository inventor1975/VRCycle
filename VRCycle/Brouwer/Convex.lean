-- VR-Brouwer — Stage 5 (extension): Brouwer for a nonempty compact convex set.
-- Architecture (after mathlib recon): the standard simplex has empty interior in its ambient
-- `Fin(n+1)→ℝ` (it lives in the hyperplane `∑=1`), so the gauge/ball homeomorphism route is blocked.
-- Instead we keep the simplex as the Brouwer universe and RETRACT it onto an embedded scaled copy of
-- `K`, via the metric (nearest-point) projection onto `K`. mathlib gives the projection's existence
-- and variational inequality but not a packaged continuous map, so we build it here (cornerstone 1).

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import VRCycle.Brouwer.Fixed

/-!
# Cornerstone 1 — the metric projection onto a convex set

For a nonempty complete convex set `K` in a real inner product space, the nearest-point projection
`projConvex K` is a `1`-Lipschitz (hence continuous) retraction onto `K`. Built from the Hilbert
projection theorem (`exists_norm_eq_iInf_of_complete_convex`) and its variational characterization.
-/

namespace Brouwer.Convex

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {K : Set F} (hne : K.Nonempty) (hcl : IsComplete K) (hcv : Convex ℝ K)

/-- The nearest point of `K` to `u` (metric projection onto a nonempty complete convex set). -/
noncomputable def projConvex (u : F) : F :=
  (exists_norm_eq_iInf_of_complete_convex hne hcl hcv u).choose

theorem projConvex_mem (u : F) : projConvex hne hcl hcv u ∈ K :=
  (exists_norm_eq_iInf_of_complete_convex hne hcl hcv u).choose_spec.1

/-- The projection achieves the infimal distance from `u` to `K`. -/
theorem projConvex_norm_eq_iInf (u : F) :
    ‖u - projConvex hne hcl hcv u‖ = ⨅ w : K, ‖u - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hcl hcv u).choose_spec.2

/-- The defining variational inequality of the projection. -/
theorem projConvex_inner_le (u : F) {w : F} (hw : w ∈ K) :
    ⟪u - projConvex hne hcl hcv u, w - projConvex hne hcl hcv u⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hcv (projConvex_mem hne hcl hcv u)).mp
    (projConvex_norm_eq_iInf hne hcl hcv u) w hw

/-- The projection fixes the points of `K`. -/
theorem projConvex_eq_self {x : F} (hx : x ∈ K) : projConvex hne hcl hcv x = x := by
  have h := projConvex_inner_le hne hcl hcv x hx
  rw [real_inner_self_eq_norm_sq] at h
  have hz : ‖x - projConvex hne hcl hcv x‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  rw [pow_eq_zero_iff (by norm_num), norm_eq_zero, sub_eq_zero] at hz
  exact hz.symm

/-- The projection is `1`-Lipschitz: the two variational inequalities give
`‖v₁ - v₂‖² ≤ ⟪u₁ - u₂, v₁ - v₂⟫ ≤ ‖u₁ - u₂‖ · ‖v₁ - v₂‖`. -/
theorem projConvex_norm_sub_le (u₁ u₂ : F) :
    ‖projConvex hne hcl hcv u₁ - projConvex hne hcl hcv u₂‖ ≤ ‖u₁ - u₂‖ := by
  set v₁ := projConvex hne hcl hcv u₁ with hv₁
  set v₂ := projConvex hne hcl hcv u₂ with hv₂
  have e1 : 0 ≤ ⟪u₁ - v₁, v₁ - v₂⟫_ℝ := by
    have h := projConvex_inner_le hne hcl hcv u₁ (hv₂ ▸ projConvex_mem hne hcl hcv u₂)
    rw [← neg_sub v₁ v₂, inner_neg_right] at h; linarith
  have e2 : ⟪u₂ - v₂, v₁ - v₂⟫_ℝ ≤ 0 :=
    projConvex_inner_le hne hcl hcv u₂ (hv₁ ▸ projConvex_mem hne hcl hcv u₁)
  have expand : ⟪u₁ - u₂, v₁ - v₂⟫_ℝ
      = ⟪u₁ - v₁, v₁ - v₂⟫_ℝ - ⟪u₂ - v₂, v₁ - v₂⟫_ℝ + ⟪v₁ - v₂, v₁ - v₂⟫_ℝ := by
    rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
  have hkey : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫_ℝ := by
    rw [expand, ← real_inner_self_eq_norm_sq]; linarith
  have hcs : ⟪u₁ - u₂, v₁ - v₂⟫_ℝ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (v₁ - v₂)) with h0 | h0
  · simp [← h0]
  · have hsq : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by nlinarith [le_trans hkey hcs]
    exact le_of_mul_le_mul_right hsq h0

/-- The projection onto a nonempty complete convex set is continuous. -/
theorem continuous_projConvex : Continuous (projConvex hne hcl hcv) := by
  refine LipschitzWith.continuous (K := 1) ?_
  intro u₁ u₂
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  have h := projConvex_norm_sub_le hne hcl hcv u₁ u₂
  simp only [ENNReal.coe_one, one_mul]
  exact_mod_cast ENNReal.ofReal_le_ofReal h

/-! ### Cornerstone 2 — Brouwer for the corner simplex

The standard simplex `stdSimplex ℝ (Fin (n+1))` is carried to the full-dimensional **corner
simplex** `{x : EuclideanSpace ℝ (Fin n) | xᵢ ≥ 0, ∑ ≤ 1}` by dropping the last coordinate
(`dropToCorner`), with inverse "append `1 - ∑`" (`extendFromCorner`). Conjugating a self-map of the
corner simplex through these gives a self-map of the standard simplex; its Brouwer fixed point maps
back to a fixed point of the original. -/

variable {n : ℕ}

/-- The unit corner simplex in Euclidean `ℝⁿ`. -/
def cornerSimplex (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Drop the last coordinate: `stdSimplex (Fin (n+1)) → cornerSimplex n`. -/
noncomputable def dropToCorner (y : Fin (n + 1) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => y i.castSucc)

@[simp] theorem dropToCorner_apply (y : Fin (n + 1) → ℝ) (i : Fin n) :
    dropToCorner y i = y i.castSucc := rfl

/-- Append `1 - ∑`: `cornerSimplex n → stdSimplex (Fin (n+1))`. -/
noncomputable def extendFromCorner (x : EuclideanSpace ℝ (Fin n)) : Fin (n + 1) → ℝ :=
  fun j => if h : j = Fin.last n then 1 - ∑ i, x i else x (j.castPred h)

@[simp] theorem extendFromCorner_castSucc (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    extendFromCorner x i.castSucc = x i := by
  rw [extendFromCorner, dif_neg (Fin.castSucc_lt_last i).ne, Fin.castPred_castSucc]

@[simp] theorem extendFromCorner_last (x : EuclideanSpace ℝ (Fin n)) :
    extendFromCorner x (Fin.last n) = 1 - ∑ i, x i := by rw [extendFromCorner, dif_pos rfl]

/-- Dropping the last coordinate is continuous. -/
theorem continuous_dropToCorner : Continuous (dropToCorner (n := n)) := by
  unfold dropToCorner
  fun_prop

/-- Coordinate access on Euclidean space is continuous. -/
theorem continuous_coord (i : Fin n) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
  (continuous_apply i).comp (EuclideanSpace.equiv (Fin n) ℝ).continuous

/-- Appending the `1 - ∑` coordinate is continuous. -/
theorem continuous_extendFromCorner : Continuous (extendFromCorner (n := n)) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · simp only [extendFromCorner, dif_pos hj]
    exact continuous_const.sub (continuous_finset_sum _ fun i _ => continuous_coord i)
  · simp only [extendFromCorner, dif_neg hj]
    exact continuous_coord _

/-- `dropToCorner ∘ extendFromCorner = id`. -/
theorem dropToCorner_extendFromCorner (x : EuclideanSpace ℝ (Fin n)) :
    dropToCorner (extendFromCorner x) = x := by
  apply (EuclideanSpace.equiv (Fin n) ℝ).injective
  funext i
  simp

/-- `dropToCorner` carries the standard simplex into the corner simplex. -/
theorem dropToCorner_mem {y : Fin (n + 1) → ℝ} (hy : y ∈ stdSimplex ℝ (Fin (n + 1))) :
    dropToCorner y ∈ cornerSimplex n := by
  refine ⟨fun i => by simpa using hy.1 i.castSucc, ?_⟩
  have : ∑ i, dropToCorner y i = (∑ j, y j) - y (Fin.last n) := by
    simp only [dropToCorner_apply]; rw [Fin.sum_univ_castSucc]; ring
  rw [this, hy.2]; linarith [hy.1 (Fin.last n)]

/-- `extendFromCorner` carries the corner simplex into the standard simplex. -/
theorem extendFromCorner_mem {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cornerSimplex n) :
    extendFromCorner x ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases hj : j = Fin.last n
    · simp only [hj, extendFromCorner_last]; linarith [hx.2]
    · rw [extendFromCorner, dif_neg hj]; exact hx.1 _
  · rw [Fin.sum_univ_castSucc]; simp only [extendFromCorner_castSucc, extendFromCorner_last]; ring

/-- **Cornerstone 2 — Brouwer for the corner simplex.** A continuous self-map of `cornerSimplex n`
has a fixed point, by conjugating through `dropToCorner`/`extendFromCorner` to the standard
simplex. -/
theorem brouwer_cornerSimplex (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : Continuous g) (hmaps : Set.MapsTo g (cornerSimplex n) (cornerSimplex n)) :
    ∃ x ∈ cornerSimplex n, g x = x := by
  set f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun y => extendFromCorner (g (dropToCorner y))
    with hf
  have hf_cont : Continuous f :=
    continuous_extendFromCorner.comp (hg.comp continuous_dropToCorner)
  have hf_maps : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1))) :=
    fun y hy => extendFromCorner_mem (hmaps (dropToCorner_mem hy))
  obtain ⟨y, hy_mem, hy_fix⟩ := Brouwer.KuhnGen.brouwer_stdSimplex_all f hf_cont hf_maps
  refine ⟨dropToCorner y, dropToCorner_mem hy_mem, ?_⟩
  have : dropToCorner (f y) = dropToCorner y := by rw [hy_fix]
  rwa [hf, dropToCorner_extendFromCorner] at this

/-! ### The general theorem — Brouwer for a nonempty compact convex set

An affine map `ψ x = a • (x + M • 1)` (with `M` a coordinate bound from compactness and `a` small)
fits a copy `K' = ψ '' K` inside the corner simplex. Projecting the corner simplex onto `K'` and
conjugating `f` by `ψ` gives a self-map of the corner simplex whose Brouwer fixed point (which lands
in `K'`, where the projection is the identity) pulls back to a fixed point of `f` in `K`. -/

/-- **BROUWER'S FIXED-POINT THEOREM (compact convex form).** Every continuous self-map of a nonempty
compact convex subset of Euclidean `ℝⁿ` has a fixed point. -/
theorem brouwer_compact_convex {K : Set (EuclideanSpace ℝ (Fin n))} (hKne : K.Nonempty)
    (hKc : IsCompact K) (hKcv : Convex ℝ K)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : Continuous f) (hmaps : Set.MapsTo f K K) : ∃ x ∈ K, f x = x := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    obtain ⟨x, hx⟩ := hKne
    exact ⟨x, hx, Subsingleton.elim _ _⟩
  -- coordinate bound `M ≥ 1` on `K`
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  set M : ℝ := max R 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hbound : ∀ x ∈ K, ∀ i, |x i| ≤ M := fun x hx i =>
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := PiLp.norm_apply_le x i
      _ ≤ R := by have := hR hx; rwa [Metric.mem_closedBall, dist_zero_right] at this
      _ ≤ M := le_max_left _ _
  -- the affine map and its inverse
  set a : ℝ := 1 / (2 * n * (M + 1)) with hadef
  have hapos : 0 < a := by rw [hadef]; positivity
  set one : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => 1) with hone
  have hone_i : ∀ i, one i = 1 := fun i => rfl
  set ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => a • (x + M • one) with hψ
  set ψinv : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => a⁻¹ • y - M • one
    with hψinv
  have hψ_i : ∀ x i, ψ x i = a * (x i + M) := by
    intro x i
    simp only [hψ, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, hone_i, mul_one]
  have hψinv_ψ : ∀ x, ψinv (ψ x) = x := fun x => by
    simp only [hψ, hψinv, smul_smul, inv_mul_cancel₀ hapos.ne', one_smul]; abel
  have hcont_ψ : Continuous ψ := by rw [hψ]; fun_prop
  have hcont_ψinv : Continuous ψinv := by rw [hψinv]; fun_prop
  -- `ψ '' K ⊆ cornerSimplex`
  have hψK_sub : ψ '' K ⊆ cornerSimplex n := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · rw [hψ_i]
      exact mul_nonneg hapos.le (by linarith [(abs_le.mp (hbound x hx i)).1])
    · have hsum : ∑ i, ψ x i = a * ((∑ i, x i) + n * M) := by
        rw [show (∑ i, ψ x i) = ∑ i, a * (x i + M) from
            Finset.sum_congr rfl fun i _ => hψ_i x i,
          ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      have hxsum : ∑ i, x i ≤ n * M := by
        calc ∑ i, x i ≤ ∑ i, |x i| := Finset.sum_le_sum fun i _ => le_abs_self _
          _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hbound x hx i
          _ = n * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [hsum, hadef, div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith [hxsum, hM1, hnpos]
  -- `K' = ψ '' K` is nonempty, compact, convex
  set K' := ψ '' K with hK'
  have hK'ne : K'.Nonempty := hKne.image ψ
  have hK'c : IsCompact K' := hKc.image hcont_ψ
  have hK'cv : Convex ℝ K' := by
    rw [hK']
    rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ s t hs ht hst
    refine ⟨s • x₁ + t • x₂, hKcv hx₁ hx₂ hs ht hst, ?_⟩
    have hts : t = 1 - s := by linarith
    subst hts
    simp only [hψ, smul_add, smul_smul]
    module
  have hψinv_mem : ∀ z ∈ K', ψinv z ∈ K := by rintro _ ⟨x, hx, rfl⟩; rw [hψinv_ψ]; exact hx
  -- the retraction and the conjugated self-map of the corner simplex
  set r := projConvex hK'ne hK'c.isComplete hK'cv with hr
  set G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => ψ (f (ψinv (r y)))
    with hG
  have hG_maps : Set.MapsTo G (cornerSimplex n) (cornerSimplex n) := fun y _ =>
    hψK_sub ⟨_, hmaps (hψinv_mem _ (projConvex_mem hK'ne hK'c.isComplete hK'cv y)), rfl⟩
  have hG_cont : Continuous G :=
    hcont_ψ.comp (hf.comp (hcont_ψinv.comp (continuous_projConvex hK'ne hK'c.isComplete hK'cv)))
  obtain ⟨y₀, hy₀_corner, hy₀_fix⟩ := brouwer_cornerSimplex G hG_cont hG_maps
  -- `G y₀ ∈ K'`, and `G y₀ = y₀`, so `y₀ ∈ K'`; the projection then fixes it.
  have hGy₀K' : G y₀ ∈ K' :=
    ⟨_, hmaps (hψinv_mem _ (projConvex_mem hK'ne hK'c.isComplete hK'cv y₀)), rfl⟩
  have hy₀K' : y₀ ∈ K' := hy₀_fix ▸ hGy₀K'
  refine ⟨ψinv y₀, hψinv_mem _ hy₀K', ?_⟩
  have hr0 : r y₀ = y₀ := projConvex_eq_self hK'ne hK'c.isComplete hK'cv hy₀K'
  have hGval : ψ (f (ψinv y₀)) = y₀ := by
    have h := hy₀_fix; simp only [hG] at h; rwa [hr0] at h
  have h := congrArg ψinv hGval
  rwa [hψinv_ψ] at h

end Brouwer.Convex
