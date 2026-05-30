-- VR-Brouwer — Stage 4 (decision C): the EXACT Brouwer fixed-point theorem (CLASSICAL layer).
-- The limit of the Stage-3 approximate fixed points. This is the ONE place `Classical.choice`
-- enters meaningfully (the subsequence extraction `IsCompact.tendsto_subseq`) — the documented
-- constructive↔classical boundary. Continuity of `f` is used here and ONLY here; everything below
-- Stage 3 is continuity-free (the differential witness).

import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import VRCycle.Brouwer.Approx

/-!
# Stage 4 — exact Brouwer via the limit

For a *continuous* self-map `f` of the standard simplex, the approximate fixed points
(`exists_approx_fixed`) at resolution `k = m+1` form a sequence in the compact simplex. A
convergent subsequence (the `Classical` extraction) limits to a point `x*`; continuity plus the
mesh `→ 0` forces `f x* i ≤ x* i` for every coordinate, and the equal coordinate sums upgrade this
to `f x* = x*`.
-/

namespace Brouwer.KuhnGen

open Finset Filter Topology

variable {n : ℕ}

/-- **Brouwer's fixed-point theorem (standard simplex form).** A continuous self-map of the
standard simplex `stdSimplex ℝ (Fin (n+1))` (dimension `n ≥ 1`) has a fixed point. The Sperner
route: approximate fixed points at every grid resolution (Stage 3) accumulate, via a compactness
extraction, at an exact fixed point. -/
theorem brouwer_stdSimplex (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (hf_cont : Continuous f)
    (hf : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1)))) (hn : 1 ≤ n) :
    ∃ x ∈ stdSimplex ℝ (Fin (n + 1)), f x = x := by
  -- Stage-3 approximate fixed points at resolution `m+1`.
  choose Y hYmem hYdec hYmesh using fun m : ℕ =>
    exists_approx_fixed (k := m + 1) f hf hn (Nat.succ_pos m)
  -- Compactness extracts a convergent subsequence of base points.
  obtain ⟨xstar, hxmem, φ, hφ, hφtend⟩ :=
    (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin (n + 1))).tendsto_subseq (fun m => hYmem m 0)
  refine ⟨xstar, hxmem, ?_⟩
  -- The mesh bound along the subsequence tends to `0`.
  have hmesh0 : Tendsto (fun m => (2 : ℝ) / ((φ m : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => (1 : ℝ) / ((φ m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    simpa [mul_one_div] using h1.const_mul (2 : ℝ)
  -- Every coordinate's witness converges to `x*` (mesh `→ 0` + base `→ x*`).
  have hconv : ∀ i, Tendsto (fun m => Y (φ m) i) atTop (𝓝 xstar) := by
    intro i
    refine tendsto_of_tendsto_of_dist hφtend ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => 0)
      (h := fun m => (2 : ℝ) / ((φ m : ℝ) + 1)) tendsto_const_nhds hmesh0
      (fun _ => dist_nonneg) (fun m => ?_)
    have h := hYmesh (φ m) 0 i
    rwa [Nat.cast_add, Nat.cast_one] at h
  -- Pass `f (Y (φ m) i) i ≤ Y (φ m) i i` to the limit.
  have hle : ∀ i, f xstar i ≤ xstar i := by
    intro i
    have hfi : Tendsto (fun m => f (Y (φ m) i) i) atTop (𝓝 (f xstar i)) :=
      tendsto_pi_nhds.mp ((hf_cont.tendsto xstar).comp (hconv i)) i
    have hxi : Tendsto (fun m => Y (φ m) i i) atTop (𝓝 (xstar i)) :=
      tendsto_pi_nhds.mp (hconv i) i
    exact le_of_tendsto_of_tendsto' hfi hxi (fun m => hYdec (φ m) i)
  -- Equal coordinate sums upgrade `≤` to `=`.
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ xstar i - f xstar i :=
    fun i _ => sub_nonneg.mpr (hle i)
  have hsum0 : ∑ i, (xstar i - f xstar i) = 0 := by
    rw [Finset.sum_sub_distrib, hxmem.2, (hf hxmem).2, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hg).mp hsum0
  funext i
  exact (sub_eq_zero.mp (hzero i (Finset.mem_univ i))).symm

/-- The `0`-dimensional standard simplex is a single point (`fun _ => 1`). -/
theorem stdSimplex_fin_one_unique {x : Fin 1 → ℝ} (hx : x ∈ stdSimplex ℝ (Fin 1)) :
    x = fun _ => 1 := by
  funext i
  have h := hx.2
  rw [Fin.sum_univ_one] at h
  fin_cases i; exact h

/-- **Brouwer's fixed-point theorem (all dimensions).** A continuous self-map of
`stdSimplex ℝ (Fin (n+1))` has a fixed point — for every `n`, including the degenerate point
`n = 0`. (For `n ≥ 1` this is `brouwer_stdSimplex`; for `n = 0` the simplex is a single point.) -/
theorem brouwer_stdSimplex_all (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hf_cont : Continuous f)
    (hf : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1)))) :
    ∃ x ∈ stdSimplex ℝ (Fin (n + 1)), f x = x := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hmem : (fun _ => (1 : ℝ)) ∈ stdSimplex ℝ (Fin 1) :=
      ⟨fun _ => zero_le_one, by simp⟩
    exact ⟨fun _ => 1, hmem, stdSimplex_fin_one_unique (hf hmem)⟩
  · exact brouwer_stdSimplex f hf_cont hf hn

end Brouwer.KuhnGen
