-- VR-Brouwer — Stage 2 (decision C): grid realization for the Kuhn–Freudenthal model.
-- Lattice points of `k · stdSimplex` map to real points of `stdSimplex ℝ (Fin (n+1))`;
-- the per-step mesh is `≤ 1/k` (→ 0), which is why the grid model makes the barycentric
-- iteration (Stage 1b) unnecessary. Tier-3 absolute (ℝ); differential witness clean
-- (no `IsCompact.tendsto_subseq`, no `Classical` in source).

import Mathlib.Analysis.Convex.StdSimplex

/-!
# Grid realization for the Kuhn–Freudenthal Sperner model (Stage 2)

A grid vertex at resolution `k` is `v : Fin (n+1) → ℕ` with `∑ i, v i = k` (a lattice point
of `k · stdSimplex`); it realizes to the point `gridToSimplex k v = (v · / k)` of
`stdSimplex ℝ (Fin (n+1))`. The mesh lemma `dist_gridToSimplex_le` shows that grid points
whose integer coordinates differ by at most `1` are within `1/k` in the sup metric — the
contraction that the Kuhn cells will inherit, giving mesh `→ 0` for free (no barycentric
subdivision of arbitrary simplices needed).

The Kuhn order-simplex cells, the door-counting handshake, and the dimension induction are the
remaining Stage-2 work (see stage report).
-/

namespace Brouwer

open Finset

variable {n : ℕ}

/-- The real point of `stdSimplex ℝ (Fin (n+1))` realized by an integer grid vector `v` at
resolution `k`: the coordinatewise quotient `v i / k`. -/
noncomputable def gridToSimplex (k : ℕ) (v : Fin (n + 1) → ℕ) : Fin (n + 1) → ℝ :=
  fun i => (v i : ℝ) / k

/-- A grid vector summing to `k` (`k > 0`) realizes to a point of the standard simplex. -/
theorem gridToSimplex_mem_stdSimplex {k : ℕ} (hk : 0 < k) {v : Fin (n + 1) → ℕ}
    (hv : ∑ i, v i = k) : gridToSimplex k v ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  unfold gridToSimplex
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hv]
  exact mul_inv_cancel₀ (by exact_mod_cast hk.ne')

/-- **Grid mesh.** Two grid vectors whose integer coordinates differ by at most `1`
realize to points within `1/k` in the sup metric. The Kuhn cells satisfy this hypothesis,
so the grid mesh is `≤ 1/k → 0` — no barycentric iteration needed. -/
theorem dist_gridToSimplex_le {k : ℕ} (hk : 0 < k) {v w : Fin (n + 1) → ℕ}
    (h : ∀ i, |(v i : ℝ) - (w i : ℝ)| ≤ 1) :
    dist (gridToSimplex k v) (gridToSimplex k w) ≤ 1 / k := by
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq]
  unfold gridToSimplex
  rw [div_sub_div_same, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
  gcongr
  exact h i

end Brouwer
