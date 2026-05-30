-- VR-Brouwer — Stage 3 (decision C): the approximate fixed point.
-- Bridges the combinatorial Sperner lemma (`KuhnGen.exists_rainbow_cell`) to a continuous
-- self-map of the standard simplex. A self-map `f : Δ → Δ` induces a Sperner labeling of the
-- resolution-`k` grid (colour a vertex by a coordinate that does not increase); a rainbow cell
-- is then an approximate fixed point — its `n+1` vertices lie within `1/k` and, between them,
-- witness `f(y)ᵢ ≤ yᵢ` for every coordinate `i`. Tier-3 absolute (ℝ); differential witness
-- clean: this file evaluates `f` pointwise but NEVER uses continuity or `tendsto_subseq` — the
-- limit/extraction is deferred to Stage 4.

import VRCycle.Brouwer.Grid
import VRCycle.Brouwer.KuhnGen

/-!
# Stage 3 — approximate fixed point of a simplex self-map

For `f : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ)` mapping the standard simplex into itself, the key
pointwise fact `exists_coord_le` says some positive coordinate of `x` is not increased by `f`
(the coordinate-sum argument: `∑ f x = ∑ x = 1`). This is the Sperner labeling rule.
-/

namespace Brouwer.KuhnGen

open Finset

variable {n : ℕ}

/-- **The Sperner labeling rule (pointwise).** If `x` and `f x` both lie in the standard simplex,
some coordinate `i` with `xᵢ > 0` is *not increased* by `f` (`f x i ≤ x i`). Proof: `∑ (f x - x) =
0`, yet if every positive coordinate strictly increased the sum would be `> 0`. -/
theorem exists_coord_le (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (x : Fin (n + 1) → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin (n + 1))) (hfx : f x ∈ stdSimplex ℝ (Fin (n + 1))) :
    ∃ i, 0 < x i ∧ f x i ≤ x i := by
  obtain ⟨hnn_x, hsum_x⟩ := hx
  obtain ⟨hnn_fx, hsum_fx⟩ := hfx
  by_contra hcon
  have hcon' : ∀ i, 0 < x i → x i < f x i := fun i hi =>
    not_le.mp fun h => hcon ⟨i, hi, h⟩
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ f x i - x i := by
    intro i _
    rcases (hnn_x i).lt_or_eq with h | h
    · exact le_of_lt (sub_pos.mpr (hcon' i h))
    · rw [← h, sub_zero]; exact hnn_fx i
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < x i := by
    by_contra hno
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), x i ≤ 0 :=
      fun i _ => not_lt.mp fun h => hno ⟨i, h⟩
    have h0 : ∑ i, x i ≤ 0 := Finset.sum_nonpos hle
    rw [hsum_x] at h0; linarith
  have hpos : 0 < ∑ i, (f x i - x i) :=
    Finset.sum_pos' hterm ⟨i₀, Finset.mem_univ _, sub_pos.mpr (hcon' i₀ hi₀)⟩
  have hzero : ∑ i, (f x i - x i) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_fx, hsum_x, sub_self]
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- Realize an integer grid vector at resolution `k` as a real point (`wᵢ / k`). -/
noncomputable def realize (k : ℕ) (w : Fin (n + 1) → ℤ) : Fin (n + 1) → ℝ :=
  fun i => (w i : ℝ) / k

/-- A positive coordinate of the realization corresponds to a positive grid coordinate. -/
theorem realize_pos_iff (k : ℕ) (hk : 0 < k) (w : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    0 < realize k w i ↔ 0 < w i := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold realize
  rw [lt_div_iff₀ hkr, zero_mul, Int.cast_pos]

/-- A nonnegative grid vector summing to `k` realizes to a point of the standard simplex. -/
theorem realize_mem (k : ℕ) (hk : 0 < k) (w : Fin (n + 1) → ℤ) (hnn : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = (k : ℤ)) : realize k w ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨fun i => div_nonneg (by exact_mod_cast hnn i) (by positivity), ?_⟩
  unfold realize
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Int.cast_sum, hsum, Int.cast_natCast]
  exact mul_inv_cancel₀ (by exact_mod_cast hk.ne')

/-- **The Sperner coloring induced by `f`.** Colour a grid vector by a positive coordinate that `f`
does not increase (the labeling rule of `exists_coord_le`); fall back to any positive coordinate
when the decrease witness is unavailable (only off the genuine grid). Total and admissible. -/
noncomputable def spernerColoring (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ)
    (w : Fin (n + 1) → ℤ) : Fin (n + 1) :=
  if h : ∃ i, 0 < w i ∧ f (realize k w) i ≤ realize k w i then h.choose
  else if h2 : ∃ i, 0 < w i then h2.choose
  else 0

/-- The chosen colour always sits at a positive coordinate (when the vector has positive sum). -/
theorem spernerColoring_pos (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ)
    (w : Fin (n + 1) → ℤ) (hsum : 0 < ∑ j, w j) : 0 < w (spernerColoring f k w) := by
  have hex2 : ∃ i, 0 < w i := by
    by_contra hno
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), w i ≤ 0 :=
      fun i _ => not_lt.mp fun h => hno ⟨i, h⟩
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos hle))
  unfold spernerColoring
  by_cases h : ∃ i, 0 < w i ∧ f (realize k w) i ≤ realize k w i
  · rw [dif_pos h]; exact h.choose_spec.1
  · rw [dif_neg h, dif_pos hex2]; exact hex2.choose_spec

/-- **The induced coloring is Sperner-admissible.** -/
theorem spernerColoring_admissible (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ) :
    SpernerAdmissible (spernerColoring f k) := by
  intro w i hsum hwi hcontra
  have hp := spernerColoring_pos f k w hsum
  rw [hcontra, hwi] at hp
  exact lt_irrefl 0 hp

/-- **The labeling property.** When the decrease witness exists (always, on a genuine grid point —
see `exists_coord_le`), the colour `i = spernerColoring f k w` satisfies `f(realize w)ᵢ ≤
realize wᵢ`: `f` does not increase the coordinate it labels. -/
theorem spernerColoring_decrease (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (k : ℕ)
    (w : Fin (n + 1) → ℤ)
    (hdec : ∃ i, 0 < w i ∧ f (realize k w) i ≤ realize k w i) :
    f (realize k w) (spernerColoring f k w) ≤ realize k w (spernerColoring f k w) := by
  unfold spernerColoring
  rw [dif_pos hdec]
  exact hdec.choose_spec.2

variable {k : ℕ}

/-- A valid cell vertex realizes to a point of the standard simplex. -/
theorem vertex_realize_mem (C : KCell n k) (hC : Valid C) (hk : 0 < k) (j : Fin (n + 1)) :
    realize k (vertex C j) ∈ stdSimplex ℝ (Fin (n + 1)) :=
  realize_mem k hk (vertex C j) (fun i => hC j i) (sum_vertex C j)

/-- **The geometric labeling property.** The colour assigned to a valid cell vertex is a coordinate
that `f` does not increase at that vertex's realization. Combines `exists_coord_le` (the witness
exists: the realization lies in `Δ`, and `f` maps `Δ` into `Δ`) with `spernerColoring_decrease`. -/
theorem rainbow_vertex_decrease (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hf : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1)))) (hk : 0 < k)
    (C : KCell n k) (hC : Valid C) (j : Fin (n + 1)) :
    f (realize k (vertex C j)) (spernerColoring f k (vertex C j))
      ≤ realize k (vertex C j) (spernerColoring f k (vertex C j)) := by
  apply spernerColoring_decrease
  have hmem := vertex_realize_mem C hC hk j
  obtain ⟨i, hi_pos, hi_le⟩ := exists_coord_le f (realize k (vertex C j)) hmem (hf hmem)
  exact ⟨i, (realize_pos_iff k hk (vertex C j) i).mp hi_pos, hi_le⟩

/-! ### Cell diameter (mesh `≤ 2/k`)

A coordinate of any cell vertex differs from the base by at most `1`: along the move-ordering, a
fixed coordinate is incremented by at most one move (`σ l = a.castPred`) and decremented by at most
one move (`σ l = a.pred`), since `σ` is injective. Hence any two vertices differ by `≤ 2` in each
coordinate, and realize to points within `2/k`. -/

/-- A block-sum of moves changes a fixed coordinate by at most `1` in absolute value: the
incrementing and decrementing moves are each unique (`σ` injective). -/
theorem abs_sum_block_move_le {m : ℕ} (σ : Equiv.Perm (Fin m)) (S : Finset (Fin m))
    (a : Fin (m + 1)) : |∑ l ∈ S, move (σ l) a| ≤ 1 := by
  have key : ∑ l ∈ S, move (σ l) a
      = ((S.filter (fun l => a = (σ l).castSucc)).card : ℤ)
        - ((S.filter (fun l => a = (σ l).succ)).card : ℤ) := by
    simp only [move, Finset.sum_sub_distrib, Finset.sum_boole]
  have hle1 : (S.filter (fun l => a = (σ l).castSucc)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro l1 h1 l2 h2
    rw [Finset.mem_filter] at h1 h2
    exact σ.injective (Fin.castSucc_injective _ (h1.2.symm.trans h2.2))
  have hle2 : (S.filter (fun l => a = (σ l).succ)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro l1 h1 l2 h2
    rw [Finset.mem_filter] at h1 h2
    exact σ.injective (Fin.succ_injective _ (h1.2.symm.trans h2.2))
  rw [key, abs_le]
  omega

/-- Each coordinate of a cell vertex differs from the base by at most `1`. -/
theorem abs_vertex_sub_base_le (C : KCell n k) (j a : Fin (n + 1)) :
    |vertex C j a - (C.base a : ℤ)| ≤ 1 := by
  have he : vertex C j a - (C.base a : ℤ)
      = ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (j : ℕ)), move (C.order l) a := by
    unfold vertex; ring
  rw [he]; exact abs_sum_block_move_le C.order _ a

/-- Any two cell vertices differ by at most `2` in each coordinate (triangle through the base). -/
theorem abs_vertex_sub_vertex_le (C : KCell n k) (j j' a : Fin (n + 1)) :
    |vertex C j a - vertex C j' a| ≤ 2 := by
  have h1 := abs_vertex_sub_base_le C j a
  have h2 := abs_vertex_sub_base_le C j' a
  rw [abs_le] at h1 h2 ⊢
  omega

/-- Grid vectors differing by `≤ 2` per coordinate realize to points within `2/k`. -/
theorem dist_realize_le (hk : 0 < k) (w w' : Fin (n + 1) → ℤ) (h : ∀ a, |w a - w' a| ≤ 2) :
    dist (realize k w) (realize k w') ≤ 2 / k := by
  rw [dist_pi_le_iff (by positivity)]
  intro a
  rw [Real.dist_eq]
  unfold realize
  rw [div_sub_div_same, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
  gcongr
  rw [← Int.cast_sub, ← Int.cast_abs]
  exact_mod_cast h a

/-- **STAGE 3 — the approximate fixed point.** For a continuous-free, merely `Δ → Δ` self-map `f`
and any resolution `k > 0`, there is a family `y : Fin (n+1) → Δ` (one point per colour, the
realized vertices of a rainbow Kuhn cell) such that for every coordinate `i`, `f (y i) i ≤ y i i`,
and all the points lie within `2/k` of each other. As `k → ∞` (Stage 4) the points coalesce to a
single exact fixed point. This file uses `f` only pointwise — no continuity, no `tendsto_subseq`. -/
theorem exists_approx_fixed (f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (hf : Set.MapsTo f (stdSimplex ℝ (Fin (n + 1))) (stdSimplex ℝ (Fin (n + 1))))
    (hn : 1 ≤ n) (hk : 0 < k) :
    ∃ y : Fin (n + 1) → (Fin (n + 1) → ℝ),
      (∀ i, y i ∈ stdSimplex ℝ (Fin (n + 1))) ∧
      (∀ i, f (y i) i ≤ y i i) ∧
      (∀ i i', dist (y i) (y i') ≤ 2 / k) := by
  obtain ⟨C, hCmem, hrain⟩ := exists_rainbow_cell (k := k) n hn (spernerColoring f k)
    (spernerColoring_admissible f k) hk
  have hCv : Valid C := (Finset.mem_filter.mp hCmem).2
  choose jj hjj using fun i => hrain.surjective i
  refine ⟨fun i => realize k (vertex C (jj i)), fun i => vertex_realize_mem C hCv hk (jj i),
    fun i => ?_, fun i i' => ?_⟩
  · have hd := rainbow_vertex_decrease f hf hk C hCv (jj i)
    have he : spernerColoring f k (vertex C (jj i)) = i := hjj i
    rwa [he] at hd
  · exact dist_realize_le hk _ _ fun a => abs_vertex_sub_vertex_le C (jj i) (jj i') a

end Brouwer.KuhnGen
