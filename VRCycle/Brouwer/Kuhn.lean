-- VR-Brouwer — Stage 2 (decision C): geometric Kuhn glue, n = 2 seam.
-- Connects the verified ingredients (odd_doors, handshake_parity, Grid) to the concrete
-- grid triangulation. This file: seam fact (a) — rainbow ⇔ odd door count per cell — the
-- combinatorial "room-degree ⇔ rainbow" link for `handshake_parity`. Pseudomanifold (b) and
-- the boundary recursion (c) are the remaining geometric work (see stage report).
-- Pure combinatorics; absolute Tier-3 from substrate, differential witness clean.

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import VRCycle.Brouwer.Grid
import VRCycle.Brouwer.Sperner

/-!
# Kuhn–Freudenthal Sperner — the n = 2 seam, fact (a)

For a triangle whose three vertices carry colors in `Fin 3`, the number of `{0,1}`-colored
edges ("doors") is odd iff the triangle is **rainbow** (all three colors distinct). This is the
"odd room degree ⇔ rainbow cell" link consumed by `Brouwer.Handshake.handshake_parity`. It is a
finite fact, settled by `decide` over the `3³` colorings.
-/

namespace Brouwer.Kuhn

/-- An edge with endpoint colors `a, b : Fin 3` is a `{0,1}`-door: its two colors are `0` and
`1` (in either order). -/
def isDoor (a b : Fin 3) : Bool := (a = 0 && b = 1) || (a = 1 && b = 0)

/-- The number of `{0,1}`-doors among the three edges of a triangle with vertex colors
`x, y, z`. -/
def triDoorCount (x y z : Fin 3) : ℕ :=
  (if isDoor x y then 1 else 0) + (if isDoor y z then 1 else 0) + (if isDoor x z then 1 else 0)

/-- A triangle is *rainbow* when its three vertex colors are pairwise distinct (hence
`{0,1,2}`). -/
def Rainbow (x y z : Fin 3) : Prop := x ≠ y ∧ y ≠ z ∧ x ≠ z

instance (x y z : Fin 3) : Decidable (Rainbow x y z) := by unfold Rainbow; infer_instance

/-- **Seam fact (a).** A triangle (with `Fin 3` colors) is rainbow iff its number of
`{0,1}`-doors is odd. This is the room-degree ⇔ rainbow link for the handshake. -/
theorem rainbow_iff_odd_doors :
    ∀ x y z : Fin 3, Rainbow x y z ↔ Odd (triDoorCount x y z) := by decide

/-! ### Grid cells of the 2-simplex (explicit `n = 2` triangulation)

Encoding choice: explicit `n = 2` up/down triangles (NOT the general order-simplex/permutation
form). Reason: the general simplex triangulation carries a correctness risk (a wrong cell set
makes the pseudomanifold property false) that needs a dedicated design pass; the explicit `n = 2`
triangulation is manifestly correct and verifiable now. Consequence: pseudomanifold `(b)` will be
`n = 2`-specific and the `Equiv.Perm` skeleton machinery is not reused here (see stage report).

Triangular coordinates `(i, j)` with `i + j ≤ k` give the grid point `![k-i-j, i, j]` of the
2-simplex at resolution `k`. -/

open Finset

/-- Grid point of the 2-simplex at resolution `k` from triangular coordinates `(i, j)`. -/
def pt (k i j : ℕ) : Fin 3 → ℕ := ![k - i - j, i, j]

/-- A grid point built from in-range triangular coordinates sums to `k` (lands in the grid). -/
theorem sum_pt {k i j : ℕ} (h : i + j ≤ k) : ∑ x, pt k i j x = k := by
  simp only [pt, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  omega

/-- The three vertices of the *up* triangle at `(i, j)`. -/
def upCell (k i j : ℕ) : Finset (Fin 3 → ℕ) := {pt k i j, pt k (i + 1) j, pt k i (j + 1)}

/-- The three vertices of the *down* triangle at `(i, j)`. -/
def downCell (k i j : ℕ) : Finset (Fin 3 → ℕ) :=
  {pt k (i + 1) j, pt k i (j + 1), pt k (i + 1) (j + 1)}

/-- Every vertex of an up-cell (with `i + j < k`) lands in the grid (`∑ = k`). -/
theorem upCell_mem_grid {k i j : ℕ} (h : i + j < k) :
    ∀ v ∈ upCell k i j, ∑ x, v x = k := by
  intro v hv
  simp only [upCell, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact sum_pt (by omega)
  · exact sum_pt (by omega)
  · exact sum_pt (by omega)

/-- Every vertex of a down-cell (with `i + j + 2 ≤ k`) lands in the grid (`∑ = k`). -/
theorem downCell_mem_grid {k i j : ℕ} (h : i + j + 2 ≤ k) :
    ∀ v ∈ downCell k i j, ∑ x, v x = k := by
  intro v hv
  simp only [downCell, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact sum_pt (by omega)
  · exact sum_pt (by omega)
  · exact sum_pt (by omega)

/-! ### Mesh-link (item 1): cell vertices realize within `1/k`

Two grid points whose integer coordinates differ by at most `1` realize to points within
`1/k` in the sup metric (`Grid.dist_gridToSimplex_le`). The cell vertices satisfy this, so each
cell has mesh `≤ 1/k`. (Orthogonal to the parity seam — this is the Stage-3 ingredient.) -/

/-- Mesh helper: grid points with coordinates differing by `≤ 1` realize within `1/k`. -/
theorem dist_gridPt_le {k : ℕ} (hk : 0 < k) {u v : Fin 3 → ℕ}
    (h : ∀ c, (u c : ℤ) - v c ≤ 1 ∧ (v c : ℤ) - u c ≤ 1) :
    dist (gridToSimplex k u) (gridToSimplex k v) ≤ 1 / k := by
  apply dist_gridToSimplex_le hk
  intro c
  rw [show ((u c : ℝ)) - (v c : ℝ) = (((u c : ℤ) - (v c : ℤ) : ℤ) : ℝ) by push_cast; ring,
    ← Int.cast_abs]
  have hz : |(u c : ℤ) - (v c : ℤ)| ≤ 1 := abs_le.mpr ⟨by linarith [(h c).2], (h c).1⟩
  exact_mod_cast hz

/-- Each up-cell (with `i + j + 1 ≤ k`) has mesh `≤ 1/k`. -/
theorem dist_upCell_le {k i j : ℕ} (hk : 0 < k) (h : i + j + 1 ≤ k) :
    ∀ u ∈ upCell k i j, ∀ v ∈ upCell k i j,
      dist (gridToSimplex k u) (gridToSimplex k v) ≤ 1 / k := by
  intro u hu v hv
  simp only [upCell, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    exact dist_gridPt_le hk (by intro c; fin_cases c <;> simp [pt] <;> omega)

/-! ### Seam fact (c) → `odd_doors`: the triangle boundary carries an odd number of doors

Design-risk check (the stitch the rest of the seam must fit). A Sperner coloring colors each
grid vertex `v` by an index where `v` is nonzero. On the bottom edge (`coord 2 = 0`) colors lie
in `{0,1}` (color `2` is excluded), so the bottom edge is a 1-dimensional Sperner instance: its
two corners are forced to colors `0` and `1`, and `odd_doors` gives an odd number of `{0,1}`
boundary doors. (Boundary `{0,1}`-edges can only occur on this edge: the other two sides exclude
color `0` resp. `1`.) This is the `(c)` endpoint; the incidence/pseudomanifold `(b)` will identify
`#boundary-doors` with this count. -/

variable {k : ℕ} {col : (Fin 3 → ℕ) → Fin 3}

/-- A Sperner (proper) coloring of the resolution-`k` grid: every grid vertex `pt k i j` is
colored by an index at which it is nonzero. -/
def SpernerColoring (k : ℕ) (col : (Fin 3 → ℕ) → Fin 3) : Prop :=
  ∀ i j, i + j ≤ k → pt k i j (col (pt k i j)) ≠ 0

/-- The bottom-edge coloring as a `Bool` (`0 ↦ false`, `1 ↦ true`). -/
def bottomColor (k : ℕ) (col : (Fin 3 → ℕ) → Fin 3) (i : ℕ) : Bool := decide (col (pt k i 0) = 1)

/-- Left corner of the bottom edge is forced to color `0`. -/
theorem corner_left (hk : 0 < k) (hc : SpernerColoring k col) : col (pt k 0 0) = 0 := by
  have h := hc 0 0 (by omega)
  obtain ⟨x, hx⟩ : ∃ x, col (pt k 0 0) = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  fin_cases x <;> simp_all [pt]

/-- Right corner of the bottom edge is forced to color `1`. -/
theorem corner_right (_hk : 0 < k) (hc : SpernerColoring k col) : col (pt k k 0) = 1 := by
  have h := hc k 0 (by omega)
  obtain ⟨x, hx⟩ : ∃ x, col (pt k k 0) = x := ⟨_, rfl⟩
  rw [hx] at h ⊢
  fin_cases x <;> simp_all [pt]

/-- **Seam fact (c) (boundary count).** Under a Sperner coloring, the bottom edge of the triangle
carries an *odd* number of `{0,1}`-doors — the `(c)` endpoint, via the 1-D core `odd_doors`. -/
theorem odd_boundary_doors (hk : 0 < k) (hc : SpernerColoring k col) :
    Odd (Sperner.doors (bottomColor k col) k) := by
  apply Sperner.odd_doors
  · simp [bottomColor, corner_left hk hc]
  · simp [bottomColor, corner_right hk hc]

/-! ### Pseudomanifold (b), local structure: the up/down sharing of an interior edge

The combinatorial heart of `(b)` is that an interior edge is shared by exactly one up- and one
down-triangle. Here is the local "shared by the up/down pair" half: the hypotenuse
`{pt (i+1) j, pt i (j+1)}` is a face of *both* `upCell k i j` and `downCell k i j`. (The full
`(b)` — that the door-degree is *exactly* `2` interior / `1` boundary — additionally needs the
global "no other cell contains this edge" count over the cell `Finset`; see stage report.) -/

/-- The hypotenuse edge is a face of the up-triangle `U(i,j)`. -/
theorem hyp_subset_upCell {k i j : ℕ} :
    ({pt k (i + 1) j, pt k i (j + 1)} : Finset (Fin 3 → ℕ)) ⊆ upCell k i j := by
  intro x hx
  simp only [upCell, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-- The hypotenuse edge is a face of the down-triangle `D(i,j)` — so it is shared by the
up/down pair (the interior-sharing core of pseudomanifold `(b)`). -/
theorem hyp_subset_downCell {k i j : ℕ} :
    ({pt k (i + 1) j, pt k i (j + 1)} : Finset (Fin 3 → ℕ)) ⊆ downCell k i j := by
  intro x hx
  simp only [downCell, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

end Brouwer.Kuhn
