-- VR-Brouwer — Stage 1: combinatorial subdivision skeleton (ℝ-FREE).
-- This file must carry NO ℝ dependency: its declarations live over Fin / Finset /
-- Equiv.Perm only, so `#print axioms` stays `[propext, Quot.sound]` — the
-- *tier-visible* boundary of finding B-1 (CLAUDE.md §5). The real (Tier-3)
-- geometric realization lives separately in `Subdivision.lean`. The ℝ-freeness is
-- enforced structurally here: this file does not import `Mathlib.Analysis.*`.

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Perm

/-!
# Barycentric subdivision skeleton of the standard `n`-simplex (combinatorial, ℝ-free)

The top cells of the (first) barycentric subdivision of the `n`-simplex over
`Fin (n+1)` are indexed by permutations `σ : Equiv.Perm (Fin (n+1))`. The cell `σ`
has as its (combinatorial) vertices the strictly increasing flag of faces
`flagFace σ 0 ⊊ flagFace σ 1 ⊊ … ⊊ flagFace σ (Fin.last n) = univ`,
where `flagFace σ k = σ '' {0,…,k}` has cardinality `k+1`.

Purely combinatorial: the geometric realization (each face ↦ its real barycentre) is
`Brouwer.cellVertex` in `Subdivision.lean`. Designed so Stage 2's Sperner's lemma can
be stated on this skeleton without touching ℝ.
-/

namespace Brouwer.Skeleton

open Finset

variable {n : ℕ}

/-- A top cell of the barycentric subdivision of the `n`-simplex, indexed by a
permutation of the vertex set `Fin (n+1)`. There are `(n+1)!` of them. -/
abbrev Cell (n : ℕ) : Type := Equiv.Perm (Fin (n + 1))

/-- The number of top cells of the barycentric subdivision is `(n+1)!`. -/
theorem card_cell : Fintype.card (Cell n) = (n + 1).factorial := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- The `k`-th face of the flag of the cell `σ`: the image under `σ` of the initial
segment `{0,…,k}` of `Fin (n+1)`. -/
def flagFace (σ : Cell n) (k : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  (Finset.Iic k).image σ

@[simp] theorem flagFace_card (σ : Cell n) (k : Fin (n + 1)) :
    (flagFace σ k).card = (k : ℕ) + 1 := by
  rw [flagFace, Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]

theorem flagFace_nonempty (σ : Cell n) (k : Fin (n + 1)) : (flagFace σ k).Nonempty := by
  rw [← Finset.card_pos, flagFace_card]; omega

/-- The flag is increasing in `k`. -/
theorem flagFace_mono (σ : Cell n) {k l : Fin (n + 1)} (h : k ≤ l) :
    flagFace σ k ⊆ flagFace σ l :=
  Finset.image_subset_image fun _x hx => Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hx).trans h)

/-- The flag is *strictly* increasing in `k`: the chain `{σ 0} ⊊ … ⊊ univ`. -/
theorem flagFace_strictMono (σ : Cell n) {k l : Fin (n + 1)} (h : k < l) :
    flagFace σ k ⊂ flagFace σ l := by
  refine ssubset_of_subset_of_ne (flagFace_mono σ h.le) (fun he => ?_)
  have hc : (flagFace σ k).card = (flagFace σ l).card := by rw [he]
  rw [flagFace_card, flagFace_card] at hc
  have hkl : (k : ℕ) < (l : ℕ) := h
  omega

/-- The top face of the flag is the whole vertex set. -/
@[simp] theorem flagFace_last (σ : Cell n) : flagFace σ (Fin.last n) = univ := by
  rw [flagFace, ← Fin.top_eq_last, Finset.Iic_top, Finset.image_univ_equiv]

end Brouwer.Skeleton
