-- VR-Brouwer — Stage 2: Sperner's lemma (combinatorial). Target: mathlib `Combinatorics`
-- as a standalone shippable result (PLAN v5). This file begins with the validated parity
-- core — the one-dimensional case (the base / first step of the dimension induction).
--
-- Per CLAUDE.md §5 v3: absolute `#print axioms` is Tier-3 over mathlib's substrate; the
-- constructive content is witnessed differentially (no choice beyond substrate; no
-- `IsCompact.tendsto_subseq`). This file is pure combinatorics over `Bool`/`Finset`/`ℕ`.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Parity

/-!
# Sperner's lemma — the one-dimensional parity core (Stage 2, base case)

A 2-coloring of the path `0, 1, …, m` (a triangulation of the `1`-simplex `[0,1]`) by
`f : ℕ → Bool`. A "door" is an edge `{i, i+1}` whose endpoints differ. The number of doors
has parity determined purely by the endpoints: it is odd iff `f 0 ≠ f m`. With the Sperner
boundary condition `f 0 = false`, `f m = true`, the number of doors is **odd** — the
1-dimensional Sperner's lemma, and the base case of the dimension induction (PLAN v5).

The general `n`-dimensional abstract triangulation interface and the door-counting induction
are the remaining Stage-2 work (see stage report).
-/

namespace Brouwer.Sperner

open Finset

/-- The number of "doors" of a 2-coloring `f` along the path `0,1,…,m`: edges whose two
endpoints receive different colors. -/
def doors (f : ℕ → Bool) (m : ℕ) : ℕ :=
  ((range m).filter (fun i => f i ≠ f (i + 1))).card

/-- The parity of the door count depends only on the endpoints: it is `0` iff `f 0 = f m`.
This is the telescoping heart of Sperner's lemma in dimension one. -/
theorem doors_mod_two (f : ℕ → Bool) (m : ℕ) :
    doors f m % 2 = if f 0 = f m then 0 else 1 := by
  unfold doors
  rw [Finset.card_filter]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    cases h0 : f 0 <;> cases hm : f m <;> cases hm1 : f (m + 1) <;>
      simp_all <;> omega

/-- **Sperner's lemma, dimension one.** A 2-coloring of the path `0,…,m` with the Sperner
boundary condition (`f 0 = false`, `f m = true`) has an *odd* number of doors; in particular
at least one door exists. -/
theorem odd_doors (f : ℕ → Bool) (m : ℕ) (h0 : f 0 = false) (hm : f m = true) :
    Odd (doors f m) := by
  have h : doors f m % 2 = 1 := by rw [doors_mod_two, h0, hm]; decide
  exact ⟨doors f m / 2, by omega⟩

end Brouwer.Sperner
