-- VR-Brouwer — Stage 2 (decision C): the handshake parity kernel.
-- The encoding-independent combinatorial core of Sperner's lemma: for any bipartite
-- incidence between "rooms" (cells) and "doors" ((n−1)-faces of a given color set), the
-- number of odd-degree rooms and odd-degree doors have equal parity (both = #incidences mod 2).
-- This is what the geometric Kuhn cells will feed: rooms = cells (odd degree ⇔ rainbow),
-- doors = {0,…,n−1}-faces (odd degree ⇔ boundary). Pure combinatorics; absolute Tier-3 from
-- substrate, differential witness clean (no `tendsto_subseq`, no extra `Classical`).

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Parity

/-!
# Handshake parity kernel (Stage 2)

`handshake_parity`: the room/door double-count. This isolates the one genuinely hard
combinatorial step of Sperner's lemma from the geometry of the triangulation, so it can be
proven once and reused at every dimension. The geometric Kuhn-cell layer (which supplies the
incidence and the "each door in 1 or 2 cells" structure) is the remaining Stage-2 work.
-/

namespace Brouwer.Handshake

open Finset

variable {ι : Type*}

/-- The parity of a `ℕ`-valued sum equals (mod 2) the number of odd summands. -/
theorem sum_mod_two (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % 2 = (s.filter (fun i => Odd (f i))).card % 2 := by
  have h : ∑ i ∈ s, f i % 2 = (s.filter (fun i => Odd (f i))).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split <;> rename_i h <;> rw [Nat.odd_iff] at h <;> omega
  rw [Finset.sum_nat_mod, h]

/-- **Handshake parity** — the combinatorial heart of Sperner's lemma. For a bipartite
incidence `I ⊆ R × D` between rooms `R` and doors `D`, the number of odd-degree rooms and the
number of odd-degree doors have the same parity (each equals `#I` mod 2). In the Sperner
application: a room (cell) has odd degree iff it is rainbow, and a door ((n−1)-face) has odd
degree iff it lies on the boundary — so `#rainbow ≡ #boundary-doors (mod 2)`. -/
theorem handshake_parity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) (D : Finset β) (I : Finset (α × β))
    (hR : ∀ p ∈ I, p.1 ∈ R) (hD : ∀ p ∈ I, p.2 ∈ D) :
    (R.filter (fun r => Odd (I.filter (fun p => p.1 = r)).card)).card % 2
      = (D.filter (fun d => Odd (I.filter (fun p => p.2 = d)).card)).card % 2 := by
  have hr : I.card = ∑ r ∈ R, (I.filter (fun p => p.1 = r)).card :=
    Finset.card_eq_sum_card_fiberwise hR
  have hd : I.card = ∑ d ∈ D, (I.filter (fun p => p.2 = d)).card :=
    Finset.card_eq_sum_card_fiberwise hD
  rw [← sum_mod_two R (fun r => (I.filter (fun p => p.1 = r)).card),
      ← sum_mod_two D (fun d => (I.filter (fun p => p.2 = d)).card),
      ← hr, ← hd]

end Brouwer.Handshake
