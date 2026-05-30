-- VR-Brouwer — Stage 2 FEASIBILITY SPIKE: general Kuhn–simplex encoding + structural pivot.
-- Question: can the pseudomanifold property (interior facet in exactly 2 cells, boundary in 1)
-- be proved STRUCTURALLY as a pivot involution (Scarf/Lemke), WITHOUT enumerating a Finset of all
-- cells (which is the n=2-specific, throwaway route)? This file pins the general cell encoding and
-- the interior pivot, and proves the pivot involution — the "shared by exactly two cells" core.
-- Deliverable: a go/no-go verdict (see stage report), not a closed theorem.

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import VRCycle.Brouwer.Handshake
import VRCycle.Brouwer.Sperner

/-!
# Feasibility spike: structural pivot for the general Kuhn–simplex triangulation

A general Kuhn cell of the resolution-`k` standard `n`-simplex is an *order-simplex*: a base grid
point together with an ordering of the `n` "transfer moves" (the Scarf/Freudenthal form). Its
vertices are the partial sums of the moves applied in that order (the geometric realization +
grid-integrity are the next phase — see verdict). The combinatorial heart of the pseudomanifold
property is the **pivot**: across an interior facet, swapping two adjacent moves in the order
produces the unique adjacent cell, and doing it twice returns the original — an involution, proved
here with no enumeration of cells.
-/

namespace Brouwer.KuhnGen

open Finset

variable {n k : ℕ}

/-- A general Kuhn cell of the resolution-`k` `n`-simplex: a base grid point (`∑ = k`) and an
ordering of the `n` transfer moves (`Equiv.Perm (Fin n)`). There are (per base) `n!` orderings —
the `Equiv.Perm` machinery of `Skeleton.lean` transfers here. -/
@[ext]
structure KCell (n k : ℕ) where
  /-- The base grid point of the cell. -/
  base : Fin (n + 1) → ℕ
  /-- The base point lies on the resolution-`k` grid (its coordinates sum to `k`). -/
  base_sum : ∑ i : Fin (n + 1), base i = k
  /-- The ordering of the `n` transfer moves generating the cell's vertices. -/
  order : Equiv.Perm (Fin n)

/-- Pivot across the interior facet selected by an adjacent transposition `s` of moves:
post-compose the move-order by `s`, keeping the base. The geometric content (this is the unique
cell sharing the dropped facet) is the next-phase lemma; here we pin the operation. -/
def pivot (C : KCell n k) (s : Equiv.Perm (Fin n)) : KCell n k where
  base := C.base
  base_sum := C.base_sum
  order := C.order * s

/-- **Structural pseudomanifold core (interior facet).** Pivoting twice across the same interior
facet (an adjacent transposition `s`, `s * s = 1`) returns the original cell. This is the
"interior facet is shared by exactly two cells" fact realized as a *pivot involution* — proved
with no `Finset` enumeration of cells (the whole point of the structural route). -/
theorem pivot_pivot (C : KCell n k) {s : Equiv.Perm (Fin n)} (hs : s * s = 1) :
    pivot (pivot C s) s = C := by
  cases C
  simp only [pivot, mul_assoc, hs, mul_one]

/-- The pivot keeps the base point (the two adjacent cells share their base grid point — a
necessary part of "they share the facet"). -/
@[simp] theorem pivot_base (C : KCell n k) (s : Equiv.Perm (Fin n)) :
    (pivot C s).base = C.base := rfl

/-! ### Coupling check: to STATE pivot-uniqueness, a vertex notion is required

A facet is a set of *shared vertices*; `KCell` (base + order) has no vertices, so uniqueness
("any cell sharing a facet is `C` or a pivot of `C`") cannot even be *stated* on the bare
`KCell`. The minimal geometric realization that makes it statable: the `m`-th vertex is the base
shifted by the first `m` transfer moves in the cell's order. (ℤ-valued: grid integrity / nonneg
is deliberately deferred — only the *positions* matter for facet-sharing.) Defining this is the
finding: uniqueness is **coupled** to the move/vertex definition, not separable from it. -/

/-- A transfer move (over ℤ): `move a` shifts one unit from coordinate `a.succ` to `a.castSucc`.
The minimal realization needed to state facets; nonneg/grid-integrity deferred. -/
def move (a : Fin n) : Fin (n + 1) → ℤ :=
  fun j => (if j = a.castSucc then 1 else 0) - (if j = a.succ then 1 else 0)

/-- The `m`-th vertex of a cell: the base shifted by the first `m` moves in the cell's order. -/
def vertex (C : KCell n k) (m : Fin (n + 1)) (j : Fin (n + 1)) : ℤ :=
  (C.base j : ℤ) +
    ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m : ℕ)), move (C.order l) j

/-- A pivot fixes the first vertex (`= base`). -/
@[simp] theorem vertex_pivot_zero (C : KCell n k) (s : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    vertex (pivot C s) 0 j = vertex C 0 j := by
  simp [vertex, pivot]

/-- A pivot fixes the last vertex (`= base + sum of all moves`), since reordering the moves does
not change their total sum. With `vertex_pivot_zero`, a pivot fixes both endpoint vertices —
the move-agnostic core of "the pivot pair shares the facet". -/
theorem vertex_pivot_last (C : KCell n k) (s : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    vertex (pivot C s) (Fin.last n) j = vertex C (Fin.last n) j := by
  have huniv : (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (Fin.last n : ℕ)))
      = Finset.univ := by
    ext l; simp [Fin.val_last]
  simp only [vertex, pivot, Equiv.Perm.mul_apply, huniv]
  congr 1
  exact Equiv.sum_comp s (fun l => move (C.order l) j)

/-! ### Integrity-for-uniqueness: the moves are distinguishable

Uniqueness needs only the *injective* half of grid-integrity (distinct moves ⇒ a cell is
recoverable from its vertices), NOT nonneg. The transfer moves `move a` are pairwise distinct:
`move a` has its unique `+1` at coordinate `a.castSucc`, and `castSucc` is injective. -/

/-- The transfer moves are pairwise distinct (`a ↦ move a` is injective). The recoverability of
the move-order `σ` from the vertex sequence rests on this. -/
theorem move_injective : Function.Injective (move (n := n)) := by
  intro a b h
  have hne : ∀ c : Fin n, c.castSucc ≠ c.succ := by
    intro c hc
    have hv := congrArg Fin.val hc
    rw [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have ha : move a a.castSucc = 1 := by simp [move, hne a]
  have hb : move b a.castSucc = 1 := by rw [← h]; exact ha
  by_cases hab : a.castSucc = b.castSucc
  · exact Fin.castSucc_injective n hab
  · exfalso
    simp only [move, if_neg hab] at hb
    split at hb <;> omega

/-! ### Uniqueness heart: two orders around a dropped vertex

The combinatorial core of "exactly 2": if two move-orders `σ`, `τ` agree off a pair `{i, j}`
(the two moves around the dropped interior vertex), then `σ = τ` or `σ = τ ∘ swap i j` — exactly
the two orderings, i.e. the original cell and its pivot. Pure `Equiv.Perm`, no geometry; with
`pivot_pivot` this is the structural "interior facet in exactly 2 cells". -/

/-- Two permutations that agree off a pair `{i, j}` are equal or differ by the transposition of
`i, j` — the "two orders around the dropped vertex" fact. -/
theorem perm_agree_off_pair {σ τ : Equiv.Perm (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (h : ∀ l, l ≠ i → l ≠ j → σ l = τ l) : σ = τ ∨ σ = τ * Equiv.swap i j := by
  have memb : ∀ a : Fin n, a = i ∨ a = j → σ a = τ i ∨ σ a = τ j := by
    intro a ha
    have htl : τ (τ⁻¹ (σ a)) = σ a := by simp
    rcases eq_or_ne (τ⁻¹ (σ a)) i with e | hli
    · exact Or.inl (by rw [← e, htl])
    rcases eq_or_ne (τ⁻¹ (σ a)) j with e | hlj
    · exact Or.inr (by rw [← e, htl])
    · exfalso
      have hh := h (τ⁻¹ (σ a)) hli hlj
      rw [htl] at hh
      have heq : τ⁻¹ (σ a) = a := σ.injective hh
      rcases ha with rfl | rfl
      · exact hli heq
      · exact hlj heq
  rcases memb i (Or.inl rfl) with hi | hi <;> rcases memb j (Or.inr rfl) with hj | hj
  · exact absurd (σ.injective (hi.trans hj.symm)) hij
  · refine Or.inl (Equiv.ext fun l => ?_)
    rcases eq_or_ne l i with rfl | hli
    · exact hi
    rcases eq_or_ne l j with rfl | hlj
    · exact hj
    · exact h l hli hlj
  · refine Or.inr (Equiv.ext fun l => ?_)
    rcases eq_or_ne l i with rfl | hli
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact hi
    rcases eq_or_ne l j with rfl | hlj
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact hj
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hli hlj]; exact h l hli hlj
  · exact absurd (σ.injective (hi.trans hj.symm)) hij

/-! ### Set ↔ positional: a linear functional orders the path (no nonneg needed)

The geometric-bridge crux is that a shared vertex *set* determines the shared *positional*
subsequence. The transfer moves are NOT monotone in the componentwise order (each has a `+1` and a
`−1`), so a componentwise chain does not work; but the linear functional `φ(w) = ∑ⱼ j·wⱼ`
decreases by exactly `1` along every move, hence strictly orders the path vertices. This needs
only the move structure — **no nonneg / grid-integrity** (it stays deferred). -/

/-- The linear functional `φ(w) = ∑ⱼ j·wⱼ`. -/
def phi (w : Fin (n + 1) → ℤ) : ℤ := ∑ j : Fin (n + 1), (j : ℤ) * w j

/-- Each transfer move decreases `φ` by exactly `1` (`φ(e_{a} − e_{a+1}) = a − (a+1) = −1`). -/
theorem phi_move (a : Fin n) : phi (move a) = -1 := by
  unfold phi move
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a.castSucc (fun j : Fin (n + 1) => (j : ℤ)),
      Finset.sum_ite_eq' Finset.univ a.succ (fun j : Fin (n + 1) => (j : ℤ))]
  simp only [Finset.mem_univ, if_true, Fin.val_castSucc, Fin.val_succ]
  omega

/-- `φ` of a cell vertex: the base value minus the number of moves taken to reach it. Since each
move drops `φ` by `1`, `φ ∘ vertex C` is strictly decreasing in `m` — giving `φ`-injectivity on a
cell's vertices, the bridge from a shared vertex *set* to a shared positional subsequence. (Stated
with the move-count as a `Finset.card`, avoiding any nonneg/grid-integrity.) -/
theorem phi_vertex (C : KCell n k) (m : Fin (n + 1)) :
    phi (vertex C m) = phi (fun j => (C.base j : ℤ))
      - ((Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m : ℕ))).card : ℤ) := by
  have h1 : phi (vertex C m) = phi (fun j => (C.base j : ℤ)) +
      ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m : ℕ)), phi (move (C.order l)) := by
    unfold phi vertex
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1]
  simp only [phi_move, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  rw [sub_eq_add_neg]

/-- The move-count `#{l | l.val < m.val}` is strictly increasing in `m` (the filter grows
properly). With `phi_vertex` this makes `φ ∘ vertex C` strictly decreasing, hence injective. -/
theorem cardf_lt {m₁ m₂ : Fin (n + 1)} (h : m₁ < m₂) :
    (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₁ : ℕ))).card
      < (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₂ : ℕ))).card := by
  apply Finset.card_lt_card
  have hsub : (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₁ : ℕ)))
      ⊆ (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₂ : ℕ))) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    omega
  rw [Finset.ssubset_iff_of_subset hsub]
  have hm₂ : (m₂ : ℕ) ≤ n := Nat.lt_succ_iff.mp m₂.isLt
  refine ⟨⟨(m₁ : ℕ), by omega⟩, ?_, ?_⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> omega

/-- Distinct positions give distinct vertices: `vertex C` is injective (`φ`-injectivity of a
cell's vertices — the "set determines the positional subsequence" foundation). -/
theorem vertex_injective (C : KCell n k) : Function.Injective (vertex C) := by
  intro m₁ m₂ h
  by_contra hne
  have hphi : phi (vertex C m₁) = phi (vertex C m₂) := by rw [h]
  rw [phi_vertex, phi_vertex] at hphi
  have hcard : (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₁ : ℕ))).card
      = (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (m₂ : ℕ))).card := by omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (cardf_lt hlt).ne hcard
  · exact (cardf_lt hgt).ne' hcard

/-- Consecutive vertices differ by the move at that position: `vertexₚ₊₁ − vertexₚ = move (σ p)`.
This recovers the move-order `σ` from the vertex sequence (with `move_injective`). -/
theorem vertex_succ_sub (C : KCell n k) (p : Fin n) (j : Fin (n + 1)) :
    vertex C p.succ j - vertex C p.castSucc j = move (C.order p) j := by
  unfold vertex
  have hf : Finset.univ.filter (fun l : Fin n => (l : ℕ) < (p.succ : ℕ))
      = insert p (Finset.univ.filter (fun l : Fin n => (l : ℕ) < (p.castSucc : ℕ))) := by
    ext l
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ,
      Fin.val_castSucc]
    constructor
    · intro hl
      rcases Nat.lt_or_ge (l : ℕ) (p : ℕ) with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | h) <;> omega
  rw [hf, Finset.sum_insert (by simp [Fin.val_castSucc])]
  omega

/-- The first vertex of any cell is its base. -/
theorem vertex_zero (C : KCell n k) (x : Fin (n + 1)) : vertex C 0 x = C.base x := by
  simp [vertex]

/-- The move-count below `x` is exactly `x` (when `x ≤ n`): the step-1 fact that makes a cell's
`φ`-values a *contiguous* integer interval. -/
theorem card_filter_lt {x : ℕ} (hx : x ≤ n) :
    (Finset.univ.filter (fun l : Fin n => (l : ℕ) < x)).card = x := by
  have himg : (Finset.univ.filter (fun l : Fin n => (l : ℕ) < x)).image Fin.val
      = Finset.range x := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

/-- `φ` of a cell vertex in closed form: `φ(vertex C m) = φ(base) − m`. Hence a cell's `φ`-values
are the contiguous interval `{φ(base), φ(base)−1, …, φ(base)−n}`. -/
theorem phi_vertex_eq (C : KCell n k) (m : Fin (n + 1)) :
    phi (vertex C m) = phi (fun j => (C.base j : ℤ)) - (m : ℤ) := by
  rw [phi_vertex, card_filter_lt (Nat.lt_succ_iff.mp m.isLt)]

/-- **Positional pseudomanifold (the structural "exactly 2", positional form).** If two cells
agree at every vertex position except an interior `m`, then they share a base and their orders are
equal or differ by the transposition of the two positions around `m` — i.e. `C'` is `C` or its
pivot. An interior positional facet is shared by exactly the two cells `{C, pivot C}`; no Finset
enumeration, no nonneg. -/
theorem positional_pseudomanifold (C C' : KCell n k) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hagree : ∀ l : Fin (n + 1), l ≠ m → vertex C' l = vertex C l) :
    C'.base = C.base ∧
      (C'.order = C.order ∨
        C'.order = C.order * Equiv.swap
          (⟨(m : ℕ) - 1, by omega⟩ : Fin n) (⟨(m : ℕ), hmn⟩ : Fin n)) := by
  set i : Fin n := ⟨(m : ℕ) - 1, by omega⟩ with hi
  set j : Fin n := ⟨(m : ℕ), hmn⟩ with hj
  have hm_ne : (0 : Fin (n + 1)) ≠ m := fun h => by rw [← h] at hm0; simp at hm0
  have hbase : C'.base = C.base := by
    funext x
    have h0 := congrFun (hagree 0 hm_ne) x
    rw [vertex_zero, vertex_zero] at h0
    exact_mod_cast h0
  refine ⟨hbase, ?_⟩
  have hij : i ≠ j := fun h => by
    have := congrArg Fin.val h; simp only [hi, hj] at this; omega
  have horder : ∀ p : Fin n, p ≠ i → p ≠ j → C'.order p = C.order p := by
    intro p hpi hpj
    apply move_injective
    have hsucc : p.succ ≠ m := fun h => hpi (by
      have hv := congrArg Fin.val h; rw [Fin.val_succ] at hv
      exact Fin.ext (by simp only [hi]; omega))
    have hcast : p.castSucc ≠ m := fun h => hpj (by
      have hv := congrArg Fin.val h; rw [Fin.val_castSucc] at hv
      exact Fin.ext (by simp only [hj]; omega))
    funext x
    rw [← vertex_succ_sub C' p x, ← vertex_succ_sub C p x, hagree _ hsucc, hagree _ hcast]
  exact perm_agree_off_pair hij horder

/-- **Structural pseudomanifold (set form).** If every vertex of an interior facet of `C` (the
`n` vertices other than the interior one at `m`) is a vertex of `C'`, then `C'` is `C` or its
pivot. So an interior facet (as a shared vertex *set*) lies in exactly the two cells
`{C, pivot C}` — no Finset enumeration, no nonneg. The `φ`-values form a contiguous interval, so
the shared extremes force `C'`'s interval to equal `C`'s (`base' = base`), and `φ`-injectivity
pins each shared vertex to its position; the result feeds `positional_pseudomanifold`. -/
theorem pseudomanifold (C C' : KCell n k) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hsub : ∀ l : Fin (n + 1), l ≠ m → ∃ l', vertex C' l' = vertex C l) :
    C'.base = C.base ∧
      (C'.order = C.order ∨
        C'.order = C.order * Equiv.swap
          (⟨(m : ℕ) - 1, by omega⟩ : Fin n) (⟨(m : ℕ), hmn⟩ : Fin n)) := by
  have hbase : C'.base = C.base := by
    obtain ⟨l0, hl0⟩ := hsub 0 (fun h => by rw [← h] at hm0; simp at hm0)
    obtain ⟨ln, hln⟩ := hsub (Fin.last n)
      (fun h => by have := congrArg Fin.val h; simp only [Fin.val_last] at this; omega)
    have e0 : phi (vertex C' l0) = phi (vertex C 0) := by rw [hl0]
    have en : phi (vertex C' ln) = phi (vertex C (Fin.last n)) := by rw [hln]
    rw [phi_vertex_eq, phi_vertex_eq] at e0 en
    have hl0n : (l0 : ℕ) ≤ n := Nat.lt_succ_iff.mp l0.isLt
    have hlnn : (ln : ℕ) ≤ n := Nat.lt_succ_iff.mp ln.isLt
    have hl0z : l0 = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero, Fin.val_last] at e0 en ⊢
      omega
    rw [hl0z] at hl0
    funext x
    have hx := congrFun hl0 x
    rw [vertex_zero, vertex_zero] at hx
    exact_mod_cast hx
  refine ⟨hbase, (positional_pseudomanifold C C' m hm0 hmn ?_).2⟩
  intro l hl
  obtain ⟨l', hl'⟩ := hsub l hl
  have eφ : phi (vertex C' l') = phi (vertex C l) := by rw [hl']
  rw [phi_vertex_eq, phi_vertex_eq, hbase] at eφ
  have hll : l' = l := by apply Fin.ext; omega
  rw [← hl', hll]

/-- If a swap of move-positions maps the prefix `{p | p.val < l.val}` to itself, it does not move
vertex `l` — only reorders moves already taken. The existence half of "exactly 2": the pivot
shares every facet vertex it is supposed to. -/
theorem vertex_pivot_swap (C : KCell n k) (i j : Fin n) (l : Fin (n + 1))
    (hinv : ∀ p : Fin n, (p : ℕ) < (l : ℕ) → ((Equiv.swap i j p : Fin n) : ℕ) < (l : ℕ)) :
    vertex (pivot C (Equiv.swap i j)) l = vertex C l := by
  funext x
  unfold vertex pivot
  simp only [Equiv.Perm.mul_apply]
  refine congrArg _ (Finset.sum_equiv (Equiv.swap i j) (fun p => ?_) (fun p _ => rfl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact hinv p
  · intro h
    have := hinv (Equiv.swap i j p) (by simpa using h)
    simpa using this

/-- A nontrivial pivot gives a *different* cell. -/
theorem pivot_ne {C : KCell n k} {s : Equiv.Perm (Fin n)} (hs : s ≠ 1) : pivot C s ≠ C := by
  intro h
  apply hs
  have ho : C.order * s = C.order := congrArg KCell.order h
  exact mul_left_cancel (a := C.order) (by rwa [mul_one])

/-- **Existence half of "exactly 2".** The pivot across an interior facet shares every vertex of
that facet (it only repositions the dropped interior vertex). With `pseudomanifold` (uniqueness)
and `pivot_ne`, an interior facet lies in EXACTLY the two cells `{C, pivot C}`. -/
theorem pivot_shares (C : KCell n k) (m : Fin (n + 1)) (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    {l : Fin (n + 1)} (hl : l ≠ m) :
    vertex (pivot C (Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin n) (⟨(m : ℕ), hmn⟩ : Fin n))) l
      = vertex C l := by
  set i : Fin n := ⟨(m : ℕ) - 1, by omega⟩ with hi
  set j : Fin n := ⟨(m : ℕ), hmn⟩ with hj
  have hiv : (i : ℕ) = (m : ℕ) - 1 := by rw [hi]
  have hjv : (j : ℕ) = (m : ℕ) := by rw [hj]
  apply vertex_pivot_swap
  intro p hp
  have hlm : (l : ℕ) ≠ (m : ℕ) := fun h => hl (Fin.ext h)
  rcases eq_or_ne p i with hp1 | hpi
  · rw [hp1, Equiv.swap_apply_left]; rw [hp1] at hp; omega
  rcases eq_or_ne p j with hp2 | hpj
  · rw [hp2, Equiv.swap_apply_right]; rw [hp2] at hp; omega
  · rw [Equiv.swap_apply_of_ne_of_ne hpi hpj]; exact hp

/-! ### Triangulation validity (nonneg / in-grid)

Vertices automatically sum to `k` (each move preserves the sum), so a cell realizes to genuine
grid points of `stdSimplex` iff its vertex coordinates stay nonneg — *triangulation validity*. Not
every `(base, σ)` is valid; the boundary↔interior distinction lives here (a pivot stays in-grid or
pushes a coordinate below `0`). nonneg over ℤ pulls only substrate `Classical`. -/

/-- Each transfer move preserves the coordinate sum (`e_a − e_{a+1}` sums to `0`). -/
theorem sum_move_zero (a : Fin n) : ∑ j : Fin (n + 1), move a j = 0 := by
  unfold move
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a.castSucc (fun _ => (1 : ℤ)),
      Finset.sum_ite_eq' Finset.univ a.succ (fun _ => (1 : ℤ))]
  simp

/-- Every vertex of a cell sums to `k` — independent of validity. -/
theorem sum_vertex (C : KCell n k) (m : Fin (n + 1)) :
    ∑ j : Fin (n + 1), vertex C m j = (k : ℤ) := by
  unfold vertex
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [sum_move_zero, Finset.sum_const_zero, add_zero]
  rw [← Nat.cast_sum, C.base_sum]

/-- A cell is *valid* (in-grid) when all its vertex coordinates are nonnegative; with `sum_vertex`
its vertices are then genuine grid points of `stdSimplex ℝ (Fin (n+1))`. -/
def Valid (C : KCell n k) : Prop := ∀ (m j : Fin (n + 1)), 0 ≤ vertex C m j

/-! ### `boundary → 1` (combinatorial route)

A *boundary facet* (combinatorially) is an interior facet of a valid cell whose pivot is NOT valid
(some vertex coordinate would go negative — the pivot "exits the grid"). Such a facet lies in
exactly ONE valid cell: by `pseudomanifold` the only other sharer is the pivot, which is invalid by
definition. No geometric `{x_c = 0}` definition is needed here — that reconciliation is deferred to
the recursion, where the geometric boundary face is actually consumed; `boundary → 1` itself is
purely combinatorial (`pseudomanifold` uniqueness + validity). -/

/-- **boundary → 1.** If the pivot across an interior facet of `C` is invalid (out of grid), then
the only valid cell sharing that facet is `C` itself. -/
theorem valid_boundary_unique (C C' : KCell n k) (m : Fin (n + 1))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n)
    (hpiv : ¬ Valid (pivot C (Equiv.swap
      (⟨(m : ℕ) - 1, by omega⟩ : Fin n) (⟨(m : ℕ), hmn⟩ : Fin n))))
    (hC' : Valid C') (hshare : ∀ l : Fin (n + 1), l ≠ m → ∃ l', vertex C' l' = vertex C l) :
    C' = C := by
  rcases pseudomanifold C C' m hm0 hmn hshare with ⟨hb, hord | hord⟩
  · exact KCell.ext hb hord
  · exfalso
    refine hpiv ?_
    have hC'eq : C' = pivot C (Equiv.swap
        (⟨(m : ℕ) - 1, by omega⟩ : Fin n) (⟨(m : ℕ), hmn⟩ : Fin n)) :=
      KCell.ext (hb.trans (pivot_base _ _).symm) hord
    rwa [hC'eq] at hC'

/-! ### Parity skeleton: rainbow ⟺ odd door count

For a coloring `c` of a cell's `n+1` vertices, a facet (drop vertex `i`) is a `{0,…,n−1}`-door
when its `n` vertices carry exactly the colors `{0,…,n−1}` (all but the last `n`). The room-degree
of the handshake is the door count, and `rainbow ⟺ odd door count`. This is the general-`n` version
of the `n=2` `decide` lemma. -/

/-- A facet (drop vertex `i`) is a `{0,…,n−1}`-door for the cell coloring `c`. -/
def IsDoor (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) : Prop :=
  (Finset.univ.erase i).image c = Finset.univ.erase (Fin.last n)

instance (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) : Decidable (IsDoor c i) := by
  unfold IsDoor; infer_instance

/-- The number of `{0,…,n−1}`-doors of a colored cell (the handshake room-degree). -/
def doorCount (c : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  (Finset.univ.filter (IsDoor c)).card

/-- For a rainbow (bijective) coloring, a facet is a door iff its dropped vertex carries color `n`,
so there is exactly **one** door (hence an odd count) — the room-degree ⇔ rainbow link, general
`n`. -/
theorem rainbow_one_door {c : Fin (n + 1) → Fin (n + 1)} (hc : Function.Bijective c) :
    doorCount c = 1 := by
  have key : ∀ i, IsDoor c i ↔ c i = Fin.last n := by
    intro i
    unfold IsDoor
    rw [Finset.image_erase hc.injective, Finset.image_univ_of_surjective hc.surjective]
    constructor
    · intro h
      by_contra hne
      have hmem : Fin.last n ∈ Finset.univ.erase (c i) := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact fun h => hne h.symm
      rw [h] at hmem
      simp at hmem
    · intro h; rw [h]
  unfold doorCount
  obtain ⟨i0, hi0⟩ := hc.surjective (Fin.last n)
  rw [Finset.card_eq_one]
  refine ⟨i0, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, key]
  exact ⟨fun h => hc.injective (h.trans hi0.symm), fun h => by rw [h]; exact hi0⟩

/-- **Forward rainbow-char.** A non-rainbow (non-bijective) coloring has an *even* number of doors:
its unique duplicated color gives doors only at that color's two vertices, and a facet is a door at
one iff at the other — so `doorCount ∈ {0, 2}`. -/
theorem even_doorCount_of_not_bijective {c : Fin (n + 1) → Fin (n + 1)}
    (hc : ¬ Function.Bijective c) : Even (doorCount c) := by
  have hni : ¬ Function.Injective c := fun hi => hc (Finite.injective_iff_bijective.mp hi)
  obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hni
  have hsub : ∀ i, IsDoor c i → i = p ∨ i = q := by
    intro i hi
    by_contra hcon
    rw [not_or] at hcon
    have hpu : p ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨fun h => hcon.1 h.symm, Finset.mem_univ p⟩
    have hqu : q ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨fun h => hcon.2 h.symm, Finset.mem_univ q⟩
    have hcard : ((Finset.univ.erase i).image c).card = (Finset.univ.erase i).card := by
      rw [show (Finset.univ.erase i).image c = Finset.univ.erase (Fin.last n) from hi]
      simp [Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
    exact hne (Finset.injOn_of_card_image_eq hcard hpu hqu hpq)
  have key : ∀ a b : Fin (n + 1), a ≠ b → c a = c b →
      (Finset.univ.erase a).image c = Finset.univ.image c := by
    intro a b hab hcab
    refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _)) ?_
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    rcases eq_or_ne y a with rfl | hya
    · exact ⟨b, Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩, hcab.symm⟩
    · exact ⟨y, Finset.mem_erase.mpr ⟨hya, Finset.mem_univ y⟩, rfl⟩
  have hiff : IsDoor c p ↔ IsDoor c q := by
    unfold IsDoor; rw [key p q hne hpq, key q p hne.symm hpq.symm]
  by_cases hp : IsDoor c p
  · have hq : IsDoor c q := hiff.mp hp
    have hset : Finset.univ.filter (IsDoor c) = {p, q} := by
      apply Finset.Subset.antisymm
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hsub i hi.2 with rfl | rfl <;> simp
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> simp [Finset.mem_filter, hp, hq]
    rw [doorCount, hset, Finset.card_pair hne]
    exact even_two
  · have hq : ¬ IsDoor c q := fun h => hp (hiff.mpr h)
    have hset : Finset.univ.filter (IsDoor c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hd
      rcases hsub i hd with rfl | rfl
      · exact hp hd
      · exact hq hd
    rw [doorCount, hset]; simp

/-- **Rainbow-characterization (general `n`).** A colored cell is rainbow (bijective coloring) iff
it has an odd number of `{0,…,n−1}`-doors — the handshake room-degree ⇔ rainbow link. -/
theorem odd_doorCount_iff_bijective {c : Fin (n + 1) → Fin (n + 1)} :
    Odd (doorCount c) ↔ Function.Bijective c := by
  refine ⟨fun h => by_contra fun hc => ?_, fun hc => by rw [rainbow_one_door hc]; exact odd_one⟩
  have he := Nat.even_iff.mp (even_doorCount_of_not_bijective hc)
  have ho := Nat.odd_iff.mp h
  omega

/-! ### Handshake instantiation: the global cell Finset

The cells at resolution `k` are indexed by a base summing to `k` (`Finset.finAntidiagonal`) and an
order (`Equiv.Perm`, a `Fintype`). This is the index set for the handshake sum; door-degrees come
from the structural pseudomanifold, not from re-enumeration. -/

instance : DecidableEq (KCell n k) := fun C C' =>
  decidable_of_iff (C.base = C'.base ∧ C.order = C'.order)
    ⟨fun ⟨h1, h2⟩ => KCell.ext h1 h2, fun h => ⟨congrArg KCell.base h, congrArg KCell.order h⟩⟩

/-- The (finite) set of all Kuhn cells at resolution `k`: bases summing to `k` paired with an
order. (Validity — vertex nonneg — is then a filter; finiteness comes from the `ℕ`-lattice cut.) -/
def cells (n k : ℕ) : Finset (KCell n k) :=
  ((Finset.finAntidiagonal (n + 1) k).attach ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin n)))).image
    (fun p => ⟨p.1.1, Finset.mem_finAntidiagonal.mp p.1.2, p.2⟩)

/-- Every cell with a base summing to `k` is in `cells`. -/
theorem mem_cells (C : KCell n k) : C ∈ cells n k := by
  unfold cells
  exact Finset.mem_image.mpr ⟨(⟨C.base, Finset.mem_finAntidiagonal.mpr C.base_sum⟩, C.order),
    Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, rfl⟩

/-- The vertex set of a cell (its `n+1` vertices as a `Finset`). -/
def vertexSet (C : KCell n k) : Finset (Fin (n + 1) → ℤ) := Finset.image (vertex C) Finset.univ

/-- The facet of `C` opposite vertex `m` (its `n` other vertices as a set) — a door candidate. -/
def facetSet (C : KCell n k) (m : Fin (n + 1)) : Finset (Fin (n + 1) → ℤ) :=
  Finset.image (vertex C) (Finset.univ.erase m)

/-- A facet of `C` is contained in `C'`'s vertex set iff every facet vertex of `C` is a vertex of
`C'` — i.e. the sharing hypothesis of `pseudomanifold`. This bridges geometric containment (used to
define door-degree) to the structural uniqueness lemma. -/
theorem facetSet_subset_iff (C C' : KCell n k) (m : Fin (n + 1)) :
    facetSet C m ⊆ vertexSet C' ↔ ∀ l : Fin (n + 1), l ≠ m → ∃ l', vertex C' l' = vertex C l := by
  unfold facetSet vertexSet
  constructor
  · intro h l hl
    have hmem : vertex C l ∈ Finset.image (vertex C') Finset.univ :=
      h (Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩, rfl⟩)
    simpa [Finset.mem_image] using hmem
  · intro h x hx
    rw [Finset.mem_image] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl'⟩ := h l (Finset.ne_of_mem_erase hl)
    exact Finset.mem_image.mpr ⟨l', Finset.mem_univ l', hl'⟩

/-- Distinct dropped vertices give distinct facets (`facetSet C` is injective). This unlocks both
the room-degree translation (a cell's facets are distinct doors) and the within-cell dedup. -/
theorem facetSet_injective (C : KCell n k) : Function.Injective (facetSet C) := by
  intro m₁ m₂ h
  apply vertex_injective C
  have h1 : vertex C m₁ ∈ Finset.image (vertex C) Finset.univ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ m₁)
  unfold facetSet at h
  rw [Finset.image_erase (vertex_injective C), Finset.image_erase (vertex_injective C)] at h
  by_contra hv
  have hmem : vertex C m₁ ∈ (Finset.image (vertex C) Finset.univ).erase (vertex C m₂) :=
    Finset.mem_erase.mpr ⟨hv, h1⟩
  rw [← h] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

/-! ### Coloring layer (prerequisite surfaced by the handshake pre-check)

The global handshake needs a coloring `col` of grid points (the structural ingredients were
coloring-agnostic): a cell is *rainbow* when its vertices receive all `n+1` colors, and a door is a
`{0,…,n−1}`-colored facet. This layer threads `col` through the room (rainbow) and door notions. -/

instance : DecidablePred (Valid : KCell n k → Prop) :=
  fun C => inferInstanceAs (Decidable (∀ m j : Fin (n + 1), 0 ≤ vertex C m j))

/-- Valid cells at resolution `k` (the handshake rooms). -/
def validCells (n k : ℕ) : Finset (KCell n k) := (cells n k).filter Valid

variable (col : (Fin (n + 1) → ℤ) → Fin (n + 1))

/-- A cell is *rainbow* under `col` when its `n+1` vertices receive all `n+1` colors. -/
def IsRainbowCell (C : KCell n k) : Prop := Function.Bijective (fun i => col (vertex C i))

/-- The vertex set of a cell has `n+1` elements (vertices are distinct). -/
theorem card_vertexSet (C : KCell n k) : (vertexSet C).card = n + 1 := by
  unfold vertexSet
  rw [Finset.card_image_of_injective _ (vertex_injective C), Finset.card_univ, Fintype.card_fin]

/-- **Matching core.** Any `n`-element subset of a cell's `n+1` vertices is one of its facets:
the single missing vertex `vertex C m` determines the dropped index `m`. This bridges the global
containment form of a door (`d ⊆ vertexSet C`) to the per-cell facet `facetSet C m`. -/
theorem facet_recover (C : KCell n k) {d : Finset (Fin (n + 1) → ℤ)}
    (hsub : d ⊆ vertexSet C) (hcard : d.card = n) : ∃ m, facetSet C m = d := by
  have hdiff : (vertexSet C \ d).card = 1 := by
    have hcs : (vertexSet C \ d).card = (vertexSet C).card - (d ∩ vertexSet C).card :=
      Finset.card_sdiff
    rw [Finset.inter_eq_left.mpr hsub, card_vertexSet, hcard] at hcs
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hdiff
  have hwv : w ∈ vertexSet C := (Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)).1
  obtain ⟨m, _, hm⟩ := Finset.mem_image.mp hwv
  refine ⟨m, ?_⟩
  unfold facetSet
  rw [Finset.image_erase (vertex_injective C), hm, Finset.erase_eq, ← hw]
  change vertexSet C \ (vertexSet C \ d) = d
  rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hsub]

/-- A vertex set `d` is a *door* under `col` when its colors are exactly `{0,…,n−1}`. -/
def IsColoredDoor (d : Finset (Fin (n + 1) → ℤ)) : Prop :=
  Finset.image col d = Finset.univ.erase (Fin.last n)

/-- The colors of a facet via `col` equal those of the per-cell coloring `col ∘ vertex C`. -/
theorem image_col_facetSet (C : KCell n k) (m : Fin (n + 1)) :
    Finset.image col (facetSet C m)
      = Finset.image (fun i => col (vertex C i)) (Finset.univ.erase m) := by
  unfold facetSet
  rw [Finset.image_image]
  rfl

/-- **Coloring-side matching.** A facet is a colored door under `col` iff it is a door of the
per-cell coloring `col ∘ vertex C` — the set-form door condition matches the abstract `IsDoor`,
via `Finset.image_image`. This closes the coloring half of the door matching. -/
theorem isColoredDoor_facetSet (C : KCell n k) (m : Fin (n + 1)) :
    IsColoredDoor col (facetSet C m) ↔ IsDoor (fun i => col (vertex C i)) m := by
  unfold IsColoredDoor IsDoor
  rw [image_col_facetSet]

instance (d : Finset (Fin (n + 1) → ℤ)) : Decidable (IsColoredDoor col d) :=
  inferInstanceAs (Decidable (Finset.image col d = Finset.univ.erase (Fin.last n)))

/-- The global door Finset: `{0,…,n−1}`-colored facets of valid cells (dedup automatic). -/
def doorFinset (n k : ℕ) (col : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    Finset (Finset (Fin (n + 1) → ℤ)) :=
  (((validCells n k) ×ˢ (Finset.univ : Finset (Fin (n + 1)))).image
    (fun p => facetSet p.1 p.2)).filter (IsColoredDoor col)

/-- Cell–door incidence: a valid cell paired with a door it contains. -/
def incidence (n k : ℕ) (col : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    Finset (KCell n k × Finset (Fin (n + 1) → ℤ)) :=
  ((validCells n k) ×ˢ (doorFinset n k col)).filter (fun p => p.2 ⊆ vertexSet p.1)

/-- Raw handshake parity over the cell–door incidence (instantiation of `handshake_parity`). The
degree-card translations (room-degree ⟺ rainbow, door-degree ⟺ degree-1) refine this to the
skeleton statement. -/
theorem handshake_raw (n k : ℕ) (col : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    ((validCells n k).filter (fun C =>
        Odd ((incidence n k col).filter (fun p => p.1 = C)).card)).card % 2
      = ((doorFinset n k col).filter (fun d =>
        Odd ((incidence n k col).filter (fun p => p.2 = d)).card)).card % 2 :=
  Brouwer.Handshake.handshake_parity (validCells n k) (doorFinset n k col) (incidence n k col)
    (fun _ hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
    (fun _ hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2)

/-! ### Room-degree card: the cell-side translation (rainbow ⟺ odd room-degree)

The handshake's *room-degree* of a valid cell `C` — the number of incident doors — equals the
`doorCount` of its induced coloring `col ∘ vertex C`. The map `m ↦ facetSet C m` is the bijection:
a colored door incident to `C` is exactly one of `C`'s `n+1` facets that happens to be
`{0,…,n−1}`-colored. With `odd_doorCount_iff_bijective` this gives "odd room-degree ⟺ rainbow",
the cell side of Sperner's parity count. This translation is position-agnostic — it needs no
interior/boundary distinction, only `facet_recover` + `facetSet_injective`. -/

/-- A facet has exactly `n` vertices (the cell has `n+1`; one is dropped). -/
theorem card_facetSet (C : KCell n k) (m : Fin (n + 1)) : (facetSet C m).card = n := by
  unfold facetSet
  rw [Finset.card_image_of_injective _ (vertex_injective C),
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]
  omega

/-- Every facet of a cell is contained in its vertex set. -/
theorem facetSet_subset_vertexSet (C : KCell n k) (m : Fin (n + 1)) :
    facetSet C m ⊆ vertexSet C := by
  unfold facetSet vertexSet
  exact Finset.image_subset_image (fun _ hx => Finset.mem_of_mem_erase hx)

/-- **Room-degree card.** For a valid cell `C`, the number of doors incident to `C` in the global
incidence equals `doorCount (col ∘ vertex C)`. The bijection `m ↦ facetSet C m` matches `C`'s
`{0,…,n−1}`-colored facets with the abstract doors of its induced coloring. -/
theorem room_degree_card (C : KCell n k) (hC : C ∈ validCells n k) :
    ((incidence n k col).filter (fun p => p.1 = C)).card
      = doorCount (fun i => col (vertex C i)) := by
  unfold doorCount
  refine (Finset.card_bij (fun m _ => (C, facetSet C m)) ?_ ?_ ?_).symm
  · -- maps into the incident-door fibre
    intro m hm
    have hdoor : IsDoor (fun i => col (vertex C i)) m := (Finset.mem_filter.mp hm).2
    have hmemdoor : facetSet C m ∈ doorFinset n k col := by
      unfold doorFinset
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr
          ⟨(C, m), Finset.mem_product.mpr ⟨hC, Finset.mem_univ m⟩, rfl⟩,
        (isColoredDoor_facetSet col C m).mpr hdoor⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    unfold incidence
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hC, hmemdoor⟩, facetSet_subset_vertexSet C m⟩
  · -- injective (distinct dropped vertices give distinct facets)
    intro m₁ _ m₂ _ heq
    exact facetSet_injective C (congrArg Prod.snd heq)
  · -- surjective onto the incident-door fibre
    intro b hb
    obtain ⟨hbI, hb1⟩ := Finset.mem_filter.mp hb
    have hb1' : b.1 = C := hb1
    unfold incidence at hbI
    obtain ⟨hbprod, hbsub⟩ := Finset.mem_filter.mp hbI
    obtain ⟨_, hbdoor⟩ := Finset.mem_product.mp hbprod
    have hbsub' : b.2 ⊆ vertexSet b.1 := hbsub
    have hsubC : b.2 ⊆ vertexSet C := hb1' ▸ hbsub'
    unfold doorFinset at hbdoor
    obtain ⟨himg, hcd⟩ := Finset.mem_filter.mp hbdoor
    have hcard : b.2.card = n := by
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp himg
      rw [← hp]; exact card_facetSet p.1 p.2
    obtain ⟨m, hm⟩ := facet_recover C hsubC hcard
    have hcdf : IsColoredDoor col (facetSet C m) := by rw [hm]; exact hcd
    have hdoor : IsDoor (fun i => col (vertex C i)) m :=
      (isColoredDoor_facetSet col C m).mp hcdf
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hdoor⟩,
      Prod.ext_iff.mpr ⟨hb1'.symm, hm⟩⟩

instance : DecidablePred (IsRainbowCell (n := n) (k := k) col) := fun C =>
  inferInstanceAs (Decidable (Function.Bijective (fun i => col (vertex C i))))

/-- **Odd room-degree ⟺ rainbow** (pointwise, over valid cells). Refining `room_degree_card` by
`odd_doorCount_iff_bijective`: the valid cells with odd room-degree are exactly the rainbow valid
cells. This is the cell-side parity filter congruence. -/
theorem odd_room_filter :
    (validCells n k).filter
        (fun C => Odd ((incidence n k col).filter (fun p => p.1 = C)).card)
      = (validCells n k).filter (IsRainbowCell col) := by
  apply Finset.filter_congr
  intro C hC
  rw [room_degree_card col C hC, odd_doorCount_iff_bijective]
  rfl

/-! ### Closed parity skeleton (rainbow ⟺ odd-degree doors)

Combining the room-degree card with `handshake_raw` closes the Sperner parity identity in the form
the structural machinery delivers: **`#(rainbow valid cells) ≡ #(odd-degree doors) (mod 2)`**. The
remaining reformulation "odd-degree door ⟺ degree-1 door" needs the door-degree ∈ {1,2} dichotomy;
its interior-position case is exactly `pseudomanifold` + `valid_boundary_unique` + `pivot_shares`,
but the boundary-*position* case (a facet dropped at position `0` or `n`) is shared across a
*base-shift* neighbour, NOT a move-order transposition — outside the structural pivot. See the stage
report (this is the door-degree wall; for `n = 1` it is the entire content). -/

/-- **Closed parity skeleton.** The number of rainbow valid cells and the number of odd-degree doors
have the same parity. This is Sperner's parity identity in the structural form: `#rainbow ≡
#odd-doors (mod 2)`. (`#odd-doors = #(degree-1 doors)` once the door-degree ∈ {1,2} dichotomy is in
place — the boundary-position half is the deferred reconciliation.) -/
theorem rainbow_parity_odd_doors (n k : ℕ) (col : (Fin (n + 1) → ℤ) → Fin (n + 1)) :
    ((validCells n k).filter (IsRainbowCell col)).card % 2
      = ((doorFinset n k col).filter (fun d =>
          Odd ((incidence n k col).filter (fun p => p.2 = d)).card)).card % 2 := by
  rw [← odd_room_filter col]
  exact handshake_raw n k col

/-! ### Base-shift pivot (boundary position `m = 0`) — FINDING K-1, the second neighbour relation

The structural `pivot` (move-order transposition) realises the neighbour across an *interior*
facet only. The neighbour across the boundary-position-`0` facet (drop the base vertex) is a
**base shift + cyclic rotation** of the move order, NOT a transposition: its base is `v₁ =
base + move (σ 0)` and its order is `σ ∘ finRotate`. Because the base changes, the new base is a
genuine grid point (`Fin → ℕ`) only when `v₁ ≥ 0`, i.e. when `C` is *valid* — so `pivot0` carries a
`Valid C` hypothesis (the interior pivot needed none). This is the concrete shape of the deferred
boundary reconciliation, localised to a named construction. -/

/-- The base of the base-shift neighbour of a valid cell: the first vertex `v₁ = base + move (σ 0)`,
realised over `ℕ` via `Int.toNat` (nonneg because `C` is valid). -/
def baseShiftBase (C : KCell (n + 1) k) : Fin (n + 2) → ℕ := fun j => (vertex C 1 j).toNat

/-- Over `ℤ`, the base-shift base is exactly the first vertex `v₁` (uses validity for nonneg). -/
theorem baseShiftBase_eq (C : KCell (n + 1) k) (hC : Valid C) (j : Fin (n + 2)) :
    (baseShiftBase C j : ℤ) = vertex C 1 j :=
  Int.toNat_of_nonneg (hC 1 j)

/-- The base-shift base sums to `k` (it is a vertex of `C`, which sums to `k`). -/
theorem baseShiftBase_sum (C : KCell (n + 1) k) (hC : Valid C) :
    ∑ j, baseShiftBase C j = k := by
  have h : ((∑ j, baseShiftBase C j : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun j _ => baseShiftBase_eq C hC j)]
    exact sum_vertex C 1
  exact_mod_cast h

/-- **Base-shift pivot (position `0`).** The neighbour of a valid cell across its base-vertex facet:
base shifted to `v₁`, move order cyclically rotated by `finRotate`. The second neighbour relation of
FINDING K-1, defined only for valid cells (the base shift needs `v₁ ≥ 0`). -/
def pivot0 (C : KCell (n + 1) k) (hC : Valid C) : KCell (n + 1) k where
  base := baseShiftBase C
  base_sum := baseShiftBase_sum C hC
  order := C.order * finRotate (n + 1)

/-- **Facet-sharing (existence) for the base-shift pivot.** The base-shift neighbour realises the
position-`0` facet of `C`: its vertex at position `p.castSucc` is `C`'s vertex at position `p.succ`.
So `pivot0 C` shares every vertex of the dropped-base facet. The move-order rotation `finRotate`
realigns the shifted base, proved by induction on the position via `vertex_succ_sub`. -/
theorem vertex_pivot0 (C : KCell (n + 1) k) (hC : Valid C) (p : Fin (n + 1)) :
    vertex (pivot0 C hC) p.castSucc = vertex C p.succ := by
  funext j
  induction p using Fin.induction with
  | zero =>
    rw [Fin.castSucc_zero, vertex_zero, Fin.succ_zero_eq_one]
    exact baseShiftBase_eq C hC j
  | succ i ih =>
    have hil : Fin.castSucc i ≠ Fin.last n := by
      have := i.isLt; rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]; omega
    have efr : finRotate (n + 1) (Fin.castSucc i) = Fin.succ i := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hil, Fin.val_castSucc, Fin.val_succ]
    have eord : (pivot0 C hC).order (Fin.castSucc i) = C.order (Fin.succ i) := by
      change (C.order * finRotate (n + 1)) (Fin.castSucc i) = C.order (Fin.succ i)
      rw [Equiv.Perm.mul_apply, efr]
    have hp := vertex_succ_sub (pivot0 C hC) (Fin.castSucc i) j
    have hc := vertex_succ_sub C (Fin.succ i) j
    rw [eord, Fin.succ_castSucc, ih, Fin.succ_castSucc] at hp
    omega

/-- The base-shift pivot shares the entire position-`0` facet of `C` (existence half of "the
boundary-position facet lies in the two cells `{C, pivot0 C}`"). -/
theorem facetSet_zero_subset (C : KCell (n + 1) k) (hC : Valid C) :
    facetSet C 0 ⊆ vertexSet (pivot0 C hC) := by
  intro x hx
  unfold facetSet at hx
  rw [Finset.mem_image] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have hl0 : l ≠ 0 := Finset.ne_of_mem_erase hl
  obtain ⟨p, rfl⟩ : ∃ p : Fin (n + 1), p.succ = l := ⟨l.pred hl0, Fin.succ_pred l hl0⟩
  rw [← vertex_pivot0 C hC p]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- Two permutations agreeing off a single point `i` are equal — a bijection fixing all but one
point fixes that point too. The off-one analogue of `perm_agree_off_pair`, used for the
boundary-position uniqueness where the dropped facet leaves exactly one free move-slot. -/
theorem perm_agree_off_one {α : Type*} {σ τ : Equiv.Perm α} {i : α}
    (h : ∀ l, l ≠ i → σ l = τ l) : σ = τ := by
  ext l
  rcases eq_or_ne l i with rfl | hl
  · rcases eq_or_ne (σ l) (τ l) with he | hne
    · exact he
    · exfalso
      have hp : τ (τ⁻¹ (σ l)) = σ l := by simp
      have hpl : τ⁻¹ (σ l) ≠ l := fun he2 => hne (by rw [he2] at hp; exact hp.symm)
      have hag := h (τ⁻¹ (σ l)) hpl
      rw [hp] at hag
      exact hpl (σ.injective hag)
  · exact h l hl

/-- **Uniqueness at the boundary position `0` (the position-`0` analogue of `pseudomanifold`).** A
cell `C'` sharing every vertex of `C`'s dropped-base facet is either `C` itself or its base-shift
pivot `pivot0 C`. The `φ`-values of the shared facet are `n+1` consecutive integers, forcing `C'`'s
`φ`-interval to start at `Φ(base)` (then `C' = C`) or one below (then `C' = pivot0 C`); the move
order is pinned by `perm_agree_off_one`. With `facetSet_zero_subset` and `pivot0_ne`, the
boundary-position facet lies in EXACTLY the two cells `{C, pivot0 C}`. -/
theorem pseudomanifold_zero (C C' : KCell (n + 1) k) (hC : Valid C)
    (hshare : ∀ l : Fin (n + 2), l ≠ 0 → ∃ l', vertex C' l' = vertex C l) :
    C' = C ∨ C' = pivot0 C hC := by
  have hone : (1 : Fin (n + 2)) ≠ 0 := by rw [Ne, Fin.ext_iff]; simp
  obtain ⟨a, ha⟩ := hshare 1 hone
  obtain ⟨b, hb⟩ := hshare (Fin.last (n + 1)) (by
    rw [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]; omega)
  have ea : phi (fun j => (C'.base j : ℤ)) - (a : ℤ)
      = phi (fun j => (C.base j : ℤ)) - ((1 : Fin (n + 2)) : ℤ) := by
    have := congrArg phi ha; rwa [phi_vertex_eq, phi_vertex_eq] at this
  have eb : phi (fun j => (C'.base j : ℤ)) - (b : ℤ)
      = phi (fun j => (C.base j : ℤ)) - ((Fin.last (n + 1) : Fin (n + 2)) : ℤ) := by
    have := congrArg phi hb; rwa [phi_vertex_eq, phi_vertex_eq] at this
  have h1v : ((1 : Fin (n + 2)) : ℤ) = 1 := by simp
  have hlv : ((Fin.last (n + 1) : Fin (n + 2)) : ℤ) = (n : ℤ) + 1 := by
    simp [Fin.val_last]
  have haub : (a : ℤ) ≤ (n : ℤ) + 1 := by have := a.isLt; exact_mod_cast Nat.lt_succ_iff.mp a.isLt
  have halb : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le _
  have hbub : (b : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast Nat.lt_succ_iff.mp b.isLt
  have hblb : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le _
  rw [h1v] at ea
  rw [hlv] at eb
  have key : phi (fun j => (C'.base j : ℤ)) = phi (fun j => (C.base j : ℤ))
      ∨ phi (fun j => (C'.base j : ℤ)) = phi (fun j => (C.base j : ℤ)) - 1 := by omega
  rcases key with hk | hk
  · -- Case Φ(base') = Φ(base): C' = C
    refine Or.inl ?_
    have h1 : ∀ l : Fin (n + 2), l ≠ 0 → vertex C' l = vertex C l := by
      intro l hl
      obtain ⟨l', hl'⟩ := hshare l hl
      have eφ : phi (fun j => (C'.base j : ℤ)) - (l' : ℤ)
          = phi (fun j => (C.base j : ℤ)) - (l : ℤ) := by
        have := congrArg phi hl'; rwa [phi_vertex_eq, phi_vertex_eq] at this
      rw [hk] at eφ
      have hll : l' = l := Fin.ext (by exact_mod_cast (by omega : (l' : ℤ) = (l : ℤ)))
      rw [← hl', hll]
    have hσ : C'.order = C.order := by
      apply perm_agree_off_one (i := 0)
      intro p hp0
      apply move_injective
      funext x
      have hsucc0 : p.succ ≠ 0 := Fin.succ_ne_zero p
      have hcast0 : p.castSucc ≠ 0 := fun hc => hp0 (by
        have := congrArg Fin.val hc
        rw [Fin.val_castSucc, Fin.val_zero] at this; exact Fin.ext this)
      rw [← vertex_succ_sub C' p x, ← vertex_succ_sub C p x,
        h1 p.succ hsucc0, h1 p.castSucc hcast0]
    have hbase : C'.base = C.base := by
      funext x
      have hssC' := vertex_succ_sub C' 0 x
      have hssC := vertex_succ_sub C 0 x
      rw [Fin.succ_zero_eq_one, Fin.castSucc_zero] at hssC' hssC
      have hmove : move (C'.order 0) x = move (C.order 0) x := by rw [hσ]
      have h1x : vertex C' 1 x = vertex C 1 x := congrFun (h1 1 hone) x
      have e0 : vertex C' 0 x = vertex C 0 x := by omega
      rw [vertex_zero, vertex_zero] at e0
      exact_mod_cast e0
    exact KCell.ext hbase hσ
  · -- Case Φ(base') = Φ(base) - 1: C' = pivot0 C
    refine Or.inr ?_
    have h2 : ∀ p : Fin (n + 1), vertex C' p.castSucc = vertex C p.succ := by
      intro p
      obtain ⟨l', hl'⟩ := hshare p.succ (Fin.succ_ne_zero p)
      have eφ : phi (fun j => (C'.base j : ℤ)) - (l' : ℤ)
          = phi (fun j => (C.base j : ℤ)) - (p.succ : ℤ) := by
        have := congrArg phi hl'; rwa [phi_vertex_eq, phi_vertex_eq] at this
      have hpsucc : ((p.succ : Fin (n + 2)) : ℤ) = (p : ℤ) + 1 := by
        simp [Fin.val_succ]
      rw [hk, hpsucc] at eφ
      have hl'eq : l' = p.castSucc :=
        Fin.ext (by rw [Fin.val_castSucc]; exact_mod_cast (by omega : (l' : ℤ) = (p : ℤ)))
      rw [hl'eq] at hl'
      exact hl'
    have hσ2 : C'.order = (pivot0 C hC).order := by
      apply perm_agree_off_one (i := Fin.last n)
      intro p hp
      apply move_injective
      funext x
      have hpn : (p : ℕ) < n := by
        have hne : (p : ℕ) ≠ n := fun h => hp (Fin.ext (by rw [Fin.val_last]; exact h))
        have := p.isLt; omega
      obtain ⟨q, hq⟩ : ∃ q : Fin (n + 1), q.castSucc = p.succ :=
        ⟨⟨p.val + 1, by omega⟩, Fin.ext (by rw [Fin.val_castSucc, Fin.val_succ])⟩
      have hcsP : vertex C' p.castSucc = vertex (pivot0 C hC) p.castSucc := by
        rw [h2 p, vertex_pivot0 C hC p]
      have hscP : vertex C' p.succ = vertex (pivot0 C hC) p.succ := by
        rw [← hq, h2 q, vertex_pivot0 C hC q]
      rw [← vertex_succ_sub C' p x, ← vertex_succ_sub (pivot0 C hC) p x, hcsP, hscP]
    have hbase2 : C'.base = (pivot0 C hC).base := by
      have h2' := h2 0
      have hP0 := vertex_pivot0 C hC 0
      rw [Fin.castSucc_zero] at h2' hP0
      have e0 : vertex C' (0 : Fin (n + 2)) = vertex (pivot0 C hC) 0 := h2'.trans hP0.symm
      funext x
      have hx := congrFun e0 x
      rw [vertex_zero, vertex_zero] at hx
      exact_mod_cast hx
    exact KCell.ext hbase2 hσ2

/-- The base-shift pivot is a genuinely different cell: its base is shifted by `move (σ 0)`, which
is nonzero at coordinate `σ0.castSucc`. With `pseudomanifold_zero` and `facetSet_zero_subset`, the
boundary-position-`0` facet lies in EXACTLY the two cells `{C, pivot0 C}` (degree `2` if `pivot0 C`
is valid, `1` otherwise). -/
theorem pivot0_ne (C : KCell (n + 1) k) (hC : Valid C) : pivot0 C hC ≠ C := by
  intro h
  set j₀ := (C.order 0).castSucc with hj₀
  have hbase_eq : (pivot0 C hC).base = C.base := congrArg KCell.base h
  have hb : (baseShiftBase C j₀ : ℤ) = (C.base j₀ : ℤ) := by
    exact_mod_cast congrFun hbase_eq j₀
  rw [baseShiftBase_eq C hC j₀] at hb
  have hne : (C.order 0).castSucc ≠ (C.order 0).succ := by
    intro he; have := congrArg Fin.val he
    rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hmove : move (C.order 0) j₀ = 1 := by rw [hj₀]; simp [move, hne]
  have hv1 : vertex C 1 j₀ = (C.base j₀ : ℤ) + move (C.order 0) j₀ := by
    have hss := vertex_succ_sub C 0 j₀
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss
    omega
  rw [hv1, hmove] at hb
  omega

/-- **Uniqueness at the boundary position `n+1` (drop the last vertex).** A cell `C'` sharing every
vertex of `C`'s dropped-last facet is either `C` itself or the "up-neighbour", whose order is the
inverse rotation `σ ∘ finRotate⁻¹` and whose base is `b − move (σ last)` (one φ-step *above* `C`).
The up-neighbour is NOT constructed as a `KCell` (its base need not be `≥ 0` under `Valid C` — it is
not a vertex of `C`); it is only *characterised*, which is all the degree bound needs. Mirror of
`pseudomanifold_zero` with the φ-extremes swapped. -/
theorem pseudomanifold_last (C C' : KCell (n + 1) k)
    (hshare : ∀ l : Fin (n + 2), l ≠ Fin.last (n + 1) → ∃ l', vertex C' l' = vertex C l) :
    C' = C ∨ (C'.order = C.order * (finRotate (n + 1)).symm
      ∧ ∀ j, (C'.base j : ℤ) = (C.base j : ℤ) - move (C.order (Fin.last n)) j) := by
  have hzl : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    rw [Ne, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
  have hnl : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by
    apply Fin.ne_of_val_ne; rw [Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega
  obtain ⟨a, ha⟩ := hshare 0 hzl
  obtain ⟨bb, hbb⟩ := hshare (Fin.last n).castSucc hnl
  have ea : phi (fun j => (C'.base j : ℤ)) - (a : ℤ)
      = phi (fun j => (C.base j : ℤ)) - ((0 : Fin (n + 2)) : ℤ) := by
    have := congrArg phi ha; rwa [phi_vertex_eq, phi_vertex_eq] at this
  have eb : phi (fun j => (C'.base j : ℤ)) - (bb : ℤ)
      = phi (fun j => (C.base j : ℤ)) - (((Fin.last n).castSucc : Fin (n + 2)) : ℤ) := by
    have := congrArg phi hbb; rwa [phi_vertex_eq, phi_vertex_eq] at this
  have h0v : ((0 : Fin (n + 2)) : ℤ) = 0 := by simp
  have hnv : (((Fin.last n).castSucc : Fin (n + 2)) : ℤ) = (n : ℤ) := by
    simp [Fin.val_castSucc, Fin.val_last]
  have haub : (a : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast Nat.lt_succ_iff.mp a.isLt
  have halb : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le _
  have hbub : (bb : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast Nat.lt_succ_iff.mp bb.isLt
  rw [h0v] at ea
  rw [hnv] at eb
  have key : phi (fun j => (C'.base j : ℤ)) = phi (fun j => (C.base j : ℤ))
      ∨ phi (fun j => (C'.base j : ℤ)) = phi (fun j => (C.base j : ℤ)) + 1 := by omega
  rcases key with hk | hk
  · -- Case Φ(base') = Φ(base): C' = C
    refine Or.inl ?_
    have h1 : ∀ l : Fin (n + 2), l ≠ Fin.last (n + 1) → vertex C' l = vertex C l := by
      intro l hl
      obtain ⟨l', hl'⟩ := hshare l hl
      have eφ : phi (fun j => (C'.base j : ℤ)) - (l' : ℤ)
          = phi (fun j => (C.base j : ℤ)) - (l : ℤ) := by
        have := congrArg phi hl'; rwa [phi_vertex_eq, phi_vertex_eq] at this
      rw [hk] at eφ
      have hll : l' = l := Fin.ext (by exact_mod_cast (by omega : (l' : ℤ) = (l : ℤ)))
      rw [← hl', hll]
    have hbase : C'.base = C.base := by
      funext x
      have hx := congrFun (h1 0 hzl) x
      rw [vertex_zero, vertex_zero] at hx
      exact_mod_cast hx
    have hσ : C'.order = C.order := by
      apply perm_agree_off_one (i := Fin.last n)
      intro p hp
      apply move_injective
      funext x
      have hpn : (p : ℕ) < n := by
        have hne : (p : ℕ) ≠ n := fun h => hp (Fin.ext (by rw [Fin.val_last]; exact h))
        have := p.isLt; omega
      have hsuccl : p.succ ≠ Fin.last (n + 1) := by
        rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.val_last]; omega
      have hcastl : p.castSucc ≠ Fin.last (n + 1) := by
        rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]; omega
      rw [← vertex_succ_sub C' p x, ← vertex_succ_sub C p x,
        h1 p.succ hsuccl, h1 p.castSucc hcastl]
    exact KCell.ext hbase hσ
  · -- Case Φ(base') = Φ(base) + 1: C' = up-neighbour
    have h2 : ∀ p : Fin (n + 1), vertex C' p.succ = vertex C p.castSucc := by
      intro p
      have hpcl : p.castSucc ≠ Fin.last (n + 1) := by
        rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]
        have := p.isLt; omega
      obtain ⟨l', hl'⟩ := hshare p.castSucc hpcl
      have eφ : phi (fun j => (C'.base j : ℤ)) - (l' : ℤ)
          = phi (fun j => (C.base j : ℤ)) - (p.castSucc : ℤ) := by
        have := congrArg phi hl'; rwa [phi_vertex_eq, phi_vertex_eq] at this
      have hpcv : ((p.castSucc : Fin (n + 2)) : ℤ) = (p : ℤ) := by simp [Fin.val_castSucc]
      have hpsv : ((p.succ : Fin (n + 2)) : ℤ) = (p : ℤ) + 1 := by simp [Fin.val_succ]
      rw [hk, hpcv] at eφ
      have hl'eq : l' = p.succ :=
        Fin.ext (by rw [Fin.val_succ]; exact_mod_cast (by omega : (l' : ℤ) = (p : ℤ) + 1))
      rw [hl'eq] at hl'
      exact hl'
    have hord2 : C'.order = C.order * (finRotate (n + 1)).symm := by
      apply perm_agree_off_one (i := 0)
      intro p hp0
      apply move_injective
      funext x
      have hpv : 1 ≤ (p : ℕ) := by
        rcases Nat.eq_zero_or_pos (p : ℕ) with h | h
        · exact absurd (Fin.ext h) hp0
        · exact h
      set r : Fin (n + 1) := (finRotate (n + 1)).symm p with hr
      have hrv : (r : ℕ) = (p : ℕ) - 1 := by rw [hr]; exact coe_finRotate_symm_of_ne_zero hp0
      have hord_p : (C.order * (finRotate (n + 1)).symm) p = C.order r := by
        rw [Equiv.Perm.mul_apply, ← hr]
      have hpc_rs : p.castSucc = r.succ :=
        Fin.ext (by rw [Fin.val_castSucc, Fin.val_succ, hrv]; omega)
      rw [hord_p, ← vertex_succ_sub C' p x, ← vertex_succ_sub C r x,
        h2 p, hpc_rs, h2 r]
    refine Or.inr ⟨hord2, ?_⟩
    intro x
    have h2'0 := congrFun (h2 0) x
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at h2'0
    have hss := vertex_succ_sub C' 0 x
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss
    have hsymm0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
      rw [finRotate_succ_symm_apply]; apply Fin.ext; simp
    have hσ0 : C'.order 0 = C.order (Fin.last n) := by
      rw [hord2, Equiv.Perm.mul_apply, hsymm0]
    rw [hσ0] at hss
    rw [h2'0] at hss
    omega

/-! ### Door-degree dichotomy: every door lies in exactly 1 or 2 valid cells (K-1d)

Combining the three uniqueness results — `pseudomanifold` (interior), `pseudomanifold_zero`
(position `0`), `pseudomanifold_last` (position `n+1`) — every facet of a valid cell lies in at most
two valid cells: besides the cell itself there is at most one neighbour (the pivot / base-shift
partner). With "at least one" (the recovering cell), the door-degree is exactly `1` or `2`, so
`odd ⟺ degree-1`. This converts `rainbow_parity_odd_doors` into the closed skeleton
`#(rainbow valid cells) ≡ #(degree-1 doors)`. -/

/-- A finite set in which every two elements other than a fixed `c` coincide has at most two
elements (`c` and at most one other). -/
theorem card_le_two_of_almost_const {α : Type*} {S : Finset α} {c : α}
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ c → b ≠ c → a = b) : S.card ≤ 2 := by
  classical
  have hsub : S ⊆ insert c (S.erase c) := fun x hx => by
    rcases eq_or_ne x c with rfl | hxc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxc, hx⟩)
  have herase : (S.erase c).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact h a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
      (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb)
  calc S.card ≤ (insert c (S.erase c)).card := Finset.card_le_card hsub
    _ ≤ (S.erase c).card + 1 := Finset.card_insert_le _ _
    _ ≤ 2 := by omega

/-- **Door-degree ≤ 2.** Any facet of a valid cell `C₀` lies in at most two valid cells: besides
`C₀`, at most one neighbour (interior pivot, base-shift `pivot0`, or the position-`n+1`
up-neighbour, per the position of the dropped vertex). The pseudomanifold property of the Kuhn
triangulation, assembled across all facet positions. -/
theorem door_sharers_card_le_two (C₀ : KCell (n + 1) k) (hC₀ : Valid C₀) (m₀ : Fin (n + 2)) :
    ((validCells (n + 1) k).filter (fun C' => facetSet C₀ m₀ ⊆ vertexSet C')).card ≤ 2 := by
  apply card_le_two_of_almost_const (c := C₀)
  intro C₁ hC₁ C₂ hC₂ hne1 hne2
  rw [Finset.mem_filter] at hC₁ hC₂
  have hs1 := (facetSet_subset_iff C₀ C₁ m₀).mp hC₁.2
  have hs2 := (facetSet_subset_iff C₀ C₂ m₀).mp hC₂.2
  rcases eq_or_ne m₀ 0 with rfl | hm0
  · rw [(pseudomanifold_zero C₀ C₁ hC₀ hs1).resolve_left hne1,
      (pseudomanifold_zero C₀ C₂ hC₀ hs2).resolve_left hne2]
  rcases eq_or_ne m₀ (Fin.last (n + 1)) with rfl | hml
  · obtain ⟨ho1, hb1⟩ := (pseudomanifold_last C₀ C₁ hs1).resolve_left hne1
    obtain ⟨ho2, hb2⟩ := (pseudomanifold_last C₀ C₂ hs2).resolve_left hne2
    exact KCell.ext (by funext j; exact_mod_cast (hb1 j).trans (hb2 j).symm) (ho1.trans ho2.symm)
  · have hm0v : 0 < (m₀ : ℕ) := by
      rcases Nat.eq_zero_or_pos (m₀ : ℕ) with h | h
      · exact absurd (Fin.ext h) hm0
      · exact h
    have hmnv : (m₀ : ℕ) < n + 1 := by
      have hne : (m₀ : ℕ) ≠ n + 1 := fun h => hml (Fin.ext (by rw [Fin.val_last]; exact h))
      have := m₀.isLt; omega
    obtain ⟨hb1, ho1⟩ := pseudomanifold C₀ C₁ m₀ hm0v hmnv hs1
    obtain ⟨hb2, ho2⟩ := pseudomanifold C₀ C₂ m₀ hm0v hmnv hs2
    have ho1' := ho1.resolve_left (fun h => hne1 (KCell.ext hb1 h))
    have ho2' := ho2.resolve_left (fun h => hne2 (KCell.ext hb2 h))
    exact KCell.ext (hb1.trans hb2.symm) (ho1'.trans ho2'.symm)

/-- The door-degree (number of incident valid cells) equals the number of valid cells whose vertex
set contains the door — the projection `(C', d) ↦ C'` of the incidence fibre over a fixed door. -/
theorem doorDegree_eq (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (d : Finset (Fin (n + 1 + 1) → ℤ)) (hd : d ∈ doorFinset (n + 1) k col) :
    ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card
      = ((validCells (n + 1) k).filter (fun C' => d ⊆ vertexSet C')).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpI, hpd⟩ := hp
    unfold incidence at hpI
    rw [Finset.mem_filter, Finset.mem_product] at hpI
    obtain ⟨⟨hval, _⟩, hsub⟩ := hpI
    exact ⟨hval, hpd ▸ hsub⟩
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    exact Prod.ext_iff.mpr ⟨hpq, hp.2.trans hq.2.symm⟩
  · intro C' hC'
    rw [Finset.mem_filter] at hC'
    refine ⟨(C', d), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    unfold incidence
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hC'.1, hd⟩, hC'.2⟩

/-- **Closed parity skeleton (degree-1 form).** The number of rainbow valid cells and the number of
degree-1 doors (doors lying in exactly one valid cell) have the same parity. Refines
`rainbow_parity_odd_doors` using the door-degree dichotomy: every door lies in `1` or `2` valid
cells, so an odd-degree door is exactly a degree-1 door. This is Sperner's parity identity in the
form the boundary recursion consumes: `#(rainbow valid cells) ≡ #(degree-1 doors) (mod 2)`. -/
theorem rainbow_parity_degree_one_doors (k : ℕ)
    (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1)) :
    ((validCells (n + 1) k).filter (IsRainbowCell col)).card % 2
      = ((doorFinset (n + 1) k col).filter
          (fun d => ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card = 1)).card % 2 := by
  have hfilt : (doorFinset (n + 1) k col).filter
        (fun d => Odd ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card)
      = (doorFinset (n + 1) k col).filter
        (fun d => ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card = 1) := by
    apply Finset.filter_congr
    intro d hd
    have hd' := hd
    unfold doorFinset at hd'
    rw [Finset.mem_filter, Finset.mem_image] at hd'
    obtain ⟨⟨⟨C₀, m₀⟩, hmem, hfd⟩, _⟩ := hd'
    rw [Finset.mem_product] at hmem
    have hC₀v : Valid C₀ := (Finset.mem_filter.mp hmem.1).2
    have hdeg := doorDegree_eq col d hd
    have hub : ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card ≤ 2 := by
      rw [hdeg, ← hfd]; exact door_sharers_card_le_two C₀ hC₀v m₀
    have hlb : 1 ≤ ((incidence (n + 1) k col).filter (fun p => p.2 = d)).card := by
      rw [hdeg, ← hfd]
      apply Finset.card_pos.mpr
      exact ⟨C₀, Finset.mem_filter.mpr ⟨hmem.1, facetSet_subset_vertexSet C₀ m₀⟩⟩
    rw [Nat.odd_iff]
    omega
  rw [rainbow_parity_odd_doors (n + 1) k col, hfilt]

/-! ### Dimension recursion — foundational layer (boundary confinement + dimension drop)

To close general Sperner from `rainbow_parity_degree_one_doors`, the degree-1 (boundary) doors must
be counted: they biject with the rainbow cells of the induced `(n−1)`-Sperner instance on one
boundary face, odd by induction. Two foundations, both established here:

* **Confinement** — under a Sperner-admissible (proper) coloring, a `{0,…,n−1}`-colored door cannot
  lie on the face `{xᵢ = 0}` for `i ≠ n`. So boundary doors are confined to the single face opposite
  vertex `n` (`not_onFace_of_coloredDoor`).
* **Dimension drop** — deleting the (zero) last coordinate of a face-`n` vertex lands in the
  resolution-`k` grid of the `(n−1)`-simplex (`sum_dropFace`).

The remaining gap (the genuinely hard reconciliation, see stage report) is the GEOMETRIC half
`degree-1 ⟺ on a boundary face`, relating a pivot exiting the grid to a door vertex's zero
coordinate. -/

/-- A coloring is *Sperner-admissible* (proper) when no **grid** vertex (one with positive
coordinate sum) lying on the face `{xᵢ = 0}` is coloured `i` — the standard boundary condition
driving the dimension recursion. The `0 < ∑ v` guard is essential: without it the all-zero vector
would force `col 0 ≠ i` for every `i`, making the predicate unsatisfiable (Finding S-1). Grid
vertices sum to `k > 0` (`sum_vertex`), so the guard is automatically met where the predicate is
used. -/
def SpernerAdmissible (col : (Fin (n + 1) → ℤ) → Fin (n + 1)) : Prop :=
  ∀ (v : Fin (n + 1) → ℤ) (i : Fin (n + 1)), 0 < ∑ j, v j → v i = 0 → col v ≠ i

/-- **Non-vacuity (Finding S-1 resolved).** The weakened `SpernerAdmissible` predicate is
satisfiable: the coloring "pick a positive coordinate" is admissible. (The unguarded predicate was
unsatisfiable — the zero vector forced `col 0 ≠ i` for every `i`.) This is what makes the Stage-2
results applicable to a concrete coloring (e.g. the Brouwer labeling of a continuous map). -/
theorem exists_spernerAdmissible :
    ∃ col : (Fin (n + 1) → ℤ) → Fin (n + 1), SpernerAdmissible col := by
  refine ⟨fun v => if h : ∃ i, 0 < v i then h.choose else 0, fun v i hsum hvi => ?_⟩
  have hex : ∃ j, 0 < v j := by
    by_contra hno
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), v j ≤ 0 :=
      fun j _ => not_lt.mp fun h => hno ⟨j, h⟩
    exact absurd hsum (not_lt.mpr (Finset.sum_nonpos hle))
  simp only [dif_pos hex]
  intro hcontra
  have hpos := hex.choose_spec
  rw [hcontra, hvi] at hpos
  exact lt_irrefl 0 hpos

/-- A facet `d` lies on the face `{xᵢ = 0}` when every vertex has `i`-th coordinate `0`. -/
def OnFace (d : Finset (Fin (n + 1) → ℤ)) (i : Fin (n + 1)) : Prop := ∀ v ∈ d, v i = 0

/-- **Boundary confinement.** Under an admissible coloring a `{0,…,n−1}`-colored door cannot lie on
the face `{xᵢ = 0}` for `i ≠ n`: the door carries colour `i`, which admissibility forbids on that
face. Hence boundary doors are confined to the face opposite vertex `n`. -/
theorem not_onFace_of_coloredDoor (col : (Fin (n + 1) → ℤ) → Fin (n + 1))
    (hadm : SpernerAdmissible col) (d : Finset (Fin (n + 1) → ℤ)) (hd : IsColoredDoor col d)
    (hdpos : ∀ v ∈ d, 0 < ∑ j, v j) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : ¬ OnFace d i := by
  intro hface
  have hmem : i ∈ Finset.image col d := by
    rw [hd]; exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
  rw [Finset.mem_image] at hmem
  obtain ⟨v, hv, hcv⟩ := hmem
  exact hadm v i (hdpos v hv) (hface v hv) hcv

/-- Delete the last coordinate of a point of the `n`-simplex, giving a point of the `(n−1)`-simplex
(the boundary-face dimension drop). -/
def dropFace {m : ℕ} (v : Fin (m + 1) → ℤ) : Fin m → ℤ := fun j => v j.castSucc

/-- The dimension drop lands in the resolution-`k` grid: deleting the (zero) last coordinate of a
face vertex preserves the coordinate sum. -/
theorem sum_dropFace {m : ℕ} (v : Fin (m + 1) → ℤ) :
    ∑ j : Fin m, dropFace v j = (∑ i : Fin (m + 1), v i) - v (Fin.last m) := by
  rw [Fin.sum_univ_castSucc]; simp only [dropFace]; omega

/-- **Changed-vertex formula for the interior pivot** (foundation of the geometric reconciliation).
The interior pivot across position `m` (swapping move-slots `i = m−1` and `jj = m`) changes only the
dropped vertex `m`: its new value is `vertex C m − move (σ i) + move (σ jj)`. Equivalently (since
`vertex C m = vertex C (m−1) + move (σ i)`) the new vertex is `vertex C (m−1) + move (σ jj)`.
Because `move (σ jj)` lowers exactly coordinate `(σ jj).succ` by `1`, the pivot exits the grid iff
`vertex C (m−1) (σ jj).succ = 0` — and nonnegativity of `C` then forces that coordinate to vanish at
every door vertex (the dropped vertex `m` being its unique peak). This is the concrete anchor of
`degree-1 ⟺ on a boundary face`. -/
theorem vertex_pivot_mid (C : KCell (n + 1) k) (m : Fin (n + 2)) (i jj : Fin (n + 1))
    (hi : (i : ℕ) = (m : ℕ) - 1) (hj : (jj : ℕ) = (m : ℕ)) (hm0 : 0 < (m : ℕ)) (x : Fin (n + 2)) :
    vertex (pivot C (Equiv.swap i jj)) m x
      = vertex C m x - move (C.order i) x + move (C.order jj) x := by
  simp only [vertex, pivot, Equiv.Perm.mul_apply]
  set S := Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (m : ℕ)) with hS
  have hiS : i ∈ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hjS : jj ∉ S := by
    rw [hS]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hswap : ∀ p ∈ S.erase i, Equiv.swap i jj p = p := by
    intro p hp
    have hpi : p ≠ i := Finset.ne_of_mem_erase hp
    have hpj : p ≠ jj := fun h => hjS (h ▸ Finset.mem_of_mem_erase hp)
    exact Equiv.swap_apply_of_ne_of_ne hpi hpj
  have key : ∑ p ∈ S, move (C.order (Equiv.swap i jj p)) x
      = move (C.order jj) x + ∑ p ∈ S.erase i, move (C.order p) x := by
    rw [← Finset.add_sum_erase S (fun p => move (C.order (Equiv.swap i jj p)) x) hiS,
      Equiv.swap_apply_left]
    congr 1
    exact Finset.sum_congr rfl (fun p hp => by rw [hswap p hp])
  have key2 : ∑ p ∈ S, move (C.order p) x
      = move (C.order i) x + ∑ p ∈ S.erase i, move (C.order p) x :=
    (Finset.add_sum_erase S (fun p => move (C.order p) x) hiS).symm
  rw [key, key2]
  omega

/-- A transfer move lowers exactly its `succ` coordinate by one. -/
theorem move_apply_succ (a : Fin n) : move a a.succ = -1 := by
  have hne : a.succ ≠ a.castSucc := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  simp [move, hne]

/-- **Interior reconciliation, extraction half.** If the interior pivot across position `m` exits
the grid, then coordinate `(σ⟨m⟩).succ` of the dropped facet's lower endpoint `v_{m−1}` is `0`.
Proof by the contradiction `v_{m−1}(c) ≥ 1 ⟹ pivot valid` (every pivot vertex stays `≥ 0`,
via `vertex_pivot_mid`). This is the step consuming degree-1; `v_{m−1}(c) = 0` then propagates to
the whole facet (validity forcing), giving `OnFace`. -/
theorem interior_invalid_basevertex (C : KCell (n + 1) k) (hC : Valid C) (m : Fin (n + 2))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n + 1)
    (hinv : ¬ Valid (pivot C (Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1))
      (⟨(m : ℕ), hmn⟩ : Fin (n + 1))))) :
    vertex C (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc
      (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))).succ = 0 := by
  set c : Fin (n + 2) := (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))).succ with hc
  have hms : m = (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).succ := by
    apply Fin.ext; rw [Fin.val_succ]; change (m : ℕ) = (m : ℕ) - 1 + 1; omega
  have hjc : move (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))) c = -1 := by
    rw [hc]; exact move_apply_succ _
  by_contra hne0
  have hge1 : 1 ≤ vertex C (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc c := by
    have := hC (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc c; omega
  apply hinv
  intro a b
  by_cases ham : a = m
  · rw [ham, vertex_pivot_mid C m _ _ rfl rfl hm0 b]
    have hvsub := vertex_succ_sub C (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)) b
    rw [← hms] at hvsub
    have heq : vertex C m b - move (C.order (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1))) b
        = vertex C (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc b := by omega
    have hmain : 0 ≤ vertex C (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc b
        + move (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))) b := by
      by_cases hbc : b = c
      · rw [hbc, hjc]; omega
      · have hge0 : 0 ≤ move (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))) b := by
          simp only [move]
          rw [if_neg (show b ≠ (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))).succ by
            rw [← hc]; exact hbc)]
          split <;> omega
        have := hC (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc b; omega
    rw [heq]
    exact hmain
  · rw [pivot_shares C m hm0 hmn ham]
    exact hC a b

/-- A transfer move changes any coordinate by at most `1`. -/
theorem move_apply_le_one (a : Fin n) (b : Fin (n + 1)) : move a b ≤ 1 := by
  simp only [move]; split <;> split <;> omega

/-- **Bottom-vertex formula for the base-shift pivot** (position-0 analogue of `vertex_pivot_mid`).
`pivot0 C` shares positions `0..n` with `C`'s facet `{v_1,…,v_{n+1}}`; its one new vertex (position
`n+1`) is `vertex C last + move (σ 0)`. This lowers exactly coordinate `(σ0).succ`, so `pivot0`
exits the grid iff `v_{n+1}((σ0).succ) = 0` — the position-0 reconciliation anchor. -/
theorem vertex_pivot0_last (C : KCell (n + 1) k) (hC : Valid C) (x : Fin (n + 2)) :
    vertex (pivot0 C hC) (Fin.last (n + 1)) x
      = vertex C (Fin.last (n + 1)) x + move (C.order 0) x := by
  have hfilt : (Finset.univ.filter
      (fun p : Fin (n + 1) => (p : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ)))
      = Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, iff_true]
    exact p.isLt
  have hreidx : ∑ p, move (C.order (finRotate (n + 1) p)) x = ∑ p, move (C.order p) x :=
    Equiv.sum_comp (finRotate (n + 1)) (fun p => move (C.order p) x)
  have hv1 : (baseShiftBase C x : ℤ) = (C.base x : ℤ) + move (C.order 0) x := by
    rw [baseShiftBase_eq C hC x]
    have hss := vertex_succ_sub C 0 x
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss
    omega
  simp only [vertex, pivot0, Equiv.Perm.mul_apply, hfilt]
  rw [hreidx, hv1]
  omega

/-- **Position-0 reconciliation, extraction half.** If `pivot0 C` exits the grid, then coordinate
`(σ0).succ` of the dropped facet's far endpoint `v_{n+1}` is `0`. As for the interior case, by the
contradiction `v_{n+1}(c) ≥ 1 ⟹ pivot0 valid` (its shared vertices are `C`'s, and the new bottom
vertex stays `≥ 0`), using `vertex_pivot0_last`/`vertex_pivot0`. -/
theorem boundary0_invalid_lastvertex (C : KCell (n + 1) k) (hC : Valid C)
    (hinv : ¬ Valid (pivot0 C hC)) :
    vertex C (Fin.last (n + 1)) (C.order 0).succ = 0 := by
  set c : Fin (n + 2) := (C.order 0).succ with hc
  have hmj : move (C.order 0) c = -1 := by rw [hc]; exact move_apply_succ _
  by_contra hne0
  have hge1 : 1 ≤ vertex C (Fin.last (n + 1)) c := by
    have := hC (Fin.last (n + 1)) c; omega
  apply hinv
  intro a b
  by_cases ham : a = Fin.last (n + 1)
  · rw [ham, vertex_pivot0_last C hC b]
    by_cases hbc : b = c
    · rw [hbc, hmj]; omega
    · have hge0 : 0 ≤ move (C.order 0) b := by
        simp only [move]
        rw [if_neg (show b ≠ (C.order 0).succ by rw [← hc]; exact hbc)]
        split <;> omega
      have := hC (Fin.last (n + 1)) b; omega
  · obtain ⟨p, rfl⟩ : ∃ p : Fin (n + 1), p.castSucc = a :=
      ⟨a.castPred ham, Fin.castSucc_castPred a ham⟩
    rw [vertex_pivot0 C hC p]
    exact hC p.succ b

/-- The total change of a fixed coordinate `c` along a full cell path: `+1` unless `c` is the first
coordinate `0`, `−1` unless `c` is the last coordinate. Summing all `n+1` transfer moves (reindexed
by the bijection `σ`); each `move a` contributes `[c = a.castSucc] − [c = a.succ]`, and the two
indicator sums telescope via `Fin.sum_univ_castSucc` / `Fin.sum_univ_succ`. -/
theorem sum_all_moves_coord (C : KCell (n + 1) k) (c : Fin (n + 2)) :
    ∑ p, move (C.order p) c
      = (if c = 0 then (1 : ℤ) else 0) - (if c = Fin.last (n + 1) then 1 else 0) := by
  rw [Equiv.sum_comp C.order (fun a => move a c)]
  have hcast : ∑ a : Fin (n + 1), (if c = a.castSucc then (1 : ℤ) else 0)
      = 1 - (if c = Fin.last (n + 1) then 1 else 0) := by
    have h := Fin.sum_univ_castSucc (fun j : Fin (n + 2) => if c = j then (1 : ℤ) else 0)
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    omega
  have hsucc : ∑ a : Fin (n + 1), (if c = a.succ then (1 : ℤ) else 0)
      = 1 - (if c = 0 then (1 : ℤ) else 0) := by
    have h := Fin.sum_univ_succ (fun j : Fin (n + 2) => if c = j then (1 : ℤ) else 0)
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    omega
  simp only [move, Finset.sum_sub_distrib, hcast, hsucc]
  omega

/-- **Position-0 reconciliation (full).** If `pivot0 C` exits the grid (the position-0 door is
degree-1), then the dropped facet `facetSet C 0` lies entirely on the boundary face `{x_c = 0}`,
`c = (σ0).succ`. By `sum_all_moves_coord` the total `c`-change along the path is `−[c=last]`, which
with `v_{n+1}(c) = 0` (extraction) and `base(c) ≥ 1` forces `c = Fin.last (n+1)` (i.e. `σ0 = last`);
then `c` is touched only at position `0` (by `−1`), so the whole facet (positions `1..n+1`) sits at
`base(c) − 1 = 0`. FINDING K-2: boundary doors are degree-1 only in this pinned configuration. -/
theorem boundary0_degree_one_onFace (C : KCell (n + 1) k) (hC : Valid C)
    (hinv : ¬ Valid (pivot0 C hC)) :
    OnFace (facetSet C 0) (C.order 0).succ := by
  set c : Fin (n + 2) := (C.order 0).succ with hc
  have hlast0 : vertex C (Fin.last (n + 1)) c = 0 := boundary0_invalid_lastvertex C hC hinv
  have hc0 : c ≠ 0 := by rw [hc]; exact Fin.succ_ne_zero _
  have hmove0 : move (C.order 0) c = -1 := by rw [hc]; exact move_apply_succ _
  have hv1 : vertex C (1 : Fin (n + 2)) c = (C.base c : ℤ) + move (C.order 0) c := by
    have hss := vertex_succ_sub C 0 c
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss
    omega
  have hbase_ge : 1 ≤ (C.base c : ℤ) := by have := hC 1 c; rw [hv1, hmove0] at this; omega
  have hfilt : (Finset.univ.filter
      (fun p : Fin (n + 1) => (p : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ))) = Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, iff_true]
    exact p.isLt
  have hlastsum : vertex C (Fin.last (n + 1)) c = (C.base c : ℤ) + ∑ p, move (C.order p) c := by
    unfold vertex; rw [hfilt]
  rw [sum_all_moves_coord, if_neg hc0] at hlastsum
  have hclast : c = Fin.last (n + 1) := by
    by_contra h; rw [if_neg h] at hlastsum; omega
  rw [if_pos hclast] at hlastsum
  have hbase1 : (C.base c : ℤ) = 1 := by omega
  have hmove : ∀ p : Fin (n + 1), move (C.order p) c = if p = 0 then (-1 : ℤ) else 0 := by
    intro p
    by_cases hp0 : p = 0
    · rw [hp0, if_pos rfl]; exact hmove0
    · rw [if_neg hp0]
      have h1 : c ≠ (C.order p).castSucc := by
        rw [hclast]; intro hcc
        have hv := congrArg Fin.val hcc
        rw [Fin.val_last, Fin.val_castSucc] at hv
        have := (C.order p).isLt; omega
      have h2 : c ≠ (C.order p).succ := by
        intro hcs
        exact hp0 (C.order.injective (Fin.succ_injective (n + 1) (hc.symm.trans hcs))).symm
      simp only [move]; rw [if_neg h1, if_neg h2]; omega
  intro v hv
  rw [facetSet, Finset.mem_image] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have hl0 : l ≠ 0 := Finset.ne_of_mem_erase hl
  have hl0v : 0 < (l : ℕ) := by
    rcases Nat.eq_zero_or_pos (l : ℕ) with h | h
    · exact absurd (Fin.ext (by rw [h, Fin.val_zero])) hl0
    · exact h
  change vertex C l c = 0
  unfold vertex
  rw [Finset.sum_congr rfl (fun p _ => hmove p), Finset.sum_ite_eq', hbase1,
    if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [Fin.val_zero]; omega⟩)]
  omega

/-- **Interior reconciliation (full).** If the interior pivot across position `m` exits the grid,
then the dropped facet `facetSet C m` lies entirely on the boundary face `{x_c = 0}`, where
`c = (σ⟨m⟩).succ`. The coordinate `c` is touched only at positions `m−1` (by `+1`) and `m` (by `−1`)
— by injectivity of `σ` — so along the path it is `0` except the single peak at the dropped vertex
`m`; validity plus the endpoint `v_{m−1}(c) = 0` (from `interior_invalid_basevertex`) pin it.
This is `degree-1 ⟹ on a boundary face` for interior positions. -/
theorem interior_degree_one_onFace (C : KCell (n + 1) k) (hC : Valid C) (m : Fin (n + 2))
    (hm0 : 0 < (m : ℕ)) (hmn : (m : ℕ) < n + 1)
    (hinv : ¬ Valid (pivot C (Equiv.swap (⟨(m : ℕ) - 1, by omega⟩ : Fin (n + 1))
      (⟨(m : ℕ), hmn⟩ : Fin (n + 1))))) :
    OnFace (facetSet C m) (C.order (⟨(m : ℕ), hmn⟩ : Fin (n + 1))).succ := by
  have hb := interior_invalid_basevertex C hC m hm0 hmn hinv
  set i : Fin (n + 1) := ⟨(m : ℕ) - 1, by omega⟩ with hidef
  set jj : Fin (n + 1) := ⟨(m : ℕ), hmn⟩ with hjdef
  set c : Fin (n + 2) := (C.order jj).succ with hc
  have hiv : (i : ℕ) = (m : ℕ) - 1 := by rw [hidef]
  have hjv : (jj : ℕ) = (m : ℕ) := by rw [hjdef]
  have hij : i ≠ jj := by
    apply Fin.ne_of_val_ne; rw [hiv, hjv]; omega
  have hisjc : i.succ = jj.castSucc := by
    apply Fin.ext; rw [Fin.val_succ, Fin.val_castSucc, hiv, hjv]; omega
  -- move (σ jj) c = -1
  have hmjj : move (C.order jj) c = -1 := by rw [hc]; exact move_apply_succ _
  -- move (σ i) c = 1, from hb + validity at position m+1
  have hmi : move (C.order i) c = 1 := by
    have hstep1 := vertex_succ_sub C i c
    rw [hb, hisjc] at hstep1
    have hstep2 := vertex_succ_sub C jj c
    have hge := hC jj.succ c
    rw [hmjj] at hstep2
    have hle := move_apply_le_one (C.order i) c
    omega
  -- (σ i).castSucc = c
  have hicast : c = (C.order i).castSucc := by
    by_contra h
    simp only [move] at hmi
    rw [if_neg h] at hmi
    split at hmi <;> omega
  -- only i, jj touch coordinate c
  have htouch : ∀ p : Fin (n + 1), p ≠ i → p ≠ jj → move (C.order p) c = 0 := by
    intro p hpi hpj
    have h1 : c ≠ (C.order p).castSucc := by
      intro hcc
      exact hpi (C.order.injective (Fin.castSucc_injective (n + 1) (hicast.symm.trans hcc))).symm
    have h2 : c ≠ (C.order p).succ := by
      intro hcs
      exact hpj (C.order.injective (Fin.succ_injective (n + 1) (hc.symm.trans hcs))).symm
    simp only [move, if_neg h1, if_neg h2, sub_zero]
  -- the move-values as an indicator
  have hg : ∀ p : Fin (n + 1),
      move (C.order p) c = (if p = i then (1 : ℤ) else 0) + (if p = jj then -1 else 0) := by
    intro p
    by_cases hpi : p = i
    · rw [hpi, if_pos rfl, if_neg hij]; simpa using hmi
    · by_cases hpj : p = jj
      · rw [hpj, if_neg (Ne.symm hij), if_pos rfl]; simpa using hmjj
      · rw [if_neg hpi, if_neg hpj]; simpa using htouch p hpi hpj
  -- the partial sum along the path
  have hsum : ∀ l : Fin (n + 2),
      ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ)), move (C.order p) c
      = (if i ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ)) then (1 : ℤ) else 0)
        + (if jj ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ)) then -1 else 0) :=
        by
    intro l
    rw [Finset.sum_congr rfl (fun p _ => hg p), Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
  -- base coordinate is 0
  have hbc : (C.base c : ℤ) = 0 := by
    have h0 : vertex C i.castSucc c = (C.base c : ℤ)
        + ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (i.castSucc : ℕ)),
          move (C.order p) c := rfl
    rw [hsum i.castSucc] at h0
    have hii : i ∉ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (i.castSucc : ℕ)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]; omega
    have hji : jj ∉ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (i.castSucc : ℕ)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
      rw [hiv, hjv]; omega
    rw [if_neg hii, if_neg hji] at h0
    rw [hb] at h0
    omega
  -- conclude OnFace
  intro v hv
  rw [facetSet, Finset.mem_image] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have hlm : (l : ℕ) ≠ (m : ℕ) := fun h => Finset.ne_of_mem_erase hl (Fin.ext h)
  have hvl : vertex C l c = (C.base c : ℤ)
      + ∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ)),
        move (C.order p) c := rfl
  rw [hsum l, hbc] at hvl
  have hil : (i ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ)))
      ↔ (jj ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ))) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hiv, hjv]; omega
  by_cases hi_mem : i ∈ Finset.univ.filter (fun p : Fin (n + 1) => (p : ℕ) < (l : ℕ))
  · rw [if_pos hi_mem, if_pos (hil.mp hi_mem)] at hvl; rw [hvl]; omega
  · rw [if_neg hi_mem, if_neg (fun h => hi_mem (hil.mpr h))] at hvl; rw [hvl]; omega

/-! ### Position-last up-neighbour (`pivotN`) — construction under nonnegativity

The neighbour across the position-`n+1` facet (drop the last vertex) is the "up-neighbour": base
shifted to `b − move (σ last)`, order rotated by `finRotate⁻¹`. Unlike `pivot0`, this base need not
be `≥ 0` under `Valid C` (it is not a vertex of `C`), so `pivotN` carries the explicit nonnegativity
hypothesis `hpos`. It is the constructed witness exhibiting degree-2 when the door is interior. -/

/-- The base of the position-last up-neighbour (over `ℕ` via `Int.toNat`, valid under `hpos`). -/
def baseShiftBaseN (C : KCell (n + 1) k) : Fin (n + 2) → ℕ :=
  fun j => ((C.base j : ℤ) - move (C.order (Fin.last n)) j).toNat

/-- Over `ℤ`, the up-neighbour base is `b − move (σ last)` (uses `hpos` for nonneg). -/
theorem baseShiftBaseN_eq (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) (j : Fin (n + 2)) :
    (baseShiftBaseN C j : ℤ) = (C.base j : ℤ) - move (C.order (Fin.last n)) j :=
  Int.toNat_of_nonneg (hpos j)

/-- The up-neighbour base sums to `k` (each move preserves the coordinate sum). -/
theorem baseShiftBaseN_sum (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) :
    ∑ j, baseShiftBaseN C j = k := by
  have h : ((∑ j, baseShiftBaseN C j : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun j _ => baseShiftBaseN_eq C hpos j),
      Finset.sum_sub_distrib, sum_move_zero, ← Nat.cast_sum, C.base_sum]
    omega
  exact_mod_cast h

/-- **Position-last up-neighbour.** The neighbour of `C` across its last-vertex facet: base shifted
to `b − move (σ last)`, order rotated by `finRotate⁻¹`. Defined only when its base is `≥ 0`
(hypothesis `hpos`) — the up-neighbour is in-grid iff the door is not on the boundary. -/
def pivotN (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) : KCell (n + 1) k where
  base := baseShiftBaseN C
  base_sum := baseShiftBaseN_sum C hpos
  order := C.order * (finRotate (n + 1)).symm

/-- **Facet-sharing for the up-neighbour.** `pivotN C` realises the position-last facet of `C`: its
vertex at position `p.succ` is `C`'s vertex at position `p.castSucc` (so positions `1..n+1` of
`pivotN` are `C`'s `{v_0,…,v_n}`). Induction on the position via `vertex_succ_sub`; the rotation
`finRotate⁻¹` realigns the shifted base. -/
theorem vertex_pivotN (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) (p : Fin (n + 1)) :
    vertex (pivotN C hpos) p.succ = vertex C p.castSucc := by
  funext x
  induction p using Fin.induction with
  | zero =>
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero]
    have hsymm : (finRotate (n + 1)).symm 0 = Fin.last n := by
      rw [finRotate_succ_symm_apply]; apply Fin.ext; simp
    have hord : (pivotN C hpos).order 0 = C.order (Fin.last n) := by
      change (C.order * (finRotate (n + 1)).symm) 0 = C.order (Fin.last n)
      rw [Equiv.Perm.mul_apply, hsymm]
    have hss := vertex_succ_sub (pivotN C hpos) 0 x
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero, hord] at hss
    have hbe : ((pivotN C hpos).base x : ℤ)
        = (C.base x : ℤ) - move (C.order (Fin.last n)) x := baseShiftBaseN_eq C hpos x
    omega
  | succ i ih =>
    have hsymm : (finRotate (n + 1)).symm i.succ = i.castSucc := by
      apply Fin.ext
      rw [coe_finRotate_symm_of_ne_zero (Fin.succ_ne_zero i), Fin.val_succ, Fin.val_castSucc]
      omega
    have hord : (pivotN C hpos).order i.succ = C.order i.castSucc := by
      change (C.order * (finRotate (n + 1)).symm) i.succ = C.order i.castSucc
      rw [Equiv.Perm.mul_apply, hsymm]
    have hp := vertex_succ_sub (pivotN C hpos) i.succ x
    rw [hord, ← Fin.succ_castSucc, ih] at hp
    have hc' := vertex_succ_sub C i.castSucc x
    rw [Fin.succ_castSucc] at hc'
    omega

/-- `pivotN C` shares the entire position-last facet of `C`. -/
theorem facetSet_last_subset (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) :
    facetSet C (Fin.last (n + 1)) ⊆ vertexSet (pivotN C hpos) := by
  intro x hx
  unfold facetSet at hx
  rw [Finset.mem_image] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  have hll : l ≠ Fin.last (n + 1) := Finset.ne_of_mem_erase hl
  obtain ⟨p, rfl⟩ : ∃ p : Fin (n + 1), p.castSucc = l :=
    ⟨l.castPred hll, Fin.castSucc_castPred l hll⟩
  rw [← vertex_pivotN C hpos p]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- A transfer move raises exactly its `castSucc` coordinate by one. -/
theorem move_apply_castSucc (a : Fin n) : move a a.castSucc = 1 := by
  have hne : a.castSucc ≠ a.succ := by
    intro h; have := congrArg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
  simp [move, hne]

/-- The up-neighbour is a valid cell (its shared vertices are `C`'s facet, its new top vertex is the
nonnegative shifted base) — so it exhibits degree-2 whenever it is in-grid. -/
theorem pivotN_valid (C : KCell (n + 1) k) (hC : Valid C)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) :
    Valid (pivotN C hpos) := by
  intro m j
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [vertex_zero]; exact Int.natCast_nonneg _
  · obtain ⟨p, rfl⟩ : ∃ p : Fin (n + 1), p.succ = m := ⟨m.pred hm0, Fin.succ_pred m hm0⟩
    rw [vertex_pivotN C hpos p]; exact hC p.castSucc j

/-- The up-neighbour is a genuinely different cell (its base is shifted at coordinate
`(σ last).succ`). -/
theorem pivotN_ne (C : KCell (n + 1) k)
    (hpos : ∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j) : pivotN C hpos ≠ C := by
  intro h
  set j₀ := (C.order (Fin.last n)).succ with hj₀
  have hbase_eq : (pivotN C hpos).base = C.base := congrArg KCell.base h
  have hb : (baseShiftBaseN C j₀ : ℤ) = (C.base j₀ : ℤ) := by exact_mod_cast congrFun hbase_eq j₀
  rw [baseShiftBaseN_eq C hpos j₀] at hb
  have hmove : move (C.order (Fin.last n)) j₀ = -1 := by rw [hj₀]; exact move_apply_succ _
  rw [hmove] at hb
  omega

/-- **Position-last reconciliation (full).** If the up-neighbour `pivotN C` cannot be formed in-grid
(`¬ hpos`, i.e. the position-last door is degree-1), then the dropped facet `facetSet C (last)` lies
on the boundary face `{x_c = 0}`, `c = (σ last).castSucc`. As for position-0 but mirrored: `¬hpos`
forces `base(c) = v_0(c) = 0`; `sum_all_moves_coord` then forces `c = 0` (i.e. `σ last = 0`); and
`c` is touched only at position `last` (by `+1`, beyond the facet), so `{v_0,…,v_n}` sits at `0`. -/
theorem boundaryN_degree_one_onFace (C : KCell (n + 1) k) (hC : Valid C)
    (hpos : ¬ (∀ j, 0 ≤ (C.base j : ℤ) - move (C.order (Fin.last n)) j)) :
    OnFace (facetSet C (Fin.last (n + 1))) (C.order (Fin.last n)).castSucc := by
  set c : Fin (n + 2) := (C.order (Fin.last n)).castSucc with hc
  have hbc0 : (C.base c : ℤ) = 0 := by
    rw [not_forall] at hpos
    obtain ⟨j, hj⟩ := hpos
    rw [not_le] at hj
    have hble := move_apply_le_one (C.order (Fin.last n)) j
    have hbge : (0 : ℤ) ≤ (C.base j : ℤ) := Int.natCast_nonneg _
    have hbj0 : (C.base j : ℤ) = 0 := by omega
    have hmove1 : move (C.order (Fin.last n)) j = 1 := by omega
    have hjc : j = c := by
      by_contra hne
      simp only [move] at hmove1
      rw [if_neg (show j ≠ (C.order (Fin.last n)).castSucc by rw [← hc]; exact hne)] at hmove1
      split at hmove1 <;> omega
    rw [← hjc]; exact hbj0
  have hcl : c ≠ Fin.last (n + 1) := by
    rw [hc]; apply Fin.ne_of_val_ne
    rw [Fin.val_castSucc, Fin.val_last]
    have := (C.order (Fin.last n)).isLt; omega
  have hmovel : move (C.order (Fin.last n)) c = 1 := by rw [hc]; exact move_apply_castSucc _
  have hfilt : (Finset.univ.filter
      (fun p : Fin (n + 1) => (p : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ))) = Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, iff_true]
    exact p.isLt
  have hlastsum : vertex C (Fin.last (n + 1)) c = (C.base c : ℤ) + ∑ p, move (C.order p) c := by
    unfold vertex; rw [hfilt]
  rw [sum_all_moves_coord, if_neg hcl, hbc0] at hlastsum
  have hlsucc : (Fin.last n).succ = Fin.last (n + 1) := by
    apply Fin.ext; simp
  have hvn := vertex_succ_sub C (Fin.last n) c
  rw [hlsucc, hmovel] at hvn
  have hvnge := hC (Fin.last n).castSucc c
  have hc0 : c = 0 := by
    by_contra h; rw [if_neg h] at hlastsum; omega
  have htouch : ∀ p : Fin (n + 1), p ≠ Fin.last n → move (C.order p) c = 0 := by
    intro p hp
    have h1 : c ≠ (C.order p).castSucc := by
      rw [hc]; intro hcc
      exact hp (C.order.injective (Fin.castSucc_injective (n + 1) hcc)).symm
    have h2 : c ≠ (C.order p).succ := by
      rw [hc0]; intro hcs; exact Fin.succ_ne_zero _ hcs.symm
    simp only [move]; rw [if_neg h1, if_neg h2]; omega
  intro v hv
  rw [facetSet, Finset.mem_image] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have hll : l ≠ Fin.last (n + 1) := Finset.ne_of_mem_erase hl
  have hlv : (l : ℕ) ≤ n := by
    have h1 := l.isLt
    have h2 : (l : ℕ) ≠ n + 1 := fun h => hll (Fin.ext (by rw [Fin.val_last]; exact h))
    omega
  change vertex C l c = 0
  unfold vertex
  rw [Finset.sum_congr rfl (fun p hp => htouch p (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Fin.ne_of_val_ne (by rw [Fin.val_last]; omega))), Finset.sum_const_zero, add_zero, hbc0]

/-- **Degree-1 ⟹ on the face opposite vertex `n` (plumbing).** A colored door `facetSet C₀ m₀` of a
valid cell `C₀`, contained in `C₀` as its *only* valid cell (`hsing` — i.e. degree-1), lies on the
boundary face `{x_last = 0}`. The unique neighbour (interior pivot / `pivot0` / `pivotN`, by the
position of `m₀`) would be a second valid sharer unless it exits the grid, so the relevant
reconciliation hypothesis holds, giving `OnFace` at some coordinate `c`; admissibility
(`not_onFace_of_coloredDoor`) then forces `c = last`. This funnels every degree-1 door onto one
face — the bridge to the dimension recursion. -/
theorem door_degree_one_onFace_last
    (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1)) (hadm : SpernerAdmissible col)
    (C₀ : KCell (n + 1) k) (hC₀ : Valid C₀) (hk : 0 < k) (m₀ : Fin (n + 2))
    (hcol : IsColoredDoor col (facetSet C₀ m₀))
    (hsing : ∀ C', Valid C' → facetSet C₀ m₀ ⊆ vertexSet C' → C' = C₀) :
    OnFace (facetSet C₀ m₀) (Fin.last (n + 1)) := by
  have hdpos : ∀ v ∈ facetSet C₀ m₀, 0 < ∑ j, v j := by
    intro v hv
    rw [facetSet, Finset.mem_image] at hv
    obtain ⟨l, _, rfl⟩ := hv
    rw [sum_vertex]; exact_mod_cast hk
  have confine : ∀ c : Fin (n + 1 + 1), OnFace (facetSet C₀ m₀) c →
      OnFace (facetSet C₀ m₀) (Fin.last (n + 1)) := by
    intro c hof
    rcases eq_or_ne c (Fin.last (n + 1)) with hcl | hcl
    · rwa [hcl] at hof
    · exact absurd hof (not_onFace_of_coloredDoor col hadm (facetSet C₀ m₀) hcol hdpos c hcl)
  rcases eq_or_ne m₀ 0 with rfl | hm0
  · refine confine _ (boundary0_degree_one_onFace C₀ hC₀ (fun hval => ?_))
    exact pivot0_ne C₀ hC₀ (hsing _ hval (facetSet_zero_subset C₀ hC₀))
  rcases eq_or_ne m₀ (Fin.last (n + 1)) with rfl | hml
  · refine confine _ (boundaryN_degree_one_onFace C₀ hC₀ (fun hpos => ?_))
    exact pivotN_ne C₀ hpos (hsing _ (pivotN_valid C₀ hC₀ hpos) (facetSet_last_subset C₀ hpos))
  · have hm0v : 0 < (m₀ : ℕ) := by
      rcases Nat.eq_zero_or_pos (m₀ : ℕ) with h | h
      · exact absurd (Fin.ext h) hm0
      · exact h
    have hmnv : (m₀ : ℕ) < n + 1 := by
      have hne : (m₀ : ℕ) ≠ n + 1 := fun h => hml (Fin.ext (by rw [Fin.val_last]; exact h))
      have := m₀.isLt; omega
    have hij : (⟨(m₀ : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ ⟨(m₀ : ℕ), hmnv⟩ := by
      apply Fin.ne_of_val_ne; simp only; omega
    refine confine _ (interior_degree_one_onFace C₀ hC₀ m₀ hm0v hmnv (fun hval => ?_))
    have hswne : Equiv.swap (⟨(m₀ : ℕ) - 1, by omega⟩ : Fin (n + 1)) ⟨(m₀ : ℕ), hmnv⟩ ≠ 1 := by
      intro h
      have h1 := Equiv.swap_apply_left (⟨(m₀ : ℕ) - 1, by omega⟩ : Fin (n + 1)) ⟨(m₀ : ℕ), hmnv⟩
      rw [h, Equiv.Perm.one_apply] at h1
      exact hij h1
    have hshare : facetSet C₀ m₀ ⊆ vertexSet (pivot C₀ (Equiv.swap
        (⟨(m₀ : ℕ) - 1, by omega⟩ : Fin (n + 1)) ⟨(m₀ : ℕ), hmnv⟩)) :=
      (facetSet_subset_iff C₀ _ m₀).mpr (fun l hl => ⟨l, pivot_shares C₀ m₀ hm0v hmnv hl⟩)
    exact pivot_ne hswne (hsing _ hval hshare)

/-- Glue: a door of incidence-degree `1` has `C₀` as its only valid sharer (`hsing`) — converting
the handshake's door-degree to the uniqueness hypothesis of `door_degree_one_onFace_last`. -/
theorem hsing_of_degree_one (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (C₀ : KCell (n + 1) k) (m₀ : Fin (n + 2)) (hC₀ : C₀ ∈ validCells (n + 1) k)
    (hd : facetSet C₀ m₀ ∈ doorFinset (n + 1) k col)
    (hdeg : ((incidence (n + 1) k col).filter (fun p => p.2 = facetSet C₀ m₀)).card = 1) :
    ∀ C', Valid C' → facetSet C₀ m₀ ⊆ vertexSet C' → C' = C₀ := by
  rw [doorDegree_eq col (facetSet C₀ m₀) hd] at hdeg
  intro C' hCv hsub
  have hmemC' : C' ∈ (validCells (n + 1) k).filter
      (fun C'' => facetSet C₀ m₀ ⊆ vertexSet C'') :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_cells C', hCv⟩, hsub⟩
  have hmemC₀ : C₀ ∈ (validCells (n + 1) k).filter
      (fun C'' => facetSet C₀ m₀ ⊆ vertexSet C'') :=
    Finset.mem_filter.mpr ⟨hC₀, facetSet_subset_vertexSet C₀ m₀⟩
  exact Finset.card_le_one.mp (le_of_eq hdeg) C' hmemC' C₀ hmemC₀

/-- **Move projection (dimension-drop atom).** Deleting the last coordinate of a non-last transfer
move yields the corresponding move one dimension down: `dropFace (move a) = move a.castPred`. (The
last move `σ = last` is the only one touching the dropped coordinate; all others project cleanly.)
This is what lets a face-`last` door's vertices form a `KCell n k` cell. -/
theorem dropFace_move (a : Fin (n + 1)) (hne : a ≠ Fin.last n) :
    dropFace (move a) = move (a.castPred hne) := by
  funext j
  simp only [dropFace, move, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, Fin.coe_castPred]

/-- The projected move order of the dropped cell: with `σ 0 = last`, the moves at positions `1..n`
land in `{0,…,n−1}` (the non-last moves) and reindex to a permutation of `Fin n`,
`p ↦ (σ p.succ).castPred`. (`σ p.succ ≠ last` since `σ⁻¹ last = 0` and `p.succ ≠ 0`.) -/
noncomputable def dropOrder (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = Fin.last n) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective
    (fun p => (σ p.succ).castPred
      (fun heq => Fin.succ_ne_zero p (σ.injective (heq.trans hσ.symm))))
    (Finite.injective_iff_bijective.mp
      (fun _ _ h => Fin.succ_injective n (σ.injective (Fin.castPred_inj.mp h))))

/-- The base of the dropped cell: the dropped first vertex `v_1` of `C₀` (`φ`-max of the door
`facetSet C₀ 0`), over `ℕ` via `Int.toNat`. -/
def dropCellBase (C₀ : KCell (n + 1) k) : Fin (n + 1) → ℕ :=
  fun j => (vertex C₀ 1 j.castSucc).toNat

theorem dropCellBase_eq (C₀ : KCell (n + 1) k) (hC₀ : Valid C₀) (j : Fin (n + 1)) :
    (dropCellBase C₀ j : ℤ) = dropFace (vertex C₀ 1) j :=
  Int.toNat_of_nonneg (hC₀ 1 j.castSucc)

theorem dropCellBase_sum (C₀ : KCell (n + 1) k) (hC₀ : Valid C₀)
    (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0) :
    ∑ j, dropCellBase C₀ j = k := by
  have h : ((∑ j, dropCellBase C₀ j : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun j _ => dropCellBase_eq C₀ hC₀ j),
      sum_dropFace, sum_vertex, hv1last]
    omega
  exact_mod_cast h

/-- **The dropped cell.** From a cell `C₀` whose first move is the last move (`σ 0 = last`, so its
position-0 facet `{v_1,…,v_{n+1}}` lies on the face `{x_last = 0}`), the dimension-dropped
`(n−1)`-cell: base `dropFace v_1`, order `dropOrder σ`. This is the image of a degree-1 colored door
under the recursion's drop. -/
noncomputable def dropCell (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n) (hC₀ : Valid C₀)
    (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0) : KCell n k where
  base := dropCellBase C₀
  base_sum := dropCellBase_sum C₀ hC₀ hv1last
  order := dropOrder C₀.order hσ

/-- **Drop link.** The vertices of the dropped cell are the dropped door vertices:
`vertex (dropCell C₀) p = dropFace (vertex C₀ p.succ)`. Induction on the position; each step uses
`dropFace_move` (the move projection) to match `dropOrder`'s moves with `C₀`'s. So `dropFace`
carries `facetSet C₀ 0` onto `vertexSet (dropCell C₀)`. -/
theorem vertex_dropCell (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n) (hC₀ : Valid C₀)
    (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0) (p : Fin (n + 1)) :
    vertex (dropCell C₀ hσ hC₀ hv1last) p = dropFace (vertex C₀ p.succ) := by
  funext x
  induction p using Fin.induction with
  | zero =>
    rw [Fin.succ_zero_eq_one, vertex_zero]
    exact dropCellBase_eq C₀ hC₀ x
  | succ i ih =>
    simp only [dropFace] at ih ⊢
    rw [Fin.succ_castSucc] at ih
    have hne : C₀.order i.succ ≠ Fin.last n :=
      fun heq => Fin.succ_ne_zero i (C₀.order.injective (heq.trans hσ.symm))
    have hdo : (dropCell C₀ hσ hC₀ hv1last).order i = (C₀.order i.succ).castPred hne := by
      simp only [dropCell, dropOrder, Equiv.ofBijective_apply]
    have hvs_drop := vertex_succ_sub (dropCell C₀ hσ hC₀ hv1last) i x
    rw [hdo] at hvs_drop
    have hvs_C := vertex_succ_sub C₀ i.succ x.castSucc
    have hMM : move ((C₀.order i.succ).castPred hne) x = move (C₀.order i.succ) x.castSucc := by
      rw [← dropFace_move (C₀.order i.succ) hne]; rfl
    omega

/-- The dropped cell's vertex set is the `dropFace`-image of the door `facetSet C₀ 0` (reindexing
positions `1..n+1` of `C₀` to `0..n` of the dropped cell). -/
theorem vertexSet_dropCell (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n) (hC₀ : Valid C₀)
    (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0) :
    vertexSet (dropCell C₀ hσ hC₀ hv1last) = Finset.image dropFace (facetSet C₀ 0) := by
  have hsucc_image : Finset.image Fin.succ (Finset.univ : Finset (Fin (n + 1)))
      = (Finset.univ : Finset (Fin (n + 2))).erase 0 := by
    ext l
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨fun ⟨p, hp⟩ => hp ▸ Fin.succ_ne_zero p, fun hl => ⟨l.pred hl, Fin.succ_pred l hl⟩⟩
  unfold vertexSet facetSet
  rw [Finset.image_image, ← hsucc_image, Finset.image_image]
  exact Finset.image_congr (fun x _ => vertex_dropCell C₀ hσ hC₀ hv1last x)

/-- The dropped cell is valid (its vertices are the dropped door vertices, all `≥ 0`). -/
theorem dropCell_valid (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n) (hC₀ : Valid C₀)
    (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0) :
    Valid (dropCell C₀ hσ hC₀ hv1last) := by
  intro p j
  rw [vertex_dropCell C₀ hσ hC₀ hv1last p]
  simp only [dropFace]
  exact hC₀ p.succ j.castSucc

/-- Embed a point of the `(n−1)`-simplex into the face `{x_last = 0}` of the `n`-simplex (inverse of
`dropFace` on that face): keep the coordinates, set the last to `0`. -/
def extend (w : Fin (n + 1) → ℤ) : Fin (n + 2) → ℤ :=
  fun j => if h : j = Fin.last (n + 1) then 0 else w (j.castPred h)

@[simp] theorem extend_last (w : Fin (n + 1) → ℤ) : extend w (Fin.last (n + 1)) = 0 := by
  simp [extend]

/-- Embedding into the face preserves the coordinate sum (the new last coordinate is `0`). -/
theorem sum_extend (w : Fin (n + 1) → ℤ) : ∑ j, extend w j = ∑ j, w j := by
  rw [Fin.sum_univ_castSucc]
  simp only [extend_last, add_zero]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [extend, dif_neg (Fin.castSucc_lt_last i).ne, Fin.castPred_castSucc]

theorem dropFace_extend (w : Fin (n + 1) → ℤ) : dropFace (extend w) = w := by
  funext j
  have hne : j.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last j).ne
  simp only [dropFace, extend, dif_neg hne, Fin.castPred_castSucc]

theorem extend_dropFace (v : Fin (n + 2) → ℤ) (hlast : v (Fin.last (n + 1)) = 0) :
    extend (dropFace v) = v := by
  funext j
  by_cases h : j = Fin.last (n + 1)
  · simp [extend, h, hlast]
  · simp only [extend, dif_neg h, dropFace, Fin.castSucc_castPred]

/-- The induced `(n−1)`-coloring on the face `{x_last = 0}`: color a point `w` by `col` of its
embedding, with the value `castPred`-ed into `Fin (n+1)`. Well-defined because admissibility forbids
color `last` on the face (`extend w` has last coordinate `0`). -/
def inducedColoring (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (hadm : SpernerAdmissible col) (w : Fin (n + 1) → ℤ) : Fin (n + 1) :=
  if h : 0 < ∑ j, w j then
    (col (extend w)).castPred
      (hadm (extend w) (Fin.last (n + 1)) (by rw [sum_extend]; exact h) (extend_last w))
  else 0

/-- On a genuine grid point (`0 < ∑ w`) the induced color is `col (extend w)`, demoted to
`Fin (n+1)`; equivalently its `castSucc` is `col (extend w)`. -/
theorem inducedColoring_castSucc (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (hadm : SpernerAdmissible col) (w : Fin (n + 1) → ℤ) (hw : 0 < ∑ j, w j) :
    (inducedColoring col hadm w).castSucc = col (extend w) := by
  rw [inducedColoring, dif_pos hw, Fin.castSucc_castPred]

/-- The induced coloring is again Sperner-admissible. -/
theorem inducedColoring_admissible (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (hadm : SpernerAdmissible col) : SpernerAdmissible (inducedColoring col hadm) := by
  intro w i hwsum hwi hcol
  have hci : col (extend w) = i.castSucc := by
    have h := congrArg Fin.castSucc hcol
    rwa [inducedColoring_castSucc col hadm w hwsum] at h
  have hwic : extend w i.castSucc = 0 := by
    have hne : i.castSucc ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last i).ne
    simp only [extend, dif_neg hne, Fin.castPred_castSucc]
    exact hwi
  exact hadm (extend w) i.castSucc (by rw [sum_extend]; exact hwsum) hwic hci

/-- The induced coloring of a dropped-cell vertex equals (the `castSucc` of) `col` on the
corresponding door vertex of `C₀` — given the door lies on the face (`hface`). Links the `(n−1)`-dim
rainbow condition of `dropCell` to the colored-door condition of `facetSet C₀ 0`. -/
theorem inducedColoring_dropCell (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (hadm : SpernerAdmissible col) (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n)
    (hC₀ : Valid C₀) (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0)
    (hface : ∀ i : Fin (n + 1), vertex C₀ i.succ (Fin.last (n + 1)) = 0) (hk : 0 < k)
    (i : Fin (n + 1)) :
    (inducedColoring col hadm (vertex (dropCell C₀ hσ hC₀ hv1last) i)).castSucc
      = col (vertex C₀ i.succ) := by
  have hpos : (0 : ℤ) < ∑ j, vertex (dropCell C₀ hσ hC₀ hv1last) i j := by
    rw [sum_vertex]; exact_mod_cast hk
  rw [inducedColoring_castSucc col hadm _ hpos, vertex_dropCell, extend_dropFace _ (hface i)]

/-- `Fin.castSucc` images `univ` onto `{0,…,n}` (everything but `last`). -/
theorem image_castSucc_univ :
    Finset.image Fin.castSucc (Finset.univ : Finset (Fin (n + 1)))
      = (Finset.univ : Finset (Fin (n + 2))).erase (Fin.last (n + 1)) := by
  ext l
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  exact ⟨fun ⟨p, hp⟩ => hp ▸ (Fin.castSucc_lt_last p).ne, fun hl => ⟨l.castPred hl, by simp⟩⟩

/-- `Fin.succ` images `univ` onto `{1,…,n+1}` (everything but `0`). -/
theorem image_succ_univ :
    Finset.image Fin.succ (Finset.univ : Finset (Fin (n + 1)))
      = (Finset.univ : Finset (Fin (n + 2))).erase 0 := by
  ext l
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  exact ⟨fun ⟨p, hp⟩ => hp ▸ Fin.succ_ne_zero p, fun hl => ⟨l.pred hl, Fin.succ_pred l hl⟩⟩

/-- **Rainbow ⟺ colored door (drop side).** The dropped cell is rainbow under the induced coloring
iff `facetSet C₀ 0` is a `{0,…,n}`-colored door — the colour side of the drop bijection. Both reduce
to "the door colours, `castSucc`-shifted, exhaust `{0,…,n}`", via `inducedColoring_dropCell`. -/
theorem rainbow_dropCell_iff (col : (Fin (n + 1 + 1) → ℤ) → Fin (n + 1 + 1))
    (hadm : SpernerAdmissible col) (C₀ : KCell (n + 1) k) (hσ : C₀.order 0 = Fin.last n)
    (hC₀ : Valid C₀) (hv1last : vertex C₀ 1 (Fin.last (n + 1)) = 0)
    (hface : ∀ i : Fin (n + 1), vertex C₀ i.succ (Fin.last (n + 1)) = 0) (hk : 0 < k) :
    IsRainbowCell (inducedColoring col hadm) (dropCell C₀ hσ hC₀ hv1last)
      ↔ IsColoredDoor col (facetSet C₀ 0) := by
  have key : Finset.image col (facetSet C₀ 0)
      = Finset.image Fin.castSucc (Finset.image
        (fun i => inducedColoring col hadm (vertex (dropCell C₀ hσ hC₀ hv1last) i))
        Finset.univ) := by
    unfold facetSet
    rw [← image_succ_univ, Finset.image_image, Finset.image_image, Finset.image_image]
    exact Finset.image_congr (fun i _ => (inducedColoring_dropCell col hadm C₀ hσ hC₀ hv1last
      hface hk i).symm)
  rw [IsRainbowCell, IsColoredDoor, key, ← image_castSucc_univ,
    (Finset.image_injective (Fin.castSucc_injective (n + 1))).eq_iff]
  constructor
  · intro hbij
    rw [Finset.eq_univ_iff_forall]
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
  · intro himg
    apply Finite.surjective_iff_bijective.mp
    intro y
    have hy : y ∈ Finset.image
        (fun i => inducedColoring col hadm (vertex (dropCell C₀ hσ hC₀ hv1last) i))
        Finset.univ := by rw [himg]; exact Finset.mem_univ y
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩

/-- **Every valid cell has last base-coordinate `≥ 1`.** The last coordinate of the path decreases
by exactly `1` (only the `val (n−1)` move touches it, lowering it once) and stays `≥ 0`, so the base
value there is `≥ 1`. Hence no valid cell has `base last = 0` — `dropCell`'s image is *all* rainbow
valid `KCell n` cells (resolving the apparent gap in the drop bijection). -/
theorem base_last_pos (D : KCell (n + 1) k) (hD : Valid D) :
    1 ≤ D.base (Fin.last (n + 1)) := by
  have hl0 : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    apply Fin.ne_of_val_ne; rw [Fin.val_last, Fin.val_zero]; omega
  have hsum := sum_all_moves_coord D (Fin.last (n + 1))
  rw [if_neg hl0, if_pos rfl] at hsum
  have hfilt : (Finset.univ.filter
      (fun p : Fin (n + 1) => (p : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ))) = Finset.univ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, iff_true]
    exact p.isLt
  have hvl : vertex D (Fin.last (n + 1)) (Fin.last (n + 1))
      = (D.base (Fin.last (n + 1)) : ℤ) + ∑ p, move (D.order p) (Fin.last (n + 1)) := by
    unfold vertex; rw [hfilt]
  have hge := hD (Fin.last (n + 1)) (Fin.last (n + 1))
  rw [hvl, hsum] at hge
  omega

/-- The lifted move order (inverse of `dropOrder`): place the last move at position `0`, then `D`'s
moves `castSucc`-shifted. `Fin.cons (last) (castSucc ∘ τ)`, a permutation since `last` avoids the
`castSucc`-image. -/
noncomputable def liftOrder (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (Fin.cons (Fin.last (n + 1)) (fun p => (τ p).castSucc))
    (Finite.injective_iff_bijective.mp (Fin.cons_injective_iff.mpr
      ⟨fun ⟨p, hp⟩ => (Fin.castSucc_lt_last (τ p)).ne hp,
        fun _ _ h => τ.injective (Fin.castSucc_injective (n + 1) h)⟩))

/-- The base (apex vertex) of the lifted cell: `extend D.base − move last` (the grid point one step
inward above the face). Nonnegative by `base_last_pos`. -/
def liftCellBase (D : KCell (n + 1) k) : Fin (n + 3) → ℕ :=
  fun j => (extend (fun i => (D.base i : ℤ)) j - move (Fin.last (n + 1)) j).toNat

theorem liftCellBase_eq (D : KCell (n + 1) k) (hD : Valid D) (j : Fin (n + 3)) :
    (liftCellBase D j : ℤ) = extend (fun i => (D.base i : ℤ)) j - move (Fin.last (n + 1)) j := by
  apply Int.toNat_of_nonneg
  have hlsucc : (Fin.last (n + 2) : Fin (n + 3)) = (Fin.last (n + 1)).succ := by
    apply Fin.ext; rw [Fin.val_succ, Fin.val_last, Fin.val_last]
  by_cases hj : j = Fin.last (n + 2)
  · subst hj
    rw [extend_last, hlsucc, move_apply_succ]; omega
  · simp only [extend, dif_neg hj]
    by_cases hjn : (j : ℕ) = n + 1
    · have hbp : j.castPred hj = Fin.last (n + 1) := by
        apply Fin.ext; rw [Fin.coe_castPred, Fin.val_last]; exact hjn
      have hmove : move (Fin.last (n + 1)) j = 1 := by
        rw [show j = (Fin.last (n + 1)).castSucc by
          apply Fin.ext; rw [Fin.val_castSucc, Fin.val_last]; exact hjn]
        exact move_apply_castSucc _
      rw [hbp, hmove]
      have := base_last_pos D hD; omega
    · have h1 : j ≠ (Fin.last (n + 1)).castSucc :=
        fun hc => hjn (by rw [hc, Fin.val_castSucc, Fin.val_last])
      have h2 : j ≠ (Fin.last (n + 1)).succ := fun hc => hj (by rw [hc, ← hlsucc])
      have hmv : move (Fin.last (n + 1)) j = 0 := by simp only [move, if_neg h1, if_neg h2]; omega
      rw [hmv]
      have : (0 : ℤ) ≤ (D.base (j.castPred hj) : ℤ) := Int.natCast_nonneg _
      omega

theorem liftCellBase_sum (D : KCell (n + 1) k) (hD : Valid D) : ∑ j, liftCellBase D j = k := by
  have h : ((∑ j, liftCellBase D j : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun j _ => liftCellBase_eq D hD j),
      Finset.sum_sub_distrib, sum_move_zero]
    have hext : ∑ j : Fin (n + 3), extend (fun i => (D.base i : ℤ)) j
        = ∑ i : Fin (n + 2), (D.base i : ℤ) := by
      rw [Fin.sum_univ_castSucc, extend_last, add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [extend, dif_neg (Fin.castSucc_lt_last i).ne, Fin.castPred_castSucc]
    rw [hext, ← Nat.cast_sum, D.base_sum]; omega
  exact_mod_cast h

/-- **The lifted cell** (inverse of `dropCell`): the `(n+2)`-cell having `D` as its position-0 facet
on the face `{x_last = 0}` — apex `liftCellBase D` (off the face), first move `last`, then `D`'s
moves. Valid for valid `D` thanks to `base_last_pos`. -/
noncomputable def liftCell (D : KCell (n + 1) k) (hD : Valid D) : KCell (n + 2) k where
  base := liftCellBase D
  base_sum := liftCellBase_sum D hD
  order := liftOrder D.order

theorem liftOrder_apply_zero (τ : Equiv.Perm (Fin (n + 1))) :
    liftOrder τ 0 = Fin.last (n + 1) := by
  simp only [liftOrder, Equiv.ofBijective_apply, Fin.cons_zero]

theorem liftOrder_apply_succ (τ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1)) :
    liftOrder τ p.succ = (τ p).castSucc := by
  simp only [liftOrder, Equiv.ofBijective_apply, Fin.cons_succ]

/-- The orders round-trip: `dropOrder (liftOrder τ) = τ`. -/
theorem dropOrder_liftOrder (τ : Equiv.Perm (Fin (n + 1)))
    (h : liftOrder τ 0 = Fin.last (n + 1)) : dropOrder (liftOrder τ) h = τ := by
  ext p
  simp only [dropOrder, Equiv.ofBijective_apply, liftOrder_apply_succ, Fin.castPred_castSucc]

/-- A non-last move, embedded into the face, becomes the `castSucc`-shifted move (inverse of
`dropFace_move`). -/
theorem extend_move (a : Fin (n + 1)) : extend (move a) = move a.castSucc := by
  funext j
  by_cases hj : j = Fin.last (n + 2)
  · subst hj
    have h1 : (Fin.last (n + 2) : Fin (n + 3)) ≠ (a.castSucc).castSucc := by
      apply Fin.ne_of_val_ne
      rw [Fin.val_last, Fin.val_castSucc, Fin.val_castSucc]; have := a.isLt; omega
    have h2 : (Fin.last (n + 2) : Fin (n + 3)) ≠ (a.castSucc).succ := by
      apply Fin.ne_of_val_ne
      rw [Fin.val_last, Fin.val_succ, Fin.val_castSucc]; have := a.isLt; omega
    rw [extend_last]; simp only [move, if_neg h1, if_neg h2]; omega
  · rw [extend, dif_neg hj]
    simp only [move, Fin.ext_iff, Fin.coe_castPred, Fin.val_castSucc, Fin.val_succ]

/-- `extend` is linear (commutes with subtraction). -/
theorem extend_sub (f g : Fin (n + 1) → ℤ) : extend (f - g) = extend f - extend g := by
  funext j
  simp only [extend, Pi.sub_apply]
  split <;> simp

/-- The first door vertex of the lifted cell is the embedded base of `D` (`v₁ = extend D.base`). -/
theorem vertex_liftCell_one (D : KCell (n + 1) k) (hD : Valid D) (j : Fin (n + 3)) :
    vertex (liftCell D hD) 1 j = extend (fun i => (D.base i : ℤ)) j := by
  have hss := vertex_succ_sub (liftCell D hD) 0 j
  rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss
  have hord0 : (liftCell D hD).order 0 = Fin.last (n + 1) := liftOrder_apply_zero D.order
  rw [hord0] at hss
  have hbe : ((liftCell D hD).base j : ℤ)
      = extend (fun i => (D.base i : ℤ)) j - move (Fin.last (n + 1)) j := liftCellBase_eq D hD j
  omega

/-- The lifted cell's door vertices are the embedded vertices of `D`:
`vertex (liftCell D) p.succ = extend (vertex D p)`. -/
theorem vertex_liftCell_succ (D : KCell (n + 1) k) (hD : Valid D) (p : Fin (n + 2)) :
    vertex (liftCell D hD) p.succ = extend (vertex D p) := by
  funext x
  induction p using Fin.induction with
  | zero =>
    rw [Fin.succ_zero_eq_one, vertex_liftCell_one,
      show vertex D 0 = (fun i => (D.base i : ℤ)) from funext (vertex_zero D)]
  | succ i ih =>
    have hord : (liftCell D hD).order i.succ = (D.order i).castSucc :=
      liftOrder_apply_succ D.order i
    have hss := vertex_succ_sub (liftCell D hD) i.succ x
    rw [hord, ← Fin.succ_castSucc, ih] at hss
    have hextf : extend (vertex D i.succ) - extend (vertex D i.castSucc)
        = move ((D.order i).castSucc) := by
      have hv : vertex D i.succ - vertex D i.castSucc = move (D.order i) := by
        funext y; rw [Pi.sub_apply]; exact vertex_succ_sub D i y
      rw [← extend_sub, hv, extend_move]
    have hext := congrFun hextf x
    rw [Pi.sub_apply] at hext
    omega

/-- The lifted cell is valid (apex base `≥ 0`, door vertices are `D`'s valid vertices). -/
theorem liftCell_valid (D : KCell (n + 1) k) (hD : Valid D) : Valid (liftCell D hD) := by
  intro p j
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [vertex_zero]; exact Int.natCast_nonneg _
  · obtain ⟨q, rfl⟩ : ∃ q, q.succ = p := ⟨p.pred hp0, Fin.succ_pred p hp0⟩
    rw [vertex_liftCell_succ]
    simp only [extend]
    split
    · omega
    · exact hD q _

theorem liftCell_order0 (D : KCell (n + 1) k) (hD : Valid D) :
    (liftCell D hD).order 0 = Fin.last (n + 1) := liftOrder_apply_zero D.order

theorem liftCell_v1last (D : KCell (n + 1) k) (hD : Valid D) :
    vertex (liftCell D hD) 1 (Fin.last (n + 2)) = 0 := by
  rw [vertex_liftCell_one, extend_last]

/-- **The cells round-trip: `dropCell (liftCell D) = D`.** With `dropOrder_liftOrder` (orders) and
`vertex_liftCell_one` + `dropFace_extend` (base), the dimension drop inverts the lift. This (plus
injectivity) gives the drop bijection. -/
theorem dropCell_liftCell (D : KCell (n + 1) k) (hD : Valid D) :
    dropCell (liftCell D hD) (liftCell_order0 D hD) (liftCell_valid D hD)
      (liftCell_v1last D hD) = D := by
  apply KCell.ext
  · funext j
    change (vertex (liftCell D hD) 1 j.castSucc).toNat = D.base j
    rw [vertex_liftCell_one]
    have hde : extend (fun i => (D.base i : ℤ)) j.castSucc = (D.base j : ℤ) :=
      congrFun (dropFace_extend (fun i => (D.base i : ℤ))) j
    rw [hde, Int.toNat_natCast]
  · exact dropOrder_liftOrder D.order (liftCell_order0 D hD)

/-- The lifted door is on the boundary: `pivot0 (liftCell D)` exits the grid (its bottom vertex has
last coordinate `0 − 1 < 0`). Hence the door `facetSet (liftCell D) 0` is degree-1. -/
theorem liftCell_pivot0_invalid (D : KCell (n + 1) k) (hD : Valid D) :
    ¬ Valid (pivot0 (liftCell D hD) (liftCell_valid D hD)) := by
  intro hval
  have hls : (Fin.last (n + 2) : Fin (n + 3)) = (Fin.last (n + 1)).succ := by
    apply Fin.ext; simp
  have h := hval (Fin.last (n + 2)) (Fin.last (n + 2))
  rw [vertex_pivot0_last] at h
  have hv : vertex (liftCell D hD) (Fin.last (n + 2)) (Fin.last (n + 2)) = 0 := by
    have hvf : vertex (liftCell D hD) (Fin.last (n + 2))
        = extend (vertex D (Fin.last (n + 1))) := by
      rw [hls]; exact vertex_liftCell_succ D hD (Fin.last (n + 1))
    rw [hvf, extend_last]
  have hm : move ((liftCell D hD).order 0) (Fin.last (n + 2)) = -1 := by
    rw [liftCell_order0, hls]; exact move_apply_succ _
  rw [hv, hm] at h
  omega

/-- `liftCell D` is the *only* valid cell containing its position-0 facet (the neighbour `pivot0` is
invalid by `liftCell_pivot0_invalid`). This is the `hsing` / degree-1 condition for the lifted
door. -/
theorem liftCell_unique_sharer (D : KCell (n + 1) k) (hD : Valid D) :
    ∀ C', Valid C' → facetSet (liftCell D hD) 0 ⊆ vertexSet C' → C' = liftCell D hD := by
  intro C' hC'v hsub
  rcases pseudomanifold_zero (liftCell D hD) C' (liftCell_valid D hD)
    ((facetSet_subset_iff (liftCell D hD) C' 0).mp hsub) with h | h
  · exact h
  · rw [h] at hC'v
    exact absurd hC'v (liftCell_pivot0_invalid D hD)

/-- A cell is determined by its vertex set (the base is the unique `φ`-maximal vertex, and `φ`
pins each position). Used for injectivity of the drop bijection. -/
theorem cell_eq_of_vertexSet (D D' : KCell n k) (h : vertexSet D = vertexSet D') : D = D' := by
  have hΦ : phi (fun j => (D.base j : ℤ)) = phi (fun j => (D'.base j : ℤ)) := by
    have h0 : ((0 : Fin (n + 1)) : ℤ) = 0 := by simp
    have hd : vertex D 0 ∈ vertexSet D' := by
      rw [← h]; exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    have hd' : vertex D' 0 ∈ vertexSet D := by
      rw [h]; exact Finset.mem_image_of_mem _ (Finset.mem_univ 0)
    rw [vertexSet, Finset.mem_image] at hd hd'
    obtain ⟨q, _, hq⟩ := hd
    obtain ⟨q', _, hq'⟩ := hd'
    have e1 := congrArg phi hq
    have e2 := congrArg phi hq'
    rw [phi_vertex_eq, phi_vertex_eq, h0] at e1 e2
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.zero_le (q : ℕ)
    have hq'0 : (0 : ℤ) ≤ (q' : ℤ) := by exact_mod_cast Nat.zero_le (q' : ℕ)
    omega
  have hv : ∀ p, vertex D p = vertex D' p := by
    intro p
    have hin : vertex D p ∈ vertexSet D' := by
      rw [← h]; exact Finset.mem_image_of_mem _ (Finset.mem_univ p)
    rw [vertexSet, Finset.mem_image] at hin
    obtain ⟨q, _, hq⟩ := hin
    have hpq := congrArg phi hq
    rw [phi_vertex_eq, phi_vertex_eq, hΦ] at hpq
    have hqp : q = p := Fin.ext (by exact_mod_cast (by omega : (q : ℤ) = (p : ℤ)))
    rw [← hq, hqp]
  apply KCell.ext
  · funext j
    have hx := congrFun (hv 0) j
    rw [vertex_zero, vertex_zero] at hx
    exact_mod_cast hx
  · apply Equiv.ext
    intro p
    refine move_injective ?_
    funext x
    rw [← vertex_succ_sub D p x, ← vertex_succ_sub D' p x, hv p.succ, hv p.castSucc]

/-- `D`'s vertex set is the `dropFace`-image of its lifted door (round-trip). -/
theorem vertexSet_eq_dropFace_facet (D : KCell (n + 1) k) (hD : Valid D) :
    vertexSet D = Finset.image dropFace (facetSet (liftCell D hD) 0) := by
  conv_lhs => rw [← dropCell_liftCell D hD]
  exact vertexSet_dropCell (liftCell D hD) (liftCell_order0 D hD) (liftCell_valid D hD)
    (liftCell_v1last D hD)

/-- The map `D ↦ facetSet (liftCell D) 0` is injective (different rainbow cells give different
doors), via the round-trip and `cell_eq_of_vertexSet`. -/
theorem liftCell_facet_inj (D D' : KCell (n + 1) k) (hD : Valid D) (hD' : Valid D')
    (heq : facetSet (liftCell D hD) 0 = facetSet (liftCell D' hD') 0) : D = D' := by
  apply cell_eq_of_vertexSet
  rw [vertexSet_eq_dropFace_facet D hD, vertexSet_eq_dropFace_facet D' hD', heq]

/-- The orders round-trip (other direction): `liftOrder (dropOrder σ) = σ` when `σ 0 = last`. -/
theorem liftOrder_dropOrder (σ : Equiv.Perm (Fin (n + 2))) (hσ : σ 0 = Fin.last (n + 1)) :
    liftOrder (dropOrder σ hσ) = σ := by
  ext p
  induction p using Fin.cases with
  | zero => rw [liftOrder_apply_zero, hσ]
  | succ q =>
    rw [liftOrder_apply_succ]
    simp only [dropOrder, Equiv.ofBijective_apply, Fin.castSucc_castPred]

/-- **The cells round-trip (other direction): `liftCell (dropCell C₀) = C₀`** when `C₀` has
`σ 0 = last` (i.e. its position-0 facet is on the boundary face). Together with `dropCell_liftCell`
this makes `dropCell`/`liftCell` mutually inverse — giving surjectivity of the drop bijection. -/
theorem liftCell_dropCell (C₀ : KCell (n + 2) k) (hσ : C₀.order 0 = Fin.last (n + 1))
    (hC₀ : Valid C₀) (hv1last : vertex C₀ 1 (Fin.last (n + 2)) = 0) :
    liftCell (dropCell C₀ hσ hC₀ hv1last) (dropCell_valid C₀ hσ hC₀ hv1last) = C₀ := by
  apply KCell.ext
  · funext j
    change liftCellBase (dropCell C₀ hσ hC₀ hv1last) j = C₀.base j
    have hbe := liftCellBase_eq (dropCell C₀ hσ hC₀ hv1last)
      (dropCell_valid C₀ hσ hC₀ hv1last) j
    have hdbase : (fun i => ((dropCell C₀ hσ hC₀ hv1last).base i : ℤ)) = dropFace (vertex C₀ 1) :=
      funext (fun i => dropCellBase_eq C₀ hC₀ i)
    rw [hdbase, extend_dropFace _ hv1last, ← hσ] at hbe
    have hvs := vertex_succ_sub C₀ 0 j
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hvs
    omega
  · exact liftOrder_dropOrder C₀.order hσ

/-- **FINDING K-3 (formalised).** A door on the face `{x_last = 0}` is dropped at position `0` from
a cell whose first move is `last`, base last-coordinate `1`. (`OnFace` at `l=0` + validity bound
`base(last) ≥ 1` ⟹ `m₀ = 0`; `l = last` ⟹ `base(last) = 1`; `l = 1` ⟹ `v₁(last) = 0` ⟹ `σ0 = last`.)
The surjectivity input for the drop bijection. -/
theorem door_onFace_last_structure (C₀ : KCell (n + 2) k) (hC₀ : Valid C₀) (m₀ : Fin (n + 3))
    (hof : OnFace (facetSet C₀ m₀) (Fin.last (n + 2))) :
    m₀ = 0 ∧ C₀.order 0 = Fin.last (n + 1) ∧ vertex C₀ 1 (Fin.last (n + 2)) = 0 := by
  set c : Fin (n + 3) := Fin.last (n + 2) with hc
  have honf : ∀ l : Fin (n + 3), l ≠ m₀ → vertex C₀ l c = 0 := fun l hl =>
    hof _ (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩))
  have hc0 : c ≠ 0 := by rw [hc]; apply Fin.ne_of_val_ne; rw [Fin.val_last, Fin.val_zero]; omega
  have hlasteq : vertex C₀ c c = (C₀.base c : ℤ) - 1 := by
    have hfilt : (Finset.univ.filter (fun p : Fin (n + 2) => (p : ℕ) < (c : ℕ))) = Finset.univ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc, Fin.val_last, iff_true]
      exact p.isLt
    have hvl : vertex C₀ c c = (C₀.base c : ℤ) + ∑ p, move (C₀.order p) c := by
      unfold vertex; rw [hfilt]
    rw [hvl, sum_all_moves_coord, if_neg hc0, ← hc, if_pos rfl]; omega
  have hbge : 1 ≤ (C₀.base c : ℤ) := by have := hC₀ c c; rw [hlasteq] at this; omega
  have hm0 : m₀ = 0 := by
    by_contra hne
    have := honf 0 (Ne.symm hne)
    rw [vertex_zero] at this; omega
  subst hm0
  have hb1 : (C₀.base c : ℤ) = 1 := by
    have hlne : c ≠ 0 := hc0
    have := honf c hlne; rw [hlasteq] at this; omega
  have hv1eq : vertex C₀ 1 c = (C₀.base c : ℤ) + move (C₀.order 0) c := by
    have hss := vertex_succ_sub C₀ 0 c
    rw [Fin.succ_zero_eq_one, Fin.castSucc_zero, vertex_zero] at hss; omega
  have h1ne : (1 : Fin (n + 3)) ≠ 0 := by rw [Ne, Fin.ext_iff]; simp
  have hv1 := honf 1 h1ne
  refine ⟨rfl, ?_, hv1⟩
  rw [hv1eq, hb1] at hv1
  have hmove : move (C₀.order 0) c = -1 := by omega
  have hcs : c = (C₀.order 0).succ := by
    by_contra h
    simp only [move] at hmove
    rw [if_neg h] at hmove
    split at hmove <;> omega
  apply Fin.ext
  have hcv := congrArg Fin.val hcs
  rw [hc, Fin.val_last, Fin.val_succ] at hcv
  rw [Fin.val_last]; omega

/-- Auxiliary: `hface` for the lifted cell (its door vertices are on the face). -/
theorem liftCell_hface (D : KCell (n + 1) k) (hD : Valid D) (i : Fin (n + 2)) :
    vertex (liftCell D hD) i.succ (Fin.last (n + 2)) = 0 := by
  rw [vertex_liftCell_succ D hD i]; exact extend_last _

/-- The lifted door is a colored door whenever `D` is rainbow under the induced coloring. -/
theorem liftCell_isColoredDoor (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (D : KCell (n + 1) k) (hD : Valid D)
    (hrain : IsRainbowCell (inducedColoring col hadm) D) (hk : 0 < k) :
    IsColoredDoor col (facetSet (liftCell D hD) 0) := by
  rw [← rainbow_dropCell_iff col hadm (liftCell D hD) (liftCell_order0 D hD) (liftCell_valid D hD)
    (liftCell_v1last D hD) (liftCell_hface D hD) hk]
  rwa [dropCell_liftCell D hD]

/-- The lifted door lies in `doorFinset`. -/
theorem liftCell_door_mem (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (D : KCell (n + 1) k) (hD : Valid D)
    (hrain : IsRainbowCell (inducedColoring col hadm) D) (hk : 0 < k) :
    facetSet (liftCell D hD) 0 ∈ doorFinset (n + 2) k col := by
  unfold doorFinset
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_image.mpr ⟨(liftCell D hD, 0),
    Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_cells _, liftCell_valid D hD⟩,
      Finset.mem_univ _⟩, rfl⟩, liftCell_isColoredDoor col hadm D hD hrain hk⟩

/-- The lifted door has incidence-degree exactly `1` (`liftCell D` is its only valid sharer). -/
theorem liftCell_door_deg1 (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (D : KCell (n + 1) k) (hD : Valid D)
    (hrain : IsRainbowCell (inducedColoring col hadm) D) (hk : 0 < k) :
    ((incidence (n + 2) k col).filter
      (fun p => p.2 = facetSet (liftCell D hD) 0)).card = 1 := by
  rw [doorDegree_eq col (facetSet (liftCell D hD) 0) (liftCell_door_mem col hadm D hD hrain hk),
    Finset.card_eq_one]
  refine ⟨liftCell D hD, ?_⟩
  ext C'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hsub⟩
    exact liftCell_unique_sharer D hD C' (Finset.mem_filter.mp hmem).2 hsub
  · rintro rfl
    exact ⟨Finset.mem_filter.mpr ⟨mem_cells _, liftCell_valid D hD⟩,
      facetSet_subset_vertexSet _ _⟩

/-- **Surjectivity of the drop bijection.** Every degree-1 colored door equals the lifted door of a
rainbow valid cell (`D = dropCell C₀`). Uses K-3 (`door_onFace_last_structure`) to get the
`σ0=last`/`m₀=0` structure and `liftCell_dropCell` to invert. -/
theorem door_deg1_eq_liftCell (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (hk : 0 < k) (d : Finset (Fin (n + 2 + 1) → ℤ))
    (hd : d ∈ doorFinset (n + 2) k col)
    (hdeg : ((incidence (n + 2) k col).filter (fun p => p.2 = d)).card = 1) :
    ∃ (D : KCell (n + 1) k) (hD : Valid D),
      IsRainbowCell (inducedColoring col hadm) D ∧ facetSet (liftCell D hD) 0 = d := by
  have hd' := hd
  unfold doorFinset at hd'
  rw [Finset.mem_filter, Finset.mem_image] at hd'
  obtain ⟨⟨⟨C₀, m₀⟩, hmem, hfd⟩, hcol⟩ := hd'
  rw [Finset.mem_product] at hmem
  have hC₀mem : C₀ ∈ validCells (n + 2) k := hmem.1
  have hC₀v : Valid C₀ := (Finset.mem_filter.mp hC₀mem).2
  have hsing := hsing_of_degree_one col C₀ m₀ hC₀mem (hfd.symm ▸ hd) (hfd.symm ▸ hdeg)
  have hcol' : IsColoredDoor col (facetSet C₀ m₀) := hfd.symm ▸ hcol
  have honf := door_degree_one_onFace_last col hadm C₀ hC₀v hk m₀ hcol' hsing
  obtain ⟨hm0, hσ, hv1⟩ := door_onFace_last_structure C₀ hC₀v m₀ honf
  subst hm0
  have hface : ∀ i : Fin (n + 2), vertex C₀ i.succ (Fin.last (n + 2)) = 0 := fun i =>
    honf _ (Finset.mem_image_of_mem _
      (Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩))
  refine ⟨dropCell C₀ hσ hC₀v hv1, dropCell_valid C₀ hσ hC₀v hv1, ?_, ?_⟩
  · rw [rainbow_dropCell_iff col hadm C₀ hσ hC₀v hv1 hface hk]; exact hcol'
  · rw [liftCell_dropCell C₀ hσ hC₀v hv1]; exact hfd

/-- **THE DROP BIJECTION (card form).** The number of degree-1 colored doors of `KCell (n+2)`
equals the number of rainbow valid `KCell (n+1)` cells under the induced coloring. The bijection
is `D ↦ facetSet (liftCell D) 0`: injective by `liftCell_facet_inj`, well-targeted by
`liftCell_door_mem`/`liftCell_door_deg1`, surjective by `door_deg1_eq_liftCell` (K-3). This is the
dimension-recursion step of Sperner's lemma. -/
theorem drop_card_bij (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (hk : 0 < k) :
    ((doorFinset (n + 2) k col).filter
        (fun d => ((incidence (n + 2) k col).filter (fun p => p.2 = d)).card = 1)).card
      = ((validCells (n + 1) k).filter (IsRainbowCell (inducedColoring col hadm))).card := by
  refine (Finset.card_bij
    (fun D hDmem => facetSet (liftCell D
      (Finset.mem_filter.mp (Finset.mem_filter.mp hDmem).1).2) 0) ?_ ?_ ?_).symm
  · intro D hDmem
    have hDv : Valid D := (Finset.mem_filter.mp (Finset.mem_filter.mp hDmem).1).2
    have hrain : IsRainbowCell (inducedColoring col hadm) D := (Finset.mem_filter.mp hDmem).2
    exact Finset.mem_filter.mpr ⟨liftCell_door_mem col hadm D hDv hrain hk,
      liftCell_door_deg1 col hadm D hDv hrain hk⟩
  · intro D₁ h₁ D₂ h₂ heq
    exact liftCell_facet_inj D₁ D₂ _ _ heq
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨D, hDv, hrain, hfd⟩ := door_deg1_eq_liftCell col hadm hk d hd.1 hd.2
    exact ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_cells D, hDv⟩, hrain⟩, hfd⟩

/-- **SPERNER PARITY RECURSION STEP.** The number of rainbow valid `KCell (n+2)` cells and the
number of rainbow valid `KCell (n+1)` cells under the induced coloring have equal parity. Chains
the parity bridge `rainbow_parity_degree_one_doors` with the drop bijection `drop_card_bij`. -/
theorem rainbow_parity_step (col : (Fin (n + 2 + 1) → ℤ) → Fin (n + 2 + 1))
    (hadm : SpernerAdmissible col) (hk : 0 < k) :
    ((validCells (n + 2) k).filter (IsRainbowCell col)).card % 2
      = ((validCells (n + 1) k).filter (IsRainbowCell (inducedColoring col hadm))).card % 2 := by
  rw [rainbow_parity_degree_one_doors k col, drop_card_bij col hadm hk]

/-- **GENERAL SPERNER (recursion closed, modulo the 1-D base).** Given the one-dimensional base
case, an admissible coloring of the grid `KCell m` (any `m ≥ 1`) has an *odd* number of rainbow
valid cells. The dimension induction runs entirely on `rainbow_parity_step` (drop bijection) and
`inducedColoring_admissible`; the base hypothesis is the `n = 1` Sperner segment count. -/
theorem sperner_odd_of_base (hk : 0 < k)
    (base : ∀ (col : (Fin (1 + 1) → ℤ) → Fin (1 + 1)) (_ : SpernerAdmissible col),
      Odd ((validCells 1 k).filter (IsRainbowCell col)).card) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (col : (Fin (m + 1) → ℤ) → Fin (m + 1)) (_ : SpernerAdmissible col),
      Odd ((validCells m k).filter (IsRainbowCell col)).card := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    intro col hadm
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ihc := ih (inducedColoring col hadm) (inducedColoring_admissible col hadm)
    rw [Nat.odd_iff] at ihc ⊢
    rw [rainbow_parity_step col hadm hk]
    exact ihc

/-! ### The one-dimensional base case `P(1)`

`KCell 1` has a trivial move-order (`Perm (Fin 1)`), so a cell is determined by `base 0`; its two
vertices are `![a, k-a]` and `![a+1, k-a-1]`. Validity forces `base 1 ≥ 1` (i.e. `base 0 < k`), and
rainbow means the two endpoint colours differ. This is exactly the 1-D Sperner door count along the
bottom edge, settled by `Sperner.odd_doors`. -/

/-- `move (0 : Fin 1)` is the elementary `e₀ − e₁` shift on `Fin 2`. -/
theorem move_zero_fin1 (j : Fin 2) :
    move (0 : Fin 1) j = (if j = 0 then 1 else 0) - (if j = 1 then 1 else 0) := by
  unfold move; rw [Fin.castSucc_zero, Fin.succ_zero_eq_one]

/-- The first vertex of a `KCell 1` cell is `![base 0, base 1]`. -/
theorem kcell1_vertex0 (C : KCell 1 k) :
    vertex C 0 = ![(C.base 0 : ℤ), (C.base 1 : ℤ)] := by
  funext j; fin_cases j <;> simp [vertex_zero]

/-- The second vertex of a `KCell 1` cell is `![base 0 + 1, base 1 − 1]`. -/
theorem kcell1_vertex1 (C : KCell 1 k) :
    vertex C 1 = ![(C.base 0 : ℤ) + 1, (C.base 1 : ℤ) - 1] := by
  have hfilt : (Finset.univ.filter (fun l : Fin 1 => (l : ℕ) < ((1 : Fin 2) : ℕ)))
      = Finset.univ := Finset.filter_true_of_mem fun l _ => l.isLt
  funext j
  unfold vertex
  rw [hfilt, Fin.sum_univ_one, show C.order 0 = (0 : Fin 1) from Subsingleton.elim _ _,
    move_zero_fin1]
  fin_cases j <;> simp [sub_eq_add_neg]

/-- A self-map of `Fin 2` is bijective iff it separates the two points. -/
theorem bijective_fin2_iff (g : Fin 2 → Fin 2) : Function.Bijective g ↔ g 0 ≠ g 1 := by
  constructor
  · intro hg h; exact absurd (hg.1 h) (by decide)
  · intro h
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => ?_, rfl⟩
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact absurd hab h | exact absurd hab.symm h

/-- For a `KCell 1` cell, rainbow means the two endpoint colours differ. -/
theorem kcell1_rainbow_iff (col : (Fin 2 → ℤ) → Fin 2) (C : KCell 1 k) :
    IsRainbowCell col C ↔ col (vertex C 0) ≠ col (vertex C 1) :=
  bijective_fin2_iff (fun i => col (vertex C i))

/-- In `Fin 2`, not equal to `1` means equal to `0`. -/
theorem fin2_eq_zero_of_ne_one {c : Fin 2} (h : c ≠ 1) : c = 0 := by
  fin_cases c <;> simp_all

/-- Two `Fin 2` values differ iff their `(· = 0)` indicators differ. -/
theorem fin2_ne_iff (a b : Fin 2) : a ≠ b ↔ (decide (a = 0) ≠ decide (b = 0)) := by
  fin_cases a <;> fin_cases b <;> simp

/-- The `KCell 1` base coordinates sum to `k`. -/
theorem kcell1_base_sum (C : KCell 1 k) : C.base 0 + C.base 1 = k := by
  have := C.base_sum; rwa [Fin.sum_univ_two] at this

/-- **SPERNER, the 1-D base case `P(1)`.** Under an admissible coloring of `Fin 2`, the number of
rainbow valid `KCell 1` cells is odd. Bridges to `Sperner.odd_doors` via the bottom-edge coloring
`f i = (col ![i, k-i] = 0)`: cells `↔ base 0 ∈ {0,…,k-1}`, rainbow `↔` a door of `f`. -/
theorem sperner_base (col : (Fin (1 + 1) → ℤ) → Fin (1 + 1)) (hadm : SpernerAdmissible col)
    (hk : 0 < k) : Odd ((validCells 1 k).filter (IsRainbowCell col)).card := by
  set f : ℕ → Bool := fun i => decide (col ![(i : ℤ), (k : ℤ) - i] = 0) with hf
  have hb1 : ∀ C : KCell 1 k, (C.base 1 : ℤ) = (k : ℤ) - C.base 0 := fun C => by
    have := kcell1_base_sum C; omega
  have hv0 : ∀ C : KCell 1 k, vertex C 0 = ![(C.base 0 : ℤ), (k : ℤ) - C.base 0] := fun C => by
    rw [kcell1_vertex0]; funext j; fin_cases j
    · rfl
    · exact hb1 C
  have hv1 : ∀ C : KCell 1 k, vertex C 1 = ![(C.base 0 : ℤ) + 1, (k : ℤ) - (C.base 0 + 1)] :=
    fun C => by
      rw [kcell1_vertex1]; funext j; have hh := hb1 C; fin_cases j
      · simp
      · simp
        omega
  have hcol0 : ∀ C : KCell 1 k, decide (col (vertex C 0) = 0) = f (C.base 0) := fun C => by
    rw [hf, hv0 C]
  have hcol1 : ∀ C : KCell 1 k, decide (col (vertex C 1) = 0) = f (C.base 0 + 1) := fun C => by
    rw [hf, hv1 C]; push_cast; rfl
  have hcard : ((validCells 1 k).filter (IsRainbowCell col)).card
      = Brouwer.Sperner.doors f k := by
    unfold Brouwer.Sperner.doors
    refine Finset.card_bij (fun C _ => C.base 0) ?_ ?_ ?_
    · intro C hC
      rw [Finset.mem_filter] at hC
      have hCv : Valid C := (Finset.mem_filter.mp hC.1).2
      have hb1pos : (1 : ℤ) ≤ C.base 1 := by
        have h := hCv 1 1
        rw [kcell1_vertex1] at h
        simp at h
        omega
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · change C.base 0 < k
        have hs := kcell1_base_sum C
        have hb1 : 1 ≤ C.base 1 := by exact_mod_cast hb1pos
        omega
      · rw [← hcol0 C, ← hcol1 C, ← fin2_ne_iff]
        exact (kcell1_rainbow_iff col C).mp hC.2
    · intro C₁ h₁ C₂ h₂ heq
      have heq' : C₁.base 0 = C₂.base 0 := heq
      have hb1eq : C₁.base 1 = C₂.base 1 := by
        have hs1 := kcell1_base_sum C₁; have hs2 := kcell1_base_sum C₂; omega
      apply KCell.ext
      · funext j
        fin_cases j
        · exact heq'
        · exact hb1eq
      · exact Subsingleton.elim _ _
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨⟨![i, k - i], by rw [Fin.sum_univ_two]; simp; omega, 1⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨mem_cells _, ?_⟩, ?_⟩
      · intro m j
        fin_cases m <;> fin_cases j <;>
          simp [kcell1_vertex0, kcell1_vertex1] <;> omega
      · rw [kcell1_rainbow_iff, fin2_ne_iff, hcol0, hcol1]
        exact hi.2
  rw [hcard]
  apply Brouwer.Sperner.odd_doors
  · rw [hf]
    simp only [Nat.cast_zero, sub_zero, decide_eq_false_iff_not]
    intro hc
    refine hadm _ 0 ?_ (by simp) hc
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  · rw [hf]
    simp only [decide_eq_true_iff]
    apply fin2_eq_zero_of_ne_one
    refine hadm _ 1 ?_ (by simp)
    rw [Fin.sum_univ_two]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

/-- **SPERNER'S LEMMA (parity form).** For every dimension `m ≥ 1` and every admissible (proper)
coloring of the resolution-`k` Kuhn grid, the number of rainbow valid cells is *odd*. Assembles the
dimension recursion (`sperner_odd_of_base`) with the one-dimensional base (`sperner_base`). -/
theorem sperner_odd (m : ℕ) (hm : 1 ≤ m) (col : (Fin (m + 1) → ℤ) → Fin (m + 1))
    (hadm : SpernerAdmissible col) (hk : 0 < k) :
    Odd ((validCells m k).filter (IsRainbowCell col)).card :=
  sperner_odd_of_base hk (fun col hadm => sperner_base col hadm hk) m hm col hadm

/-- **SPERNER'S LEMMA (existence form).** Every admissible coloring of the resolution-`k` Kuhn grid
(dimension `m ≥ 1`) has at least one rainbow valid cell — a cell whose vertices realize all `m+1`
colors. This is the combinatorial fixed-point precursor consumed by the approximate Brouwer step. -/
theorem exists_rainbow_cell (m : ℕ) (hm : 1 ≤ m) (col : (Fin (m + 1) → ℤ) → Fin (m + 1))
    (hadm : SpernerAdmissible col) (hk : 0 < k) :
    ∃ C, C ∈ validCells m k ∧ IsRainbowCell col C := by
  have hpos : 0 < ((validCells m k).filter (IsRainbowCell col)).card := by
    have h := sperner_odd (k := k) m hm col hadm hk; rw [Nat.odd_iff] at h; omega
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hC
  exact ⟨C, hC.1, hC.2⟩

end Brouwer.KuhnGen
