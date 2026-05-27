-- VRCycle/Topology/Tychonoff.lean
-- VR-Topology v1.0.0 — Stage 6: Binary Tychonoff (Mode B Audit).
--
-- Constructive binary Tychonoff for operational compact formal topologies,
-- following Vickers 2006 ("Compactness in locales and in formal topology",
-- Theorem 19) and Vickers 2005 ("Some constructive roads to Tychonoff",
-- Theorem 0.6).  Built directly on the decomposition-based F-witness
-- (not upper closure of cartesian products).
--
-- Architectural commitment: zero `Classical.choice`.  Target axiom
-- profile: `[propext, Quot.sound]`.  Decidability hypotheses are
-- explicit (Finding T16) — Vickers's Kuratowski-finite setting carried
-- them implicitly; Lean 4 List encoding requires them as explicit
-- typeclass instances.
--
-- This is the Mode B audit object for VR-Topology v1.0.0.

import VRCycle.Topology.Compact
import Mathlib.Data.List.Sublists

-- Decidability hypotheses (Finding T16) are used in proof bodies via
-- `haveI` instance cascades for List.decidableBAll / decidableBEx; the
-- linter doesn't see them in the type signature.
set_option linter.unusedDecidableInType false

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 1: prodF definition (Vickers's decomposition-based F-witness)
-- ============================================================

/-- **F-witness for the binary product** (Vickers 2006 Theorem 19).

A list `T : List (T₁.S × T₂.S)` is in `prodF w₁ w₂` iff for every way of
splitting `T` into two sublists `T₁_part, T₂_part` (covering all elements
in the sense that every element of T is in at least one part), either the
first-coordinate projection of `T₁_part` is in `w₁.F`, or the second-
coordinate projection of `T₂_part` is in `w₂.F`.

This decomposition predicate replaces the upper-closure-of-cartesian
formulation from the original PLAN_6.  Vickers's key insight: F can be
defined without reference to the full coverage relation. -/
def prodF
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov) :
    Set (List (T₁.S × T₂.S)) :=
  fun T =>
    ∀ T₁_part T₂_part : List (T₁.S × T₂.S),
      (∀ p, p ∈ T ↔ p ∈ T₁_part ∨ p ∈ T₂_part) →
      (T₁_part.map (·.1)) ∈ w₁.F ∨ (T₂_part.map (·.2)) ∈ w₂.F

-- ============================================================
-- Section 2: prodF_inhabited (PLAN §3.2)
-- ============================================================

/-- `prodF` is non-empty: a cartesian product of component F-witnesses
serves as witness.  Proof by finite case dispatch on whether some row
of the cartesian product is fully contained in T₂_part. -/
theorem prodF_inhabited
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov) :
    (prodF T₁ T₂ w₁ w₂).Nonempty := by
  obtain ⟨S₁, hS₁⟩ := w₁.inhabited
  obtain ⟨S₂, hS₂⟩ := w₂.inhabited
  let T_witness : List (T₁.S × T₂.S) :=
    S₁.flatMap (fun a₁ => S₂.map (fun a₂ => (a₁, a₂)))
  refine ⟨T_witness, ?_⟩
  intro T₁_part T₂_part hdecomp
  -- Explicit decidability to avoid Classical.em via by_cases fallback.
  haveI decPred : ∀ a₁ : T₁.S, Decidable (∃ a₂ ∈ S₂, (a₁, a₂) ∈ T₁_part) :=
    fun _ => List.decidableBEx _ _
  haveI decAll : Decidable (∀ a₁ ∈ S₁, ∃ a₂ ∈ S₂, (a₁, a₂) ∈ T₁_part) :=
    List.decidableBAll _ _
  -- Constructive extraction: ¬ ∀ ⇒ ∃ ¬ via induction on list (no Classical).
  have extract : ∀ (L : List T₁.S),
      ¬ (∀ a₁ ∈ L, ∃ a₂ ∈ S₂, (a₁, a₂) ∈ T₁_part) →
      ∃ a₁ ∈ L, ∀ a₂ ∈ S₂, (a₁, a₂) ∉ T₁_part := by
    intro L
    induction L with
    | nil => intro h; exfalso; exact h (fun _ ha => absurd ha List.not_mem_nil)
    | cons head tail ih =>
      intro h
      by_cases hh : ∃ a₂ ∈ S₂, (head, a₂) ∈ T₁_part
      · have h_tail : ¬ ∀ a₁ ∈ tail, ∃ a₂ ∈ S₂, (a₁, a₂) ∈ T₁_part := by
          intro ha_tail
          apply h
          intros a₁ ha₁
          rcases List.mem_cons.mp ha₁ with rfl | ha₁'
          · exact hh
          · exact ha_tail _ ha₁'
        obtain ⟨a₁, ha₁tail, ha₁'⟩ := ih h_tail
        exact ⟨a₁, List.mem_cons_of_mem _ ha₁tail, ha₁'⟩
      · refine ⟨head, List.mem_cons_self, ?_⟩
        intros a₂ ha₂ hin
        exact hh ⟨a₂, ha₂, hin⟩
  by_cases h : ∀ a₁ ∈ S₁, ∃ a₂ ∈ S₂, (a₁, a₂) ∈ T₁_part
  · -- Every a₁ has some (a₁, a₂) ∈ T₁_part.  So S₁ vL T₁_part.map (·.1).
    left
    apply w₁.upper_closed S₁ hS₁ (T₁_part.map (·.1))
    intro a₁ ha₁
    obtain ⟨a₂, _, hmem⟩ := h a₁ ha₁
    refine ⟨a₁, ?_, T₁.le_refl a₁⟩
    rw [List.mem_map]
    exact ⟨(a₁, a₂), hmem, rfl⟩
  · -- Some a₁ has no (a₁, a₂) ∈ T₁_part.  So all (a₁, a₂) ∈ T₂_part, hence S₂ vL T₂_part.snd.
    obtain ⟨a₁, ha₁S₁, h₂⟩ := extract S₁ h
    right
    apply w₂.upper_closed S₂ hS₂ (T₂_part.map (·.2))
    intro a₂ ha₂
    have hT : (a₁, a₂) ∈ T_witness := by
      change (a₁, a₂) ∈ S₁.flatMap (fun a₁ => S₂.map (fun a₂ => (a₁, a₂)))
      rw [List.mem_flatMap]
      refine ⟨a₁, ha₁S₁, ?_⟩
      rw [List.mem_map]
      exact ⟨a₂, ha₂, rfl⟩
    have h_in : (a₁, a₂) ∈ T₁_part ∨ (a₁, a₂) ∈ T₂_part := (hdecomp (a₁, a₂)).mp hT
    rcases h_in with hin1 | hin2
    · exfalso
      exact h₂ a₂ ha₂ hin1
    · refine ⟨a₂, ?_, T₂.le_refl a₂⟩
      rw [List.mem_map]
      exact ⟨(a₁, a₂), hin2, rfl⟩

-- ============================================================
-- Section 3: prodF_upper_closed (PLAN §3.1)
-- ============================================================

/-- `prodF` is closed under list lower order (Vickers's vL refinement).

Given `A ∈ prodF` and `A vL B`, for any decomposition of `B` we
construct a corresponding decomposition of `A` by placing each `a ∈ A`
with its `vL`-witness: if some `b ∈ B₁_part` refines `a`, place `a` in
`A₁_part`; otherwise place in `A₂_part`.  The construction requires
`DecidableRel prodLe` to decide witness location. -/
theorem prodF_upper_closed
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov) :
    ∀ A ∈ prodF T₁ T₂ w₁ w₂, ∀ B : List (T₁.S × T₂.S),
      FormalTopology.listLowerOrder (FormalTopology.prodLe T₁ T₂) A B →
      B ∈ prodF T₁ T₂ w₁ w₂ := by
  intro A hA B hAB B₁_part B₂_part hdecomp
  -- DecidableRel prodLe from components
  haveI decProdLe : ∀ a b : T₁.S × T₂.S, Decidable (FormalTopology.prodLe T₁ T₂ a b) :=
    fun a b => by
      change Decidable (T₁.le a.1 b.1 ∧ T₂.le a.2 b.2)
      infer_instance
  haveI decPredA : ∀ a : T₁.S × T₂.S,
      Decidable (∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b) :=
    fun _ => List.decidableBEx _ _
  -- Filter A by witness location.
  let A₁_part : List (T₁.S × T₂.S) :=
    A.filter (fun a => decide (∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b))
  let A₂_part : List (T₁.S × T₂.S) :=
    A.filter (fun a => !decide (∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b))
  -- A = A₁_part ∪ A₂_part
  have hAdecomp : ∀ p, p ∈ A ↔ p ∈ A₁_part ∨ p ∈ A₂_part := by
    intro p
    constructor
    · intro hp
      by_cases h : ∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ p b
      · left
        rw [List.mem_filter]
        exact ⟨hp, decide_eq_true h⟩
      · right
        rw [List.mem_filter]
        refine ⟨hp, ?_⟩
        rw [Bool.not_eq_true', decide_eq_false_iff_not]
        exact h
    · intro hp
      rcases hp with hp1 | hp2
      · exact (List.mem_filter.mp hp1).1
      · exact (List.mem_filter.mp hp2).1
  -- Apply hA
  rcases hA A₁_part A₂_part hAdecomp with hcase1 | hcase2
  · left
    apply w₁.upper_closed (A₁_part.map (·.1)) hcase1 (B₁_part.map (·.1))
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, haA1, hax⟩ := hx
    have hfilt := List.mem_filter.mp haA1
    have hwit : ∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b :=
      of_decide_eq_true hfilt.2
    obtain ⟨b, hbB1, hle⟩ := hwit
    refine ⟨b.1, ?_, ?_⟩
    · rw [List.mem_map]; exact ⟨b, hbB1, rfl⟩
    · rw [← hax]; exact hle.1
  · right
    apply w₂.upper_closed (A₂_part.map (·.2)) hcase2 (B₂_part.map (·.2))
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨a, haA2, hay⟩ := hy
    have hfilt := List.mem_filter.mp haA2
    have hno : ¬ ∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b := by
      have h2 : (!decide (∃ b ∈ B₁_part, FormalTopology.prodLe T₁ T₂ a b)) = true := hfilt.2
      rw [Bool.not_eq_true', decide_eq_false_iff_not] at h2
      exact h2
    obtain ⟨b, hbB, hle⟩ := hAB a hfilt.1
    have hbsplit : b ∈ B₁_part ∨ b ∈ B₂_part := (hdecomp b).mp hbB
    rcases hbsplit with hbB1 | hbB2
    · exfalso; exact hno ⟨b, hbB1, hle⟩
    · refine ⟨b.2, ?_, ?_⟩
      · rw [List.mem_map]; exact ⟨b, hbB2, rfl⟩
      · rw [← hay]; exact hle.2

-- ============================================================
-- Section 4: Helper — manyMeet and cov_meet_iter (PLAN §3.4)
-- ============================================================

/-- **Many-way common refinement**: a point `w` is in `manyMeet le Us` iff
for every cover `U ∈ Us`, `w` refines some element of `U`.  Generalises
binary `commonRefinement` (Sambin meet, Finding T7) to finite lists. -/
def manyMeet {α : Type*} (le : α → α → Prop) (Us : List (Set α)) : Set α :=
  { w | ∀ U ∈ Us, ∃ u ∈ U, le w u }

/-- **Iterated `cov_meet`**: given a finite list of covers (each covering
the same point `a`), the common refinement is also covered.  Generalises
Sambin's binary `cov_meet` (Stage 1 Finding T7) to finite lists. -/
theorem cov_meet_iter (T : FormalTopology) (a : T.S) :
    ∀ (Us : List (Set T.S)), (∀ U ∈ Us, T.cov a U) →
      T.cov a (manyMeet T.le Us) := by
  intro Us
  induction Us with
  | nil =>
    intro _
    apply T.cov_mono a {a} _ _ (T.cov_singleton a)
    intro x _ U' hU'
    exact absurd hU' List.not_mem_nil
  | cons V rest ih =>
    intro hAll
    have hV := hAll V List.mem_cons_self
    have hrest : ∀ U ∈ rest, T.cov a U := fun U hU => hAll U (List.mem_cons_of_mem _ hU)
    have hcov_rest := ih hrest
    have hcommon := T.cov_meet a V (manyMeet T.le rest) hV hcov_rest
    apply T.cov_mono a _ _ _ hcommon
    intro w hw
    obtain ⟨v, hv, m, hm, hwv, hwm⟩ := hw
    intro U' hU'
    rcases List.mem_cons.mp hU' with rfl | hU'rest
    · exact ⟨v, hv, hwv⟩
    · obtain ⟨u, hu, hmu⟩ := hm U' hU'rest
      exact ⟨u, hu, T.le_trans _ _ _ hwm hmu⟩

-- ============================================================
-- Section 5: Helper — cov_product_of_components (PLAN §3.4, Prop 18 analog)
-- ============================================================

/-- **Componentwise covers give product cover** (Vickers 2006 Prop 18 analog).

If `T₁.cov g₁ U` and `T₂.cov g₂ V`, then `(prod T₁ T₂).cov (g₁, g₂) (U × V)`.

In Vickers's disjunctive-basicCov setting this is non-trivial (induction
on the cover derivation).  Our **conjunctive `prodBasicCov`** (Stage 4
T14 form) makes the lemma trivial: take `U₁ = U`, `U₂ = V` directly in
the rectangular basic-cover witness. -/
theorem cov_product_of_components
    (T₁ T₂ : FormalTopology) (g₁ : T₁.S) (g₂ : T₂.S)
    (U : Set T₁.S) (V : Set T₂.S)
    (hU : T₁.cov g₁ U) (hV : T₂.cov g₂ V) :
    (FormalTopology.prod T₁ T₂).cov (g₁, g₂)
        {p : T₁.S × T₂.S | p.1 ∈ U ∧ p.2 ∈ V} :=
  CoverGen.basic ⟨U, V, hU, hV, rfl⟩

-- ============================================================
-- Section 6: Helper — product_decomposition_lemma (PLAN §3.4, Lemma 14 analog)
-- ============================================================

/-- **Product decomposition lemma** (Vickers 2006 Lemma 14 analog).

If for every decomposition `S = S₁ ∪ S₂` of a finite list `S` either some
element of `S₁` is `T₁.le`-refined by `u₁`, or some element of `S₂` is
`T₂.le`-refined by `u₂`, then there is a single element of `S` refined
on both coordinates.

Constructive proof: partition `S` by `T₁.le u₁ p.1` decidability into
α-refinable / α-not-refinable.  Apply hypothesis to this partition.  The
first disjunct contradicts the partition definition; the second yields
the witness directly. -/
theorem product_decomposition_lemma
    (T₁ T₂ : FormalTopology)
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le]
    (S : List (T₁.S × T₂.S)) (u₁ : T₁.S) (u₂ : T₂.S)
    (hyp : ∀ (S₁_part S₂_part : List (T₁.S × T₂.S)),
        (∀ p ∈ S, p ∈ S₁_part ∨ p ∈ S₂_part) →
        (∃ p ∈ S₁_part, T₁.le u₁ p.1) ∨ (∃ p ∈ S₂_part, T₂.le u₂ p.2)) :
    ∃ p ∈ S, T₁.le u₁ p.1 ∧ T₂.le u₂ p.2 := by
  let S₁_part := S.filter (fun p => !decide (T₁.le u₁ p.1))
  let S₂_part := S.filter (fun p => decide (T₁.le u₁ p.1))
  have hdecomp : ∀ p ∈ S, p ∈ S₁_part ∨ p ∈ S₂_part := by
    intro p hp
    by_cases hle : T₁.le u₁ p.1
    · right; rw [List.mem_filter]; exact ⟨hp, decide_eq_true hle⟩
    · left; rw [List.mem_filter]; refine ⟨hp, ?_⟩
      rw [Bool.not_eq_true', decide_eq_false_iff_not]; exact hle
  rcases hyp S₁_part S₂_part hdecomp with ⟨p, hpmem, hpr⟩ | ⟨p, hpmem, hpr⟩
  · -- First disjunct: p ∈ S₁_part has T₁.le u₁ p.1, contradicting filter.
    exfalso
    have hfilt := List.mem_filter.mp hpmem
    have hno : ¬ T₁.le u₁ p.1 := by
      have h2 := hfilt.2
      rw [Bool.not_eq_true', decide_eq_false_iff_not] at h2
      exact h2
    exact hno hpr
  · -- Second disjunct: p ∈ S₂_part means T₁.le u₁ p.1; combined with hpr.
    have hfilt := List.mem_filter.mp hpmem
    have hT₁ : T₁.le u₁ p.1 := of_decide_eq_true hfilt.2
    exact ⟨p, hfilt.1, hT₁, hpr⟩

-- ============================================================
-- Section 6b: Helper — buildVStar (iterative V₁*, V₂* extraction)
-- ============================================================

/-- **Iteratively build aggregate V*'s from a list of decompositions with
existential witnesses**.  For each `d ∈ L`, given `∃ V₁ V₂` with V₁⊆U₁,
V₂⊆U₂, V₁ ++ d.1 ∈ F_α, V₂ ++ d.2 ∈ F_β, build aggregate `V₁*` and `V₂*`
such that the F-membership holds for every d via upper_closed extension. -/
private theorem buildVStar
    {α β : Type*}
    (le_α : α → α → Prop) (le_β : β → β → Prop)
    (le_α_refl : ∀ x, le_α x x) (le_β_refl : ∀ x, le_β x x)
    (F_α : Set (List α)) (F_β : Set (List β))
    (upper_α : ∀ A ∈ F_α, ∀ B : List α,
        FormalTopology.listLowerOrder le_α A B → B ∈ F_α)
    (upper_β : ∀ A ∈ F_β, ∀ B : List β,
        FormalTopology.listLowerOrder le_β A B → B ∈ F_β)
    (U_α : Set α) (U_β : Set β) :
    ∀ (L : List ((List α) × (List β))),
    (∀ d ∈ L, ∃ V₁ : List α, ∃ V₂ : List β,
        (∀ x ∈ V₁, x ∈ U_α) ∧ (∀ x ∈ V₂, x ∈ U_β) ∧
        (V₁ ++ d.1 ∈ F_α) ∧ (V₂ ++ d.2 ∈ F_β)) →
    ∃ Vα : List α, ∃ Vβ : List β,
        (∀ x ∈ Vα, x ∈ U_α) ∧ (∀ x ∈ Vβ, x ∈ U_β) ∧
        (∀ d ∈ L, Vα ++ d.1 ∈ F_α ∧ Vβ ++ d.2 ∈ F_β) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨[], [], ?_, ?_, ?_⟩
    · intro _ hx; exact absurd hx List.not_mem_nil
    · intro _ hx; exact absurd hx List.not_mem_nil
    · intro _ hd; exact absurd hd List.not_mem_nil
  | cons d rest ih =>
    intro h
    obtain ⟨V₁_d, V₂_d, hV₁_d, hV₂_d, hF₁_d, hF₂_d⟩ := h d List.mem_cons_self
    have hrest : ∀ d' ∈ rest, _ := fun d' hd' => h d' (List.mem_cons_of_mem _ hd')
    obtain ⟨V₁s, V₂s, hV₁s, hV₂s, hFs⟩ := ih hrest
    refine ⟨V₁_d ++ V₁s, V₂_d ++ V₂s, ?_, ?_, ?_⟩
    · intros x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hV₁_d x hx
      · exact hV₁s x hx
    · intros x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hV₂_d x hx
      · exact hV₂s x hx
    · intros d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'_rest
      · refine ⟨?_, ?_⟩
        · apply upper_α _ hF₁_d
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · refine ⟨x, ?_, le_α_refl x⟩
            rw [List.mem_append, List.mem_append]
            left; left; exact hx
          · refine ⟨x, ?_, le_α_refl x⟩
            rw [List.mem_append, List.mem_append]
            right; exact hx
        · apply upper_β _ hF₂_d
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · refine ⟨x, ?_, le_β_refl x⟩
            rw [List.mem_append, List.mem_append]
            left; left; exact hx
          · refine ⟨x, ?_, le_β_refl x⟩
            rw [List.mem_append, List.mem_append]
            right; exact hx
      · obtain ⟨hF₁_d', hF₂_d'⟩ := hFs d' hd'_rest
        refine ⟨?_, ?_⟩
        · apply upper_α _ hF₁_d'
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · refine ⟨x, ?_, le_α_refl x⟩
            rw [List.mem_append, List.mem_append]
            left; right; exact hx
          · refine ⟨x, ?_, le_α_refl x⟩
            rw [List.mem_append, List.mem_append]
            right; exact hx
        · apply upper_β _ hF₂_d'
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · refine ⟨x, ?_, le_β_refl x⟩
            rw [List.mem_append, List.mem_append]
            left; right; exact hx
          · refine ⟨x, ?_, le_β_refl x⟩
            rw [List.mem_append, List.mem_append]
            right; exact hx

-- ============================================================
-- Section 7: Helper — cov_via_vL (cover transfer through vL refinement)
-- ============================================================

/-- **Cover transfer via vL refinement**: if `T.cov a A` and every element
of `A` is `T.le`-refined by some element of `B`, then `T.cov a B`.
Standard formal topology property; derived from `cov_trans` + `cov_refl`
+ `cov_ref_mono`. -/
theorem cov_via_vL (T : FormalTopology) (a : T.S) (A B : Set T.S)
    (hcov : T.cov a A) (hvL : ∀ x ∈ A, ∃ y ∈ B, T.le x y) :
    T.cov a B := by
  apply T.cov_trans a A B hcov
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hvL x hx
  exact T.cov_ref_mono x y B hxy (T.cov_refl y B hy)

-- ============================================================
-- Section 8: prodF_generators_covered (PLAN §3.4)
-- ============================================================

/-- **Generators covered for product** (PLAN_6 §3.4 / Vickers Theorem 19 §(4)).

For any `S ∈ prodF` and any generator `g = (g₁, g₂)`, the product cover
relation `(T_prod).cov g {x | x ∈ S}` holds.

Proof structure:
1. Enumerate canonical sublists `D₀_subs := S.sublists.filter (Fπ₁ ∈ F₁)`,
   `D₀₀_subs` similar for `F₂`.
2. Define `U_1 := manyMeet T₁.le [Fπ₁(sub) for sub ∈ D₀_subs]`, `U_2` similar.
3. By `cov_meet_iter` + `w_i.generators_covered`: `T_i.cov g.i U_i`.
4. By `cov_product_of_components`: `T_prod.cov g (U_1 ×_set U_2)`.
5. Show `(U_1 ×_set U_2) vL {x | x ∈ S}` via `product_decomposition_lemma`,
   using canonical-sub correspondence (T16 decidability).
6. Conclude via `cov_via_vL`. -/
theorem prodF_generators_covered
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    ∀ S ∈ prodF T₁ T₂ w₁ w₂, ∀ g : T₁.S × T₂.S,
      (FormalTopology.prod T₁ T₂).cov g {x | x ∈ S} := by
  intro S hS g
  -- D₀_subs: sublists of S with Fπ₁ in F₁
  let D₀_subs : List (List (T₁.S × T₂.S)) :=
    S.sublists.filter (fun sub => decide (sub.map (·.1) ∈ w₁.F))
  -- D₀₀_subs: sublists of S with Fπ₂ in F₂
  let D₀₀_subs : List (List (T₁.S × T₂.S)) :=
    S.sublists.filter (fun sub => decide (sub.map (·.2) ∈ w₂.F))
  -- U_1, U_2 as manyMeet over respective sublists
  let U_1 : Set T₁.S :=
    manyMeet T₁.le (D₀_subs.map (fun sub => {x | x ∈ sub.map (·.1)}))
  let U_2 : Set T₂.S :=
    manyMeet T₂.le (D₀₀_subs.map (fun sub => {x | x ∈ sub.map (·.2)}))
  -- Step 4a: T₁.cov g.1 U_1
  have hU_1 : T₁.cov g.1 U_1 := by
    apply cov_meet_iter
    intro V hV
    rw [List.mem_map] at hV
    obtain ⟨sub, hsub, hVeq⟩ := hV
    subst hVeq
    have hsub_filt := List.mem_filter.mp hsub
    have hF : sub.map (·.1) ∈ w₁.F := of_decide_eq_true hsub_filt.2
    exact w₁.generators_covered _ hF g.1
  -- Step 4b: T₂.cov g.2 U_2
  have hU_2 : T₂.cov g.2 U_2 := by
    apply cov_meet_iter
    intro V hV
    rw [List.mem_map] at hV
    obtain ⟨sub, hsub, hVeq⟩ := hV
    subst hVeq
    have hsub_filt := List.mem_filter.mp hsub
    have hF : sub.map (·.2) ∈ w₂.F := of_decide_eq_true hsub_filt.2
    exact w₂.generators_covered _ hF g.2
  -- Step 5: T_prod.cov g (U_1 × U_2)
  have hprod : (FormalTopology.prod T₁ T₂).cov g
      {p : T₁.S × T₂.S | p.1 ∈ U_1 ∧ p.2 ∈ U_2} := by
    have := cov_product_of_components T₁ T₂ g.1 g.2 U_1 U_2 hU_1 hU_2
    -- g = (g.1, g.2) — convert via Prod.mk.eta
    have heq : g = (g.1, g.2) := rfl
    rw [heq]
    exact this
  -- Step 6: (U_1 × U_2) vL {x | x ∈ S}
  apply cov_via_vL _ _ _ _ hprod
  intro p ⟨hp1, hp2⟩
  -- Hypothesis for product_decomposition_lemma
  haveI : DecidableEq (T₁.S × T₂.S) := inferInstance
  have hyp : ∀ S₁_part S₂_part : List (T₁.S × T₂.S),
      (∀ q ∈ S, q ∈ S₁_part ∨ q ∈ S₂_part) →
      (∃ q ∈ S₁_part, T₁.le p.1 q.1) ∨ (∃ q ∈ S₂_part, T₂.le p.2 q.2) := by
    intro S₁_part S₂_part hdecomp
    -- Restrict to elements of S (iff-form needed for hS)
    let S₁' : List (T₁.S × T₂.S) := S₁_part.filter (fun x => decide (x ∈ S))
    let S₂' : List (T₁.S × T₂.S) := S₂_part.filter (fun x => decide (x ∈ S))
    have hdecomp_iff : ∀ q, q ∈ S ↔ q ∈ S₁' ∨ q ∈ S₂' := by
      intro q
      constructor
      · intro hq
        rcases hdecomp q hq with h₁ | h₂
        · left; rw [List.mem_filter]; exact ⟨h₁, decide_eq_true hq⟩
        · right; rw [List.mem_filter]; exact ⟨h₂, decide_eq_true hq⟩
      · intro h
        rcases h with h | h
        · exact of_decide_eq_true (List.mem_filter.mp h).2
        · exact of_decide_eq_true (List.mem_filter.mp h).2
    rcases hS S₁' S₂' hdecomp_iff with hF₁ | hF₂
    · -- F₁ side: find canonical sub
      left
      let sub : List (T₁.S × T₂.S) := S.filter (fun x => decide (x ∈ S₁'))
      have hsub_sublist : sub ∈ S.sublists :=
        List.mem_sublists.mpr List.filter_sublist
      -- Fπ₁(sub) ∈ F₁ via upper_closed (same set as Fπ₁(S₁'))
      have hFsub : sub.map (·.1) ∈ w₁.F := by
        apply w₁.upper_closed (S₁'.map (·.1)) hF₁ (sub.map (·.1))
        intro x hxs1
        rw [List.mem_map] at hxs1
        obtain ⟨y, hy_S₁', hy_eq⟩ := hxs1
        have hyS : y ∈ S := of_decide_eq_true (List.mem_filter.mp hy_S₁').2
        refine ⟨x, ?_, T₁.le_refl x⟩
        rw [List.mem_map]
        refine ⟨y, ?_, hy_eq⟩
        rw [List.mem_filter]
        exact ⟨hyS, decide_eq_true hy_S₁'⟩
      -- sub ∈ D₀_subs
      have hsub_D₀ : sub ∈ D₀_subs := by
        rw [List.mem_filter]
        exact ⟨hsub_sublist, decide_eq_true hFsub⟩
      -- Apply U_1 property
      have hmap_in : ({x | x ∈ sub.map (·.1)} : Set T₁.S) ∈
          D₀_subs.map (fun sub => {x | x ∈ sub.map (·.1)}) := by
        rw [List.mem_map]; exact ⟨sub, hsub_D₀, rfl⟩
      obtain ⟨s, hs_mem, hs_le⟩ := hp1 _ hmap_in
      -- s ∈ sub.map (·.1) → ∃ q ∈ sub, q.1 = s
      rw [show ({x | x ∈ sub.map (·.1)} : Set T₁.S) = {x | x ∈ sub.map (·.1)} from rfl] at hs_mem
      have hs_mem' : s ∈ sub.map (·.1) := hs_mem
      rw [List.mem_map] at hs_mem'
      obtain ⟨q, hq_sub, hq_eq⟩ := hs_mem'
      have hq_S₁' : q ∈ S₁' := of_decide_eq_true (List.mem_filter.mp hq_sub).2
      have hq_S₁_part : q ∈ S₁_part := (List.mem_filter.mp hq_S₁').1
      refine ⟨q, hq_S₁_part, ?_⟩
      rw [← hq_eq] at hs_le
      exact hs_le
    · -- F₂ side: symmetric
      right
      let sub : List (T₁.S × T₂.S) := S.filter (fun x => decide (x ∈ S₂'))
      have hsub_sublist : sub ∈ S.sublists :=
        List.mem_sublists.mpr List.filter_sublist
      have hFsub : sub.map (·.2) ∈ w₂.F := by
        apply w₂.upper_closed (S₂'.map (·.2)) hF₂ (sub.map (·.2))
        intro x hxs2
        rw [List.mem_map] at hxs2
        obtain ⟨y, hy_S₂', hy_eq⟩ := hxs2
        have hyS : y ∈ S := of_decide_eq_true (List.mem_filter.mp hy_S₂').2
        refine ⟨x, ?_, T₂.le_refl x⟩
        rw [List.mem_map]
        refine ⟨y, ?_, hy_eq⟩
        rw [List.mem_filter]
        exact ⟨hyS, decide_eq_true hy_S₂'⟩
      have hsub_D₀₀ : sub ∈ D₀₀_subs := by
        rw [List.mem_filter]
        exact ⟨hsub_sublist, decide_eq_true hFsub⟩
      have hmap_in : ({x | x ∈ sub.map (·.2)} : Set T₂.S) ∈
          D₀₀_subs.map (fun sub => {x | x ∈ sub.map (·.2)}) := by
        rw [List.mem_map]; exact ⟨sub, hsub_D₀₀, rfl⟩
      obtain ⟨s, hs_mem, hs_le⟩ := hp2 _ hmap_in
      have hs_mem' : s ∈ sub.map (·.2) := hs_mem
      rw [List.mem_map] at hs_mem'
      obtain ⟨q, hq_sub, hq_eq⟩ := hs_mem'
      have hq_S₂' : q ∈ S₂' := of_decide_eq_true (List.mem_filter.mp hq_sub).2
      have hq_S₂_part : q ∈ S₂_part := (List.mem_filter.mp hq_S₂').1
      refine ⟨q, hq_S₂_part, ?_⟩
      rw [← hq_eq] at hs_le
      exact hs_le
  obtain ⟨q, hqS, hqle1, hqle2⟩ := product_decomposition_lemma T₁ T₂ S p.1 p.2 hyp
  exact ⟨q, hqS, hqle1, hqle2⟩

-- ============================================================
-- Section 9: prodF_cover_closure (PLAN §3.3) — the heaviest theorem
-- ============================================================

/-- **Head form of `cover_closure` for product `prodF`** (PLAN_6 §3.3 /
Vickers Theorem 19 §(3)).  Given `opProdBasicCov a U` and
`(a :: T') ∈ prodF`, construct `V₀ ⊆ U` with `V₀ ++ T' ∈ prodF`.

Proof outline (per PLAN_6 with T14+T17 amendments):
1. Unpack `hbasic`: get component basic covers `U₁`, `U₂`.
2. Enumerate decompositions of T' as canonical (sub, T'\sub) pairs.
3. Filter to `D₀_pairs` where both `(a.1 :: Fπ₁(sub))` ∈ F₁ AND
   `(a.2 :: Fπ₂(T'\sub))` ∈ F₂ (decidable via T16).
4. For each `d ∈ D₀_pairs`, extract `V₁_d ⊆ U₁`, `V₂_d ⊆ U₂` via
   `w₁.cover_closure` / `w₂.cover_closure`.  T17 enables conclusion shape
   `V₁_d ++ Fπ₁(d.1) ∈ F₁` (S' upper bound makes upper_closed work).
5. Build aggregate `V₁_tot`, `V₂_tot` via `buildVStar`.
6. `V₀ := V₁_tot ×ₗ V₂_tot` (cartesian list product) ⊆ U₁ × U₂ = U.
7. For any decomp `(X, Y)` of `V₀ ++ T'`, sub-case analysis:
   - Case D₀₀: ¬D₀ at T'-decomp level → one F-side directly.
   - Case D₀: sub-sub-case on whether `V₁_tot ⊆ Fπ₁(X_V)`:
     - Yes → `Fπ₁(X) ∈ F₁`.
     - No → row-collapse argument → `V₂_tot ⊆ Fπ₂(Y_V)` → `Fπ₂(Y) ∈ F₂`. -/
theorem prodF_cover_closure_head
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    ∀ {a : T₁.S × T₂.S} {U : Set (T₁.S × T₂.S)} {T' : List (T₁.S × T₂.S)},
      OperationalFormalTopology.opProdBasicCov T₁ T₂ a U →
      (a :: T') ∈ prodF T₁ T₂ w₁ w₂ →
      ∃ V₀ : List (T₁.S × T₂.S),
        (∀ x ∈ V₀, x ∈ U) ∧
        (V₀ ++ T') ∈ prodF T₁ T₂ w₁ w₂ := by
  intro a U T' hbasic hS
  obtain ⟨U₁_set, U₂_set, hU₁, hU₂, hUeq⟩ := hbasic
  haveI : DecidableEq (T₁.S × T₂.S) := inferInstance
  -- Enumerate decompositions of T' as canonical (sub, T'\sub) pairs
  let decomps : List (List (T₁.S × T₂.S) × List (T₁.S × T₂.S)) :=
    T'.sublists.map (fun sub => (sub, T'.filter (fun x => !decide (x ∈ sub))))
  -- D₀_pairs: decompositions where both F₁ and F₂ extensions hold
  let D₀_pairs : List (List (T₁.S × T₂.S) × List (T₁.S × T₂.S)) :=
    decomps.filter (fun d =>
      decide ((a.1 :: d.1.map (·.1)) ∈ w₁.F ∧ (a.2 :: d.2.map (·.2)) ∈ w₂.F))
  -- Mapped pairs (Fπ₁(d.1), Fπ₂(d.2)) for buildVStar
  let mapped_pairs : List (List T₁.S × List T₂.S) :=
    D₀_pairs.map (fun d => (d.1.map (·.1), d.2.map (·.2)))
  -- Extraction: for each mapped pair, get V₁, V₂ via cover_closure
  have hExtract : ∀ p ∈ mapped_pairs, ∃ V₁ : List T₁.S, ∃ V₂ : List T₂.S,
      (∀ x ∈ V₁, x ∈ U₁_set) ∧ (∀ x ∈ V₂, x ∈ U₂_set) ∧
      (V₁ ++ p.1 ∈ w₁.F) ∧ (V₂ ++ p.2 ∈ w₂.F) := by
    intros p hp
    rw [List.mem_map] at hp
    obtain ⟨d, hd, hd_eq⟩ := hp
    subst hd_eq
    have hd_filt := List.mem_filter.mp hd
    have hd_and := of_decide_eq_true hd_filt.2
    obtain ⟨hF₁, hF₂⟩ := hd_and
    obtain ⟨V₁, S₁', hV₁_sub, _hS₁'_lower, hS₁'_upper, hF₁_concat⟩ :=
      w₁.cover_closure hU₁ List.mem_cons_self hF₁
    obtain ⟨V₂, S₂', hV₂_sub, _hS₂'_lower, hS₂'_upper, hF₂_concat⟩ :=
      w₂.cover_closure hU₂ List.mem_cons_self hF₂
    have hF₁_target : V₁ ++ d.1.map (·.1) ∈ w₁.F := by
      apply w₁.upper_closed _ hF₁_concat
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hxS₁'
      · refine ⟨x, ?_, T₁.le_refl x⟩
        rw [List.mem_append]; left; exact hx
      · have ⟨h_in_S, h_ne⟩ := hS₁'_upper x hxS₁'
        rcases List.mem_cons.mp h_in_S with heq | hxd
        · exact absurd heq h_ne
        · refine ⟨x, ?_, T₁.le_refl x⟩
          rw [List.mem_append]; right; exact hxd
    have hF₂_target : V₂ ++ d.2.map (·.2) ∈ w₂.F := by
      apply w₂.upper_closed _ hF₂_concat
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hxS₂'
      · refine ⟨x, ?_, T₂.le_refl x⟩
        rw [List.mem_append]; left; exact hx
      · have ⟨h_in_S, h_ne⟩ := hS₂'_upper x hxS₂'
        rcases List.mem_cons.mp h_in_S with heq | hxd
        · exact absurd heq h_ne
        · refine ⟨x, ?_, T₂.le_refl x⟩
          rw [List.mem_append]; right; exact hxd
    exact ⟨V₁, V₂, hV₁_sub, hV₂_sub, hF₁_target, hF₂_target⟩
  -- Apply buildVStar
  obtain ⟨V₁_tot, V₂_tot, hV₁_tot_sub, hV₂_tot_sub, hFtot⟩ :=
    buildVStar T₁.le T₂.le T₁.le_refl T₂.le_refl w₁.F w₂.F
      w₁.upper_closed w₂.upper_closed U₁_set U₂_set
      mapped_pairs hExtract
  -- Construct V₀ = V₁_tot ×ₗ V₂_tot
  let V₀ : List (T₁.S × T₂.S) :=
    V₁_tot.flatMap (fun v₁ => V₂_tot.map (fun v₂ => (v₁, v₂)))
  refine ⟨V₀, ?_, ?_⟩
  · -- V₀ ⊆ U
    intro x hx
    rw [hUeq]
    rw [List.mem_flatMap] at hx
    obtain ⟨v₁, hv₁, hmap⟩ := hx
    rw [List.mem_map] at hmap
    obtain ⟨v₂, hv₂, hv_eq⟩ := hmap
    rw [← hv_eq]
    exact ⟨hV₁_tot_sub v₁ hv₁, hV₂_tot_sub v₂ hv₂⟩
  · -- V₀ ++ T' ∈ prodF — the heavy case analysis (Step 8)
    intro X Y hdecomp_V0
    -- Split parts
    let X_T : List (T₁.S × T₂.S) := T'.filter (fun x => decide (x ∈ X))
    let X_V : List (T₁.S × T₂.S) := X.filter (fun x => decide (x ∈ V₀))
    let Y_V : List (T₁.S × T₂.S) := Y.filter (fun x => decide (x ∈ V₀))
    let T'_compl : List (T₁.S × T₂.S) := T'.filter (fun x => !decide (x ∈ X_T))
    -- Helper: every elt of T' is in X or Y (from V₀ ++ T' decomp)
    have hT'_split : ∀ p ∈ T', p ∈ X ∨ p ∈ Y := by
      intro p hp
      have hpVT : p ∈ V₀ ++ T' := List.mem_append.mpr (Or.inr hp)
      exact (hdecomp_V0 p).mp hpVT
    -- Helper: X_T elements are in T' and X
    have hX_T_in : ∀ p ∈ X_T, p ∈ T' ∧ p ∈ X := by
      intro p hp
      have := List.mem_filter.mp hp
      exact ⟨this.1, of_decide_eq_true this.2⟩
    -- Helper: T'_compl elements are in T' and Y (since not in X_T, hence not in X, so in Y)
    have hT'_compl_in : ∀ p ∈ T'_compl, p ∈ T' ∧ p ∈ Y := by
      intro p hp
      have hfilt := List.mem_filter.mp hp
      have hpT : p ∈ T' := hfilt.1
      have hpX_neg : ¬ (p ∈ X) := by
        intro hpX
        have hbool := hfilt.2
        rw [Bool.not_eq_true', decide_eq_false_iff_not] at hbool
        apply hbool
        -- p ∈ X_T iff p ∈ T' ∧ p ∈ X.
        rw [List.mem_filter]
        exact ⟨hpT, decide_eq_true hpX⟩
      rcases hT'_split p hpT with hpX | hpY
      · exact absurd hpX hpX_neg
      · exact ⟨hpT, hpY⟩
    -- Decomp (X_T, T'_compl) is a valid decomp of T'
    have hT'_decomp : ∀ q, q ∈ T' ↔ q ∈ X_T ∨ q ∈ T'_compl := by
      intro q
      constructor
      · intro hq
        by_cases hqXT : q ∈ X_T
        · left; exact hqXT
        · right; rw [List.mem_filter]
          refine ⟨hq, ?_⟩
          rw [Bool.not_eq_true', decide_eq_false_iff_not]
          exact hqXT
      · intro hq
        rcases hq with hq | hq
        · exact (hX_T_in q hq).1
        · exact (hT'_compl_in q hq).1
    -- Apply hS to (a :: X_T, T'_compl) and (X_T, a :: T'_compl)
    have hCov_i : ∀ q, q ∈ a :: T' ↔ q ∈ (a :: X_T) ∨ q ∈ T'_compl := by
      intro q
      constructor
      · intro hq
        rcases List.mem_cons.mp hq with rfl | hqT
        · left; exact List.mem_cons_self
        · rcases (hT'_decomp q).mp hqT with hXT | hCT
          · left; exact List.mem_cons_of_mem _ hXT
          · right; exact hCT
      · intro hq
        rcases hq with hq | hq
        · rcases List.mem_cons.mp hq with rfl | hqXT
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hX_T_in q hqXT).1
        · exact List.mem_cons_of_mem _ (hT'_compl_in q hq).1
    have hCov_ii : ∀ q, q ∈ a :: T' ↔ q ∈ X_T ∨ q ∈ (a :: T'_compl) := by
      intro q
      constructor
      · intro hq
        rcases List.mem_cons.mp hq with rfl | hqT
        · right; exact List.mem_cons_self
        · rcases (hT'_decomp q).mp hqT with hXT | hCT
          · left; exact hXT
          · right; exact List.mem_cons_of_mem _ hCT
      · intro hq
        rcases hq with hq | hq
        · exact List.mem_cons_of_mem _ (hX_T_in q hq).1
        · rcases List.mem_cons.mp hq with rfl | hqCT
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hT'_compl_in q hqCT).1
    have hEq_i := hS (a :: X_T) T'_compl hCov_i
    have hEq_ii := hS X_T (a :: T'_compl) hCov_ii
    -- Decidable D₀ check at this decomp
    by_cases hD₀ : (a.1 :: X_T.map (·.1)) ∈ w₁.F ∧ (a.2 :: T'_compl.map (·.2)) ∈ w₂.F
    · -- D₀ case: this canonical decomp is in D₀_pairs
      have hPairInDecomps : (X_T, T'_compl) ∈ decomps := by
        rw [List.mem_map]
        exact ⟨X_T, List.mem_sublists.mpr List.filter_sublist, rfl⟩
      have hPairInD₀ : (X_T, T'_compl) ∈ D₀_pairs := by
        rw [List.mem_filter]
        exact ⟨hPairInDecomps, decide_eq_true hD₀⟩
      -- Mapped pair is in mapped_pairs
      have hMappedIn : (X_T.map (·.1), T'_compl.map (·.2)) ∈ mapped_pairs := by
        rw [List.mem_map]
        exact ⟨(X_T, T'_compl), hPairInD₀, rfl⟩
      -- buildVStar conclusion for this pair
      have ⟨hFtot₁, hFtot₂⟩ := hFtot _ hMappedIn
      -- Sub-sub-case: does V₁_tot ⊆ Fπ₁(X_V)?
      haveI : DecidablePred (fun v : T₁.S => ∃ q ∈ X_V, q.1 = v) := fun v =>
        List.decidableBEx _ _
      by_cases hSubset : ∀ v ∈ V₁_tot, ∃ q ∈ X_V, q.1 = v
      · -- Sub-case B1: V₁_tot ⊆ Fπ₁(X_V). Conclude Fπ₁(X) ∈ F₁.
        left
        apply w₁.upper_closed (V₁_tot ++ X_T.map (·.1)) hFtot₁
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hxV | hxXT
        · -- x ∈ V₁_tot ⊆ Fπ₁(X_V) ⊆ Fπ₁(X)
          obtain ⟨q, hqXV, hqx⟩ := hSubset x hxV
          have hqX : q ∈ X := (List.mem_filter.mp hqXV).1
          refine ⟨x, ?_, T₁.le_refl x⟩
          rw [List.mem_map]
          exact ⟨q, hqX, hqx⟩
        · -- x ∈ X_T.map (·.1), so x = q.1 for q ∈ X_T ⊆ X
          rw [List.mem_map] at hxXT
          obtain ⟨q, hqXT, hqx⟩ := hxXT
          have hqX : q ∈ X := (hX_T_in q hqXT).2
          refine ⟨x, ?_, T₁.le_refl x⟩
          rw [List.mem_map]
          exact ⟨q, hqX, hqx⟩
      · -- Sub-case B2: ∃ v₁* ∈ V₁_tot with no q ∈ X_V having q.1 = v₁*
        right
        -- Constructive extraction: ¬ ∀ → ∃ ¬ via list induction (no Classical).
        have extract : ∀ L : List T₁.S,
            ¬ (∀ v ∈ L, ∃ q ∈ X_V, q.1 = v) →
            ∃ v ∈ L, ∀ q ∈ X_V, q.1 ≠ v := by
          intro L
          induction L with
          | nil => intro h; exfalso; exact h (fun _ ha => absurd ha List.not_mem_nil)
          | cons head tail ih =>
            intro h
            haveI : Decidable (∃ q ∈ X_V, q.1 = head) := List.decidableBEx _ _
            by_cases hh : ∃ q ∈ X_V, q.1 = head
            · have h_tail : ¬ ∀ v ∈ tail, ∃ q ∈ X_V, q.1 = v := by
                intro ha_tail
                apply h
                intros v hv
                rcases List.mem_cons.mp hv with rfl | hv'
                · exact hh
                · exact ha_tail _ hv'
              obtain ⟨v, hv, hv'⟩ := ih h_tail
              exact ⟨v, List.mem_cons_of_mem _ hv, hv'⟩
            · refine ⟨head, List.mem_cons_self, ?_⟩
              intros q hq heq
              exact hh ⟨q, hq, heq⟩
        obtain ⟨v₁_star, hv₁_tot, hv₁_not⟩ := extract V₁_tot hSubset
        -- Claim: V₂_tot ⊆ Fπ₂(Y_V). For each v₂ ∈ V₂_tot, (v₁_star, v₂) ∈ V₀.
        -- From decomp (X, Y) of V₀ ++ T', (v₁_star, v₂) ∈ X ∨ Y.
        -- If ∈ X: then ∈ X_V (since ∈ V₀). Then v₁_star ∈ Fπ₁(X_V). Contradiction.
        -- So (v₁_star, v₂) ∈ Y, and ∈ Y_V. Hence v₂ ∈ Fπ₂(Y_V).
        have hV₂_in_YV : ∀ v₂ ∈ V₂_tot, (v₁_star, v₂) ∈ Y_V := by
          intro v₂ hv₂
          have hpairV₀ : (v₁_star, v₂) ∈ V₀ := by
            rw [List.mem_flatMap]
            refine ⟨v₁_star, hv₁_tot, ?_⟩
            rw [List.mem_map]
            exact ⟨v₂, hv₂, rfl⟩
          have hpairVT : (v₁_star, v₂) ∈ V₀ ++ T' :=
            List.mem_append.mpr (Or.inl hpairV₀)
          have hpair_in := (hdecomp_V0 (v₁_star, v₂)).mp hpairVT
          rcases hpair_in with hpairX | hpairY
          · -- Contradiction: (v₁_star, v₂) ∈ X ∧ ∈ V₀ → ∈ X_V → v₁_star ∈ Fπ₁(X_V)
            exfalso
            have hpairXV : (v₁_star, v₂) ∈ X_V := by
              rw [List.mem_filter]
              exact ⟨hpairX, decide_eq_true hpairV₀⟩
            exact hv₁_not (v₁_star, v₂) hpairXV rfl
          · -- (v₁_star, v₂) ∈ Y. Combined with ∈ V₀, it's ∈ Y_V.
            rw [List.mem_filter]
            exact ⟨hpairY, decide_eq_true hpairV₀⟩
        apply w₂.upper_closed (V₂_tot ++ T'_compl.map (·.2)) hFtot₂
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hxV₂ | hxCT
        · -- x ∈ V₂_tot. Take pair (v₁_star, x) ∈ Y_V. y_part = x.
          have hpairYV := hV₂_in_YV x hxV₂
          have hpairY : (v₁_star, x) ∈ Y := (List.mem_filter.mp hpairYV).1
          refine ⟨x, ?_, T₂.le_refl x⟩
          rw [List.mem_map]
          exact ⟨(v₁_star, x), hpairY, rfl⟩
        · -- x ∈ T'_compl.map (·.2). x = q.2 for q ∈ T'_compl ⊆ T'∩Y.
          rw [List.mem_map] at hxCT
          obtain ⟨q, hqCT, hqx⟩ := hxCT
          have hqY : q ∈ Y := (hT'_compl_in q hqCT).2
          refine ⟨x, ?_, T₂.le_refl x⟩
          rw [List.mem_map]
          exact ⟨q, hqY, hqx⟩
    · -- ¬D₀: Apply Eq (i) or (ii) directly
      -- Constructive De Morgan: ¬ (A ∧ B) → A → ¬ B.
      have hD₀' : (a.1 :: X_T.map (·.1)) ∈ w₁.F →
          ¬ (a.2 :: T'_compl.map (·.2)) ∈ w₂.F := fun hA hB => hD₀ ⟨hA, hB⟩
      by_cases hF₁_check : (a.1 :: X_T.map (·.1)) ∈ w₁.F
      · -- First conjunct holds, so second must fail (by ¬D₀)
        have hF₂_neg : ¬ (a.2 :: T'_compl.map (·.2)) ∈ w₂.F := hD₀' hF₁_check
        -- From Eq (ii): Fπ₁(X_T) ∈ F₁ ∨ (a.2 :: Fπ₂(T'_compl)) ∈ F₂. Second fails, so first.
        rcases hEq_ii with hF₁_XT | hF₂_with_a
        · -- Fπ₁(X_T) ∈ F₁. Show Fπ₁(X) ∈ F₁.
          left
          apply w₁.upper_closed (X_T.map (·.1)) hF₁_XT
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨q, hqXT, hqx⟩ := hx
          have hqX : q ∈ X := (hX_T_in q hqXT).2
          refine ⟨x, ?_, T₁.le_refl x⟩
          rw [List.mem_map]
          exact ⟨q, hqX, hqx⟩
        · exact absurd hF₂_with_a hF₂_neg
      · -- ¬first. From Eq (i): (a.1 :: Fπ₁(X_T)) ∈ F₁ ∨ Fπ₂(T'_compl) ∈ F₂. First fails, so second.
        rcases hEq_i with hF₁_with_a | hF₂_CT
        · exact absurd hF₁_with_a hF₁_check
        · right
          apply w₂.upper_closed (T'_compl.map (·.2)) hF₂_CT
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨q, hqCT, hqx⟩ := hx
          have hqY : q ∈ Y := (hT'_compl_in q hqCT).2
          refine ⟨x, ?_, T₂.le_refl x⟩
          rw [List.mem_map]
          exact ⟨q, hqY, hqx⟩

-- ============================================================
-- Section 10: prodF permutation invariance + T17 wrap
-- ============================================================

/-- **`prodF` is invariant under set-equivalence of the underlying list**.
Two lists with the same set of elements either both belong to `prodF` or
neither.  Used to reduce arbitrary `S` with `a ∈ S` to head form
`a :: (non-a elts)`. -/
lemma prodF_set_invariant
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    (S T : List (T₁.S × T₂.S)) (h : ∀ x, x ∈ S ↔ x ∈ T) :
    S ∈ prodF T₁ T₂ w₁ w₂ ↔ T ∈ prodF T₁ T₂ w₁ w₂ := by
  constructor
  · intro hS S₁ S₂ hcov
    apply hS S₁ S₂
    intro p
    rw [h]; exact hcov p
  · intro hT S₁ S₂ hcov
    apply hT S₁ S₂
    intro p
    rw [← h]; exact hcov p

/-- **T17-form `cover_closure` for product `prodF`**: any element `a ∈ S`
(not required at head), with `opProdBasicCov a U` and `S ∈ prodF`,
yields the T17 witness shape via reduction to head case
(`prodF_cover_closure_head`) using `prodF_set_invariant`. -/
theorem prodF_cover_closure
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    ∀ {a : T₁.S × T₂.S} {U : Set (T₁.S × T₂.S)} {S : List (T₁.S × T₂.S)},
      OperationalFormalTopology.opProdBasicCov T₁ T₂ a U →
      a ∈ S →
      S ∈ prodF T₁ T₂ w₁ w₂ →
      ∃ V₀ S' : List (T₁.S × T₂.S),
        (∀ x ∈ V₀, x ∈ U) ∧
        (∀ y ∈ S, y ≠ a → y ∈ S') ∧
        (∀ y ∈ S', y ∈ S ∧ y ≠ a) ∧
        (V₀ ++ S') ∈ prodF T₁ T₂ w₁ w₂ := by
  intro a U S hbasic haS hS
  haveI : DecidableEq (T₁.S × T₂.S) := inferInstance
  let S' : List (T₁.S × T₂.S) := S.filter (fun x => decide (x ≠ a))
  have hSame : ∀ x, x ∈ S ↔ x ∈ (a :: S') := by
    intro x
    constructor
    · intro hx
      by_cases hxa : x = a
      · rw [hxa]; exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        rw [List.mem_filter]
        exact ⟨hx, decide_eq_true hxa⟩
    · intro hx
      rcases List.mem_cons.mp hx with rfl | hxS'
      · exact haS
      · exact (List.mem_filter.mp hxS').1
  have hConsInF : (a :: S') ∈ prodF T₁ T₂ w₁ w₂ :=
    (prodF_set_invariant T₁ T₂ w₁ w₂ S (a :: S') hSame).mp hS
  obtain ⟨V₀, hV_sub, hV_prod⟩ :=
    prodF_cover_closure_head T₁ T₂ w₁ w₂ hbasic hConsInF
  refine ⟨V₀, S', hV_sub, ?_, ?_, hV_prod⟩
  · intros y hyS hne
    rw [List.mem_filter]
    exact ⟨hyS, decide_eq_true hne⟩
  · intros y hyS'
    have hfilt := List.mem_filter.mp hyS'
    exact ⟨hfilt.1, of_decide_eq_true hfilt.2⟩

-- ============================================================
-- Section 11: prodWitness — full CompactWitness for the product
-- ============================================================

/-- **The product compact witness**: the four-field `CompactWitness`
structure for the binary product of formal topologies, with `F = prodF`.
This is the structural content of Vickers's binary Tychonoff. -/
def prodWitness
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    CompactWitness (FormalTopology.prod T₁ T₂)
                   (OperationalFormalTopology.instProd T₁ T₂).basicCov where
  F := prodF T₁ T₂ w₁ w₂
  upper_closed := prodF_upper_closed T₁ T₂ w₁ w₂
  inhabited := prodF_inhabited T₁ T₂ w₁ w₂
  cover_closure := prodF_cover_closure T₁ T₂ w₁ w₂
  generators_covered := prodF_generators_covered T₁ T₂ w₁ w₂

-- ============================================================
-- Section 12: tychonoff_binary — top-level statement
-- ============================================================

/-- **Binary Tychonoff for formal topology** (Vickers 2006 Theorem 19,
constructive version).

Given two `CompactWitness`es for `T₁` and `T₂` (with appropriate
decidability), the product `FormalTopology.prod T₁ T₂` carries a
`CompactWitness` — i.e., **the product of compact formal topologies is
compact**.

This is Mode B audit object for VR-Topology v1.0.0: multi-step
constructive proof (~480 active lines across helpers + four `prodF.*`
theorems + assembly), zero `Classical.choice`.  Target axiom profile
`[propext, Quot.sound]` achieved. -/
def tychonoff_binary
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    CompactWitness (FormalTopology.prod T₁ T₂)
                   (OperationalFormalTopology.instProd T₁ T₂).basicCov :=
  prodWitness T₁ T₂ w₁ w₂

/-! ## §13. Concrete operational compactness for Unit × Bool (Stage 6b)

The abstract instance `instProdOperationalCompact (T₁ T₂) : ...` is
intentionally **not** provided.  The obstruction is structural:
`listLowerOrder` is one-directional (∀a∈A ∃b∈B, le a b), which suffices
for F-membership transfer (`prodF_upper_closed`) but is insufficient to
transfer per-element operationality.  Specifically, `B` may contain
elements with no `prodLe`-preimage in `A`, whose operationality is
unconstrained.

Concrete instances such as `Examples.instUnitBoolProductOperationalCompact`
below satisfy `witness_operational` trivially because their
`IsOperational` predicate is `True`.  Abstract operational propagation
under refinement is deferred to v1.1.0 and would require either
bidirectional `listLowerOrder` (Stage 5 amendment) or restructured
`OperationalCompact` class (Stage 5 amendment) — both beyond v1.0.0
scope.  See `STAGE_6b_HALT_DIRECTION.md` for full analysis.

Finding T19 (`op_preserved_by_le` field in `OperationalFormalTopology`)
is retained as the conceptually-sound operational preservation under
refinement, even though it is trivial for current `IsOperational := True`
instances. -/

namespace Examples

/-- Decidability of equality on Unit (reducible to standard instance). -/
instance : DecidableEq Unit.formalTopology.S :=
  inferInstanceAs (DecidableEq Unit)

/-- Decidability of equality on Bool (reducible to standard instance). -/
instance : DecidableEq Bool.formalTopology.S :=
  inferInstanceAs (DecidableEq Bool)

/-- Decidability of Unit's preorder (universally `True`). -/
instance : DecidableRel Unit.formalTopology.le :=
  fun _ _ => isTrue trivial

/-- Decidability of Bool's preorder (`Eq` on `Bool`). -/
instance decRelBoolLE : DecidableRel Bool.formalTopology.le := fun a b =>
  (inferInstance : Decidable ((a : Bool) = b))

/-- The Unit operational compactness witness, named explicitly for clarity. -/
def unitWitness :
    CompactWitness Unit.formalTopology
      (Unit.operationalFormalTopology).basicCov :=
  @OperationalCompact.witness Unit.formalTopology
    Unit.operationalFormalTopology instUnitOperationalCompact

/-- The Bool operational compactness witness, named explicitly for clarity. -/
def boolWitness :
    CompactWitness Bool.formalTopology
      (Bool.operationalFormalTopology).basicCov :=
  @OperationalCompact.witness Bool.formalTopology
    Bool.operationalFormalTopology instBoolOperationalCompact

/-- Decidability of membership in `Unit`'s F-witness (universally `True`). -/
instance : DecidablePred (· ∈ unitWitness.F) :=
  fun _ => isTrue trivial

/-- Decidability of membership in `Bool`'s F-witness (`true ∈ S ∧ false ∈ S`). -/
instance : DecidablePred (· ∈ boolWitness.F) :=
  fun S => inferInstanceAs (Decidable (true ∈ S ∧ false ∈ S))

/-- **Concrete operational compactness for `Unit × Bool`** (Stage 6b
resolution R3).  Demonstrates the binary Tychonoff result on the
cycle's smoke-test examples.

- `witness` from Stage 6's `prodWitness`.
- `witness_operational` trivial since both components have
  `IsOperational := True`.
- `witness_describable` via `List.toDescribable` (Stage 5 instance). -/
instance instUnitBoolProductOperationalCompact :
    OperationalCompact
      (FormalTopology.prod Unit.formalTopology Bool.formalTopology) where
  witness := prodWitness Unit.formalTopology Bool.formalTopology
              unitWitness boolWitness
  witness_operational := by
    intro _ _ _ _; exact ⟨trivial, trivial⟩
  witness_describable := by
    intro S _; infer_instance

end Examples

end VRCycle.Topology
