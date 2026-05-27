-- VRCycle/Topology/Bridge.lean
-- VR-Topology v1.0.0 — Stage 7: Bridge to mathlib (Order.Frame).
--
-- **Architectural framing**: Stage 7 crosses the predicative→impredicative
-- boundary.  Stages 1-6b were strict-constructive `Classical.choice`-free
-- formal topology.  Mathlib's `Order.Frame` is impredicative classical
-- infrastructure.  Stage 7 establishes the bridge.
--
-- **Expected axiom profile**: Stage 7 outputs legitimately acquire
-- `Classical.choice` through mathlib's frame typeclass machinery.  This
-- is documented and expected, not a regression.  Stage 6 outputs
-- (`tychonoff_binary` etc.) remain in `[propext, Quot.sound]` unchanged.
--
-- See PLAN_7.md §0 for full architectural justification.

import VRCycle.Topology.Tychonoff
import Mathlib.Order.CompleteBooleanAlgebra

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 1: SatSet T — saturated subsets (frame elements)
-- ============================================================

/-- A set `U : Set T.S` is **saturated** iff every element covered by
`U` is already in `U`. -/
def IsSaturated (T : FormalTopology) (U : Set T.S) : Prop :=
  ∀ a, T.cov a U → a ∈ U

/-- `SatSet T` carries the frame of `T`'s saturated subsets. -/
def SatSet (T : FormalTopology) : Type _ := { U : Set T.S // IsSaturated T U }

namespace SatSet

variable {T : FormalTopology}

instance : Membership T.S (SatSet T) where
  mem U a := a ∈ U.1

@[simp] lemma mem_def (U : SatSet T) (a : T.S) : a ∈ U ↔ a ∈ U.1 := Iff.rfl

instance : CoeHead (SatSet T) (Set T.S) := ⟨Subtype.val⟩

@[ext] theorem ext {U V : SatSet T} (h : ∀ a, a ∈ U ↔ a ∈ V) : U = V := by
  apply Subtype.ext; exact Set.ext h

/-- Saturation of a set: smallest saturated set containing it. -/
def saturate (T : FormalTopology) (U : Set T.S) : Set T.S :=
  { a | T.cov a U }

theorem saturate_isSaturated (T : FormalTopology) (U : Set T.S) :
    IsSaturated T (saturate T U) := by
  intro a hcov
  apply T.cov_trans a {b | T.cov b U} U hcov
  intro b hb; exact hb

theorem subset_saturate (T : FormalTopology) (U : Set T.S) : U ⊆ saturate T U :=
  fun a ha => T.cov_refl a U ha

/-- Down-closure of saturated set is itself (via `cov_ref_mono`). -/
theorem le_mem (U : SatSet T) (a b : T.S)
    (hba : T.le b a) (haU : a ∈ U) : b ∈ U := by
  apply U.2
  exact T.cov_ref_mono b a U.1 hba (T.cov_refl a U.1 haU)

end SatSet

-- ============================================================
-- Section 2: Order and lattice structure
-- ============================================================

instance instLE (T : FormalTopology) : LE (SatSet T) where
  le U V := U.1 ⊆ V.1

/-- Full `CompleteLattice` instance, providing all fields explicitly so
that `inf` is direct intersection and `sSup` is saturate-of-union.  This
is essential for the frame distributivity proof to unfold cleanly. -/
instance instCompleteLattice (T : FormalTopology) : CompleteLattice (SatSet T) where
  -- PartialOrder
  le_refl _ := fun _ h => h
  le_trans _ _ _ hUV hVW := fun _ h => hVW (hUV h)
  le_antisymm U V hUV hVU := by
    apply Subtype.ext; exact Set.Subset.antisymm hUV hVU
  -- SemilatticeSup / SemilatticeInf
  sup U V := ⟨SatSet.saturate T (U.1 ∪ V.1), SatSet.saturate_isSaturated T _⟩
  inf U V := ⟨U.1 ∩ V.1, by
    intro a hcov
    refine ⟨U.2 a (T.cov_mono a _ U.1 (fun _ h => h.1) hcov),
            V.2 a (T.cov_mono a _ V.1 (fun _ h => h.2) hcov)⟩⟩
  le_sup_left U V := by intro a ha; exact SatSet.subset_saturate _ _ (Or.inl ha)
  le_sup_right U V := by intro a ha; exact SatSet.subset_saturate _ _ (Or.inr ha)
  sup_le U V W hUW hVW := by
    intro a ha
    apply W.2
    apply T.cov_mono a _ W.1 _ ha
    intro x hx
    rcases hx with hx | hx
    · exact hUW hx
    · exact hVW hx
  inf_le_left _ _ := fun _ h => h.1
  inf_le_right _ _ := fun _ h => h.2
  le_inf _ _ _ hUV hUW := fun _ h => ⟨hUV h, hUW h⟩
  -- BoundedOrder
  top := ⟨Set.univ, fun _ _ => trivial⟩
  bot := ⟨SatSet.saturate T ∅, SatSet.saturate_isSaturated T _⟩
  le_top _ := fun _ _ => trivial
  bot_le U := by
    intro a ha
    apply U.2
    apply T.cov_mono a ∅ U.1 (Set.empty_subset _) ha
  -- SupSet / InfSet + CompleteSemilattices
  sSup S := ⟨SatSet.saturate T (⋃ U ∈ S, U.1), SatSet.saturate_isSaturated T _⟩
  sInf S := ⟨⋂ U ∈ S, U.1, by
    intro a hcov
    rw [Set.mem_iInter]
    intro U
    rw [Set.mem_iInter]
    intro hU
    apply U.2 a
    apply T.cov_mono a _ U.1 _ hcov
    intro x hx
    rw [Set.mem_iInter] at hx
    exact (Set.mem_iInter.mp (hx U)) hU⟩
  isLUB_sSup S := by
    refine ⟨?_, ?_⟩
    · intro U hU a haU
      apply SatSet.subset_saturate
      rw [Set.mem_iUnion]
      exact ⟨U, Set.mem_iUnion.mpr ⟨hU, haU⟩⟩
    · intro V hV a ha
      apply V.2
      apply T.cov_mono a _ V.1 _ ha
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨U, hxU⟩ := hx
      rw [Set.mem_iUnion] at hxU
      obtain ⟨hUS, hxU⟩ := hxU
      exact hV hUS hxU
  isGLB_sInf S := by
    refine ⟨?_, ?_⟩
    · intro U hU a ha
      have ha' : a ∈ ⋂ V ∈ S, V.1 := ha
      rw [Set.mem_iInter] at ha'
      exact (Set.mem_iInter.mp (ha' U)) hU
    · intro V hV a haV
      change a ∈ ⋂ U ∈ S, U.1
      rw [Set.mem_iInter]
      intro U
      rw [Set.mem_iInter]
      intro hU
      exact hV hU haV

-- ============================================================
-- Section 5: Frame distributivity via cov_meet (Stage 1 T7)
-- ============================================================

/-- **Frame minimal axioms** for `SatSet T`.

The non-trivial requirement `A ⊓ sSup S ≤ ⨆ b ∈ S, A ⊓ b` follows from
`cov_meet` (Stage 1 T7) plus saturation closure under `le`.

Key step: `⨆ (_ : U ∈ S), A ⊓ U = A ⊓ U` via `iSup_pos hUS` (mathlib
lemma), bridging the conditional-iSup notation with our explicit sSup. -/
instance frameMinAx (T : FormalTopology) : Order.Frame.MinimalAxioms (SatSet T) where
  inf_sSup_le_iSup_inf A S := by
    intro x hx
    obtain ⟨hxA, hxSup⟩ := hx
    have hcovA : T.cov x A.1 := T.cov_refl x A.1 hxA
    have hcovSup : T.cov x (⋃ U ∈ S, U.1) := hxSup
    have hmeet := T.cov_meet x A.1 (⋃ U ∈ S, U.1) hcovA hcovSup
    -- Each commonRefinement element c ∈ (A ⊓ U).1 for some U ∈ S, hence
    -- c ∈ (A ⊓ U : SatSet T) ≤ ⨆ b ∈ S, A ⊓ b.
    apply T.cov_mono x _ _ _ hmeet
    intro c hc
    obtain ⟨a', ha'A, y, hyU, hca', hcy⟩ := hc
    rw [Set.mem_iUnion] at hyU
    obtain ⟨U, hyU⟩ := hyU
    rw [Set.mem_iUnion] at hyU
    obtain ⟨hUS, hyU⟩ := hyU
    have hcA : c ∈ A := SatSet.le_mem A a' c hca' ha'A
    have hcU : c ∈ U.1 := SatSet.le_mem U y c hcy hyU
    -- Build c ∈ ⋃ V' ∈ Set.range ..., V'.1 explicitly.
    -- The V' we want is `⨆ (_ : U ∈ S), A ⊓ U`, which via `iSup_pos hUS`
    -- equals `A ⊓ U`.
    rw [Set.mem_iUnion]
    refine ⟨⨆ (_ : U ∈ S), A ⊓ U, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨⟨U, rfl⟩, ?_⟩
    -- Goal: c ∈ (⨆ (_ : U ∈ S), A ⊓ U).1
    rw [iSup_pos hUS]
    exact ⟨hcA, hcU⟩

/-- `SatSet T` is an `Order.Frame`. -/
instance instFrame (T : FormalTopology) : Order.Frame (SatSet T) :=
  Order.Frame.ofMinimalAxioms (frameMinAx T)

-- ============================================================
-- Section 6: Concrete frame instances — smoke tests
-- ============================================================

/-- The frame of `Unit.formalTopology` exists. -/
example : Order.Frame (SatSet Examples.Unit.formalTopology) := inferInstance

/-- The frame of `Bool.formalTopology` exists. -/
example : Order.Frame (SatSet Examples.Bool.formalTopology) := inferInstance

/-- The frame of `Unit × Bool` exists. -/
example : Order.Frame
    (SatSet (FormalTopology.prod Examples.Unit.formalTopology
                                 Examples.Bool.formalTopology)) :=
  inferInstance

end VRCycle.Topology
