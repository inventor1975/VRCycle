-- VRCycle/Continuum/BarSound.lean
-- Operational Continuum (Path 1) — Stage B (file 4): full cover soundness, under bar induction.
--
-- STAGE: B. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md. Vehicle: HYPOTHESIS.
--
-- ## What this file does — the honest version of the CONT-2 gap
-- Finding CONT-2 showed FULL soundness `IsBar B → ∀ α, α.Meets B` is NOT free by
-- structural induction on `CoverGen` (local_/ref_mono pull opposite ways).  It is the
-- genuine bar theorem, tied to BAR INDUCTION.  Here we state monotone bar induction as a
-- `Prop` hypothesis (`BarInduction`) — never adopted; note it is even *classically* valid,
-- so certainly consistent — and derive full soundness CLEANLY from it, with NO induction
-- on `CoverGen`.  Choice-free; the principle lives in the statement.
--
-- ## Proof shape
-- Take `Q s := every branch through s meets B`.  Then `B ⊆ Q` (a branch through `s ∈ B`
-- meets `B` at `s`), `Q` is hereditary (`Q (s++[false]) → Q (s++[true]) → Q s`, since a
-- branch through `s` continues through one child), and `cov [] B` holds; bar induction
-- yields `Q []` = every branch (all pass through `[]`) meets `B`.

import VRCycle.Continuum.Cover

namespace VRCycle.Continuum

-- ============================================================
-- §  Bar induction — STATED as a Prop, never adopted
-- ============================================================

/-- **Monotone bar induction** for the binary spread, as a hypothesis only.  If `B` is a
formal bar (`cov [] B`), every bar node has property `Q`, and `Q` is hereditary upward
(both children have `Q` ⇒ the node has `Q`), then the root has `Q`.  A Brouwerian
principle (here classically valid too); carried as a hypothesis, not adopted. -/
def BarInduction : Prop :=
  ∀ (B : Set (List Bool)) (Q : List Bool → Prop),
    (∀ s, s ∈ B → Q s) →
    (∀ s, Q (s ++ [false]) → Q (s ++ [true]) → Q s) →
    binarySpread.cov [] B → Q []

-- ============================================================
-- §  Full cover soundness, under bar induction
-- ============================================================

/-- **Full soundness of the formal cover for branches, under bar induction.**  If `B` is
a bar (`IsBar B`), then every branch meets `B`.  Derived from `BarInduction` via the
"deciding node" property `Q s := every branch through s meets B` — no induction on
`CoverGen`, sidestepping the CONT-2 obstruction.  Choice-free; `hBI` is a hypothesis. -/
theorem cover_sound (hBI : BarInduction) {B : Set (List Bool)} (hB : IsBar B) :
    ∀ α : Branch, α.Meets B := by
  have hQ : ∀ γ : Branch, γ.Through ([] : List Bool) → γ.Meets B := by
    refine hBI B (fun s => ∀ γ : Branch, γ.Through s → γ.Meets B) ?_ ?_ hB
    · -- B ⊆ Q: a branch through s ∈ B meets B at s.
      intro s hs γ hγ
      exact ⟨s.length, by rw [hγ]; exact hs⟩
    · -- Q hereditary: a branch through s continues through one child.
      intro s hf ht γ hγ
      cases hb : γ s.length with
      | false =>
          refine hf γ ?_
          change γ.take (s ++ [false]).length = s ++ [false]
          have hlen : (s ++ [false]).length = s.length + 1 := by simp
          rw [hlen, Branch.take_succ, hγ, hb]
      | true =>
          refine ht γ ?_
          change γ.take (s ++ [true]).length = s ++ [true]
          have hlen : (s ++ [true]).length = s.length + 1 := by simp
          rw [hlen, Branch.take_succ, hγ, hb]
  intro α
  exact hQ α (by simp [Branch.Through, Branch.take])

-- ============================================================
-- Axiom audit — Stage B (file 4)
-- ============================================================
-- Must be choice-free; `hBI` is a hypothesis (no global axiom added).
#print axioms cover_sound

end VRCycle.Continuum
