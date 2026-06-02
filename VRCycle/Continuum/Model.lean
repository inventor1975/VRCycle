-- VRCycle/Continuum/Model.lean
-- Operational Continuum (Path 1) — Stage C: the operational model where Continuity holds.
--
-- STAGE: C. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md.
--
-- ## The two-register thesis, machine-checked
-- ClassicalBoundary.lean proved `Continuity` is FALSE in the classical/formal register.
-- Here we prove `Continuity` HOLDS in the OPERATIONAL register: functionals presented
-- operationally — by a finite-information "associate" `φ : List Bool → Option ℕ` that is
-- total along branches (`bar`) — are continuous, as a THEOREM (`continuity_of_nbhd`).
-- Continuity is not baked in; it is EARNED from the finite-information presentation
-- (the value is read at the least deciding prefix, so it is fixed by that finite segment).
--
--   * formal register:      Continuity FALSE  (ClassicalBoundary.not_continuity)
--   * operational register: Continuity TRUE   (Model.continuity_of_nbhd)
--
-- This is VR's two-register split, on a genuinely Brouwerian principle, machine-checked —
-- and it makes the `Continuity`-dependent results (uniform_continuity) non-vacuous over
-- the operational domain (Finding CONT-4 addressed for that domain).

import VRCycle.Continuum.UniformContinuity

namespace VRCycle.Continuum

/-- An **operationally-presented functional**: a finite-information associate
`φ : List Bool → Option ℕ` that **decides along every branch** (`bar`).  No modulus and no
continuity is assumed — only that some finite performed segment of each branch is decided. -/
structure NbhdFun where
  /-- The associate: a partial value on finite performed segments. -/
  φ : List Bool → Option ℕ
  /-- Totality along branches: every branch has a decided performed segment. -/
  bar : ∀ α : Branch, ∃ n, (φ (α.take n)).isSome = true

namespace NbhdFun

/-- The value of the functional at `α`: read at the **least** decided performed segment. -/
noncomputable def eval (F : NbhdFun) (α : Branch) : ℕ :=
  (F.φ (α.take (Nat.find (F.bar α)))).get (Nat.find_spec (F.bar α))

/-- The defining property of `eval`: `some (eval F α)` is the associate's value at the
least decided prefix. -/
theorem some_eval (F : NbhdFun) (α : Branch) :
    some (F.eval α) = F.φ (α.take (Nat.find (F.bar α))) := by
  simp only [eval]
  exact Option.some_get _

/-- **Continuity holds in the operational register.**  Every operationally-presented
functional is continuous: the value at `α` is fixed by the finite performed segment up to
the least deciding depth.  A THEOREM (no `Continuity` hypothesis) — the operational-side
of the two-register split (cf. `ClassicalBoundary.not_continuity`). -/
theorem continuity_of_nbhd (F : NbhdFun) (α : Branch) :
    ∃ n, ∀ β : Branch, α.take n = β.take n → F.eval α = F.eval β := by
  refine ⟨Nat.find (F.bar α), ?_⟩
  intro β hβ
  -- α and β agree on every prefix up to the deciding depth.
  have hagree : ∀ j, j ≤ Nat.find (F.bar α) → α.take j = β.take j :=
    fun j hj => take_le_eq hj hβ
  -- β decides at exactly the same least depth.
  -- `Nat.find_eq_iff` pulls Classical.choice (Finding CONT-5); go via antisymmetry
  -- of the choice-free `Nat.find_le` / `Nat.le_find_iff`.
  have hfindβ : Nat.find (F.bar β) = Nat.find (F.bar α) := by
    apply Nat.le_antisymm
    · apply Nat.find_le
      rw [← hagree _ (Nat.le_refl _)]
      exact Nat.find_spec (F.bar α)
    · rw [Nat.le_find_iff]
      intro j hj
      rw [← hagree j (Nat.le_of_lt hj)]
      exact Nat.find_min (F.bar α) hj
  -- the values agree.
  have hsβ : some (F.eval β) = F.φ (α.take (Nat.find (F.bar α))) := by
    rw [some_eval, hfindβ, hagree _ (Nat.le_refl _)]
  have hsα : some (F.eval α) = F.φ (α.take (Nat.find (F.bar α))) := some_eval F α
  exact Option.some.inj (hsα.trans hsβ.symm)

end NbhdFun

-- ============================================================
-- Axiom audit — Stage C
-- ============================================================
-- Expect choice-free: Nat.find over a decidable predicate; the bar is data-free `∃`.
#print axioms NbhdFun.eval
#print axioms NbhdFun.continuity_of_nbhd

end VRCycle.Continuum
