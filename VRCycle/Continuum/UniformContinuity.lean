-- VRCycle/Continuum/UniformContinuity.lean
-- Operational Continuum (Path 1) — Stage B (file 3): the hypothesis vehicle in action.
--
-- STAGE: B. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md. Vehicle: HYPOTHESIS.
--
-- ## What this file does — the canonical Brouwer theorem, hypothesis-tracked
-- `uniform_continuity` : `Continuity → FanTheorem → ` every `F : Branch → ℕ` is
-- UNIFORMLY continuous (one modulus `N` works for all branches).  This is Brouwer's
-- "every function on Cantor space is uniformly continuous", derived from the two
-- principles carried AS HYPOTHESES — never adopted.  The axiom audit shows the result
-- adds no global axiom: it depends only on `[propext]` (+ Quot.sound), the principles
-- live in the statement.  This is the whole point of the chosen vehicle.
--
-- ## Proof shape
--   * pointwise `Continuity` gives, per branch `α`, a modulus `n` such that `F` is
--     constant on all branches through `α.take n` — so the "deciding nodes"
--     `B = {s | F is constant on branches through s}` form a bar (every branch meets it);
--   * `FanTheorem` collapses that bar to a uniform depth `N`;
--   * any two branches agreeing to depth `N` agree at the deciding node, so `F` agrees.

import VRCycle.Continuum.Cover
import Mathlib.Data.List.Basic

namespace VRCycle.Continuum

-- ============================================================
-- §  take helpers: length, pointwise agreement, prefix-of-prefix
-- ============================================================

/-- A performed segment of length `n` has length `n`. -/
theorem Branch.length_take (α : Branch) (n : ℕ) : (α.take n).length = n := by
  simp [Branch.take]

/-- If two branches agree to depth `N`, they agree to any smaller depth `m ≤ N`.
By induction on `N`, peeling the last bit with `Branch.take_succ` and `List.append_inj_left'`. -/
theorem take_le_eq {α β : Branch} {m : ℕ} :
    ∀ {N : ℕ}, m ≤ N → α.take N = β.take N → α.take m = β.take m := by
  intro N
  induction N with
  | zero => intro hmN h; obtain rfl := Nat.le_zero.mp hmN; exact h
  | succ N ih =>
      intro hmN h
      rw [Branch.take_succ, Branch.take_succ] at h
      have h1 : α.take N = β.take N := List.append_inj_left' h rfl
      rcases (by omega : m ≤ N ∨ m = N + 1) with hm | heq
      · exact ih hm h1
      · subst heq; rw [Branch.take_succ, Branch.take_succ]; exact h

-- ============================================================
-- §  Continuity + Fan ⟹ Uniform continuity
-- ============================================================

/-- **Brouwer's uniform continuity theorem, hypothesis-tracked.**  Under `Continuity`
(WC-N) and `FanTheorem` — both carried as hypotheses, never adopted — every operation
`F : Branch → ℕ` has a single modulus `N` good for all branches.  No global axiom is
added (audit: `[propext]`-tier); the principles live in the statement.  This exhibits
the chosen vehicle: a genuinely Brouwerian result, consistently, over classical Lean. -/
theorem uniform_continuity (hC : Continuity) (hF : FanTheorem) (F : Branch → ℕ) :
    ∃ N, ∀ α β : Branch, α.take N = β.take N → F α = F β := by
  -- The "deciding nodes": `s` such that `F` is constant on all branches through `s`.
  have hbar : ∀ α : Branch,
      α.Meets {s | ∀ β γ : Branch, β.Through s → γ.Through s → F β = F γ} := by
    intro α
    obtain ⟨n, hn⟩ := hC F α
    refine ⟨n, ?_⟩
    rw [Set.mem_setOf_eq]
    intro β γ hβ hγ
    have hlen : (α.take n).length = n := Branch.length_take α n
    have hβn : β.take n = α.take n := by rw [Branch.Through, hlen] at hβ; exact hβ
    have hγn : γ.take n = α.take n := by rw [Branch.Through, hlen] at hγ; exact hγ
    have hFβ : F α = F β := hn β hβn.symm
    have hFγ : F α = F γ := hn γ hγn.symm
    rw [← hFβ, ← hFγ]
  obtain ⟨N, hN⟩ := hF _ hbar
  refine ⟨N, ?_⟩
  intro α β hαβ
  obtain ⟨m, hmN, hmem⟩ := hN α
  rw [Set.mem_setOf_eq] at hmem
  have hlenm : (α.take m).length = m := Branch.length_take α m
  have hαT : α.Through (α.take m) := by rw [Branch.Through, hlenm]
  have hβT : β.Through (α.take m) := by
    rw [Branch.Through, hlenm]; exact (take_le_eq hmN hαβ).symm
  exact hmem α β hαT hβT

-- ============================================================
-- Axiom audit — Stage B (file 3)
-- ============================================================
-- The result must add NO global axiom (the principles are hypotheses).
#print axioms uniform_continuity

end VRCycle.Continuum
