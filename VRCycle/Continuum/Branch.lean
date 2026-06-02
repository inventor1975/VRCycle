-- VRCycle/Continuum/Branch.lean
-- Operational Continuum (Path 1) — Stage B: branches, non-enumerability, principles.
--
-- STAGE: B (of A→B→C). SOURCE: PLAN_OPERATIONAL_CONTINUUM.md. Vehicle: HYPOTHESIS.
--
-- ## The hard constraint (PLAN §"THE pinned hazard")
-- We must NOT `axiom` Brouwer's continuity / the fan theorem: over classical mathlib
-- that is inconsistent (classical logic proves a discontinuous `Branch → ℕ` exists).
-- So the Brouwerian principles are stated here as `Prop`s and only ever used as
-- HYPOTHESES.  Consistency is preserved: any theorem that needs them carries them in
-- its statement, and the axiom audit shows no global axiom is added.
--
-- ## What this file does
-- B1 (unconditional, constructive — the payoff of Path 1):
--   `branches_not_enumerable` — the space of branches is non-enumerable (Cantor's
--   diagonal).  Choice-free.  This is, concretely, VR's becoming-space failing to be
--   countable — the whole point of the operational continuum.
-- B2 (seeds, stated not adopted):
--   `Branch.take` / `Through` / `Meets` — a branch's finite performed segments and how
--   it enters a bar; `Continuity` (WC-N) and `FanTheorem` as `Prop`s for later
--   hypothesis-tracked theorems.
--
-- ## The three registers, now with branches as objects
-- A `Branch` (`ℕ → Bool`) is the *becoming/potential* sequence as a whole; its finite
-- prefixes `Branch.take α n` are the *operational* performed segments (nodes of the
-- Stage-A spread).  The non-enumerability theorem is the structural witness that the
-- becoming register genuinely exceeds the (countable) operational register.

import VRCycle.Continuum.Spread
import Mathlib.Data.List.Range

namespace VRCycle.Continuum

-- ============================================================
-- §B0.  Branches and their finite performed segments
-- ============================================================

/-- A **branch** of the binary spread: a full (becoming) binary sequence. -/
def Branch : Type := ℕ → Bool

/-- The length-`n` performed segment of a branch: `[α 0, …, α (n-1)]` — a Stage-A node. -/
def Branch.take (α : Branch) (n : ℕ) : List Bool := (List.range n).map α

/-- A branch **passes through** node `s` when its prefix of that length is `s`. -/
def Branch.Through (α : Branch) (s : List Bool) : Prop := α.take s.length = s

/-- A branch **meets** a set of nodes `B` when one of its performed segments lands in `B`. -/
def Branch.Meets (α : Branch) (B : Set (List Bool)) : Prop := ∃ n, α.take n ∈ B

-- ============================================================
-- §B1.  Non-enumerability (constructive, choice-free) — the payoff
-- ============================================================

/-- **The space of branches is non-enumerable.**  No `e : ℕ → Branch` is surjective:
the diagonal branch `fun n => !(e n n)` differs from every `e k` at `k`.  Constructive —
Cantor's diagonal needs no choice and no Brouwerian principle.  This is the concrete
sense in which VR's becoming-space is not countable. -/
theorem branches_not_enumerable : ¬ ∃ e : ℕ → Branch, Function.Surjective e := by
  rintro ⟨e, he⟩
  obtain ⟨k, hk⟩ := he (fun n => !(e n n))
  have h : e k k = !(e k k) := congrFun hk k
  cases hb : e k k <;> rw [hb] at h <;> simp at h

-- ============================================================
-- §B2.  Brouwerian principles — STATED as Props, never adopted
-- ============================================================

/-- **Weak continuity for numbers (WC-N)**, as a hypothesis only.  Every operation from
branches to numbers is decided by a finite performed segment.  Classically FALSE; here
it is never asserted, only carried as a hypothesis in B2 theorems. -/
def Continuity : Prop :=
  ∀ (F : Branch → ℕ) (α : Branch), ∃ n, ∀ β : Branch, α.take n = β.take n → F α = F β

/-- **The fan theorem**, as a hypothesis only.  If every branch meets `B`, then `B` is met
within a uniform finite depth `N`.  The constructive compactness of the binary spread;
carried as a hypothesis, not adopted. -/
def FanTheorem : Prop :=
  ∀ B : Set (List Bool), (∀ α : Branch, α.Meets B) →
    ∃ N, ∀ α : Branch, ∃ n ≤ N, α.take n ∈ B

-- ============================================================
-- Axiom audit — Stage B (file 1)
-- ============================================================
-- B1 must be choice-free.  Principles are mere `Prop`s.

#print axioms branches_not_enumerable
#print axioms Continuity
#print axioms FanTheorem

end VRCycle.Continuum
