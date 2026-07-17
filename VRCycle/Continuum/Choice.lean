-- VRCycle/Continuum/Choice.lean
-- Operational Continuum (Path 1) — choice, read operationally (the AC package).
--
-- STAGE: B (consolidation). SOURCE: VR-LOGIC.md §3 (AC), ADDENDUM (AC/AD as T→T).
--
-- ## The operational reading of choice, in four parts
--   (1) DC — process-based dependent choice — is OPERATIONALLY AVAILABLE: a history-dependent
--       rule `f : List Bool → Bool` determines a branch step by step, CHOICE-FREE (recursion).
--       `operational_dependent_choice`.  Choice here is available because there is a RULE.
--   (2) WC-N / Continuity — choice decided by finite information — is the two-register split,
--       already proved: FALSE formally (`ClassicalBoundary.not_continuity`), TRUE operationally
--       (`Model.continuity_of_nbhd`).
--   (3) full AC — simultaneous selection over an uncountable family WITHOUT a rule — has no
--       operational correlate: no rule, no step-by-step construction.  It is a FORMAL-REGISTER
--       LABEL (essay-level, VR-LOGIC §2/§3) — NOT formalised as an operational object here.
--   (4) AC + AD → ⊥ is a T→T phenomenon (ADDENDUM): the contradiction needs both formal
--       contexts co-asserted in one deduction, with no operational material between; it never
--       returns through the operational floor.  Essay-level, not a Lean claim.
--   (5) Russell's SOCKS — selection over indistinguishable pairs — splits the same way:
--       as a RULE it is impossible (no swap-symmetric selector, `no_symmetric_selector`,
--       the Fraenkel–Mostowski statement in miniature); as an ACT it is a continuum (every
--       branch — operationally, a lawless coin — selects; `selectors_not_enumerable`).
--       Rules: zero.  Acts: uncountable.  Choice lives as an act, never as an object.
--
-- This file formalises (1) and bundles (1)+(2, operational side) choice-free; (2-formal), (3),
-- (4) are cited / essay, by design.
--
-- ## Axiom profile: choice-free for the operational side (verified below).

import VRCycle.Continuum.Model              -- NbhdFun, continuity_of_nbhd  (operational Continuity TRUE)
import VRCycle.Continuum.ClassicalBoundary  -- not_continuity               (formal Continuity FALSE)
import Mathlib.Data.List.Range

namespace VRCycle.Continuum

-- ============================================================
-- §DC.  Process-based dependent choice — operationally available, choice-free
-- ============================================================

/-- The finite performed segment built by a history-dependent rule `f`: at each step the next
bit is `f` applied to the segment so far.  Pure recursion — no choice. -/
def dcPrefix (f : List Bool → Bool) : ℕ → List Bool
  | 0     => []
  | n + 1 => dcPrefix f n ++ [f (dcPrefix f n)]

/-- The branch determined by the rule `f`: its `n`-th bit is `f` of the length-`n` segment. -/
def dcSeq (f : List Bool → Bool) (n : ℕ) : Bool := f (dcPrefix f n)

/-- The branch's length-`n` performed segment is exactly `dcPrefix f n`. -/
theorem take_dcSeq (f : List Bool → Bool) (n : ℕ) :
    Branch.take (dcSeq f) n = dcPrefix f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (List.range (k + 1)).map (dcSeq f) = dcPrefix f (k + 1)
    rw [List.range_succ, List.map_append]
    have ihm : (List.range k).map (dcSeq f) = dcPrefix f k := ih
    rw [ihm]; rfl

/-- **Process-based dependent choice is operationally available (choice-free).**  Every
history-dependent rule `f : List Bool → Bool` determines a branch `α` with `α n = f (α.take n)`
— the choice at each step is delivered by the rule, and the whole sequence is built by
recursion, with no appeal to `Classical.choice`.  This is DC as an operational act: choice is
available because there is a rule. -/
theorem operational_dependent_choice (f : List Bool → Bool) :
    ∃ α : Branch, ∀ n, α n = f (Branch.take α n) := by
  refine ⟨dcSeq f, fun n => ?_⟩
  rw [take_dcSeq]
  rfl

-- ============================================================
-- §AC-package.  The operational side, bundled (choice-free)
-- ============================================================

/-- **Operational choice, the choice-free side.**  (1) DC is available — a rule determines a
branch (`operational_dependent_choice`); (2) every operationally-presented functional is
continuous — choice decided by finite information (`continuity_of_nbhd`).  Both choice-free.
The formal-register contrast — `Continuity` is classically FALSE (`not_continuity`) — and full
AC as a label with no operational correlate, and AC+AD as a T→T phenomenon, are cited/essay
(see the file header), not bundled here (they are not operational objects). -/
theorem operational_choice_available :
    (∀ f : List Bool → Bool, ∃ α : Branch, ∀ n, α n = f (Branch.take α n)) ∧
    (∀ (F : NbhdFun) (α : Branch), ∃ n, ∀ β : Branch,
        Branch.take α n = Branch.take β n → F.eval α = F.eval β) :=
  ⟨operational_dependent_choice, NbhdFun.continuity_of_nbhd⟩

-- ============================================================
-- §Socks.  Russell's socks: rules number zero, acts a continuum
-- ============================================================

/-- The swap of the indistinguishable pair in box `k`, acting on selections.
The two socks of a box are `false`/`true` only in the formal register's
bookkeeping — the box itself offers no mark; the swap at `k` flips the pick
there.  A rule that "does not read our labels" must be invariant under these
swaps beyond some finite bookkeeping bound. -/
def swapAt (k : ℕ) (c : ℕ → Bool) : ℕ → Bool :=
  fun n => if n = k then !(c n) else c n

theorem swapAt_self (k : ℕ) (c : ℕ → Bool) : swapAt k c k = !(c k) := by
  unfold swapAt
  rw [if_pos rfl]

/-- **No selection rule exists** (Russell's socks; the Fraenkel–Mostowski sock
statement in miniature).  A rule may read the bookkeeping labels only up to a
finite bound and must be swap-invariant beyond it; no selection is — the swap
at any box beyond the bound moves the pick there.  Choice-free, and rule-free
by theorem. -/
theorem no_symmetric_selector :
    ¬ ∃ (c : ℕ → Bool) (N : ℕ), ∀ k, N ≤ k → swapAt k c = c := by
  rintro ⟨c, N, h⟩
  have h1 : swapAt N c N = c N := congrFun (h N (Nat.le_refl N)) N
  rw [swapAt_self] at h1
  cases hc : c N with
  | false => rw [hc] at h1; exact Bool.noConfusion h1
  | true  => rw [hc] at h1; exact Bool.noConfusion h1

/-- Every branch — every performed sequence; operationally, a lawless coin —
IS a selection: the act picks where no rule can.  Definitionally choice-free. -/
def actSelector (β : Branch) : ℕ → Bool := β

/-- **The selectors are exactly the branches**, so the acts are not even
enumerable (`branches_not_enumerable`) while the rules number zero
(`no_symmetric_selector`): selection over indistinguishable pairs exists
never as a rule and uncountably as an act. -/
theorem selectors_not_enumerable :
    ¬ ∃ e : ℕ → (ℕ → Bool), Function.Surjective e :=
  branches_not_enumerable

-- ============================================================
-- §Twins.  The computational face: anonymous symmetry cannot break
-- ============================================================

/-- One synchronous round of an anonymous network: every node applies the
SAME rule `f` to (left neighbour, self, right neighbour).  The wiring
`L, R` is arbitrary — this is stronger than a ring. -/
def netStep (f : S → S → S → S) (L R : Fin m → Fin m)
    (c : Fin m → S) : Fin m → S :=
  fun i => f (c (L i)) (c i) (c (R i))

/-- The run of the network from the identical start `s0`. -/
def netRun (f : S → S → S → S) (L R : Fin m → Fin m) (s0 : S) :
    ℕ → Fin m → S
  | 0     => fun _ => s0
  | t + 1 => netStep f L R (netRun f L R s0 t)

/-- **Deterministic twins never break** (the folklore core of Angluin 1980):
in an anonymous network of identical deterministic automata started
identically, the configuration is constant across nodes at EVERY round,
whatever the wiring.  Symmetry is not broken — it is reproduced by every
step. -/
theorem twins_never_break (f : S → S → S → S) (L R : Fin m → Fin m)
    (s0 : S) : ∀ t, ∀ i j : Fin m, netRun f L R s0 t i = netRun f L R s0 t j := by
  intro t
  induction t with
  | zero => intro i j; rfl
  | succ t ih =>
    intro i j
    show f _ _ _ = f _ _ _
    rw [ih (L i) (L j), ih i j, ih (R i) (R j)]

/-- **No leader, ever**: with at least two nodes, no round distinguishes a
unique one — whatever "distinguished" means (any predicate `P`).  The
deterministic half of the sock story, machine-checked: without a coin —
without a cell invariant under negation — the symmetric cannot choose. -/
theorem no_unique_leader (f : S → S → S → S) (L R : Fin m → Fin m)
    (s0 : S) (P : S → Prop) (i j : Fin m) (hij : i ≠ j) :
    ∀ t, ¬ ∃! k, P (netRun f L R s0 t k) := by
  rintro t ⟨k, hk, huniq⟩
  have hi : P (netRun f L R s0 t i) := by
    rw [twins_never_break f L R s0 t i k]; exact hk
  have hj : P (netRun f L R s0 t j) := by
    rw [twins_never_break f L R s0 t j k]; exact hk
  exact hij ((huniq i hi).trans (huniq j hj).symm)

-- ============================================================
-- Axiom audit
-- ============================================================
#print axioms operational_dependent_choice
#print axioms operational_choice_available
#print axioms not_continuity   -- the formal-register contrast: classical by design
#print axioms no_symmetric_selector
#print axioms selectors_not_enumerable
#print axioms twins_never_break
#print axioms no_unique_leader

end VRCycle.Continuum
