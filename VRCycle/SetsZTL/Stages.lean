-- VRCycle/SetsZTL/Stages.lean
-- VR Part II, step (б): choice sequences as the lazy register — the
-- Lean half of the measured stand ZTL/zchoice.py (E22).
--
-- The stitch: a growing binary sequence is VR's own `Branch`
-- (Continuum, Path 1); its performed segment `take` is the LAZY
-- register (data, monotone), and what a stage may assert is what the
-- segment FORCES over every admitted continuation — the GREEDY
-- register's court. Machine-checked here (each measured first):
--
--   * `Forces` — the stage court — and its HEREDITY (`forces_mono`):
--     a verdict earned at a node survives every future choice; the
--     Kripke persistence the greedy register lacks (E12/E21) is
--     native to the lazy one.
--   * THE LADDER CELLS at the kernel: p→p is REDEEMED by the stage
--     court (`identity_forced_at_root` — every branch satisfies it;
--     `identity_greedy_abstains` — zimp Z Z = F: a law of logic, not
--     of data), while the ¬¬ ladder OVERCLAIMS (`ladder_overclaims` —
--     znot (znot Z) = T yet no prefix forces the atom:
--     `atom_not_forced_at_root`).
--   * LAWLESS STAGE = SUPERVALUATION (`stage_eq_super`): for a
--     horizon-H property, forcing over all continuations of a node is
--     exactly the universal quantifier over all finite completions —
--     the world-set of E10's global □. Zero trust is assertability
--     against a maximally ignorant future.
--   * STREAMS: equality of branches is never forced at a finite stage
--     (`eq_never_forced` — two explicit continuations diverge), while
--     apartness is earned by one disagreeing reveal and, being an
--     ∃-fact of the branches, persists (`apart_earned`).
--
-- Axiom profile: MEASURED at the bottom; the kernel cells are [];
-- the Branch layer sits at [propext(, Quot.sound)] — the Continuum's
-- own choice-free tier (Branch.lean itself is [propext]); no
-- Classical.choice anywhere.
--
-- TODO (optional, curator 2026-07-12; twin of the Describable note):
-- the residual propext here is mathlib's, not ours — every List lemma
-- used (length_append, getElem_map, take_range, ext_getElem, …) is
-- constructively true but proved with simp upstream. Removable at a
-- price: either hand-roll ~9 list lemmas (the List.range ones are the
-- painful part — tail-recursive loop implementation; 1–2 days, chain
-- risk), or refactor Continuum's Branch.take to a structural seg
-- (cleaner lemmas, but surgery on a published module used by
-- Cantor/BarSound). Reopen only if the whole Continuum wing is ever
-- lifted to the empty list; the tier as it stands matches the wing.

import VRCycle.Continuum.Branch
import VRCycle.Continuum.ListCore
import VRCycle.Continuum.Cover
import VRCycle.SetsZTL.Kernel

namespace VRCycle.SetsZTL

open VRCycle.Continuum

-- ============================================================
-- §1.  The stage court and its heredity
-- ============================================================

/-- The stage court: node `s` (a performed segment) **forces** `P` when
every branch passing through `s` satisfies `P`. -/
def Forces (s : List Bool) (P : Branch → Prop) : Prop :=
  ∀ α : Branch, α.Through s → P α

/-- A performed segment of length `n` has length `n` (on `[]`, via `ListCore`). -/
theorem take_length (α : Branch) (n : ℕ) : (α.take n).length = n := by
  show ((List.range n).map α).length = n
  rw [ListCore.length_map', ListCore.length_range']

/-- Reading the `i`-th bit of a performed segment gives the branch's `i`-th bit. -/
theorem nth_take (α : Branch) : ∀ (n i : ℕ), i < n → ListCore.nth (α.take n) i = some (α i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
      rcases Nat.lt_or_ge i n with hi | hi
      · rw [Branch.take_succ, ListCore.nth_append_left _ _ _ (by rw [take_length]; exact hi)]
        exact nth_take α n i hi
      · have hin : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hi
        subst hin
        have e := ListCore.nth_append_length (α i) (α.take i)
        rw [take_length] at e
        rw [Branch.take_succ]; exact e

/-- A shorter performed segment is a prefix of a longer one. -/
theorem take_take_branch (α : Branch) : ∀ (m k : ℕ), k ≤ m → (α.take m).take k = α.take k
  | 0, k, h => by
      have hk : k = 0 := Nat.le_zero.mp h
      subst hk; rfl
  | m + 1, k, h => by
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · have hk' : k ≤ m := Nat.le_of_lt_succ hk
        rw [Branch.take_succ, ListCore.take_append_of_le _ _ _ (by rw [take_length]; exact hk')]
        exact take_take_branch α m k hk'
      · have hkm : k = m + 1 := Nat.le_antisymm h hk
        subst hkm
        have e := ListCore.take_length' (α.take (m + 1))
        rw [take_length] at e
        exact e

/-- A branch through a node passes through every earlier node. -/
theorem through_mono {s t : List Bool} (hst : s <+: t) {α : Branch}
    (h : α.Through t) : α.Through s := by
  obtain ⟨u, rfl⟩ := hst
  unfold Branch.Through at h ⊢
  have hlen : s.length ≤ (s ++ u).length := by
    rw [ListCore.length_append']; exact Nat.le_add_right _ _
  calc α.take s.length
      = (α.take (s ++ u).length).take s.length := (take_take_branch α _ _ hlen).symm
    _ = ((s ++ u).take s.length) := by rw [h]
    _ = s := List.take_left

/-- **Heredity of the stage court**: a verdict forced at a node is
forced at every extension — earned-at-a-stage survives every future
choice. The Kripke persistence the greedy register refuses as a free
axiom (E12) is native to the lazy register. -/
theorem forces_mono {s t : List Bool} (hst : s <+: t)
    {P : Branch → Prop} (h : Forces s P) : Forces t P :=
  fun α hα => h α (through_mono hst hα)

-- ============================================================
-- §2.  The ladder cells at the kernel (E22 §1)
-- ============================================================

/-- The identity law, REDEEMED by the stage court: at the root every
branch satisfies `α 0 → α 0` (read through the classical kernel of the
implication) — truth by logic, needing no data. -/
theorem identity_forced_at_root :
    Forces [] (fun α => (!(α 0) || α 0) = true) := by
  intro α _
  cases α 0 <;> rfl

/-- ...while the greedy court abstains on the same law over an
unrevealed atom: `zimp Z Z = F`. A law of logic, not of data. -/
theorem identity_greedy_abstains : V.zimp V.Z V.Z = V.F := by decide

/-- The ¬¬ ladder verdict of the greedy court... -/
theorem ladder_overclaims : V.znot (V.znot V.Z) = V.T := by decide

/-- ...asserts what NO prefix forces: at the root the atom `α 0` is not
forced — the all-false branch refutes it. Raw greedy verdicts are not
assertions about the future; only warranted ones are (E22 §1). -/
theorem atom_not_forced_at_root :
    ¬ Forces [] (fun α => α 0 = true) := by
  intro h
  have := h (fun _ => false) rfl
  exact Bool.false_ne_true this

-- ============================================================
-- §3.  Lawless stage = supervaluation over finite completions (E22 §2)
-- ============================================================

/-- Extend a node to a full branch by an arbitrary continuation. -/
def pad (s : List Bool) (f : ℕ → Bool) : Branch := fun n =>
  if h : n < s.length then s[n] else f (n - s.length)

theorem pad_through (s : List Bool) (f : ℕ → Bool) :
    (pad s f).Through s := by
  unfold Branch.Through
  apply ListCore.nth_ext _ _ (take_length _ _)
  intro i
  rcases Nat.lt_or_ge i s.length with hi | hi
  · rw [nth_take _ _ _ hi, ListCore.nth_eq_getElem s i hi]
    show some (if h : i < s.length then s[i] else f (i - s.length)) = some s[i]
    rw [dif_pos hi]
  · rw [ListCore.nth_eq_none _ _ (by rw [take_length]; exact hi), ListCore.nth_eq_none s i hi]

/-- **Lawless stage = global supervaluation.** For a property read off
the horizon-`H` segment, the stage court at node `s` is EXACTLY the
universal quantifier over all finite completions of `s` to length `H` —
the world-set of E10's global □. Measured totally in E22 §2 (49545
pairs); here the equivalence is kernel-checked. -/
theorem stage_eq_super (s : List Bool) (H : ℕ) (hsH : s.length ≤ H)
    (Q : List Bool → Prop) :
    Forces s (fun α => Q (α.take H)) ↔
      ∀ w : List Bool, w.length = H → s <+: w → Q w := by
  constructor
  · intro h w hw hsw
    have hthr : (pad w (fun _ => false)).Through s :=
      through_mono hsw (pad_through w _)
    have hq : Q ((pad w (fun _ => false)).take H) := h _ hthr
    have htw : (pad w (fun _ => false)).take H = w := by
      have hthru := pad_through w (fun _ => false)
      unfold Branch.Through at hthru
      rw [← hw]; exact hthru
    rwa [htw] at hq
  · intro h α hα
    show Q (α.take H)
    refine h (α.take H) (take_length α H) ?_
    have hs : (α.take H).take s.length = s := by
      rw [take_take_branch α H s.length hsH]; exact hα
    exact hs ▸ List.take_prefix s.length (α.take H)

-- ============================================================
-- §4.  Streams: equality never forced, apartness earned (E22 §4, E6)
-- ============================================================

/-- Apartness of branches: a disagreement earned at a finite index —
an ∃-fact, hence persistent once earned. -/
def Apart (α β : Branch) : Prop := ∃ n, α n ≠ β n

/-- **Equality of branches is never forced at a finite stage**: below
any node two explicit continuations diverge right after the segment.
Stream identity is Z-permanent (E6, E22 §4). -/
theorem eq_never_forced (s : List Bool) :
    ¬ (∀ α β : Branch, α.Through s → β.Through s → α = β) := by
  intro h
  have heq := h (pad s (fun _ => false)) (pad s (fun _ => true))
    (pad_through s _) (pad_through s _)
  have := congrFun heq s.length
  unfold pad at this
  rw [dif_neg (Nat.lt_irrefl s.length), dif_neg (Nat.lt_irrefl s.length)]
    at this
  exact Bool.false_ne_true this

/-- A branch through a node agrees with the node pointwise. -/
theorem through_nth {α : Branch} {s : List Bool}
    (h : α.Through s) (i : ℕ) (hi : i < s.length) : ListCore.nth s i = some (α i) := by
  have e := nth_take α s.length i hi
  unfold Branch.Through at h
  rw [h] at e
  exact e

theorem through_pointwise {α : Branch} {s : List Bool}
    (h : α.Through s) (i : ℕ) (hi : i < s.length) : α i = s[i] := by
  have e := through_nth h i hi
  rw [ListCore.nth_eq_getElem s i hi] at e
  exact (Option.some.inj e).symm

/-- **Apartness is earned by one disagreeing reveal**: branches passing
through `s ++ [true]` and `s ++ [false]` are apart at index `s.length`;
being an ∃-fact of the branches, the apartness persists under all
further growth. -/
theorem apart_earned {s : List Bool} {α β : Branch}
    (hα : α.Through (s ++ [true])) (hβ : β.Through (s ++ [false])) :
    Apart α β := by
  have hlen1 : s.length < (s ++ [true]).length := by
    rw [ListCore.length_append_singleton]; exact Nat.lt_succ_self s.length
  have hlen2 : s.length < (s ++ [false]).length := by
    rw [ListCore.length_append_singleton]; exact Nat.lt_succ_self s.length
  refine ⟨s.length, ?_⟩
  have h1 : α s.length = true := by
    have e := through_nth hα s.length hlen1
    rw [ListCore.nth_append_length] at e
    exact (Option.some.inj e).symm
  have h2 : β s.length = false := by
    have e := through_nth hβ s.length hlen2
    rw [ListCore.nth_append_length] at e
    exact (Option.some.inj e).symm
  rw [h1, h2]; exact fun hc => Bool.false_ne_true hc.symm

-- CHECKS: no sorry, no admit.

-- Axiom audit — MEASURED per object (VR discipline).
#print axioms Forces
#print axioms through_mono
#print axioms forces_mono
#print axioms identity_forced_at_root
#print axioms identity_greedy_abstains
#print axioms ladder_overclaims
#print axioms atom_not_forced_at_root
#print axioms pad_through
#print axioms stage_eq_super
#print axioms eq_never_forced
#print axioms through_pointwise
#print axioms apart_earned

end VRCycle.SetsZTL
