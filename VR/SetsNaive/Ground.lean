-- VR/SetsNaive/Ground.lean
-- VR-Sets, naive edition — Stage N2: the GROUNDED register, Kripke's least fixed point as an
-- inductive predicate.
--
-- `Val b φ` reads "φ is grounded with value b".  It is the least fixed point of the strong-
-- Kleene jump (`Jump`) — the LAZY register of ZTL (cf. ZTL/lean/ZGround.lean, which proves the
-- same for finite systems by iteration).  Here the universe is infinite, so the fixed point is
-- not iterated: it is the inductive definition itself, and leastness is its induction
-- principle.  A universal statement is earned by a RULE (`allT` takes a function covering every
-- closed term), never by a survey.  A formula grounded neither way is a quarantine cell — the
-- input mark Z.
--
-- Machine-checked here:
--   * `val_fix` / `val_least` — `Val` IS a fixed point of the jump, and the least one;
--   * `consistent` — nothing is grounded both T and F (the clean part is consistent);
--   * `comprehension` — naive comprehension holds as a LAW, in every cell: `a ∈ {x : φ}` and
--     `φ(a)` have the same status, clean or dirty (no restriction on φ);
--   * `em_iff` / `em_never_false` — the excluded middle is earned EXACTLY in the clean cells
--     and refuted in none (ZTL's thesis, for naive sets);
--   * `russell_quarantine`, `S_quarantine` — R∈R and S∈S stay Z; `V_mem_V`, `all_in_V` —
--     the universal set is clean, and "everything is in V" is earned by a rule.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Syntax

namespace VRCycle.SetsNaive

-- No auto-generated `injEq` lemmas (they carry `propext`; the guard rejects them). Proofs use
-- `cases` on constructor equalities (noConfusion), which is axiom-free.
set_option genInjectivity false

/-- The strong-Kleene jump: what one step of evaluation makes of an assignment `P`. -/
def Jump (P : Bool → Fm → Prop) : Bool → Fm → Prop
  | true,  .top => True
  | false, .top => False
  | b, .mem a (.abs φ) => P b (φ.inst a)
  | _, .mem _ (.var _) => False
  | b, .neg φ => P (!b) φ
  | true,  .and φ ψ => P true φ ∧ P true ψ
  | false, .and φ ψ => P false φ ∨ P false ψ
  | true,  .all φ => ∀ c, P true (φ.inst c)
  | false, .all φ => ∃ c, P false (φ.inst c)

/-- The grounded register: the least fixed point of `Jump`. -/
inductive Val : Bool → Fm → Prop where
  | top : Val true .top
  | memT {a φ} : Val true (φ.inst a) → Val true (.mem a (.abs φ))
  | memF {a φ} : Val false (φ.inst a) → Val false (.mem a (.abs φ))
  | negT {φ} : Val false φ → Val true (.neg φ)
  | negF {φ} : Val true φ → Val false (.neg φ)
  | andT {φ ψ} : Val true φ → Val true ψ → Val true (.and φ ψ)
  | andFl {φ ψ} : Val false φ → Val false (.and φ ψ)
  | andFr {φ ψ} : Val false ψ → Val false (.and φ ψ)
  | allT {φ} : (∀ c, Val true (φ.inst c)) → Val true (.all φ)
  | allF {φ} (c : Tm) : Val false (φ.inst c) → Val false (.all φ)

/-- `Val` is a fixed point of the jump. -/
theorem val_fix : ∀ (b : Bool) (φ : Fm), Val b φ ↔ Jump Val b φ := by
  intro b φ
  constructor
  · intro h
    cases h with
    | top => exact trivial
    | memT h => exact h
    | memF h => exact h
    | negT h => exact h
    | negF h => exact h
    | andT h1 h2 => exact ⟨h1, h2⟩
    | andFl h => exact Or.inl h
    | andFr h => exact Or.inr h
    | allT h => exact h
    | allF c h => exact ⟨c, h⟩
  · intro h
    cases b <;> cases φ with
    | top => first | exact False.elim h | exact .top
    | mem a t =>
        cases t with
        | var n => exact False.elim h
        | abs φ => first | exact .memT h | exact .memF h
    | neg φ => first | exact .negT h | exact .negF h
    | and φ ψ =>
        first
        | exact .andT h.1 h.2
        | exact (match h with | Or.inl h => .andFl h | Or.inr h => .andFr h)
    | all φ =>
        first
        | exact .allT h
        | exact (match h with | ⟨c, hc⟩ => .allF c hc)

/-- `Val` is the LEAST fixed point: it lies below every assignment closed under the jump. -/
theorem val_least (P : Bool → Fm → Prop) (hP : ∀ b φ, Jump P b φ → P b φ) :
    ∀ {b φ}, Val b φ → P b φ := by
  intro b φ h
  induction h with
  | top => exact hP true .top trivial
  | memT _ ih => exact hP _ _ ih
  | memF _ ih => exact hP _ _ ih
  | negT _ ih => exact hP _ _ ih
  | negF _ ih => exact hP _ _ ih
  | andT _ _ ih1 ih2 => exact hP _ _ ⟨ih1, ih2⟩
  | andFl _ ih => exact hP _ _ (Or.inl ih)
  | andFr _ ih => exact hP _ _ (Or.inr ih)
  | allT _ ih => exact hP _ _ ih
  | allF c _ ih => exact hP _ _ ⟨c, ih⟩

/-- **Consistency of the clean part**: nothing is grounded both T and F. -/
theorem consistent : ∀ {b φ}, Val b φ → Val (!b) φ → False := by
  intro b φ h
  induction h with
  | top => intro h'; cases h'
  | memT _ ih => intro h'; cases h' with | memF h'' => exact ih h''
  | memF _ ih => intro h'; cases h' with | memT h'' => exact ih h''
  | negT _ ih => intro h'; cases h' with | negF h'' => exact ih h''
  | negF _ ih => intro h'; cases h' with | negT h'' => exact ih h''
  | andT _ _ ih1 ih2 => intro h'; cases h' with
      | andFl h'' => exact ih1 h''
      | andFr h'' => exact ih2 h''
  | andFl _ ih => intro h'; cases h' with | andT h'' _ => exact ih h''
  | andFr _ ih => intro h'; cases h' with | andT _ h'' => exact ih h''
  | allT _ ih => intro h'; cases h' with | allF c h'' => exact ih c h''
  | allF c _ ih => intro h'; cases h' with | allT h'' => exact ih (h'' c)

/-- **Naive comprehension is a law in every cell**: `a ∈ {x : φ}` has exactly the status of
`φ(a)` — earned T, earned F, or quarantined together.  No restriction on `φ`. -/
theorem comprehension (b : Bool) (a : Tm) (φ : Fm) :
    Val b (.mem a (.abs φ)) ↔ Val b (φ.inst a) := by
  cases b <;> exact val_fix _ _

theorem val_neg (b : Bool) (φ : Fm) : Val b (.neg φ) ↔ Val (!b) φ := by
  cases b <;> exact val_fix _ _

/-- **The excluded middle is earned exactly in the clean cells.** -/
theorem em_iff (φ : Fm) : Val true φ.em ↔ (Val true φ ∨ Val false φ) := by
  constructor
  · intro h
    cases h with
    | negT h =>
      cases h with
      | andFl h => cases h with | negF h => exact Or.inl h
      | andFr h => cases h with | negF h => cases h with | negT h => exact Or.inr h
  · intro h
    apply Val.negT
    cases h with
    | inl h => exact .andFl (.negF h)
    | inr h => exact .andFr (.negF (.negT h))

/-- **The excluded middle is refuted in no cell** — at a dirty cell it is not earned, but it
is never false: the dirty parameter withholds, it does not contradict. -/
theorem em_never_false (φ : Fm) : ¬ Val false φ.em := by
  intro h
  cases h with
  | negF h =>
    cases h with
    | andT h1 h2 =>
      cases h1 with
      | negT h1 => cases h2 with | negT h2 => cases h2 with | negF h2 => exact consistent h2 h1

/-- Russell: R∈R is grounded neither way. -/
theorem russell_aux : ∀ {b φ}, Val b φ → φ ≠ .mem R R ∧ φ ≠ .neg (.mem R R) := by
  intro b φ h
  induction h with
  | memT _ ih => exact ⟨(by intro e; cases e; exact ih.2 R_inst), (by intro e; cases e)⟩
  | memF _ ih => exact ⟨(by intro e; cases e; exact ih.2 R_inst), (by intro e; cases e)⟩
  | negT _ ih => exact ⟨(by intro e; cases e), (by intro e; cases e; exact ih.1 rfl)⟩
  | negF _ ih => exact ⟨(by intro e; cases e), (by intro e; cases e; exact ih.1 rfl)⟩
  | _ => exact ⟨(by intro e; cases e), (by intro e; cases e)⟩

theorem russell_quarantine (b : Bool) : ¬ Val b (.mem R R) :=
  fun h => (russell_aux h).1 rfl

/-- The truth-teller set: S∈S is grounded neither way in the least fixed point. -/
theorem S_aux : ∀ {b φ}, Val b φ → φ ≠ .mem S S := by
  intro b φ h
  induction h with
  | memT _ ih => intro e; cases e; exact ih S_inst
  | memF _ ih => intro e; cases e; exact ih S_inst
  | _ => intro e; cases e

theorem S_quarantine (b : Bool) : ¬ Val b (.mem S S) := fun h => S_aux h rfl

/-- Russell works as a set for everyone but himself: `V ∈ R` is earned FALSE (V ∈ V is clean). -/
theorem V_mem_V : Val true (.mem V V) := .memT .top
theorem V_not_mem_R : Val false (.mem V R) := .memF (.negF V_mem_V)

/-- "Everything is in V" — a universal over the infinite universe, earned by a rule. -/
theorem all_in_V : Val true (.all (.mem x0 V)) := .allT (fun _ => .memT .top)

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.val_fix
#print axioms VRCycle.SetsNaive.val_least
#print axioms VRCycle.SetsNaive.consistent
#print axioms VRCycle.SetsNaive.comprehension
#print axioms VRCycle.SetsNaive.em_iff
#print axioms VRCycle.SetsNaive.em_never_false
#print axioms VRCycle.SetsNaive.russell_quarantine
#print axioms VRCycle.SetsNaive.S_quarantine
#print axioms VRCycle.SetsNaive.V_not_mem_R
#print axioms VRCycle.SetsNaive.all_in_V
