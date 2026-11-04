-- VR/SetsNaive/Passport.lean
-- VR-Sets, naive edition — Stage N3: the PASSPORT of a dirty cell.
--
-- A quarantine cell is Z in the least fixed point — but two kinds of Z differ, and the passport
-- names which (the ZTL §10 passport, here for naive sets):
--   * PARADOX — the cell is decided in NO consistent fixed point (Russell, R∈R): no stipulation
--     can repair it, every completion contradicts itself;
--   * UNDERDETERMINED — the cell is T in some consistent fixed point and F in another (the
--     truth-teller set, S∈S): what is owed is a STIPULATION, and either one is consistent.
-- And a clean cell is ABSOLUTE: its value is the same in every consistent fixed point
-- (`grounded_absolute`) — the grounded register is not a choice among models.
--
-- The two witness fixed points for S∈S are built as seeded least fixed points (`ValS s`): the
-- jump's least fixed point above the single seed "S∈S has value s".  Both are consistent; the
-- seed is self-justifying exactly because S's defining body IS the cell itself.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Ground

namespace VRCycle.SetsNaive

-- No auto-generated `injEq` lemmas (they carry `propext`; the guard rejects them). Proofs use
-- `cases` on constructor equalities (noConfusion), which is axiom-free.
set_option genInjectivity false

/-- A consistent fixed point of the jump: a three-valued model of naive comprehension. -/
structure FixPt where
  P : Bool → Fm → Prop
  fix : ∀ b φ, P b φ ↔ Jump P b φ
  cons : ∀ b φ, P b φ → P (!b) φ → False

/-- The grounded register as a fixed point. -/
def FixPt.least : FixPt := ⟨Val, val_fix, fun _ _ h h' => consistent h h'⟩

/-- **Clean cells are absolute**: a grounded value holds in EVERY consistent fixed point, and
its opposite in none. -/
theorem grounded_absolute {b : Bool} {φ : Fm} (h : Val b φ) (M : FixPt) :
    M.P b φ ∧ ¬ M.P (!b) φ := by
  have hb : M.P b φ := val_least M.P (fun b φ hj => (M.fix b φ).mpr hj) h
  exact ⟨hb, fun h' => M.cons b φ hb h'⟩

/-- A cell is a PARADOX if no consistent fixed point decides it. -/
def Paradox (φ : Fm) : Prop := ∀ (M : FixPt) (b : Bool), ¬ M.P b φ

/-- A cell is UNDERDETERMINED if consistent fixed points decide it both ways. -/
def Underdetermined (φ : Fm) : Prop := (∃ M : FixPt, M.P true φ) ∧ (∃ M : FixPt, M.P false φ)

/-- **Russell is a paradox**: R∈R is decided in no consistent fixed point. -/
theorem russell_paradox : Paradox (.mem R R) := by
  intro M b h
  have h1 : M.P b (.neg (.mem R R)) := by
    have := (M.fix b (.mem R R)).mp h
    cases b <;> exact this
  have h2 : M.P (!b) (.mem R R) := by
    have := (M.fix b (.neg (.mem R R))).mp h1
    cases b <;> exact this
  exact M.cons b _ h h2

/-! ## The truth-teller set: two consistent stipulations -/

/-- The least fixed point of the jump above the seed "S∈S has value `s`". -/
inductive ValS (s : Bool) : Bool → Fm → Prop where
  | seed : ValS s s (.mem S S)
  | top : ValS s true .top
  | memT {a φ} : ValS s true (φ.inst a) → ValS s true (.mem a (.abs φ))
  | memF {a φ} : ValS s false (φ.inst a) → ValS s false (.mem a (.abs φ))
  | negT {φ} : ValS s false φ → ValS s true (.neg φ)
  | negF {φ} : ValS s true φ → ValS s false (.neg φ)
  | andT {φ ψ} : ValS s true φ → ValS s true ψ → ValS s true (.and φ ψ)
  | andFl {φ ψ} : ValS s false φ → ValS s false (.and φ ψ)
  | andFr {φ ψ} : ValS s false ψ → ValS s false (.and φ ψ)
  | allT {φ} : (∀ c, Cl c → ValS s true (φ.inst c)) → ValS s true (.all φ)
  | allF {φ} (c : Tm) : Cl c → ValS s false (φ.inst c) → ValS s false (.all φ)

/-- In the seeded fixed point, S∈S can only carry the seeded value. -/
theorem valS_SS {s : Bool} : ∀ {b φ}, ValS s b φ → φ = .mem S S → b = s := by
  intro b φ h
  induction h with
  | seed => intro _; rfl
  | memT _ ih => intro e; cases e; exact ih S_inst
  | memF _ ih => intro e; cases e; exact ih S_inst
  | _ => intro e; cases e

theorem valS_fix (s : Bool) : ∀ (b : Bool) (φ : Fm), ValS s b φ ↔ Jump (ValS s) b φ := by
  intro b φ
  constructor
  · intro h
    cases h with
    | seed => cases s <;> exact .seed
    | top => exact trivial
    | memT h => exact h
    | memF h => exact h
    | negT h => exact h
    | negF h => exact h
    | andT h1 h2 => exact ⟨h1, h2⟩
    | andFl h => exact Or.inl h
    | andFr h => exact Or.inr h
    | allT h => exact h
    | allF c hc h => exact ⟨c, hc, h⟩
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
        | exact (match h with | ⟨c, hc, h⟩ => .allF c hc h)

theorem valS_cons (s : Bool) : ∀ {b φ}, ValS s b φ → ValS s (!b) φ → False := by
  intro b φ h
  induction h with
  | seed => intro h'; have := valS_SS h' rfl; cases s <;> cases this
  | top => intro h'; cases h'
  | @memT a φ hb ih =>
      intro h'
      have hj := (valS_fix s false (.mem a (.abs φ))).mp h'
      exact ih hj
  | @memF a φ hb ih =>
      intro h'
      have hj := (valS_fix s true (.mem a (.abs φ))).mp h'
      exact ih hj
  | negT _ ih => intro h'; cases h' with | negF h'' => exact ih h''
  | negF _ ih => intro h'; cases h' with | negT h'' => exact ih h''
  | andT _ _ ih1 ih2 => intro h'; cases h' with
      | andFl h'' => exact ih1 h''
      | andFr h'' => exact ih2 h''
  | andFl _ ih => intro h'; cases h' with | andT h'' _ => exact ih h''
  | andFr _ ih => intro h'; cases h' with | andT _ h'' => exact ih h''
  | allT _ ih => intro h'; cases h' with | allF c hc h'' => exact ih c hc h''
  | allF c hc _ ih => intro h'; cases h' with | allT h'' => exact ih (h'' c hc)

/-- The seeded fixed point as a consistent model. -/
def FixPt.seeded (s : Bool) : FixPt :=
  ⟨ValS s, valS_fix s, fun _ _ h h' => valS_cons s h h'⟩

/-- **The truth-teller set is underdetermined**: S∈S is T in one consistent model, F in
another — a stipulation is owed, and both stipulations are consistent. -/
theorem S_underdetermined : Underdetermined (.mem S S) :=
  ⟨⟨FixPt.seeded true, .seed⟩, ⟨FixPt.seeded false, .seed⟩⟩

/-- **The passport separates the two dirty cells**: both are Z in the grounded register, but
Russell is a paradox and the truth-teller an underdetermined cell. -/
theorem passport_separates :
    (∀ b, ¬ Val b (.mem R R)) ∧ (∀ b, ¬ Val b (.mem S S)) ∧
    Paradox (.mem R R) ∧ Underdetermined (.mem S S) ∧ ¬ Paradox (.mem S S) :=
  ⟨russell_quarantine, S_quarantine, russell_paradox, S_underdetermined,
   fun h => h (FixPt.seeded true) true .seed⟩

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.grounded_absolute
#print axioms VRCycle.SetsNaive.russell_paradox
#print axioms VRCycle.SetsNaive.S_underdetermined
#print axioms VRCycle.SetsNaive.passport_separates
