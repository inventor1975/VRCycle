-- VR/SetsNaive/Judge.lean
-- VR-Sets, naive edition — Stage N8: the VERDICT register over the naive sets (the curator's
-- correction, 2026-11-05 01:30: "no verdict" is the lazy register; a verdict on a CLAIM is the
-- judge's, by ZTL's dispositions).
--
-- ZTL's judge (ZTL/ztljudge.py, 2026-10-29 rule): EARNED = T in the lazy register; EARNED IF
-- STABLE = T in every completion of the dirty atoms (each atom one value at all its
-- occurrences); OPEN = the completions disagree.  Here a COMPLETION is a DECIDED two-valued
-- membership oracle that agrees with every grounded cell; a claim is read under it by `Rd` (the
-- same strong-Kleene clauses as `Val`, but every atom answered by the oracle).
--
-- The price of the stable reading, measured: a completion must decide EVERY cell of an infinite
-- universe, and the grounded cells are not decidable — so no completion is exhibited without the
-- excluded middle over the universe.  The lazy register costs nothing; the stable reading sits at
-- the classical floor.  Here that floor is an explicit HYPOTHESIS `lem` of the theorems that need
-- a completion to exist — never an axiom (the module stays on `[]`).
--
-- Machine-checked here:
--   * `Completion.lfp lem` — given excluded middle, the lfp's own T-cells form a completion: the
--     stable reading is NOT vacuous (classically);
--   * `earned_stable` / `refuted_stable` — EARNED ⇒ T in every completion, REFUTED ⇒ F in every
--     completion (the two registers agree where both speak);
--   * `subset_refl` — "every set is a subset of itself" is NOT earned (the dirty probe D) but
--     EARNED IF STABLE;
--   * "A is empty", two spellings of ONE claim:
--       – by its DEFINITION `∀z ¬(z∈Empt ∧ ¬z∈Empt)` — not earned, EARNED IF STABLE;
--       – by the ATOM `∀z ¬(z∈A)` — OPEN (`A_empty_atom_open`, under `lem`): a completion may set
--         the dirty cell D∈A either way, since completions are free at dirty cells.
--     So the disposition depends on WHERE THE JUDGE CUTS the unfolding of comprehension: the
--     lazy register is invariant under comprehension (`Ground.comprehension`), the stable
--     reading is not.
--   * `no_comprehension_completion` — the cut cannot be removed: no completion respects
--     comprehension at every cell (Russell), so "completions that respect all definitions"
--     would make every claim vacuously stable — a dirty deal, refused.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Leak

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- Excluded middle, as a HYPOTHESIS (the classical floor), never assumed as an axiom here. -/
def LEM : Prop := ∀ P : Prop, P ∨ ¬ P

/-- Reading of a formula under a two-valued membership oracle `o` (strong-Kleene clauses; every
atom answered by `o`). -/
inductive Rd (o : Tm → Tm → Prop) : Bool → Fm → Prop where
  | top : Rd o true .top
  | memT {a b} : o a b → Rd o true (.mem a b)
  | memF {a b} : ¬ o a b → Rd o false (.mem a b)
  | negT {φ} : Rd o false φ → Rd o true (.neg φ)
  | negF {φ} : Rd o true φ → Rd o false (.neg φ)
  | andT {φ ψ} : Rd o true φ → Rd o true ψ → Rd o true (.and φ ψ)
  | andFl {φ ψ} : Rd o false φ → Rd o false (.and φ ψ)
  | andFr {φ ψ} : Rd o false ψ → Rd o false (.and φ ψ)
  | allT {φ} : (∀ c, Cl c → Rd o true (φ.inst c)) → Rd o true (.all φ)
  | allF {φ} (c : Tm) : Cl c → Rd o false (φ.inst c) → Rd o false (.all φ)

/-- A completion: a DECIDED two-valued membership oracle agreeing with every grounded cell. -/
structure Completion where
  o : Tm → Tm → Prop
  dec : ∀ a b, o a b ∨ ¬ o a b
  agreeT : ∀ {a b}, Val true (.mem a b) → o a b
  agreeF : ∀ {a b}, Val false (.mem a b) → ¬ o a b

/-- T in every completion (the "if stable" reading). -/
def StableT (φ : Fm) : Prop := ∀ M : Completion, Rd M.o true φ
/-- F in every completion. -/
def StableF (φ : Fm) : Prop := ∀ M : Completion, Rd M.o false φ

/-- Given excluded middle, the lfp's own T-cells form a completion. -/
def Completion.lfp (lem : LEM) : Completion :=
  ⟨fun a b => Val true (.mem a b), fun _ _ => lem _, fun h => h, fun h h' => consistent h h'⟩

/-- The two registers agree where both speak. -/
theorem val_rd (M : Completion) : ∀ {b φ}, Val b φ → Rd M.o b φ := by
  intro b φ h
  induction h with
  | top => exact .top
  | @memT a φ h _ => exact .memT (M.agreeT (.memT h))
  | @memF a φ h _ => exact .memF (M.agreeF (.memF h))
  | negT _ ih => exact .negT ih
  | negF _ ih => exact .negF ih
  | andT _ _ ih1 ih2 => exact .andT ih1 ih2
  | andFl _ ih => exact .andFl ih
  | andFr _ ih => exact .andFr ih
  | allT _ ih => exact .allT ih
  | allF c hc _ ih => exact .allF c hc ih

/-- EARNED ⇒ EARNED IF STABLE. -/
theorem earned_stable {φ : Fm} (h : Val true φ) : StableT φ := fun M => val_rd M h
/-- REFUTED ⇒ REFUTED IF STABLE. -/
theorem refuted_stable {φ : Fm} (h : Val false φ) : StableF φ := fun M => val_rd M h

/-- Material implication, defined: `p → q := ¬(p ∧ ¬q)`. -/
def Fm.imp (φ ψ : Fm) : Fm := .neg (.and φ (.neg ψ))

/-- Under a decided oracle, `p → p` (i.e. `¬(p ∧ ¬p)`) reads TRUE at every atom. -/
theorem rd_self_imp (M : Completion) (a b : Tm) : Rd M.o true (Fm.imp (.mem a b) (.mem a b)) := by
  apply Rd.negT
  cases M.dec a b with
  | inl h => exact .andFr (.negF (.memT h))
  | inr h => exact .andFl (.memF h)

/-! ## "Every set is a subset of itself" -/

/-- `∀x ∀z (z∈x → z∈x)` (inside: z = index 0, x = index 1). -/
def subsetRefl : Fm := .all (.all (Fm.imp (.mem x0 (.var 1)) (.mem x0 (.var 1))))

/-- Not earned: the instance at the dirty probe D withholds the T. -/
theorem subsetRefl_not_earned : ¬ Val true subsetRefl := by
  intro h
  cases h with
  | allT h =>
    have h1 := h D D_closed
    cases h1 with
    | allT h2 =>
      have h3 := h2 E rfl
      cases h3 with
      | negT h4 =>
        cases h4 with
        | andFl h5 => exact D_no_value E false h5
        | andFr h5 => cases h5 with | negF h6 => exact D_no_value E true h6

theorem subsetRefl_inst (x z : Tm) (hx : Cl x) :
    ((Fm.imp (.mem x0 x) (.mem x0 x))).inst z = Fm.imp (.mem z x) (.mem z x) := by
  show Fm.neg (.and (.mem (Tm.subst 0 z x0) (Tm.subst 0 z x))
    (.neg (.mem (Tm.subst 0 z x0) (Tm.subst 0 z x)))) = _
  rw [Cl.subst hx 0 z]
  rfl

theorem subsetRefl_outer (x : Tm) (hx : Cl x) :
    (Fm.all (Fm.imp (.mem x0 (.var 1)) (.mem x0 (.var 1)))).inst x
      = .all (Fm.imp (.mem x0 x) (.mem x0 x)) := rfl

/-- …but EARNED IF STABLE: under every completion each instance is `p → p`. -/
theorem subsetRefl_stable : StableT subsetRefl := by
  intro M
  apply Rd.allT
  intro x hx
  rw [subsetRefl_outer x hx]
  apply Rd.allT
  intro z _
  rw [subsetRefl_inst x z hx]
  exact rd_self_imp M z x

/-! ## "A is empty", two spellings -/

/-- By the definition of A: `∀z ¬(z∈Empt ∧ ¬z∈Empt)`. -/
def A_empty_def : Fm := .all (Fm.imp (.mem x0 Empt) (.mem x0 Empt))
/-- By the atom: `∀z ¬(z∈A)`. -/
def A_empty_atom : Fm := .all (.neg (.mem x0 A))

theorem A_empty_atom_inst (c : Tm) : (Fm.neg (.mem x0 A)).inst c = .neg (.mem c A) := by
  show Fm.neg (.mem (Tm.subst 0 c x0) (Tm.subst 0 c A)) = _
  rw [Cl.subst A_closed 0 c]
  rfl

/-- By definition: not earned (D∈Empt is dirty)… -/
theorem A_empty_def_not_earned : ¬ Val true A_empty_def := by
  intro h
  cases h with
  | allT h =>
    have h1 := h D D_closed
    rw [subsetRefl_inst Empt D Empt_closed] at h1
    cases h1 with
    | negT h2 =>
      cases h2 with
      | andFl h3 => exact Empt_dirty_at_D false h3
      | andFr h3 => cases h3 with | negF h4 => exact Empt_dirty_at_D true h4

/-- …but EARNED IF STABLE: every instance is `¬(p ∧ ¬p)`. -/
theorem A_empty_def_stable : StableT A_empty_def := by
  intro M
  apply Rd.allT
  intro c _
  rw [subsetRefl_inst Empt c Empt_closed]
  exact rd_self_imp M c Empt

/-- Given excluded middle, a completion that reads the dirty cell D∈A as TRUE. -/
def Completion.DinA (lem : LEM) : Completion :=
  ⟨fun a b => Val true (.mem a b) ∨ (a = D ∧ b = A),
   fun _ _ => lem _,
   fun h => Or.inl h,
   fun {a b} h h' => by
     cases h' with
     | inl h' => exact consistent h h'
     | inr e => obtain ⟨e1, e2⟩ := e; subst e1; subst e2; exact A_dirty_at_D false h⟩

/-- **By the atom, the same claim is OPEN**: one completion reads it true, another false. -/
theorem A_empty_atom_open (lem : LEM) :
    Rd (Completion.lfp lem).o true A_empty_atom ∧ Rd (Completion.DinA lem).o false A_empty_atom := by
  constructor
  · apply Rd.allT
    intro c _
    rw [A_empty_atom_inst]
    exact .negT (.memF (A_no_member c))
  · apply Rd.allF D D_closed
    rw [A_empty_atom_inst]
    exact .negF (.memT (Or.inr ⟨rfl, rfl⟩))

/-- **The cut cannot be removed**: no oracle respects comprehension at every cell (Russell), so
"completions respecting all definitions" do not exist — reading claims over them would make
every claim vacuously stable. -/
theorem no_comprehension_completion (o : Tm → Tm → Prop)
    (h : ∀ a φ, o a (.abs φ) ↔ Rd o true (φ.inst a)) : False := by
  have hR : o R R ↔ Rd o true (.neg (.mem R R)) := h R (.neg (.mem x0 x0))
  have to : Rd o true (.neg (.mem R R)) → ¬ o R R := by
    intro hr; cases hr with | negT hr => cases hr with | memF hr => exact hr
  have hn : ¬ o R R := fun hr => to (hR.mp hr) hr
  exact hn (hR.mpr (.negT (.memF hn)))

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.Completion.lfp
#print axioms VRCycle.SetsNaive.earned_stable
#print axioms VRCycle.SetsNaive.refuted_stable
#print axioms VRCycle.SetsNaive.subsetRefl_not_earned
#print axioms VRCycle.SetsNaive.subsetRefl_stable
#print axioms VRCycle.SetsNaive.A_empty_def_not_earned
#print axioms VRCycle.SetsNaive.A_empty_def_stable
#print axioms VRCycle.SetsNaive.A_empty_atom_open
#print axioms VRCycle.SetsNaive.no_comprehension_completion
