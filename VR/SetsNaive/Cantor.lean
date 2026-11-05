-- VR/SetsNaive/Cantor.lean
-- VR-Sets, naive edition — Stage N17: Cantor's diagonal on ZTL's ground (2026-11-05, the curator's list of
-- mathematical paradoxes, "the most important first").
--
-- WORDS FIRST. A map `f` from sets to sets is written as a term `T` with one free variable (index 0): `f(d)` is
-- `T` with `d` put for the variable.  Cantor's diagonal is `D = {y : y ∉ f(y)}`.  Cantor's theorem says `D` is
-- no value of `f`: for every `d`, `D ≠ f(d)`, with `d` itself as the witness — `d ∈ D` and `d ∈ f(d)` disagree.
-- Cantor's PARADOX is the case of the universal set with `f` the identity: then `D` is Russell's set and the
-- reductio meets Russell's cell.
--
-- MEASURED HERE (Lean, the grounded register, all on `[]`):
--   1. `cantor_witness`: if the diagonal cell `d ∈ f(d)` is decided (earned or refuted), then `D ≐ f(d)` is
--      REFUTED, with `d` as the witness — the diagonal STEP holds, as a verdict, wherever the map is clean at `d`
--      (a step, not Cantor's theorem on cardinality: there are no functions-as-objects and no counting here);
--   2. `cantor_witness_silent`: if the diagonal cell is undecided, the witness `d` decides nothing — the instance
--      of the identity at `d` is neither earned nor refuted.  So the DIAGONAL WITNESS works exactly at the clean
--      cells of the map; at a dirty cell that witness says nothing — which is local: another witness may still
--      refute the identity (3b);
--   3. `cantor_paradox`: for the identity map, `D` is Russell's set `R`, the would-be refutation `R ≐ f(R)` is
--      `R ≐ R`, and it is never refuted — nor earned, since its instance at `R` is Russell's undecided cell.
--      Cantor's paradox is not a contradiction here: it is Russell's PARADOX cell (`russell_paradox`), met by the
--      diagonal through the identity map.
--   3b. `cantor_other_witness`: f = R at d = R — dirty diagonal cell, refuted all the same by the witness V;
--   4. `cantor_const_V`: not vacuous — the constant map `f = V` refutes `D ≐ f(R)` at Russell's own set: the
--      argument may be dirty; only the diagonal CELL must be clean.
-- What this does NOT show: anything about cardinalities as such (there are no functions-as-objects and no
-- counting in this language); it is the diagonal step, cell by cell.

import VR.SetsNaive.Residue
import VR.SetsNaive.Passport

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- The diagonal of the map written by the term `T` (index 0 = the argument): `{y : y ∉ T(y)}`. -/
def diag (T : Tm) : Tm := .abs (.neg (.mem x0 T))

/-- The value of the map at `d`. -/
abbrev app (T d : Tm) : Tm := Tm.subst 0 d T

/-- `d ∈ D` has the opposite status of `d ∈ f(d)` (naive comprehension, cell by cell). -/
theorem diag_cell (T d : Tm) (b : Bool) : Val b (.mem d (diag T)) ↔ Val (!b) (.mem d (app T d)) := by
  -- no `rw` with an iff (it would cost `propext`): chain the two iffs directly
  exact (comprehension b d (.neg (.mem x0 T))).trans (val_neg b (.mem d (app T d)))

/-- `p ↔ q` is refuted when `p` and `q` are decided opposite. -/
theorem iff_false_of_opposite {p q : Fm} :
    (Val true p ∧ Val false q) ∨ (Val false p ∧ Val true q) → Val false (Fm.iff p q) := by
  intro h
  cases h with
  | inl h => exact .andFl (.negF (.andT h.1 (.negT h.2)))
  | inr h => exact .andFr (.negF (.andT h.2 (.negT h.1)))

/-- **1. Cantor's witness, where the map is clean.** If the diagonal cell `d ∈ f(d)` is decided, then
`D ≐ f(d)` is refuted, with `d` as the counterexample. -/
theorem cantor_witness (T d : Tm) (hD : Cl (diag T)) (hf : Cl (app T d)) (hd : Cl d)
    (hdec : Val true (.mem d (app T d)) ∨ Val false (.mem d (app T d))) :
    Val false (Eqv (diag T) (app T d)) := by
  apply Val.allF d hd
  rw [Eqv_inst hD hf d]
  apply iff_false_of_opposite
  cases hdec with
  | inl h => exact Or.inr ⟨(diag_cell T d false).2 h, h⟩
  | inr h => exact Or.inl ⟨(diag_cell T d true).2 h, h⟩

/-- **2. Cantor's witness is silent at a dirty cell.** If `d ∈ f(d)` is undecided, the instance of `D ≐ f(d)` at
`d` is neither earned nor refuted: the diagonal step proves nothing there, either way. -/
theorem cantor_witness_silent (T d : Tm) (hD : Cl (diag T)) (hf : Cl (app T d))
    (hz : ¬ Val true (.mem d (app T d)) ∧ ¬ Val false (.mem d (app T d))) :
    ¬ Val true ((Fm.iff (.mem x0 (diag T)) (.mem x0 (app T d))).inst d) ∧
    ¬ Val false ((Fm.iff (.mem x0 (diag T)) (.mem x0 (app T d))).inst d) := by
  rw [Eqv_inst hD hf d]
  have hD' : ¬ Val true (.mem d (diag T)) ∧ ¬ Val false (.mem d (diag T)) :=
    ⟨fun h => hz.2 ((diag_cell T d true).1 h), fun h => hz.1 ((diag_cell T d false).1 h)⟩
  constructor
  · intro h
    cases h with
    | andT h1 _ =>
      cases h1 with
      | negT h1 =>
        cases h1 with
        | andFl h1 => exact hD'.2 h1
        | andFr h1 => cases h1 with | negF h1 => exact hz.1 h1
  · intro h
    cases h with
    | andFl h =>
      cases h with
      | negF h => cases h with | andT h1 _ => exact hD'.1 h1
    | andFr h =>
      cases h with
      | negF h => cases h with | andT h1 _ => exact hz.1 h1

/-- The identity map: `f(d) = d`. -/
abbrev idMap : Tm := x0

theorem diag_id : diag idMap = R := rfl
theorem app_id (d : Tm) : app idMap d = d := rfl

theorem R_closed : Cl R := rfl

/-- **3. Cantor's paradox is Russell's cell.** For the identity map the diagonal is `R`, the would-be refutation
`R ≐ f(R)` is `R ≐ R`, and it is never refuted; it is not earned either, because its instance at `R` is
Russell's undecided cell. -/
theorem cantor_paradox :
    diag idMap = R ∧ app idMap R = R ∧
    ¬ Val false (Eqv (diag idMap) (app idMap R)) ∧ ¬ Val true (Eqv (diag idMap) (app idMap R)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show ¬ Val false (Eqv R R)
    intro h
    cases h with
    | allF c hc h =>
      rw [Eqv_inst R_closed R_closed c] at h
      exact iff_self_never_false _ h
  · show ¬ Val true (Eqv R R)
    intro h
    cases h with
    | allT h =>
      have hi := h R R_closed
      rw [Eqv_inst R_closed R_closed R] at hi
      -- an earned `R∈R ↔ R∈R` would decide `R ∈ R`
      cases hi with
      | andT h1 _ =>
        cases h1 with
        | negT h1 =>
          cases h1 with
          | andFl h1 => exact russell_quarantine false h1
          | andFr h1 => cases h1 with | negF h1 => exact russell_quarantine true h1

/-- **3b. A dirty diagonal cell, refuted all the same — by another witness.** (Suggested by an outside review,
2026-11-05.) The constant map `f(d) = R` at `d = R`: the diagonal cell `R ∈ f(R)` is Russell's cell, undecided,
so the diagonal witness is silent (2.); yet `D ≐ f(R)` is refuted, with `V` as the witness: `V ∉ R` is earned,
so `V ∈ D` is earned. The local silence of the diagonal witness is not a global failure of the identity. Together
with 1. and 3., all three cases occur: refuted by the diagonal witness; refuted by another witness while the
diagonal cell is dirty; neither refuted nor earned. Which one holds is, in general, `all_refuted_iff`: the
identity is refuted iff SOME witness has its two cells decided opposite. -/
theorem cantor_other_witness :
    (∀ b, ¬ Val b (.mem R (app R R))) ∧ Val false (Eqv (diag R) (app R R)) := by
  refine ⟨fun b => russell_quarantine b, ?_⟩
  apply Val.allF V rfl
  rw [Eqv_inst (a := diag R) (b := app R R) rfl rfl V]
  apply iff_false_of_opposite
  exact Or.inl ⟨(diag_cell R V true).2 V_not_mem_R, V_not_mem_R⟩

/-- **Not vacuous: a clean map refutes even at Russell's set.** The constant map `f(d) = V`: its diagonal is
`{y : y ∉ V}`, the cell `R ∈ V` is earned, so `D ≐ f(R)` is refuted with `R` itself as the witness — the
argument's set need not be clean; the diagonal CELL must be. -/
theorem cantor_const_V : Val false (Eqv (diag V) (app V R)) :=
  cantor_witness V R rfl rfl rfl (Or.inl (.memT .top))

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.diag_cell
#print axioms VRCycle.SetsNaive.iff_false_of_opposite
#print axioms VRCycle.SetsNaive.cantor_witness
#print axioms VRCycle.SetsNaive.cantor_witness_silent
#print axioms VRCycle.SetsNaive.cantor_paradox
#print axioms VRCycle.SetsNaive.cantor_const_V
#print axioms VRCycle.SetsNaive.cantor_other_witness
