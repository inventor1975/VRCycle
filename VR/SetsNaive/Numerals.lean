-- VR/SetsNaive/Numerals.lean
-- VR-Sets, naive edition — Stage N10: the STRENGTH of the clean part, measured on the von Neumann
-- numerals.  Result: NEGATIVE, and sharp.
--
-- Machine-checked here:
--   * `eqv_self_never_refuted` — `X ≐ X` is refuted for no set;
--   * `eqv_earned_decides_D` / `earned_identity_trivial` — an EARNED identity forces both sides
--     to decide the dirty probe D, hence (N6) to be TRIVIAL (∅ or V): the unbounded ∀ inside
--     `≐` always meets D;
--   * `nontrivial_self_quarantine` — every nontrivial set fails even `X ≐ X`: quarantined;
--   * the numerals `zero = E`, `one = {x : x ≐ 0}`, `two = {x : x ≐ 0 ∨ x ≐ 1}`: 0 ∈ 1, 0 ∈ 2 are
--     EARNED, V ∉ 1 is EARNED — but `1 ∈ 2` is QUARANTINED (`vn_two_breaks`): 1 is nontrivial, so
--     `1 ≐ 1` is never earned.  The lazy register of naive comprehension does not reach 2.
--   * `one_in_two_stable` — under every completion, by its DEFINITION (`1 ≐ 0 ∨ 1 ≐ 1`), it is
--     EARNED IF STABLE: the classical register reaches it, the operational one does not.
-- Contrast: SetsOp builds the naturals and ω natively and their identity atoms are TOTAL
-- (VR/ZTL/Atoms `vnVerdict_ne_Z`).  So the arithmetic strength lives in the CARRIER; the naive
-- layer is the language and the paradox passport.  This is the measured reason to keep both.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Identity

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- `X ≐ X` is refuted for no set: every instance is `p ↔ p`, never earned false. -/
theorem eqv_self_never_refuted {X : Tm} (hX : Cl X) : ¬ Val false (Eqv X X) := by
  intro h
  cases h with
  | allF c _ h =>
    rw [Eqv_inst hX hX c] at h
    cases h with
    | andFl h => cases h with | negF h => cases h with | andT h1 h2 => cases h2 with | negT h2 => exact consistent h1 h2
    | andFr h => cases h with | negF h => cases h with | andT h1 h2 => cases h2 with | negT h2 => exact consistent h1 h2

/-- An earned biconditional decides its left side, given that its sides are decided together. -/
theorem iff_earned_decides {p q : Fm} (h : Val true (Fm.iff p q)) : Val true p ∨ Val false p := by
  cases h with
  | andT h1 h2 =>
    cases h1 with
    | negT h1 =>
      cases h1 with
      | andFl h1 => exact Or.inr h1
      | andFr h1 =>
        cases h1 with
        | negF hq =>
          cases h2 with
          | negT h2 =>
            cases h2 with
            | andFl h2 => exact absurd hq (fun hq => consistent h2 hq)
            | andFr h2 => cases h2 with | negF hp => exact Or.inl hp

/-- **An earned identity decides the dirty probe** on its left side. -/
theorem eqv_earned_decides_D {X Y : Tm} (hX : Cl X) (hY : Cl Y) (h : Val true (Eqv X Y)) :
    Val true (.mem D X) ∨ Val false (.mem D X) := by
  cases h with
  | allT h =>
    have hi := h D D_closed
    rw [Eqv_inst hX hY D] at hi
    exact iff_earned_decides hi

/-- **Earned identity is trivial**: its left side decides every object the same way (∅ or V). -/
theorem earned_identity_trivial {X Y : Tm} (hX : Cl X) (hY : Cl Y) (h : Val true (Eqv X Y)) :
    (∀ t, Cl t → Val true (.mem t X)) ∨ (∀ t, Cl t → Val false (.mem t X)) := by
  cases eqv_earned_decides_D hX hY h with
  | inl h => exact Or.inl (total_trivial hX true h)
  | inr h => exact Or.inr (total_trivial hX false h)

/-- **A nontrivial set fails even self-identity**: `X ≐ X` is quarantined. -/
theorem nontrivial_self_quarantine {X s t : Tm} (hX : Cl X) (hs : Cl s) (ht : Cl t)
    (hin : Val true (.mem s X)) (hout : Val false (.mem t X)) (v : Bool) :
    ¬ Val v (Eqv X X) := by
  cases v with
  | false => exact eqv_self_never_refuted hX
  | true =>
    intro h
    cases eqv_earned_decides_D hX hX h with
    | inl h => exact nontrivial_dirty_at_D hX hs ht hin hout true h
    | inr h => exact nontrivial_dirty_at_D hX hs ht hin hout false h

/-! ## The von Neumann numerals -/

/-- `x ≐ a` as a comprehension body (x = index 0; inside the ∀, z = 0 and x = 1). -/
def eqBody (a : Tm) : Fm := .all (Fm.iff (.mem x0 (.var 1)) (.mem x0 a))

def zero : Tm := E
def one : Tm := .abs (eqBody zero)
def two : Tm := .abs (Fm.or (eqBody zero) (eqBody one))

theorem zero_closed : Cl zero := rfl
theorem V_closed : Cl V := rfl
theorem one_closed : Cl one := rfl
theorem two_closed : Cl two := rfl

theorem eqBody_inst {a : Tm} (ha : Cl a) (c : Tm) : (eqBody a).inst c = Eqv c a := by
  show Fm.all (Fm.subst 1 c (Fm.iff (.mem x0 (.var 1)) (.mem x0 a))) = _
  show Fm.all (Fm.and (.neg (.and (.mem x0 c) (.neg (.mem x0 (Tm.subst 1 c a)))))
    (.neg (.and (.mem x0 (Tm.subst 1 c a)) (.neg (.mem x0 c))))) = _
  rw [Cl.subst ha 1 c]
  rfl

theorem two_inst (c : Tm) : (Fm.or (eqBody zero) (eqBody one)).inst c = Fm.or (Eqv c zero) (Eqv c one) := by
  show Fm.neg (Fm.and (.neg ((eqBody zero).inst c)) (.neg ((eqBody one).inst c))) = _
  rw [eqBody_inst zero_closed c, eqBody_inst one_closed c]
  rfl

/-- `0 ≐ 0` is earned (0 = E is trivial). -/
theorem zero_eq_zero : Val true (Eqv zero zero) := by
  apply Val.allT
  intro c _
  rw [Eqv_inst zero_closed zero_closed c]
  have hE : Val false (.mem c zero) := .memF (.negF .top)
  exact .andT (.negT (.andFl hE)) (.negT (.andFl hE))

/-- `0 ∈ 1` — EARNED. -/
theorem zero_in_one : Val true (.mem zero one) := by
  apply Val.memT; rw [eqBody_inst zero_closed zero]; exact zero_eq_zero

/-- `V ≐ 0` is refuted (E ∈ V, E ∉ E). -/
theorem V_eq_zero_refuted : Val false (Eqv V zero) := by
  apply Val.allF E E_closed
  rw [Eqv_inst V_closed zero_closed E]
  exact .andFl (.negF (.andT (.memT .top) (.negT (.memF (.negF .top)))))

/-- `V ∉ 1` — EARNED (refuted membership). -/
theorem V_not_in_one : Val false (.mem V one) := by
  apply Val.memF; rw [eqBody_inst zero_closed V]; exact V_eq_zero_refuted

/-- `1 ≐ 0` is refuted (0 ∈ 1, 0 ∉ 0). -/
theorem one_eq_zero_refuted : Val false (Eqv one zero) := by
  apply Val.allF zero zero_closed
  rw [Eqv_inst one_closed zero_closed zero]
  exact .andFl (.negF (.andT zero_in_one (.negT (.memF (.negF .top)))))

/-- `1 ≐ 1` is quarantined: 1 is nontrivial. -/
theorem one_eq_one_quarantine (v : Bool) : ¬ Val v (Eqv one one) :=
  nontrivial_self_quarantine one_closed zero_closed V_closed zero_in_one V_not_in_one v

/-- `0 ∈ 2` — EARNED. -/
theorem zero_in_two : Val true (.mem zero two) := by
  apply Val.memT; rw [two_inst]; exact .negT (.andFl (.negF zero_eq_zero))

/-- **The lazy register does not reach 2**: `0 ∈ 2` is earned, `1 ∈ 2` is quarantined. -/
theorem vn_two_breaks : Val true (.mem zero two) ∧ ∀ v, ¬ Val v (.mem one two) := by
  refine ⟨zero_in_two, ?_⟩
  intro v h
  cases v with
  | true =>
    cases h with
    | memT h =>
      rw [two_inst] at h
      cases h with
      | negT h =>
        cases h with
        | andFl h => cases h with | negF h => exact consistent one_eq_zero_refuted h
        | andFr h => cases h with | negF h => exact one_eq_one_quarantine true h
  | false =>
    cases h with
    | memF h =>
      rw [two_inst] at h
      cases h with
      | negF h => cases h with | andT _ h2 => cases h2 with | negT h2 => exact one_eq_one_quarantine false h2

/-- …but by its definition `1 ≐ 0 ∨ 1 ≐ 1`, it is EARNED IF STABLE: the classical register
reaches 2, the operational one does not. -/
theorem one_in_two_stable : StableT (Fm.or (Eqv one zero) (Eqv one one)) := by
  intro M
  apply Rd.negT
  apply Rd.andFr
  apply Rd.negF
  apply Rd.allT
  intro c _
  rw [Eqv_inst one_closed one_closed c]
  exact .andT (rd_self_imp M c one) (rd_self_imp M c one)

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.eqv_self_never_refuted
#print axioms VRCycle.SetsNaive.earned_identity_trivial
#print axioms VRCycle.SetsNaive.nontrivial_self_quarantine
#print axioms VRCycle.SetsNaive.zero_in_one
#print axioms VRCycle.SetsNaive.V_not_in_one
#print axioms VRCycle.SetsNaive.one_eq_one_quarantine
#print axioms VRCycle.SetsNaive.vn_two_breaks
#print axioms VRCycle.SetsNaive.one_in_two_stable
