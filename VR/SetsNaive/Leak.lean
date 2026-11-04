-- VR/SetsNaive/Leak.lean
-- VR-Sets, naive edition — Stage N7: the unbounded quantifier IMPORTS the dirt of the universe.
--
-- N6 showed total cleanliness is trivial, so strength must be read on clean probes.  This file
-- measures why that is not yet enough: a quantifier over the whole universe also ranges over the
-- dirty probe.  The witness `A = {x : x∈Empt ∧ ¬ x∈Empt}` has NO earned member and is earned
-- false at every probe where `x∈Empt` is decided (E, V, …) — yet "A is empty" is QUARANTINED
-- (`A_emptiness_quarantine`): the instance at `D` withholds the T, and no instance gives an F.
-- So a set can be clean on the clean probes and still have dirty properties, because the
-- property quantifies over the dirt.  This is the structural fork handed to the curator:
-- unbounded quantifiers (naive, leaky) vs bounded/relativised ones (clean, less naive).
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Strength

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- `A = {x : x∈Empt ∧ ¬ x∈Empt}`: contradictory where decided, dirty where not. -/
def A : Tm := .abs (.and (.mem x0 Empt) (.neg (.mem x0 Empt)))

theorem A_inst (c : Tm) :
    (Fm.and (.mem x0 Empt) (.neg (.mem x0 Empt))).inst c = .and (.mem c Empt) (.neg (.mem c Empt)) := by
  show Fm.and (.mem (Tm.subst 0 c x0) (Tm.subst 0 c Empt)) (.neg (.mem (Tm.subst 0 c x0) (Tm.subst 0 c Empt))) = _
  rw [Cl.subst Empt_closed 0 c]
  rfl

/-- A has no earned member. -/
theorem A_no_member (c : Tm) : ¬ Val true (.mem c A) := by
  intro h
  cases h with
  | memT h =>
    rw [A_inst] at h
    cases h with
    | andT h1 h2 => cases h2 with | negT h2 => exact consistent h1 h2

/-- Where `c∈Empt` is decided, `c∈A` is earned FALSE (clean at the clean probes). -/
theorem A_clean_where_decided {c : Tm} {b : Bool} (h : Val b (.mem c Empt)) :
    Val false (.mem c A) := by
  apply Val.memF
  rw [A_inst]
  cases b with
  | true => exact .andFr (.negF h)
  | false => exact .andFl h

theorem E_in_A_false : Val false (.mem E A) := A_clean_where_decided E_in_Empt
theorem V_in_A_false : Val false (.mem V A) := A_clean_where_decided V_not_in_Empt

/-- …but at the dirty probe, `D∈A` is quarantined. -/
theorem A_dirty_at_D (b : Bool) : ¬ Val b (.mem D A) := by
  intro h
  cases b with
  | true => exact A_no_member D h
  | false =>
    cases h with
    | memF h =>
      rw [A_inst] at h
      cases h with
      | andFl h => exact Empt_dirty_at_D false h
      | andFr h => cases h with | negF h => exact Empt_dirty_at_D true h

theorem A_closed : Cl A := rfl

/-- **The leak**: A has no member at all and is clean at every decided probe, yet "A is empty"
(`A ∈ Empt`) is quarantined — the unbounded quantifier reached the dirty probe. -/
theorem A_emptiness_quarantine (b : Bool) : ¬ Val b (.mem A Empt) := by
  intro h
  cases b with
  | true =>
    cases h with
    | memT h =>
      cases h with
      | allT h =>
        have hD := h D D_closed
        cases hD with
        | negT hD => exact A_dirty_at_D false hD
  | false =>
    cases h with
    | memF h =>
      cases h with
      | allF c _ h =>
        cases h with
        | negF h => exact A_no_member c h

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.A_no_member
#print axioms VRCycle.SetsNaive.A_clean_where_decided
#print axioms VRCycle.SetsNaive.A_dirty_at_D
#print axioms VRCycle.SetsNaive.A_emptiness_quarantine
