-- VR/SetsNaive/Bridge.lean
-- VR-Sets, naive edition — Stage N4: the bridge to the carrier, and what it FORGETS.
--
-- The naive term universe, read through its EARNED memberships, is itself a pointed graph:
-- vertices are the closed terms, `a → t` iff `a ∈ t` is grounded TRUE.  So every term is an
-- operational set of SetsOp (`tGraph t : OpSet.{0}`), and an earned membership is an
-- operational membership (`mem_to_op`) — the language layer lands on the carrier with no
-- translation.
--
-- But the carrier is two-valued and the naive membership is three-valued, and this file
-- measures the price (risk 1 of the programme, now a theorem): `carrier_forgets_mark`.  The
-- empty set `E = {x : ¬⊤}` and the DIRTY set `D = {x : R∈R}` have no earned members either of
-- them, so their T-graphs are bisimilar — the same operational set — yet "x has no members"
-- is EARNED for E and QUARANTINED for D.  The T-graph cannot tell a clean empty set from a set
-- whose every membership is dirty.  Identifying the two memberships would therefore be a
-- dirty deal; the honest bridge carries the F-edges (or the mark) as well.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsOp
import VR.SetsNaive.Passport

namespace VRCycle.SetsNaive

open VRCycle.SetsOp

set_option genInjectivity false

/-- The T-graph of a term: the closed terms, with an edge `a → b` iff `a ∈ b` is earned. -/
def tGraph (t : Tm) : OpSet.{0} := ⟨Tm, fun a b => Val true (.mem a b), t⟩

/-- **An earned membership is an operational membership.** -/
theorem mem_to_op {a t : Tm} (h : Val true (.mem a t)) : (tGraph a).Mem (tGraph t) :=
  ⟨a, h, OpSet.Equiv.refl (tGraph a)⟩

/-- The clean empty set `{x : ¬⊤}`. -/
def E : Tm := .abs (.neg .top)
/-- A dirty set `{x : R∈R}`: every membership in it rests on Russell's cell. -/
def D : Tm := .abs (.mem R R)
/-- The set of the empty sets, `{y : ∀z ¬ z∈y}` (inside the ∀: z = index 0, y = index 1). -/
def Empt : Tm := .abs (.all (.neg (.mem x0 (.var 1))))

theorem E_no_member (a : Tm) : ¬ Val true (.mem a E) := by
  intro h
  cases h with | memT h => cases h with | negT h => cases h

theorem D_no_member (a : Tm) : ¬ Val true (.mem a D) := by
  intro h
  cases h with | memT h => exact russell_quarantine true h

/-- E and D are the SAME operational set: both T-graphs have no members at their point. -/
theorem E_equiv_D : (tGraph E).Equiv (tGraph D) := by
  refine ⟨fun x y => x = E ∧ y = D, ⟨rfl, rfl⟩, ?_⟩
  intro x y hxy
  obtain ⟨hx, hy⟩ := hxy
  subst hx; subst hy
  exact ⟨fun a' h => absurd h (E_no_member a'), fun b' h => absurd h (D_no_member b')⟩

/-- E is EARNED to be empty. -/
theorem E_in_Empt : Val true (.mem E Empt) :=
  .memT (.allT (fun _ _ => .negT (.memF (.negF .top))))

/-- D's emptiness is QUARANTINED: neither earned nor refuted. -/
theorem D_Empt_quarantine (b : Bool) : ¬ Val b (.mem D Empt) := by
  intro h
  cases b with
  | true =>
    cases h with
    | memT h => cases h with
      | allT h => have := h E rfl; cases this with
        | negT h => cases h with | memF h => exact russell_quarantine false h
  | false =>
    cases h with
    | memF h => cases h with
      | allF c _ h => cases h with
        | negF h => cases h with | memT h => exact russell_quarantine true h

/-- **The two-valued carrier forgets the mark.**  E and D are operationally identical, yet
"has no members" is earned for one and quarantined for the other: the T-graph bridge is
sound for earned membership (`mem_to_op`) but it is NOT the naive membership. -/
theorem carrier_forgets_mark :
    (tGraph E).Equiv (tGraph D) ∧ Val true (.mem E Empt) ∧ (∀ b, ¬ Val b (.mem D Empt)) :=
  ⟨E_equiv_D, E_in_Empt, D_Empt_quarantine⟩

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.mem_to_op
#print axioms VRCycle.SetsNaive.E_equiv_D
#print axioms VRCycle.SetsNaive.E_in_Empt
#print axioms VRCycle.SetsNaive.D_Empt_quarantine
#print axioms VRCycle.SetsNaive.carrier_forgets_mark
