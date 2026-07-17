-- VRCycle/Continuum/Cardinal.lean
-- Operational cardinals — the cardinal as a type of BECOMING (the curator's
-- definition, 2026-07-17).
--
-- ## The operational reading
--   A cardinal here is not a completed set but a type of becoming, and a
--   comparison of cardinals is an ACT: an embedding counts only when it is
--   PERFORMED — the witness is data (an explicit injection), never a bare
--   existence claim.
--   * The order is PARTIAL by design.  Classical trichotomy of cardinals is
--     equivalent to full AC (Hartogs) — a formal-register label, cited here,
--     not claimed: two becomings are comparable where a comparison has been
--     performed, and nowhere else for free.
--   * The ladder climbs by the Cantor–Lawvere diagonal at EVERY floor,
--     uniformly and choice-free (`cantor_ladder`): no floor surjects onto its
--     power floor — the doubling ("adding a colleague") never closes from
--     below.
--   * The first step is fully performed: an explicit injection ℕ ↪ Branch
--     (`natIntoBranch`) plus the proved absence of any surjection back
--     (`branches_not_enumerable`): ℕ is operationally strictly below 2^ℕ
--     (`nat_strictly_below_branch`).
--
-- ## Axiom profile: choice-free throughout (audited below).

import VRCycle.Continuum.Branch

namespace VRCycle.Continuum

-- ============================================================
-- §Witnessed comparison
-- ============================================================

/-- A performed comparison: an injection carried as DATA — the act, not the
existence claim. -/
def OpInj (A B : Type) : Type := {f : A → B // Function.Injective f}

/-- ℕ embeds into the branches by an explicit witness: `n ↦` the branch that
fires exactly at `n`.  The comparison is performed, not postulated. -/
def natIntoBranch : OpInj ℕ Branch :=
  ⟨fun n => (fun k => Nat.beq k n), by
    intro m n h
    have hm : Nat.beq m m = Nat.beq m n := congrFun h m
    rw [Nat.beq_refl] at hm
    exact (Nat.eq_of_beq_eq_true hm.symm)⟩

-- ============================================================
-- §The ladder
-- ============================================================

/-- **The Cantor–Lawvere diagonal, uniform and choice-free**: no type surjects
onto its power floor `A → Bool`.  Each doubling — each added colleague — opens
a floor the previous one cannot reach; the ladder of becomings never closes
from below. -/
theorem cantor_ladder (A : Type) :
    ¬ ∃ f : A → (A → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf (fun x => !(f x x))
  have h := congrFun ha a
  cases hx : f a a with
  | false => rw [hx] at h; exact Bool.noConfusion h
  | true  => rw [hx] at h; exact Bool.noConfusion h

/-- **ℕ is operationally strictly below its power floor**: the injection up is
performed (`natIntoBranch`) and no surjection comes back
(`branches_not_enumerable`).  The first step of the ladder, with both halves
earned. -/
theorem nat_strictly_below_branch :
    (∃ f : ℕ → Branch, Function.Injective f) ∧
    ¬ ∃ e : ℕ → Branch, Function.Surjective e :=
  ⟨⟨natIntoBranch.1, natIntoBranch.2⟩, branches_not_enumerable⟩

-- ============================================================
-- Axiom audit
-- ============================================================
#print axioms natIntoBranch
#print axioms cantor_ladder
#print axioms nat_strictly_below_branch

end VRCycle.Continuum
