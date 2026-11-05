-- VR/SetsNaive/Residue.lean
-- VR-Sets, naive edition — Stage N13: the Z of a universal is the RESIDUE (the curator's point,
-- 2026-11-05 02:13: "having checked the quantifier on the true and false memberships, the Z check
-- is only what remains of the set").
--
-- Machine-checked here:
--   * `all_refuted_iff` — a universal is REFUTED iff some DECIDED instance is false (a counterexample);
--   * `all_earned_iff` — a universal is EARNED iff every instance is earned (no residue, no
--     counterexample);
--   * `all_quarantine_iff` — so a universal is Z exactly when the decided instances hold no
--     counterexample and not every instance is earned: the Z is the RESIDUE, not a third test;
--   * `RelT` — the residue verdict: "no decided counterexample", with the residue NAMED.  It is a
--     verdict read off the finished fixed point — never fed back into membership (feeding it back
--     is N12's revocation) — and it needs no excluded middle (unlike EARNED IF STABLE);
--   * "A is empty" by the atom (`A_empty_atom`, OPEN under completions, N8): RelT holds, the residue
--     is non-empty (it contains D) — the operational verdict is "true outside the residue {D, …}".
-- The residue is in general infinite: what can be reported is WHICH probes it holds (a predicate),
-- not a count.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Levels

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- An instance is decided. -/
def Decided (φ : Fm) : Prop := Val true φ ∨ Val false φ

/-- **A universal is refuted iff some decided instance is false.** -/
theorem all_refuted_iff (φ : Fm) :
    Val false (.all φ) ↔ ∃ c, Cl c ∧ Val false (φ.inst c) :=
  ⟨fun h => by cases h with | allF c hc h => exact ⟨c, hc, h⟩,
   fun ⟨c, hc, h⟩ => .allF c hc h⟩

/-- **A universal is earned iff every instance is earned.** -/
theorem all_earned_iff (φ : Fm) :
    Val true (.all φ) ↔ ∀ c, Cl c → Val true (φ.inst c) :=
  ⟨fun h => by cases h with | allT h => exact h, fun h => .allT h⟩

/-- **The Z of a universal is the residue**: quarantined exactly when no instance is a
counterexample and not every instance is earned. -/
theorem all_quarantine_iff (φ : Fm) :
    (¬ Val true (.all φ) ∧ ¬ Val false (.all φ)) ↔
    ((¬ ∀ c, Cl c → Val true (φ.inst c)) ∧ ¬ ∃ c, Cl c ∧ Val false (φ.inst c)) :=
  ⟨fun ⟨h1, h2⟩ => ⟨fun h => h1 ((all_earned_iff φ).2 h), fun h => h2 ((all_refuted_iff φ).2 h)⟩,
   fun ⟨h1, h2⟩ => ⟨fun h => h1 ((all_earned_iff φ).1 h), fun h => h2 ((all_refuted_iff φ).1 h)⟩⟩

/-- The residue of a universal body: the probes whose instance is undecided. -/
def Residue (φ : Fm) (c : Tm) : Prop := Cl c ∧ ¬ Decided (φ.inst c)

/-- The residue verdict: no decided counterexample (the residue is reported, not completed). -/
def RelT (φ : Fm) : Prop := ∀ c, Cl c → ¬ Val false (φ.inst c)

/-- EARNED refines the residue verdict, with an empty residue. -/
theorem earned_relT {φ : Fm} (h : Val true (.all φ)) : RelT φ ∧ ∀ c, ¬ Residue φ c := by
  have hall := (all_earned_iff φ).1 h
  exact ⟨fun c hc hf => consistent (hall c hc) hf, fun c ⟨hc, hnd⟩ => hnd (Or.inl (hall c hc))⟩

/-- "A is empty" by the atom: no decided counterexample… -/
theorem A_empty_relT : RelT (.neg (.mem x0 A)) := by
  intro c _ h
  rw [A_empty_atom_inst] at h
  cases h with | negF h => exact A_no_member c h

/-- …and the residue is not empty: it holds the dirty probe D. -/
theorem D_in_A_residue : Residue (.neg (.mem x0 A)) D := by
  refine ⟨D_closed, ?_⟩
  rw [A_empty_atom_inst]
  intro h
  cases h with
  | inl h => cases h with | negT h => exact A_dirty_at_D false h
  | inr h => cases h with | negF h => exact A_dirty_at_D true h

/-- **The operational verdict on "A is empty"**: true outside the residue, the residue holds D,
and the lazy register says Z — the Z is exactly that residue. -/
theorem A_empty_residue_verdict :
    RelT (.neg (.mem x0 A)) ∧ Residue (.neg (.mem x0 A)) D ∧
    ¬ Val true A_empty_atom ∧ ¬ Val false A_empty_atom :=
  ⟨A_empty_relT, D_in_A_residue,
   fun h => by cases h with | allT h => exact D_in_A_residue.2 (Or.inl (h D D_closed)),
   fun h => by cases h with | allF c hc h => exact A_empty_relT c hc h⟩

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.all_refuted_iff
#print axioms VRCycle.SetsNaive.all_earned_iff
#print axioms VRCycle.SetsNaive.all_quarantine_iff
#print axioms VRCycle.SetsNaive.earned_relT
#print axioms VRCycle.SetsNaive.A_empty_relT
#print axioms VRCycle.SetsNaive.D_in_A_residue
#print axioms VRCycle.SetsNaive.A_empty_residue_verdict
