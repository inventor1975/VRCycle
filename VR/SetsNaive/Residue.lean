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

/-! ## "1 ∈ 2" outside the residue (the measurement asked for, 2026-11-05 02:19) -/

/-- An earned or refuted cell makes `p ↔ p` earned. -/
theorem iff_self_of_decided {p : Fm} (h : Val true p ∨ Val false p) : Val true (Fm.iff p p) := by
  cases h with
  | inl h => exact .andT (.negT (.andFr (.negF h))) (.negT (.andFr (.negF h)))
  | inr h => exact .andT (.negT (.andFl h)) (.negT (.andFl h))

/-- `p ↔ p` is never refuted. -/
theorem iff_self_never_false (p : Fm) : ¬ Val false (Fm.iff p p) := by
  intro h
  cases h with
  | andFl h => cases h with | negF h => cases h with | andT h1 h2 => cases h2 with | negT h2 => exact consistent h1 h2
  | andFr h => cases h with | negF h => cases h with | andT h1 h2 => cases h2 with | negT h2 => exact consistent h1 h2

/-- The body of `1 ≐ 1`. -/
def oneSelf : Fm := Fm.iff (.mem x0 one) (.mem x0 one)

/-- `1 ≐ 1` outside the residue: no decided counterexample. -/
theorem oneSelf_relT : RelT oneSelf := by
  intro c _ h
  rw [show oneSelf.inst c = Fm.iff (.mem c one) (.mem c one) from Eqv_inst one_closed one_closed c] at h
  exact iff_self_never_false _ h

/-- `D ∈ 1` is quarantined (`D ≐ 0` is neither earned nor refuted). -/
theorem D_in_one_quarantine (v : Bool) : ¬ Val v (.mem D one) := by
  intro h
  have h' : Val v (Eqv D zero) := by
    cases v with
    | true => cases h with | memT h => rw [eqBody_inst zero_closed D] at h; exact h
    | false => cases h with | memF h => rw [eqBody_inst zero_closed D] at h; exact h
  cases v with
  | true =>
    cases h' with
    | allT h' =>
      have hi := h' E E_closed
      rw [Eqv_inst D_closed zero_closed E] at hi
      cases iff_earned_decides hi with
      | inl h => exact D_no_value E true h
      | inr h => exact D_no_value E false h
  | false =>
    cases h' with
    | allF c _ h' =>
      rw [Eqv_inst D_closed zero_closed c] at h'
      cases h' with
      | andFl h' => cases h' with | negF h' => cases h' with | andT h1 _ => exact D_no_value c true h1
      | andFr h' => cases h' with
        | negF h' => cases h' with | andT _ h2 => cases h2 with | negT h2 => exact D_no_value c false h2

/-- The residue of `1 ≐ 1` holds D… -/
theorem D_in_oneSelf_residue : Residue oneSelf D := by
  refine ⟨D_closed, ?_⟩
  rw [show oneSelf.inst D = Fm.iff (.mem D one) (.mem D one) from Eqv_inst one_closed one_closed D]
  intro h
  cases h with
  | inl h => cases iff_earned_decides h with
    | inl h => exact D_in_one_quarantine true h
    | inr h => exact D_in_one_quarantine false h
  | inr h => exact iff_self_never_false _ h

/-- …but NOT 0, V or 1 itself: the residue is not everything (the verdict is not vacuous). -/
theorem oneSelf_residue_not_all :
    ¬ Residue oneSelf zero ∧ ¬ Residue oneSelf V ∧ ¬ Residue oneSelf one := by
  have hinst : ∀ c, oneSelf.inst c = Fm.iff (.mem c one) (.mem c one) :=
    fun c => Eqv_inst one_closed one_closed c
  have one_in_one_false : Val false (.mem one one) := by
    apply Val.memF; rw [eqBody_inst zero_closed one]; exact one_eq_zero_refuted
  refine ⟨fun ⟨_, h⟩ => h ?_, fun ⟨_, h⟩ => h ?_, fun ⟨_, h⟩ => h ?_⟩
  · rw [hinst]; exact Or.inl (iff_self_of_decided (Or.inl zero_in_one))
  · rw [hinst]; exact Or.inl (iff_self_of_decided (Or.inr V_not_in_one))
  · rw [hinst]; exact Or.inl (iff_self_of_decided (Or.inr one_in_one_false))

/-- **"1 ∈ 2" outside the residue**: its definition `1 ≐ 0 ∨ 1 ≐ 1` has `1 ≐ 0` REFUTED and
`1 ≐ 1` true outside a residue that holds D but not 0, V, 1 — while the lazy cell `1 ∈ 2` itself is
quarantined (`vn_two_breaks`).  The operational verdict, no excluded middle, nothing fed back. -/
theorem one_in_two_residue :
    Val false (Eqv one zero) ∧ RelT oneSelf ∧ Residue oneSelf D ∧
    (¬ Residue oneSelf zero ∧ ¬ Residue oneSelf V ∧ ¬ Residue oneSelf one) ∧
    (∀ v, ¬ Val v (.mem one two)) :=
  ⟨one_eq_zero_refuted, oneSelf_relT, D_in_oneSelf_residue, oneSelf_residue_not_all,
   vn_two_breaks.2⟩

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.all_refuted_iff
#print axioms VRCycle.SetsNaive.all_earned_iff
#print axioms VRCycle.SetsNaive.all_quarantine_iff
#print axioms VRCycle.SetsNaive.earned_relT
#print axioms VRCycle.SetsNaive.A_empty_relT
#print axioms VRCycle.SetsNaive.D_in_A_residue
#print axioms VRCycle.SetsNaive.A_empty_residue_verdict
#print axioms VRCycle.SetsNaive.D_in_one_quarantine
#print axioms VRCycle.SetsNaive.oneSelf_residue_not_all
#print axioms VRCycle.SetsNaive.one_in_two_residue
