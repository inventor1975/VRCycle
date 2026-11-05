-- VR/SetsNaive/OmegaN.lean
-- VR-Sets, naive edition — Stage N15: ω in the naive layer, measured (path 1, last door).
--
-- ω à la Dedekind: `ω = {x : ∀y (Ind y → x ∈ y)}`, `Ind y = 0 ∈ y ∧ ∀z (z ∈ y → s z ∈ y)`, with the
-- successor `s z = {w : w ∈ z ∨ w ≐ z}` (identity by extension, N9).
--
-- Measured here:
--   * `omega_no_earned_member` — in the OPERATIONAL (lazy) register ω has NO earned member at all,
--     not even 0: the instance y := D (the dirty probe) withholds every T;
--   * `num_in_omega_stable` — in the CLASSICAL register (every completion, given excluded middle as
--     a hypothesis) every numeral `sᵏ 0` is in ω by its definition — EARNED IF STABLE, for all k;
--   * `D_in_omega_open` — but the junk is NOT excluded: whether the dirty set D is in ω is OPEN —
--     one completion puts it in, another keeps it out.  Completions cannot respect comprehension
--     (N8 `no_comprehension_completion`), so the classical register does not pin ω's extension:
--     "ω contains the numerals" holds, "ω contains only numerals" does not.
-- Verdict for path 1: the naive layer does not give VR a standard ω — not operationally (no member),
-- not classically (no exclusion of junk).
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Curry

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- The successor of the bound variable z (z = index 0 here): `{w : w ∈ z ∨ w ≐ z}`. -/
def succOpen : Tm := .abs (Fm.or (.mem x0 (.var 1)) (eqBody (.var 2)))
/-- The successor of a closed term. -/
def nsucc (t : Tm) : Tm := .abs (Fm.or (.mem x0 t) (eqBody t))

/-- `Ind y` with y = index 0. -/
def IndY : Fm := .and (.mem zero (.var 0)) (.all (Fm.imp (.mem x0 (.var 1)) (.mem succOpen (.var 1))))
/-- `Ind c` for a closed c. -/
def Ind (c : Tm) : Fm := .and (.mem zero c) (.all (Fm.imp (.mem x0 c) (.mem succOpen c)))

/-- ω. -/
def natω : Tm := .abs (.all (Fm.imp IndY (.mem (.var 1) (.var 0))))

theorem IndY_inst (c : Tm) : IndY.inst c = Ind c := rfl

theorem memω_def (x : Tm) : ((Fm.all (Fm.imp IndY (.mem (.var 1) (.var 0)))).inst x)
    = .all (Fm.imp IndY (.mem x (.var 0))) := rfl

theorem outer_inst {x : Tm} (hx : Cl x) (c : Tm) :
    (Fm.imp IndY (.mem x (.var 0))).inst c = Fm.imp (Ind c) (.mem x c) := by
  show Fm.neg (.and (IndY.inst c) (.neg (.mem (Tm.subst 0 c x) c))) = _
  rw [Cl.subst hx 0 c]
  rfl

theorem inner_inst {c : Tm} (hc : Cl c) (n : Tm) :
    (Fm.imp (.mem x0 c) (.mem succOpen c)).inst n = Fm.imp (.mem n c) (.mem (nsucc n) c) := by
  show Fm.neg (.and (.mem n (Tm.subst 0 n c)) (.neg (.mem (nsucc n) (Tm.subst 0 n c)))) = _
  rw [Cl.subst hc 0 n]
  rfl

/-! ## Operational register: ω has no earned member -/

/-- **ω has no earned member** — not even 0. -/
theorem omega_no_earned_member {x : Tm} (hx : Cl x) : ¬ Val true (.mem x natω) := by
  intro h
  cases h with
  | memT h =>
    rw [memω_def] at h
    cases h with
    | allT h =>
      have hD := h D D_closed
      rw [outer_inst hx D] at hD
      cases hD with
      | negT hD =>
        cases hD with
        | andFl hI =>
          cases hI with
          | andFl h0 => exact D_no_value zero false h0
          | andFr hR =>
            cases hR with
            | allF t ht hR =>
              rw [inner_inst D_closed t] at hR
              cases hR with | negF hR => cases hR with | andT hR _ => exact D_no_value t true hR
        | andFr hm => cases hm with | negF hm => exact D_no_value x true hm

/-! ## Classical register: the numerals are in ω -/

/-- The numerals `sᵏ 0`. -/
def num : Nat → Tm
  | 0 => zero
  | k + 1 => nsucc (num k)

theorem nsucc_closed {t : Tm} (h : Cl t) : Cl (nsucc t) := by
  show (Tm.closedAt 1 t && Fm.closedAt 1 (eqBody t)) = true
  have h1 : Tm.closedAt 1 t = true := Cl.mono h 1
  have h2 : Fm.closedAt 1 (eqBody t) = true := by
    show (Fm.closedAt 2 (Fm.iff (.mem x0 (.var 1)) (.mem x0 t))) = true
    show ((Nat.blt 0 2 && Nat.blt 1 2) && (Nat.blt 0 2 && Tm.closedAt 2 t) &&
          ((Nat.blt 0 2 && Tm.closedAt 2 t) && (Nat.blt 0 2 && Nat.blt 1 2))) = true
    rw [Cl.mono h 2]; rfl
  rw [h1, h2]; rfl

theorem num_closed : ∀ k, Cl (num k)
  | 0 => rfl
  | k + 1 => nsucc_closed (num_closed k)

/-- Under any completion, if `Ind c → n ∈ c` reads true, so does `Ind c → s n ∈ c`. -/
theorem stable_succ (M : Completion) {c n : Tm} (hc : Cl c) (hn : Cl n)
    (h : Rd M.o true (Fm.imp (Ind c) (.mem n c))) : Rd M.o true (Fm.imp (Ind c) (.mem (nsucc n) c)) := by
  cases h with
  | negT h =>
    cases h with
    | andFl hI => exact .negT (.andFl hI)
    | andFr hm =>
      cases hm with
      | negF hm =>
        cases M.dec (nsucc n) c with
        | inl hs => exact .negT (.andFr (.negF (.memT hs)))
        | inr hs =>
          cases hm with
          | memT hm =>
            apply Rd.negT; apply Rd.andFl; apply Rd.andFr
            apply Rd.allF n hn
            rw [inner_inst hc n]
            exact .negF (.andT (.memT hm) (.negT (.memF hs)))

/-- **Every numeral is in ω, EARNED IF STABLE** (by ω's definition). -/
theorem num_in_omega_stable (k : Nat) : StableT (.all (Fm.imp IndY (.mem (num k) (.var 0)))) := by
  intro M
  apply Rd.allT
  intro c hc
  rw [outer_inst (num_closed k) c]
  induction k with
  | zero =>
    cases M.dec zero c with
    | inl h => exact .negT (.andFr (.negF (.memT h)))
    | inr h => exact .negT (.andFl (.andFl (.memF h)))
  | succ k ih => exact stable_succ M hc (num_closed k) ih

/-! ## …but the junk is not excluded -/

theorem E_ne_D : E ≠ D := fun h => by cases h
theorem nsucc_ne_D (t : Tm) : nsucc t ≠ D := fun h => by cases h

/-- Given excluded middle: the completion "everything not refuted is in". -/
def Completion.notRefuted (lem : LEM) : Completion :=
  ⟨fun a b => ¬ Val false (.mem a b), fun _ _ => lem _, fun h h' => consistent h h', fun h h' => h' h⟩

/-- Given excluded middle: the completion that keeps D out of D and puts everything else in D. -/
def Completion.Dout (lem : LEM) : Completion :=
  ⟨fun a b => (b = D ∧ a ≠ D) ∨ (b ≠ D ∧ Val true (.mem a b)),
   fun _ _ => lem _,
   fun {a b} h => Or.inr ⟨fun e => by subst e; exact D_no_value a true h, h⟩,
   fun {a b} h h' => by
     cases h' with
     | inl h' => obtain ⟨e, _⟩ := h'; subst e; exact D_no_value a false h
     | inr h' => exact consistent h h'.2⟩

/-- **Whether D is in ω is OPEN**: the "not refuted" completion puts it in, the "D out" completion
keeps it out. -/
theorem D_in_omega_open (lem : LEM) :
    Rd (Completion.notRefuted lem).o true (.all (Fm.imp IndY (.mem D (.var 0)))) ∧
    Rd (Completion.Dout lem).o false (.all (Fm.imp IndY (.mem D (.var 0)))) := by
  constructor
  · apply Rd.allT
    intro c hc
    rw [outer_inst D_closed c]
    cases lem (Val false (.mem D c)) with
    | inr h => exact .negT (.andFr (.negF (.memT h)))
    | inl h =>
      have h0 : Val false (.mem zero c) := by
        have := D_bottom (t := zero) zero_closed (.mem x0 c) false
        rw [inst_mem_closed hc D, inst_mem_closed hc zero] at this
        exact this h
      exact .negT (.andFl (.andFl (.memF (fun h' => h' h0))))
  · apply Rd.allF D D_closed
    rw [outer_inst D_closed D]
    apply Rd.negF
    apply Rd.andT
    · apply Rd.andT
      · exact .memT (Or.inl ⟨rfl, E_ne_D⟩)
      · apply Rd.allT
        intro z _
        rw [inner_inst D_closed z]
        exact .negT (.andFr (.negF (.memT (Or.inl ⟨rfl, nsucc_ne_D z⟩))))
    · apply Rd.negT
      apply Rd.memF
      intro h
      cases h with
      | inl h => exact h.2 rfl
      | inr h => exact h.1 rfl

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.omega_no_earned_member
#print axioms VRCycle.SetsNaive.num_in_omega_stable
#print axioms VRCycle.SetsNaive.D_in_omega_open
