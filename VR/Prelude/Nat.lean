-- VR/Prelude/Nat.lean — the least witness of a decidable property, on `[]`.
--
-- Mathlib's `Nat.find` (`Mathlib/Data/Nat/Find.lean`) is axiom-free in `find`/`find_spec`/`find_min`;
-- it is reproduced here so that the VR core depends on Lean alone (curator, 2026-09-13). The
-- construction is the well-founded descent of Mathlib's `Nat.findX`: from a witness of `∃ n, p n`
-- the relation "next candidate" is well-founded, and the search from `0` terminates.

namespace VRCycle.Nat

variable {p : Nat → Prop} [DecidablePred p]

private def lbp (m n : Nat) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬ p k

private theorem wf_lbp (H : ∃ n, p n) : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
   suffices ∀ m k, n ≤ k + m → Acc lbp k from fun a => this _ _ (Nat.le_add_left _ _)
   fun m => Nat.rec
     (fun k kn => ⟨_, fun y r => by rw [r.1]; exact absurd pn (r.2 _ kn)⟩)
     (fun m IH k kn => ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩)
     m⟩

/-- The least witness, carried with its certificate. -/
protected def findX (H : ∃ n, p n) : { n // p n ∧ ∀ m, m < n → ¬ p m } :=
  @WellFounded.fix _ (fun k => (∀ n, n < k → ¬ p n) → { n // p n ∧ ∀ m, m < n → ¬ p m })
    lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n, n ≤ m → ¬ p n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n (Nat.le_of_lt_succ h))
    0 fun n h => absurd h (Nat.not_lt_zero _)

/-- The least `n` with `p n`, given that one exists. -/
protected def find (H : ∃ n, p n) : Nat := (VRCycle.Nat.findX H).1

protected theorem find_spec (H : ∃ n, p n) : p (VRCycle.Nat.find H) := (VRCycle.Nat.findX H).2.1

protected theorem find_min (H : ∃ n, p n) {m : Nat} : m < VRCycle.Nat.find H → ¬ p m :=
  (VRCycle.Nat.findX H).2.2 m

#print axioms VRCycle.Nat.find
#print axioms VRCycle.Nat.find_spec
#print axioms VRCycle.Nat.find_min

end VRCycle.Nat
