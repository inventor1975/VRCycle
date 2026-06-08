-- VRCycle/SetsOp/Becoming.lean
-- VR-Sets, Brouwer edition — Stage S4: the operational universe is NON-ENUMERABLE.
-- The real, machine-checked replacement of the erroneous §VI ("the universe is countable"):
-- no ℕ-enumeration is surjective (up to ≈) onto the operational sets.  A self-contained
-- Cantor diagonal on `OpSet`, using the distinctness of the von Neumann naturals.
--
-- This file imports `Continuum` ONLY for ℕ arithmetic (strong induction, order); it adds no
-- Classical.choice.  The operational core (Pointed…Congruence) stays self-contained.
-- Target: choice-free ([propext, Quot.sound]).

import VRCycle.SetsOp.Congruence
import VRCycle.Continuum

namespace VRCycle.SetsOp

-- ============================================================
-- §1.  Members of the von Neumann naturals; their distinctness
-- ============================================================

/-- The members of `vn m` are exactly `vn 0, …, vn (m-1)` (up to `≈`). -/
theorem OpSet.vn_mem_iff (x : OpSet.{0}) (m : Nat) :
    x.Mem (OpSet.vn m) ↔ ∃ k, k < m ∧ x.Equiv (OpSet.vn k) := by
  induction m with
  | zero =>
      constructor
      · intro h; exact absurd h (OpSet.not_mem_emptySup x)
      · rintro ⟨k, hk, _⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ m ih =>
      show x.Mem (OpSet.succ (OpSet.vn m)) ↔ _
      rw [OpSet.mem_succ, ih]
      constructor
      · rintro (⟨k, hk, h⟩ | h)
        · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
        · exact ⟨m, Nat.lt_succ_self m, h⟩
      · rintro ⟨k, hk, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
        · exact Or.inl ⟨k, hk', h⟩
        · exact Or.inr (hk' ▸ h)

/-- `k < m → vn k ∈ vn m`. -/
theorem OpSet.vn_lt_mem {k m : Nat} (h : k < m) : (OpSet.vn k).Mem (OpSet.vn m) :=
  (OpSet.vn_mem_iff (OpSet.vn k) m).2 ⟨k, h, OpSet.Equiv.refl _⟩

/-- No von Neumann natural is a member of itself (the ZFC-fragment acyclicity, by strong
induction — choice-free). -/
theorem OpSet.vn_not_self_mem (n : Nat) : ¬ (OpSet.vn n).Mem (OpSet.vn n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hself
    obtain ⟨k, hk, hek⟩ := (OpSet.vn_mem_iff (OpSet.vn n) n).1 hself
    have h1 : (OpSet.vn k).Mem (OpSet.vn n) := OpSet.vn_lt_mem hk
    have h2 : (OpSet.vn k).Mem (OpSet.vn k) :=
      (OpSet.equiv_iff_same_mem.1 hek (OpSet.vn k)).1 h1
    exact ih k hk h2

/-- **The operational naturals are distinct**: `vn n ≈ vn m → n = m`. -/
theorem OpSet.vn_inj {n m : Nat} (h : (OpSet.vn n).Equiv (OpSet.vn m)) : n = m := by
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · exact absurd ((OpSet.equiv_iff_same_mem.1 h (OpSet.vn n)).2 (OpSet.vn_lt_mem hlt))
      (OpSet.vn_not_self_mem n)
  · exact heq
  · exact absurd ((OpSet.equiv_iff_same_mem.1 h (OpSet.vn m)).1 (OpSet.vn_lt_mem hgt))
      (OpSet.vn_not_self_mem m)

-- ============================================================
-- §2.  The diagonal: the universe is non-enumerable
-- ============================================================

/-- The diagonal set of a candidate enumeration `e`: `{ vn n | vn n ∉ e n }`. -/
def OpSet.diag (e : Nat → OpSet.{0}) : OpSet.{0} :=
  OpSet.sup (fun p : { n : Nat // ¬ (OpSet.vn n).Mem (e n) } => OpSet.vn p.val)

theorem OpSet.mem_diag (e : Nat → OpSet.{0}) (k : Nat) :
    (OpSet.vn k).Mem (OpSet.diag e) ↔ ¬ (OpSet.vn k).Mem (e k) := by
  rw [OpSet.diag, OpSet.mem_sup]
  constructor
  · rintro ⟨⟨n, hn⟩, hk⟩
    rw [OpSet.vn_inj hk]; exact hn
  · intro hk
    exact ⟨⟨k, hk⟩, OpSet.Equiv.refl _⟩

/-- **The operational universe is non-enumerable.**  No `ℕ`-indexed enumeration `e` is
surjective up to operational identity: there is always a set (the diagonal) that `e` misses.
This is the Brouwerian payoff — the universe as becoming is genuinely uncountable — and it
replaces the erroneous §VI claim that the operational universe is countable.  Choice-free. -/
theorem OpSet.universe_not_enumerable :
    ¬ ∃ e : Nat → OpSet.{0}, ∀ x : OpSet.{0}, ∃ n, (e n).Equiv x := by
  rintro ⟨e, he⟩
  obtain ⟨m, hm⟩ := he (OpSet.diag e)
  have key : (OpSet.vn m).Mem (e m) ↔ ¬ (OpSet.vn m).Mem (e m) :=
    (OpSet.equiv_iff_same_mem.1 hm (OpSet.vn m)).trans (OpSet.mem_diag e m)
  have np : ¬ (OpSet.vn m).Mem (e m) := fun p => (key.1 p) p
  exact np (key.2 np)

-- CHECKS: no sorry, no admit.

-- Axiom audit (Stage S4) — MEASURED
#print axioms OpSet.vn_inj
#print axioms OpSet.universe_not_enumerable

end VRCycle.SetsOp
