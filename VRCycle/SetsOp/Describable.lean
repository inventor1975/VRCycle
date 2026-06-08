-- VRCycle/SetsOp/Describable.lean
-- VR-Sets, Brouwer edition — Stage S5: the DESCRIBABLE register is countable.
-- The correct, machine-checked replacement of the erroneous §VI.1: NOT "the universe is
-- countable" (false — see `universe_not_enumerable`), but "the sets given by a FINITE
-- description (a finite rule) are countable".  Countability needs finiteness of the
-- description, exactly the preprint's "finite syntactic record".
--
-- Together with `Becoming.universe_not_enumerable` this is the corrected §VI in full:
--   * the DONE / describable register is enumerable (this file);
--   * the BECOMING / whole universe is not (Becoming.lean).
--
-- Axiom profile: MEASURED below = [propext, Classical.choice, Quot.sound].  The residual
-- `Classical.choice` is INHERENT in mathlib's `deriving Encodable` instance (its decode/encode)
-- and mathlib's Nat pairing INVERSION — NOT in this file's logic.  Pinpointed (measured):
-- `Nat.pair` is axiom-free, but `Nat.unpair_pair` and `Nat.pair_eq_pair` are BOTH
-- `[propext, Classical.choice, Quot.sound]`; `Encodable.encodek`/`Option.getD_some` are
-- axiom-free.  So the choice is mathlib using `Classical` INCIDENTALLY to prove a fact that
-- is constructively TRUE (the known "mathlib casually uses choice" phenomenon) — borrowed
-- plumbing, not a VR commitment.  DECISION (A), 2026-06-08: KEEP this strong theorem (a
-- genuine ℕ-enumeration of the describable sets); the single borrowed-from-mathlib choice is
-- documented here and confined to this META countability claim (formal-register accounting,
-- where choice is legitimately accepted — cf. VR-Audit).  Removing it would mean re-deriving
-- ℕ-pairing injectivity choice-free from scratch (disproportionate, orthogonal to VR).  Note:
-- the enumeration is nonetheless EXHIBITED as a rule (`descEnum`), not choice-asserted.  The
-- substantive operational payoff (the universe IS non-enumerable) is choice-free in
-- `Becoming.lean`; this is its countable counterpart.  Everything else in `SetsOp/` is
-- choice-free (axiom-free or `[propext]`).

import VRCycle.SetsOp.Becoming

namespace VRCycle.SetsOp

/-- A **finite description** of an operational set: ∅, unordered pair, union, and ω.  A
finite inductive — hence countably many descriptions.  (Singleton/binUnion/succ are
derived; this language already generates them and all hereditarily finite sets plus ω.) -/
inductive Desc where
  | empty : Desc
  | pair  : Desc → Desc → Desc
  | union : Desc → Desc
  | omega : Desc
deriving Encodable

/-- Interpretation of a finite description as an operational set. -/
def Desc.eval : Desc → OpSet.{0}
  | .empty    => OpSet.emptySup
  | .pair a b => OpSet.pair a.eval b.eval
  | .union a  => a.eval.union
  | .omega    => OpSet.omega

/-- `x` is **describable** if it is operationally identical to the value of some finite
description. -/
def OpSet.IsDescribable (x : OpSet.{0}) : Prop := ∃ d : Desc, x.Equiv d.eval

/-- An EXPLICIT enumeration of descriptions (a rule, not a choice-asserted surjection):
decode the index, defaulting to `∅`'s description.  This exhibits the countability of the
describable register as a CONSTRUCTED rule — faithful to VR (exhibit the witness, don't
invoke choice). -/
def descEnum (n : ℕ) : Desc := (Encodable.decode n).getD Desc.empty

theorem descEnum_surjective : Function.Surjective descEnum := by
  intro d
  refine ⟨Encodable.encode d, ?_⟩
  show (Encodable.decode (Encodable.encode d)).getD Desc.empty = d
  rw [Encodable.encodek d, Option.getD_some]

/-- **The describable register is countable.**  A single EXPLICIT `ℕ`-indexed enumeration
(`descEnum`, a rule) reaches every describable set (up to `≈`).  Contrast
`universe_not_enumerable`: the describable (done) register is enumerable, the whole universe
(becoming) is not — this is the corrected §VI.  Choice-free: the enumeration is exhibited. -/
theorem OpSet.describable_countable :
    ∃ f : ℕ → OpSet.{0}, ∀ x, OpSet.IsDescribable x → ∃ n, (f n).Equiv x := by
  refine ⟨fun n => (descEnum n).eval, ?_⟩
  rintro x ⟨d, hd⟩
  obtain ⟨n, hn⟩ := descEnum_surjective d
  subst hn
  exact ⟨n, hd.symm⟩

-- Concrete: ∅, pair, union, ω are describable.
theorem OpSet.emptySup_describable : OpSet.IsDescribable OpSet.emptySup :=
  ⟨Desc.empty, OpSet.Equiv.refl _⟩
theorem OpSet.omega_describable : OpSet.IsDescribable OpSet.omega :=
  ⟨Desc.omega, OpSet.Equiv.refl _⟩

-- CHECKS: no sorry, no admit.

-- Axiom audit (Stage S5) — MEASURED
#print axioms descEnum_surjective
#print axioms OpSet.describable_countable

end VRCycle.SetsOp
