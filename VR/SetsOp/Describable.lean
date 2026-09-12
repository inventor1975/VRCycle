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
-- Axiom profile: `[]` (2026-09-12, integrity programme).  Until that day the enumeration used
-- Mathlib's `deriving Encodable`, which carries `Classical.choice` through `Nat.unpair_pair`
-- (measured); it was flagged as borrowed plumbing.  The flag is now repaid without any ℕ-pairing:
-- the descriptions are enumerated by NESTED FINITE STAGES (`stage n` = every description of depth
-- ≤ n, a list built by a rule), and `descEnum k` reads the `k`-th entry of stage `k` — the diagonal
-- reaches every entry because the stages are nested and stage `k` is longer than `k`.  Surjectivity
-- is a structural induction with the `[]` list lemmas of `Continuum/ListCore.lean`.  The
-- enumeration is EXHIBITED, not choice-asserted, and the module is axiom-free throughout.

import VR.SetsOp.Becoming
import VR.Continuum.ListCore

namespace VRCycle.SetsOp
open VRCycle.Continuum.ListCore

set_option genInjectivity false in
/-- A **finite description** of an operational set: ∅, unordered pair, union, and ω.  A
finite inductive — hence countably many descriptions.  (Singleton/binUnion/succ are
derived; this language already generates them and all hereditarily finite sets plus ω.) -/
inductive Desc where
  | empty : Desc
  | pair  : Desc → Desc → Desc
  | union : Desc → Desc
  | omega : Desc

/-- Interpretation of a finite description as an operational set. -/
def Desc.eval : Desc → OpSet.{0}
  | .empty    => OpSet.emptySup
  | .pair a b => OpSet.pair a.eval b.eval
  | .union a  => a.eval.union
  | .omega    => OpSet.omega

/-- `x` is **describable** if it is operationally identical to the value of some finite
description. -/
def OpSet.IsDescribable (x : OpSet.{0}) : Prop := ∃ d : Desc, x.Equiv d.eval

/-- Nesting depth of a description (the stage at which it first appears). -/
def Desc.depth : Desc → ℕ
  | .empty    => 0
  | .omega    => 0
  | .pair a b => a.depth + b.depth + 1
  | .union a  => a.depth + 1

/-- The descriptions one step deeper than a list `l`: unions of members and pairs of members. -/
def newAt (l : List Desc) : List Desc :=
  l.map Desc.union ++ l.flatMap (fun a => l.map (Desc.pair a))

/-- Stage `n` of the enumeration — a finite LIST, built by a rule: `stage 0 = [∅, ω]`,
`stage (n+1) = stage n ++ newAt (stage n)`.  Every description of depth `≤ n` occurs in `stage n`
(`mem_stage`), each stage is a prefix of the next (`stage_prefix`), and stage `n` has more than `n`
entries (`length_stage`). -/
def stage : ℕ → List Desc
  | 0     => [Desc.empty, Desc.omega]
  | n + 1 => stage n ++ newAt (stage n)

theorem stage_prefix : ∀ (n k : ℕ), ∃ t, stage (n + k) = stage n ++ t
  | n, 0     => ⟨[], (append_nil' (stage n)).symm⟩
  | n, k + 1 =>
      match stage_prefix n k with
      | ⟨t, ht⟩ => ⟨t ++ newAt (stage (n + k)), by
          change stage (n + k) ++ newAt (stage (n + k)) = stage n ++ (t ++ newAt (stage (n + k)))
          rw [ht, append_assoc']⟩

theorem mem_stage_mono {d : Desc} {n : ℕ} (h : d ∈ stage n) (k : ℕ) : d ∈ stage (n + k) :=
  match stage_prefix n k with
  | ⟨t, ht⟩ => by rw [ht]; exact mem_append_iff.mpr (Or.inl h)

theorem mem_stage : ∀ d : Desc, d ∈ stage d.depth
  | .empty    => show Desc.empty ∈ [Desc.empty, Desc.omega] from List.Mem.head _
  | .omega    => show Desc.omega ∈ [Desc.empty, Desc.omega] from List.Mem.tail _ (List.Mem.head _)
  | .pair a b =>
      have ha : a ∈ stage (a.depth + b.depth) := mem_stage_mono (mem_stage a) b.depth
      have e : b.depth + a.depth = a.depth + b.depth := Nat.add_comm _ _
      have hb : b ∈ stage (a.depth + b.depth) := e ▸ mem_stage_mono (mem_stage b) a.depth
      show Desc.pair a b ∈ stage (a.depth + b.depth) ++ newAt (stage (a.depth + b.depth)) from
        mem_append_iff.mpr (Or.inr (mem_append_iff.mpr (Or.inr
          (mem_flatMap_iff.mpr ⟨a, ha, mem_map_iff.mpr ⟨b, hb, rfl⟩⟩))))
  | .union a  =>
      show Desc.union a ∈ stage a.depth ++ newAt (stage a.depth) from
        mem_append_iff.mpr (Or.inr (mem_append_iff.mpr (Or.inl
          (mem_map_iff.mpr ⟨a, mem_stage a, rfl⟩))))

theorem length_stage : ∀ n : ℕ, n < (stage n).length
  | 0     => show 0 < 0 + 1 + 1 from Nat.zero_lt_succ _
  | n + 1 =>
      have h1 : n < (stage n).length := length_stage n
      have h0 : 1 ≤ (stage n).length := Nat.lt_of_le_of_lt (Nat.zero_le n) h1
      have h2 : (stage n).length ≤ (newAt (stage n)).length := by
        change (stage n).length ≤ ((stage n).map Desc.union ++ _).length
        rw [length_append', length_map']
        exact Nat.le_add_right _ _
      by
        change n + 1 < (stage n ++ newAt (stage n)).length
        rw [length_append']
        exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ h1) (Nat.add_le_add_left (Nat.le_trans h0 h2) _)

theorem nth_stage_stable (n k i : ℕ) (hi : i < (stage n).length) :
    nth (stage (n + k)) i = nth (stage n) i :=
  match stage_prefix n k with
  | ⟨t, ht⟩ => by rw [ht]; exact nth_append_left (stage n) t i hi

/-- Read an optional description, defaulting to `∅`'s description. -/
def orEmpty : Option Desc → Desc
  | some d => d
  | none   => Desc.empty

/-- An EXPLICIT enumeration of descriptions (a rule, not a choice-asserted surjection): the `k`-th
entry of stage `k`.  Since the stages are nested and stage `k` is longer than `k`, this diagonal
reads every entry of every stage exactly where it first appears (`descEnum_surjective`).  Built
by hand on `[]` (2026-09-12) — Mathlib's `deriving Encodable` carried `Classical.choice`. -/
def descEnum (k : ℕ) : Desc := orEmpty (nth (stage k) k)

theorem descEnum_surjective : Function.Surjective descEnum := by
  intro d
  obtain ⟨i, hi⟩ := nth_of_mem (mem_stage d)
  refine ⟨i, ?_⟩
  have key : nth (stage i) i = some d := by
    cases Nat.le_total i d.depth with
    | inl h =>
        obtain ⟨k, hk⟩ := Nat.le.dest h
        have hs := nth_stage_stable i k i (length_stage i)
        rw [hk] at hs
        exact hs.symm.trans hi
    | inr h =>
        obtain ⟨k, hk⟩ := Nat.le.dest h
        have hlt : i < (stage d.depth).length := by
          cases Nat.lt_or_ge i (stage d.depth).length with
          | inl h' => exact h'
          | inr h' =>
              have e := hi.symm.trans (nth_eq_none _ _ h')
              cases e
        have hs := nth_stage_stable d.depth k i hlt
        rw [hk] at hs
        exact hs.trans hi
  change orEmpty (nth (stage i) i) = d
  rw [key]
  rfl

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
