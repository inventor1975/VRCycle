-- VRCycle/Topology/Continuous.lean
-- VR-Topology v1.0.0 — Stage 3: Continuous maps as relators.
--
-- Defines morphisms between formal topologies as relators
-- `rel : T₂.S → T₁.S → Prop` (Sambin-Battilotti convention: continuous map
-- `T₁ → T₂` is given by a backward relator).  Operational version
-- `OpContinuous` adds operational tracking on the relator and on cover
-- preservation, plus a slice-describability field for composition.
--
-- Identity and composition are constructed; Mode A theorems established
-- declaratively.  Smoke-test examples: identity on `Unit`/`Bool` and the
-- unique continuous map to the terminal `Unit` formal topology.
--
-- Plan corrections (recorded as findings in STAGE_3_REPORT.md):
--
-- * Finding T5: PLAN_3 §1 `respects_le` direction error.  PLAN wrote
--   `T₁.le a a' → ...`; the correct direction (consistent with identity
--   relator `rel = Eq` satisfying the axiom, and with Sambin-Battilotti
--   morphism conventions) is `T₁.le a' a → ...` — refinement on the
--   source propagates to refinement on the target.
--
-- * Plan-anticipated activation: `OpContinuous.rel_slice_desc` field
--   added per PLAN_3 §note (k).  Without it, the intermediate
--   describability needed in `OpContinuous.comp.preserves_op_cov` is
--   not constructible, since `IsDescribable.preimage_of_relator` requires
--   slice-describability as input.

import VR.Topology.Operational
open scoped VRCycle.Set

namespace VRCycle.Topology
-- No auto-generated `injEq` lemmas (they carry `propext`); the empty axiom list is the bar (2026-09-12).
set_option genInjectivity false

universe u

-- ============================================================
-- Section 3 (helper, placed first — used by composition): preimage_of_relator
-- ============================================================

namespace IsDescribable

-- ============================================================
-- Custom constructive pair on Nat (Finding T6 — see module docstring).
-- ============================================================
--
-- Mathlib's `Nat.unpair_pair` and `Encodable (Nat × Nat)` both pull
-- `Classical.choice` via `Nat.sqrt`.  We build a bit-interleaved pair
-- here, locally, with a clean axiom profile.  Bit 2k of `pair m n` is
-- bit k of m; bit 2k+1 is bit k of n.

-- Empty-list sweep (2026-09-12): `%`, `/` and `omega` reach `propext` through core's Int/Nat
-- simp lemmas; the pair is rebuilt on `ListCore.halve` (quotient + parity bit by structural
-- recursion) with fuel, and every inequality is by hand.  Same specification as before:
-- bit 2k of `pair m n` is bit k of m, bit 2k+1 is bit k of n.

/-- `2q + b`: one bit appended below `q`. -/
private def bit (q : Nat) : Bool → Nat
  | false => q + q
  | true  => q + q + 1

private theorem halve_bit (q : Nat) :
    ∀ b : Bool, VRCycle.Continuum.ListCore.halve (bit q b) = (q, b)
  | false => VRCycle.Continuum.ListCore.halve_double q
  | true  => VRCycle.Continuum.ListCore.halve_double_succ q

private theorem bit_succ (q : Nat) : ∀ b : Bool, bit (q + 1) b = bit q b + 2
  | false => congrArg Nat.succ (Nat.succ_add q q)
  | true  => congrArg Nat.succ (congrArg Nat.succ (Nat.succ_add q q))

/-- Recomposition: a number is its half with its parity bit appended. -/
private theorem bit_halve : ∀ n : Nat,
    bit (VRCycle.Continuum.ListCore.halve n).1 (VRCycle.Continuum.ListCore.halve n).2 = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show bit ((VRCycle.Continuum.ListCore.halve n).1 + 1)
          (VRCycle.Continuum.ListCore.halve n).2 = n + 2
      rw [bit_succ, bit_halve n]

private theorem halve_fst_lt : ∀ n : Nat, 0 < n → (VRCycle.Continuum.ListCore.halve n).1 < n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => Nat.zero_lt_succ 0
  | n + 2, _ =>
      Nat.succ_lt_succ (Nat.lt_of_le_of_lt (VRCycle.Continuum.ListCore.halve_fst_le n)
        (Nat.lt_succ_self n))

private theorem le_bit (q : Nat) : ∀ b : Bool, q ≤ bit q b
  | false => Nat.le_add_right q q
  | true  => Nat.le_succ_of_le (Nat.le_add_right q q)

private theorem lt_bit_of_pos {q : Nat} (h : 0 < q) : ∀ b : Bool, q < bit q b
  | false => Nat.add_lt_add_left h q
  | true  => Nat.lt_succ_of_lt (Nat.add_lt_add_left h q)

private theorem bit_pos_of_pos {q : Nat} (h : 0 < q) (b : Bool) : 0 < bit q b :=
  Nat.lt_of_lt_of_le h (le_bit q b)

private theorem bit_true_pos (q : Nat) : 0 < bit q true := Nat.zero_lt_succ _

private theorem add_eq_zero_left : ∀ {m n : Nat}, m + n = 0 → m = 0
  | 0, _, _ => rfl
  | k + 1, n, h => by cases (show (k + n) + 1 = 0 from (Nat.succ_add k n).symm.trans h)

private theorem add_eq_zero_right {m n : Nat} (h : m + n = 0) : n = 0 :=
  add_eq_zero_left ((Nat.add_comm n m).trans h)

private theorem add_lt_add_of_lt_of_le' {a b c d : Nat} (h1 : a < b) (h2 : c ≤ d) :
    a + c < b + d :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 c) (Nat.add_le_add_left h2 b)

/-- Interleaving pair, with fuel `f ≥ m + n`. -/
private def pairAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, m, n =>
      if m + n = 0 then 0
      else bit (bit (pairAux f (VRCycle.Continuum.ListCore.halve m).1
                              (VRCycle.Continuum.ListCore.halve n).1)
                    (VRCycle.Continuum.ListCore.halve n).2)
               (VRCycle.Continuum.ListCore.halve m).2

/-- Constructive bit-interleaving pair on Nat. -/
private def pair (m n : Nat) : Nat := pairAux (m + n) m n

/-- Inverse, with fuel `f ≥ k`: peel two bits, recurse on the quarter. -/
private def unpairAux : Nat → Nat → Nat × Nat
  | 0, _ => (0, 0)
  | f + 1, k =>
      if k = 0 then (0, 0)
      else
        (bit (unpairAux f (VRCycle.Continuum.ListCore.halve
                (VRCycle.Continuum.ListCore.halve k).1).1).1
             (VRCycle.Continuum.ListCore.halve k).2,
         bit (unpairAux f (VRCycle.Continuum.ListCore.halve
                (VRCycle.Continuum.ListCore.halve k).1).1).2
             (VRCycle.Continuum.ListCore.halve
                (VRCycle.Continuum.ListCore.halve k).1).2)

/-- Constructive inverse: bits of m at even positions, bits of n at odd positions. -/
private def unpair (k : Nat) : Nat × Nat := unpairAux k k

private theorem unpairAux_zero : ∀ f : Nat, unpairAux f 0 = (0, 0)
  | 0 => rfl
  | f + 1 => by
      show (if 0 = 0 then ((0, 0) : Nat × Nat) else _) = (0, 0)
      rw [if_pos rfl]

/-- The quarter is strictly smaller when the pair is not `(0,0)`. -/
private theorem halves_lt {m n : Nat} (h : m + n ≠ 0) :
    (VRCycle.Continuum.ListCore.halve m).1 + (VRCycle.Continuum.ListCore.halve n).1 < m + n := by
  cases m with
  | zero =>
      have hn : 0 < n := Nat.pos_of_ne_zero (fun e => h ((Nat.zero_add n).trans e))
      show 0 + (VRCycle.Continuum.ListCore.halve n).1 < 0 + n
      rw [Nat.zero_add, Nat.zero_add]
      exact halve_fst_lt n hn
  | succ k =>
      exact add_lt_add_of_lt_of_le' (halve_fst_lt (k + 1) (Nat.zero_lt_succ k))
        (VRCycle.Continuum.ListCore.halve_fst_le n)

/-- `pair` of a non-zero pair is non-zero. -/
private theorem pairAux_pos : ∀ (f m n : Nat), m + n ≤ f → m + n ≠ 0 → 0 < pairAux f m n
  | 0, m, n, h, h0 => absurd (Nat.le_zero.mp h) h0
  | f + 1, m, n, h, h0 => by
      show 0 < (if m + n = 0 then 0 else bit (bit (pairAux f _ _) _) _)
      rw [if_neg h0]
      cases hmb : (VRCycle.Continuum.ListCore.halve m).2 with
      | true => exact bit_true_pos _
      | false =>
        cases hnb : (VRCycle.Continuum.ListCore.halve n).2 with
        | true => exact bit_pos_of_pos (bit_true_pos _) false
        | false =>
          refine bit_pos_of_pos (bit_pos_of_pos (pairAux_pos f _ _ ?_ ?_) false) false
          · exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (halves_lt h0) h)
          · intro hz
            apply h0
            have hm : m = 0 := by
              rw [← bit_halve m, hmb, add_eq_zero_left hz]; rfl
            have hn : n = 0 := by
              rw [← bit_halve n, hnb, add_eq_zero_right hz]; rfl
            rw [hm, hn]

/-- The key inverse lemma, fuel-general: `unpair (pair m n) = (m, n)`. -/
private theorem unpairAux_pairAux : ∀ (f m n : Nat), m + n ≤ f →
    ∀ f' : Nat, pairAux f m n ≤ f' → unpairAux f' (pairAux f m n) = (m, n)
  | 0, m, n, h, f', _ => by
      have hm : m = 0 := add_eq_zero_left (Nat.le_zero.mp h)
      have hn : n = 0 := add_eq_zero_right (Nat.le_zero.mp h)
      subst hm; subst hn
      exact unpairAux_zero f'
  | f + 1, m, n, h, f', hf' => by
      by_cases h0 : m + n = 0
      · have hm : m = 0 := add_eq_zero_left h0
        have hn : n = 0 := add_eq_zero_right h0
        subst hm; subst hn
        have e : pairAux (f + 1) 0 0 = 0 := by
          show (if 0 + 0 = 0 then 0 else _) = 0
          rw [if_pos rfl]
        rw [e]
        exact unpairAux_zero f'
      · have hP : pairAux (f + 1) m n
            = bit (bit (pairAux f (VRCycle.Continuum.ListCore.halve m).1
                                  (VRCycle.Continuum.ListCore.halve n).1)
                        (VRCycle.Continuum.ListCore.halve n).2)
                   (VRCycle.Continuum.ListCore.halve m).2 := by
          show (if m + n = 0 then 0 else _) = _
          rw [if_neg h0]
        have hpos : 0 < pairAux (f + 1) m n := pairAux_pos (f + 1) m n h h0
        have hle : (VRCycle.Continuum.ListCore.halve m).1
            + (VRCycle.Continuum.ListCore.halve n).1 ≤ f :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (halves_lt h0) h)
        rw [hP] at hpos hf' ⊢
        cases f' with
        | zero => exact absurd (Nat.lt_of_lt_of_le hpos hf') (Nat.lt_irrefl 0)
        | succ f'' =>
          have hne : bit (bit (pairAux f (VRCycle.Continuum.ListCore.halve m).1
                                  (VRCycle.Continuum.ListCore.halve n).1)
                        (VRCycle.Continuum.ListCore.halve n).2)
                   (VRCycle.Continuum.ListCore.halve m).2 ≠ 0 :=
            Nat.ne_of_gt hpos
          -- inner fuel bound: Q ≤ f'' (Q = 0, or Q < bit (bit Q _) _ ≤ f'' + 1)
          have hQ : pairAux f (VRCycle.Continuum.ListCore.halve m).1
                              (VRCycle.Continuum.ListCore.halve n).1 ≤ f'' := by
            cases hq : pairAux f (VRCycle.Continuum.ListCore.halve m).1
                              (VRCycle.Continuum.ListCore.halve n).1 with
            | zero => exact Nat.zero_le _
            | succ q =>
              rw [hq] at hf'
              have h1 : q + 1 < bit (q + 1) (VRCycle.Continuum.ListCore.halve n).2 :=
                lt_bit_of_pos (Nat.zero_lt_succ q) _
              have h2 : bit (q + 1) (VRCycle.Continuum.ListCore.halve n).2
                  ≤ bit (bit (q + 1) (VRCycle.Continuum.ListCore.halve n).2)
                        (VRCycle.Continuum.ListCore.halve m).2 :=
                le_bit _ _
              exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) hf')
          show (if _ = 0 then ((0, 0) : Nat × Nat) else _) = (m, n)
          rw [if_neg hne, halve_bit, halve_bit]
          show (bit (unpairAux f'' (pairAux f (VRCycle.Continuum.ListCore.halve m).1
                              (VRCycle.Continuum.ListCore.halve n).1)).1
                    (VRCycle.Continuum.ListCore.halve m).2,
                bit (unpairAux f'' (pairAux f (VRCycle.Continuum.ListCore.halve m).1
                              (VRCycle.Continuum.ListCore.halve n).1)).2
                    (VRCycle.Continuum.ListCore.halve n).2) = (m, n)
          rw [unpairAux_pairAux f _ _ hle f'' hQ]
          show (bit (VRCycle.Continuum.ListCore.halve m).1 (VRCycle.Continuum.ListCore.halve m).2,
                bit (VRCycle.Continuum.ListCore.halve n).1 (VRCycle.Continuum.ListCore.halve n).2)
              = (m, n)
          rw [bit_halve, bit_halve]

/-- The inverse lemma in usable form. -/
private theorem unpair_pair (m n : Nat) : unpair (pair m n) = (m, n) :=
  unpairAux_pairAux (m + n) m n (Nat.le_refl _) (pairAux (m + n) m n) (Nat.le_refl _)

/-- Pre-image describability through a relator.  Given `U : Set β` describable
and each slice `{a | r b a}` describable (for all `b : β`), the relational
pre-image `{a | ∃ b ∈ U, r b a}` is describable.

Construction uses our custom constructive `pair`/`unpair` (Finding T6) —
no `Classical.choice` inheritance from `Nat.sqrt`. -/
@[reducible] def preimage_of_relator
    {α β : Type _} (r : β → α → Prop) (U : Set β)
    [descU : IsDescribable U]
    (descSlice : (b : β) → IsDescribable {a | r b a}) :
    IsDescribable {a | ∃ b ∈ U, r b a} where
  enumerator n :=
    (descU.enumerator (unpair n).1).bind
      (fun b => (descSlice b).enumerator (unpair n).2)
  enumerator_some_mem n a h := by
    rcases hb : descU.enumerator (unpair n).1 with _ | b
    · rw [hb] at h; cases h
    · rw [hb] at h
      refine ⟨b, ?_, ?_⟩
      · exact descU.enumerator_some_mem _ _ hb
      · exact (descSlice b).enumerator_some_mem _ _ h
  enumerator_surj x := by
    rintro ⟨b, hbU, hrx⟩
    obtain ⟨i, hi⟩ := descU.enumerator_surj b hbU
    obtain ⟨j, hj⟩ := (descSlice b).enumerator_surj x hrx
    refine ⟨pair i j, ?_⟩
    -- Goal: (descU.enumerator (unpair (pair i j)).1).bind ... = some x
    -- By unpair_pair: unpair (pair i j) = (i, j)
    have hup : unpair (pair i j) = (i, j) := unpair_pair i j
    rw [hup]
    -- Goal: (descU.enumerator i).bind ... = some x
    rw [hi]
    exact hj

end IsDescribable

-- ============================================================
-- Section 1: ContinuousMap (non-operational base structure)
-- ============================================================

/-- A **continuous map** between formal topologies `T₁ → T₂` is a relator
`rel : T₂.S → T₁.S → Prop` (backward — Sambin-Battilotti convention)
satisfying:

* `respects_le`: refinement on the source propagates to refinement on the
  target.  If `rel b a` holds and `a' ≤ a` (a' refines a), then there is
  some `b' ≤ b` with `rel b' a'`.

* `preserves_cov`: the relational pre-image of a cover is a cover. -/
structure ContinuousMap (T₁ T₂ : FormalTopology) where
  rel : T₂.S → T₁.S → Prop
  respects_le : ∀ {b : T₂.S} {a a' : T₁.S}, rel b a → T₁.le a' a →
                ∃ b', T₂.le b' b ∧ rel b' a'
  preserves_cov : ∀ {b : T₂.S} {a : T₁.S} {U : Set T₂.S},
                  rel b a → T₂.cov b U →
                  T₁.cov a {a' | ∃ b' ∈ U, rel b' a'}

namespace ContinuousMap

variable {T₁ T₂ : FormalTopology}

/-- The relational pre-image of a set under a continuous map. -/
def preimage (f : ContinuousMap T₁ T₂) (U : Set T₂.S) : Set T₁.S :=
  {a | ∃ b ∈ U, f.rel b a}

end ContinuousMap

-- ============================================================
-- Section 2: OpContinuous (operational structure)
-- ============================================================

/-- An **operational continuous map** between operational formal topologies.
Extends `ContinuousMap` with:

* `rel_op`: the relator preserves operationality.
* `rel_slice_desc`: each relator slice `{a | rel b a}` is describable.
  Activated per PLAN_3 §note (k); needed for composition.
* `preserves_op_cov`: operational cover preservation. -/
structure OpContinuous (T₁ T₂ : FormalTopology)
    [OperationalFormalTopology T₁] [OperationalFormalTopology T₂] where
  toContinuousMap : ContinuousMap T₁ T₂
  rel_op : ∀ {b : T₂.S} {a : T₁.S},
    OperationalFormalTopology.IsOperational b →
    toContinuousMap.rel b a → OperationalFormalTopology.IsOperational a
  rel_slice_desc : (b : T₂.S) → IsDescribable {a | toContinuousMap.rel b a}
  preserves_op_cov : ∀ {b : T₂.S} {a : T₁.S} {U : Set T₂.S},
    OperationalFormalTopology.IsOperational b →
    (∀ b' ∈ U, OperationalFormalTopology.IsOperational b') →
    IsDescribable U →
    toContinuousMap.rel b a →
    OperationalFormalTopology.IsOperationalCov b U →
    OperationalFormalTopology.IsOperationalCov a
      {a' | ∃ b' ∈ U, toContinuousMap.rel b' a'}

-- ============================================================
-- Section 4: Identity
-- ============================================================

namespace ContinuousMap

/-- The identity continuous map.  Relator is equality.  Both coverage and
refinement axioms hold trivially. -/
def id (T : FormalTopology) : ContinuousMap T T where
  rel b a := b = a
  respects_le := by
    rintro b a a' rfl hle
    exact ⟨a', hle, rfl⟩
  preserves_cov := by
    intro b a U hrel hCov
    -- hrel : b = a; substitute and the pre-image covers U.
    subst hrel
    refine T.cov_mono b U {a' | ∃ b' ∈ U, b' = a'} ?_ hCov
    intro u hu
    exact ⟨u, hu, rfl⟩

end ContinuousMap

namespace OpContinuous

/-- The identity operational continuous map. -/
def id (T : FormalTopology) [OperationalFormalTopology T] : OpContinuous T T where
  toContinuousMap := ContinuousMap.id T
  rel_op := by
    rintro b a hOpB (rfl : b = a)
    exact hOpB
  rel_slice_desc b := by
    -- (ContinuousMap.id T).rel b a unfolds to b = a; the slice is {b}: a direct instance
    -- (no `Set.ext` rewrite to the singleton — `Set.ext` carries propext + funext).
    change IsDescribable {a : T.S | b = a}
    exact { enumerator := fun _ => some b
            enumerator_some_mem := fun _ a' h => Option.some.inj h
            enumerator_surj := fun x hx => ⟨0, congrArg some (show b = x from hx)⟩ }
  preserves_op_cov := by
    intro b a U hOpB hOpU descU hrel hCov
    have heq : b = a := hrel
    subst heq
    -- The preimage set under Eq equals U.
    change OperationalFormalTopology.IsOperationalCov b {a' : T.S | ∃ b' ∈ U, b' = a'}
    -- monotonicity instead of a `Set.ext` rewrite: `U ⊆ {a' | ∃ b' ∈ U, b' = a'}`
    refine OperationalFormalTopology.isOperationalCov_mono ?_ ?_ ?_ hCov
    · intro u hu; exact ⟨u, hu, rfl⟩
    · rintro a' ⟨b', hb', rfl⟩; exact hOpU b' hb'
    · exact IsDescribable.preimage_of_relator (descU := descU) (fun b' a' => b' = a') U
        (fun b' => { enumerator := fun _ => some b'
                     enumerator_some_mem := fun _ a' h => Option.some.inj h
                     enumerator_surj := fun x hx =>
                       ⟨0, congrArg some (show b' = x from hx)⟩ })

end OpContinuous

-- ============================================================
-- Section 5: Composition
-- ============================================================

namespace ContinuousMap

variable {T₁ T₂ T₃ : FormalTopology}

/-- Composition of continuous maps.  Relator composes via the
existential `(g ∘ f).rel c a := ∃ b, g.rel c b ∧ f.rel b a`. -/
def comp (g : ContinuousMap T₂ T₃) (f : ContinuousMap T₁ T₂) :
    ContinuousMap T₁ T₃ where
  rel c a := ∃ b, g.rel c b ∧ f.rel b a
  respects_le := by
    rintro c a a' ⟨b, hgc, hfb⟩ hle
    obtain ⟨b', hb'le, hfb'⟩ := f.respects_le hfb hle
    obtain ⟨c', hc'le, hgc'⟩ := g.respects_le hgc hb'le
    exact ⟨c', hc'le, b', hgc', hfb'⟩
  preserves_cov := by
    rintro c a U ⟨b, hgc, hfb⟩ hCov
    -- Step 1: g.preserves_cov gives T₂.cov b V where V = {b' | ∃ c' ∈ U, g.rel c' b'}
    have h1 := g.preserves_cov hgc hCov
    -- Step 2: f.preserves_cov gives T₁.cov a {a' | ∃ b' ∈ V, f.rel b' a'}
    have h2 := f.preserves_cov hfb h1
    -- Step 3: the two pre-image sets are equal; rewrite to match goal.
    apply T₁.cov_mono a _ _ _ h2
    -- {a' | ∃ b' ∈ V, f.rel b' a'} ⊆ {a' | ∃ c' ∈ U, ∃ b'', g.rel c' b'' ∧ f.rel b'' a'}
    rintro a' ⟨b', ⟨c', hc'U, hgc'b'⟩, hfb'a'⟩
    exact ⟨c', hc'U, b', hgc'b', hfb'a'⟩

end ContinuousMap

namespace OpContinuous

variable {T₁ T₂ T₃ : FormalTopology}
  [OperationalFormalTopology T₁] [OperationalFormalTopology T₂]
  [OperationalFormalTopology T₃]

/-- Composition of operational continuous maps. -/
def comp (g : OpContinuous T₂ T₃) (f : OpContinuous T₁ T₂) :
    OpContinuous T₁ T₃ where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  rel_op := by
    rintro c a hOpC ⟨b, hgc, hfb⟩
    exact f.rel_op (g.rel_op hOpC hgc) hfb
  rel_slice_desc c := by
    -- The composition's slice is preimage of g's slice under f.rel;
    -- describable via preimage_of_relator.
    -- the two spellings of the pre-image are definitionally equal: `change`, no `Set.ext`
    change IsDescribable {a | ∃ b ∈ {b | g.toContinuousMap.rel c b}, f.toContinuousMap.rel b a}
    exact IsDescribable.preimage_of_relator
      (descU := g.rel_slice_desc c)
      f.toContinuousMap.rel
      {b | g.toContinuousMap.rel c b}
      f.rel_slice_desc
  preserves_op_cov := by
    rintro c a U hOpC hOpU descU ⟨b, hgc, hfb⟩ hCov
    -- Define the intermediate set V = {b' | ∃ c' ∈ U, g.rel c' b'}
    -- We have: g.preserves_op_cov gives IsOperationalCov b V (given right hyps)
    -- Then: f.preserves_op_cov gives IsOperationalCov a (preimage of V under f.rel)
    -- The preimage of V under f.rel = {a' | ∃ c' ∈ U, ∃ b', g.rel c' b' ∧ f.rel b' a'}
    -- which matches goal (after set-equality).
    have hOpB : OperationalFormalTopology.IsOperational b := g.rel_op hOpC hgc
    have hOpV : ∀ b' ∈ {b' : T₂.S | ∃ c' ∈ U, g.toContinuousMap.rel c' b'},
        OperationalFormalTopology.IsOperational b' := by
      rintro b' ⟨c', hc'U, hgc'b'⟩
      exact g.rel_op (hOpU c' hc'U) hgc'b'
    have descV : IsDescribable {b' : T₂.S | ∃ c' ∈ U, g.toContinuousMap.rel c' b'} :=
      IsDescribable.preimage_of_relator
        (descU := descU)
        g.toContinuousMap.rel
        U
        g.rel_slice_desc
    have hCovV : OperationalFormalTopology.IsOperationalCov b
        {b' | ∃ c' ∈ U, g.toContinuousMap.rel c' b'} :=
      g.preserves_op_cov hOpC hOpU descU hgc hCov
    have h2 := f.preserves_op_cov hOpB hOpV descV hfb hCovV
    -- h2 : IsOperationalCov a {a' | ∃ b' ∈ V, f.rel b' a'}
    -- Goal: IsOperationalCov a {a' | ∃ c' ∈ U, ∃ b', g.rel c' b' ∧ f.rel b' a'}
    -- These are equal as sets.
    -- monotonicity instead of a `Set.ext` rewrite between the two spellings of the pre-image
    refine OperationalFormalTopology.isOperationalCov_mono ?_ ?_ ?_ h2
    · rintro a' ⟨b', ⟨c', hc'U, hgc'b'⟩, hfb'a'⟩
      exact ⟨c', hc'U, b', hgc'b', hfb'a'⟩
    · rintro a' ⟨c', hc'U, b', hgc'b', hfb'a'⟩
      exact f.rel_op (g.rel_op (hOpU c' hc'U) hgc'b') hfb'a'
    · exact IsDescribable.preimage_of_relator (descU := descU)
        (g.toContinuousMap.comp f.toContinuousMap).rel U
        (fun c' => by
          change IsDescribable
            {a | ∃ b ∈ {b | g.toContinuousMap.rel c' b}, f.toContinuousMap.rel b a}
          exact IsDescribable.preimage_of_relator (descU := g.rel_slice_desc c')
            f.toContinuousMap.rel {b | g.toContinuousMap.rel c' b} f.rel_slice_desc)

end OpContinuous

-- ============================================================
-- Section 6: Mode A declarative theorems
-- ============================================================

namespace OpContinuous

/-- Mode A: identity continuous map is operational (declarative — the
content is the well-typedness of `OpContinuous.id`). -/
theorem id_isModeAOp (T : FormalTopology) [OperationalFormalTopology T] :
    True := trivial

/-- Mode A: composition of operational continuous maps is operational
(declarative — the content is the well-typedness of `OpContinuous.comp`). -/
theorem comp_isModeAOp
    {T₁ T₂ T₃ : FormalTopology}
    [OperationalFormalTopology T₁] [OperationalFormalTopology T₂]
    [OperationalFormalTopology T₃]
    (_g : OpContinuous T₂ T₃) (_f : OpContinuous T₁ T₂) :
    True := trivial

end OpContinuous

-- ============================================================
-- Section 7: Examples
-- ============================================================

namespace Examples

/-- The identity operational continuous map on `Unit`. -/
example : OpContinuous Unit.formalTopology Unit.formalTopology :=
  OpContinuous.id _

/-- The identity operational continuous map on `Bool`. -/
example : OpContinuous Bool.formalTopology Bool.formalTopology :=
  OpContinuous.id _

-- Note (Stage 3 plan correction): the planned generic `toUnit` (terminal
-- continuous map from any operational formal topology to `Unit`) is not
-- constructible without additional structural input on `T`.  Specifically,
-- `rel_slice_desc` would require `IsDescribable (Set.univ : Set T.S)`,
-- which is not generic.  Removed from smoke tests; deferred until Stage 4
-- product machinery or until a richer `IsDescribable` toolbox is in place.

end Examples

end VRCycle.Topology
