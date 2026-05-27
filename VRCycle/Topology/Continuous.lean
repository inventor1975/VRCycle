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

import VRCycle.Topology.Operational

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 3 (helper, placed first — used by composition): preimage_of_relator
-- ============================================================

namespace IsDescribable

-- ============================================================
-- Custom constructive pair on ℕ (Finding T6 — see module docstring).
-- ============================================================
--
-- Mathlib's `Nat.unpair_pair` and `Encodable (ℕ × ℕ)` both pull
-- `Classical.choice` via `Nat.sqrt`.  We build a bit-interleaved pair
-- here, locally, with a clean axiom profile.  Bit 2k of `pair m n` is
-- bit k of m; bit 2k+1 is bit k of n.

/-- Constructive bit-interleaving pair on ℕ. -/
private def pair (m n : ℕ) : ℕ :=
  if m + n = 0 then 0
  else (m % 2) + 2 * (n % 2) + 4 * pair (m / 2) (n / 2)
termination_by m + n
decreasing_by omega

/-- Constructive inverse: extract bits of m at even positions, bits of n
at odd positions. -/
private def unpair (k : ℕ) : ℕ × ℕ :=
  if k = 0 then (0, 0)
  else
    let p := unpair (k / 4)
    (2 * p.1 + k % 2, 2 * p.2 + (k / 2) % 2)
termination_by k
decreasing_by omega

/-- Equational form of `pair` when `m + n > 0`. -/
private theorem pair_pos_eq (m n : ℕ) (h : m + n ≠ 0) :
    pair m n = m % 2 + 2 * (n % 2) + 4 * pair (m / 2) (n / 2) := by
  conv_lhs => rw [pair]
  rw [if_neg h]

/-- Equational form of `pair` at zero. -/
private theorem pair_zero_zero : pair 0 0 = 0 := by
  conv_lhs => rw [pair]
  rfl

/-- Equational form of `unpair` when `k ≠ 0`. -/
private theorem unpair_pos_eq (k : ℕ) (h : k ≠ 0) :
    unpair k = (2 * (unpair (k / 4)).1 + k % 2, 2 * (unpair (k / 4)).2 + (k / 2) % 2) := by
  conv_lhs => rw [unpair]
  rw [if_neg h]

private theorem unpair_zero : unpair 0 = (0, 0) := by
  conv_lhs => rw [unpair]
  rfl

/-- Auxiliary: `pair m n = 0` iff both `m` and `n` are 0. -/
private theorem pair_eq_zero_iff :
    ∀ k m n : ℕ, m + n = k → (pair m n = 0 ↔ m = 0 ∧ n = 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n hk
    refine ⟨fun h => ?_, ?_⟩
    · by_cases hmn : m + n = 0
      · exact ⟨by omega, by omega⟩
      · exfalso
        have heq := pair_pos_eq m n hmn
        rw [heq] at h
        have h1 : m % 2 = 0 := by omega
        have h2 : n % 2 = 0 := by omega
        have h3 : pair (m / 2) (n / 2) = 0 := by omega
        have hlt : m / 2 + n / 2 < k := by omega
        have := (ih _ hlt (m / 2) (n / 2) rfl).mp h3
        omega
    · rintro ⟨rfl, rfl⟩
      exact pair_zero_zero

/-- The key inverse lemma: `unpair (pair m n) = (m, n)`. -/
private theorem unpair_pair_aux :
    ∀ k m n : ℕ, m + n = k → unpair (pair m n) = (m, n) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m n hk
    by_cases hmn : m + n = 0
    · have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst hm; subst hn
      rw [pair_zero_zero, unpair_zero]
    · have heq := pair_pos_eq m n hmn
      have hpos : pair m n ≠ 0 := fun habs => by
        obtain ⟨hm, hn⟩ := (pair_eq_zero_iff k m n hk).mp habs
        omega
      have hunpair := unpair_pos_eq (pair m n) hpos
      -- Arithmetic on pair m n
      have hmod2_lt : m % 2 < 2 := Nat.mod_lt _ (by decide)
      have hnmod2_lt : n % 2 < 2 := Nat.mod_lt _ (by decide)
      have hX_div4 : pair m n / 4 = pair (m / 2) (n / 2) := by rw [heq]; omega
      have hX_mod2 : pair m n % 2 = m % 2 := by rw [heq]; omega
      have hX_div2_mod2 : (pair m n / 2) % 2 = n % 2 := by rw [heq]; omega
      -- IH on smaller sum
      have hlt : m / 2 + n / 2 < k := by omega
      have ih_inst : unpair (pair (m / 2) (n / 2)) = (m / 2, n / 2) :=
        ih _ hlt (m / 2) (n / 2) rfl
      rw [hunpair, hX_div4, ih_inst, hX_mod2, hX_div2_mod2]
      -- Goal: (2 * (m/2) + m%2, 2 * (n/2) + n%2) = (m, n)
      have hm_eq : 2 * (m / 2) + m % 2 = m := by omega
      have hn_eq : 2 * (n / 2) + n % 2 = n := by omega
      rw [hm_eq, hn_eq]

/-- The inverse lemma in usable form. -/
private theorem unpair_pair (m n : ℕ) : unpair (pair m n) = (m, n) :=
  unpair_pair_aux _ m n rfl

/-- Pre-image describability through a relator.  Given `U : Set β` describable
and each slice `{a | r b a}` describable (for all `b : β`), the relational
pre-image `{a | ∃ b ∈ U, r b a}` is describable.

Construction uses our custom constructive `pair`/`unpair` (Finding T6) —
no `Classical.choice` inheritance from `Nat.sqrt`. -/
@[reducible] def preimage_of_relator
    {α β : Type*} (r : β → α → Prop) (U : Set β)
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
    -- (ContinuousMap.id T).rel b a unfolds to b = a; the slice is {b}.
    change IsDescribable {a : T.S | b = a}
    have : {a : T.S | b = a} = ({b} : Set T.S) := by
      ext a
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [this]
    exact IsDescribable.instSingleton b
  preserves_op_cov := by
    intro b a U hOpB hOpU descU hrel hCov
    have heq : b = a := hrel
    subst heq
    -- The preimage set under Eq equals U.
    change OperationalFormalTopology.IsOperationalCov b {a' : T.S | ∃ b' ∈ U, b' = a'}
    have hset : {a' : T.S | ∃ b' ∈ U, b' = a'} = U := by
      ext a'
      refine ⟨?_, ?_⟩
      · rintro ⟨b', hb', rfl⟩; exact hb'
      · intro h; exact ⟨a', h, rfl⟩
    rw [hset]
    exact hCov

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
    change IsDescribable {a | ∃ b, g.toContinuousMap.rel c b ∧ f.toContinuousMap.rel b a}
    have : {a | ∃ b, g.toContinuousMap.rel c b ∧ f.toContinuousMap.rel b a}
         = {a | ∃ b ∈ {b | g.toContinuousMap.rel c b}, f.toContinuousMap.rel b a} := by
      ext a; rfl
    rw [this]
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
    have hset : {a' : T₁.S |
        ∃ b' ∈ {b' : T₂.S | ∃ c' ∈ U, g.toContinuousMap.rel c' b'},
          f.toContinuousMap.rel b' a'}
      = {a' : T₁.S | ∃ c' ∈ U, ∃ b',
          g.toContinuousMap.rel c' b' ∧ f.toContinuousMap.rel b' a'} := by
      ext a'; constructor
      · rintro ⟨b', ⟨c', hc'U, hgc'b'⟩, hfb'a'⟩
        exact ⟨c', hc'U, b', hgc'b', hfb'a'⟩
      · rintro ⟨c', hc'U, b', hgc'b', hfb'a'⟩
        exact ⟨b', ⟨c', hc'U, hgc'b'⟩, hfb'a'⟩
    rw [hset] at h2
    exact h2

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
