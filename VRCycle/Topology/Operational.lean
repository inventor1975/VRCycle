-- VRCycle/Topology/Operational.lean
-- VR-Topology v1.0.0 — Stage 2: Operational predicate layer.
--
-- Adds the operational layer to formal topology.  Operational predicate lives
-- on the presentation (`basicCov`); operational status flows through the
-- coverage relation via the parallel inductive `OpCoverGen` that carries
-- operational + describability witnesses inside its constructors.
--
-- Design decisions (Stage 2, recorded as findings):
--
-- * Finding T3 (Stage 1→2 plan correction).  `IsDescribable` is declared as
--   a data class with explicit `Option`-valued `enumerator : ℕ → Option α`,
--   not as a `Prop` with `∃ f : ℕ → α, ...` per PLAN_2 §1.  Rationale:
--   `Prop`-form forces `Classical.choice` to extract `f` for derived
--   constructions (binary_union, etc.), violating Stage 2's target axiom
--   profile.  Data form keeps constructive baseline.  `Option` allows the
--   empty set to be describable (no element to enumerate) and is the
--   `mathlib`-standard pattern (`Encodable`).
--
-- * Finding T4 (Stage 2 pre-implementation halt — bridge insufficiency).
--   Structural induction on `CoverGen le basicCov a U` does not close in
--   the `trans` case: the intermediate cover `U₀` is existentially absorbed
--   by the constructor and the inductive hypothesis cannot be invoked
--   without operational + describability witnesses for `U₀`.  Resolution:
--   parallel inductive `OpCoverGen op le basicCov a U` which carries
--   operational and describability witnesses inside each constructor.
--   `OpCoverGen ⊆ CoverGen` via a forgetful map (`OpCoverGen.toCoverGen`).
--   Operational covers are operational-good covers — not all
--   `CoverGen`-generated covers.
--
-- * Variant P (PLAN_2 design decision §0).  Operational predicate is at
--   the presentation level (on `basicCov`), not at closure level (on
--   `CoverGen`).  This matches the established cycle pattern from
--   VR-Algebra and VR-Audit.

import VRCycle.Topology.FormalTopology
import VRCycle.Apparatus.Wrapping

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 1: IsDescribable typeclass (data form — Finding T3)
-- ============================================================

/-- A set `s : Set α` is **describable** if there is a constructive
enumeration `ℕ → Option α` whose image-with-`some` is exactly `s`.

This is the data form (not a `Prop`): the enumerator is explicit, accessible
without `Classical.choice`.  Empty sets are describable via `fun _ => none`. -/
class IsDescribable {α : Type*} (s : Set α) where
  /-- An enumeration of `s` via natural numbers.  `none` indicates a skipped index. -/
  enumerator : ℕ → Option α
  /-- Every `some`-value of `enumerator` is in `s`. -/
  enumerator_some_mem : ∀ n a, enumerator n = some a → a ∈ s
  /-- Every element of `s` is hit by some `enumerator n`. -/
  enumerator_surj : ∀ x ∈ s, ∃ n, enumerator n = some x

namespace IsDescribable

/-- The empty set is describable: the enumerator returns `none` everywhere. -/
instance instEmpty {α : Type*} : IsDescribable (∅ : Set α) where
  enumerator _ := none
  enumerator_some_mem n a h := by cases h
  enumerator_surj x hx := hx.elim

/-- A singleton is describable: the enumerator returns `some a` everywhere. -/
instance instSingleton {α : Type*} (a : α) : IsDescribable ({a} : Set α) where
  enumerator _ := some a
  enumerator_some_mem _ a' h := by
    have hyp : a = a' := by injection h
    change a' ∈ ({a} : Set α)
    exact hyp.symm
  enumerator_surj x hx := by
    refine ⟨0, ?_⟩
    have : x = a := hx
    simp [this]

/-- The whole universe of `Bool` is describable. -/
instance instBoolUniv : IsDescribable (Set.univ : Set Bool) where
  enumerator
    | 0 => some false
    | 1 => some true
    | _ => none
  enumerator_some_mem n a h := by
    match n, h with
    | 0, _ => exact Set.mem_univ _
    | 1, _ => exact Set.mem_univ _
  enumerator_surj x _ := by
    cases x with
    | false => exact ⟨0, rfl⟩
    | true => exact ⟨1, rfl⟩

/-- The whole universe of `Unit` is describable. -/
instance instUnitUniv : IsDescribable (Set.univ : Set Unit) where
  enumerator _ := some ()
  enumerator_some_mem _ a _ := Set.mem_univ a
  enumerator_surj x _ := ⟨0, by cases x; rfl⟩

/-- Binary union of describable sets is describable, by interleaving
the two enumerations (even indices from `s`, odd indices from `t`).
Constructive: no `Classical.choice`. -/
@[reducible] def binaryUnion {α : Type*} (s t : Set α) [hs : IsDescribable s]
    [ht : IsDescribable t] : IsDescribable (s ∪ t) where
  enumerator n :=
    if n % 2 = 0 then hs.enumerator (n / 2) else ht.enumerator (n / 2)
  enumerator_some_mem n a h := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn] at h
      exact Or.inl (hs.enumerator_some_mem _ _ h)
    · rw [if_neg hn] at h
      exact Or.inr (ht.enumerator_some_mem _ _ h)
  enumerator_surj x hx := by
    cases hx with
    | inl h =>
        obtain ⟨n, hn⟩ := hs.enumerator_surj x h
        refine ⟨2 * n, ?_⟩
        have h1 : (2 * n) % 2 = 0 := by omega
        have h2 : (2 * n) / 2 = n := by omega
        simp [h1, h2, hn]
    | inr h =>
        obtain ⟨n, hn⟩ := ht.enumerator_surj x h
        refine ⟨2 * n + 1, ?_⟩
        have h1 : (2 * n + 1) % 2 = 1 := by omega
        have h2 : (2 * n + 1) / 2 = n := by omega
        simp [h1, h2, hn]

end IsDescribable

-- ============================================================
-- Section 2: OpCoverGen — operational cover generator (Finding T4)
-- ============================================================

/-- The **operational cover generator**.  Parallel to `CoverGen`, but each
constructor carries witnesses that the relevant elements are operational
(via `op`) and the relevant cover families are describable (via `IsDescribable`).

By construction, every `OpCoverGen op le basicCov a U` term certifies:
- `op a` and `∀ b ∈ U, op b` (operational base + operational cover family),
- `IsDescribable U` (cover family enumerable).

This is the inductive structure that makes operational status survive
through coverage axioms — see Finding T4 in module docstring. -/
inductive OpCoverGen {S : Type*} (op : S → Prop) (le : S → S → Prop)
    (basicCov : S → Set S → Prop) : S → Set S → Prop where
  | basic    : ∀ {a : S} {U : Set S}, op a → (∀ b ∈ U, op b) →
               IsDescribable U → basicCov a U →
               OpCoverGen op le basicCov a U
  | mem      : ∀ {a : S} {U : Set S}, op a → (∀ b ∈ U, op b) →
               IsDescribable U → a ∈ U →
               OpCoverGen op le basicCov a U
  | trans    : ∀ {a : S} {U V : Set S},
               OpCoverGen op le basicCov a U →
               (∀ b ∈ U, OpCoverGen op le basicCov b V) →
               OpCoverGen op le basicCov a V
  | ref_mono : ∀ {a b : S} {U : Set S}, op a → op b → le a b →
               OpCoverGen op le basicCov b U →
               OpCoverGen op le basicCov a U
  | local_   : ∀ {a b : S} {U : Set S}, op a → op b → le a b →
               OpCoverGen op le basicCov a U →
               IsDescribable {c ∈ U | le c b} →
               OpCoverGen op le basicCov a {c ∈ U | le c b}
  | meet     : ∀ {a : S} {U V : Set S},
               OpCoverGen op le basicCov a U →
               OpCoverGen op le basicCov a V →
               OpCoverGen op le basicCov a (commonRefinement le U V)

-- ============================================================
-- Section 2 (cont.): OperationalFormalTopology typeclass
-- ============================================================

/-- An **operational formal topology** equips a `FormalTopology` with:
- an operational predicate on base elements (`IsOperational`);
- a presentation by basic covers (`basicCov`), with operational status carried
  via the parallel inductive `OpCoverGen`.

The four `cov_*_op` "axioms" of PLAN_2 §2 are derived as theorems from
`OpCoverGen`'s constructors — they are no longer typeclass fields. -/
class OperationalFormalTopology (T : FormalTopology) where
  /-- Operational predicate on base elements. -/
  IsOperational : T.S → Prop
  /-- The basic-cover presentation underlying the operational structure. -/
  basicCov : T.S → Set T.S → Prop
  /-- **Finding T19**: operationality propagates up the refinement order.
  If `T.le a b` and `a` is operational, then `b` is operational.

  Conceptual justification: in Sambin-style operational formal topology,
  operationality is the property that an element has a constructive
  presentation.  If `a` is operational and `b` is a coarser refinement
  (`T.le a b`), then `b`'s presentation derives from `a`'s.

  This field is necessary for Stage 6b — `prodF_op_upper_closed` — to
  derive operationality of B from operationality of A and `A vL B`. -/
  op_preserved_by_le : ∀ {a b : T.S}, T.le a b → IsOperational a → IsOperational b

/-- The operational cover predicate: a set is operationally covered if it
is reachable by `OpCoverGen` from the operational presentation. -/
abbrev OperationalFormalTopology.IsOperationalCov {T : FormalTopology}
    [self : OperationalFormalTopology T] (a : T.S) (U : Set T.S) : Prop :=
  OpCoverGen self.IsOperational T.le self.basicCov a U

-- ============================================================
-- Section 3: Apparatus instance
-- ============================================================

/-- `OperationalFormalTopology` integrates with VR-Apparatus via
`PredicateOperationality` on the base type, with `IsOperational` as the
operational predicate.  The `PredicateOperationality` class is a marker
(zero-field `Prop`), so this instance is trivial. -/
instance opFormalTopologyPredicate (T : FormalTopology)
    [self : OperationalFormalTopology T] :
    VR.Apparatus.PredicateOperationality T.S self.IsOperational := ⟨⟩

-- ============================================================
-- Section 4: Forgetful map — OpCoverGen ⊆ CoverGen
-- ============================================================

/-- Every operational cover is, in particular, a cover.  This is the
"forgetful" direction: discard operational + describability witnesses. -/
theorem OpCoverGen.toCoverGen {S : Type*} {op : S → Prop} {le : S → S → Prop}
    {basicCov : S → Set S → Prop} {a : S} {U : Set S}
    (h : OpCoverGen op le basicCov a U) : CoverGen le basicCov a U := by
  induction h with
  | basic _ _ _ hb => exact .basic hb
  | mem _ _ _ hm => exact .mem hm
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | ref_mono _ _ hab _ ih => exact .ref_mono hab ih
  | local_ _ _ hab _ _ ih => exact .local_ hab ih
  | meet _ _ ih₁ ih₂ => exact .meet ih₁ ih₂

-- ============================================================
-- Section 4 (cont.): Bridge theorem — OpCoverGen.toOpCov
-- ============================================================

/-- The **bridge theorem**: operational status on the presentation
(`basicCov_op`) plus closure properties of `opCov` (matching `OpCoverGen`'s
five constructors) propagate through the inductive structure to give
operational status on the closure.

This is the technical core of Stage 2.  Proof is mechanical structural
induction on `OpCoverGen` — five cases, each applies the corresponding
hypothesis directly. -/
theorem OpCoverGen.toOpCov {S : Type*} {op : S → Prop} {le : S → S → Prop}
    {basicCov : S → Set S → Prop} (opCov : S → Set S → Prop)
    (basicCov_op : ∀ {a U}, op a → (∀ b ∈ U, op b) → IsDescribable U →
                   basicCov a U → opCov a U)
    (mem_op : ∀ {a U}, op a → (∀ b ∈ U, op b) → IsDescribable U →
              a ∈ U → opCov a U)
    (trans_op : ∀ {a U V}, opCov a U → (∀ b ∈ U, opCov b V) → opCov a V)
    (ref_mono_op : ∀ {a b U}, op a → op b → le a b → opCov b U → opCov a U)
    (local_op : ∀ {a b U}, op a → op b → le a b → opCov a U →
                IsDescribable {c ∈ U | le c b} →
                opCov a {c ∈ U | le c b})
    (meet_op : ∀ {a U V}, opCov a U → opCov a V →
               opCov a (commonRefinement le U V))
    {a : S} {U : Set S} (h : OpCoverGen op le basicCov a U) : opCov a U := by
  induction h with
  | basic ha hU dU hb => exact basicCov_op ha hU dU hb
  | mem ha hU dU hm => exact mem_op ha hU dU hm
  | trans _ _ ih₁ ih₂ => exact trans_op ih₁ (fun b hb => ih₂ b hb)
  | ref_mono ha hb hab _ ih => exact ref_mono_op ha hb hab ih
  | local_ ha hb hab _ dr ih => exact local_op ha hb hab ih dr
  | meet _ _ ih₁ ih₂ => exact meet_op ih₁ ih₂

-- ============================================================
-- Section 5: OperationalFormalTopology.ofPresentation
-- ============================================================

/-- Build an `OperationalFormalTopology` from an operational presentation:
a preorder, basic covers, and an operational predicate on base elements.

The underlying `FormalTopology` is `FormalTopology.ofPresentation`. -/
@[reducible] def OperationalFormalTopology.ofPresentation
    (S : Type*)
    (le : S → S → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ a b c, le a b → le b c → le a c)
    (basicCov : S → Set S → Prop)
    (op : S → Prop)
    (op_le : ∀ {a b : S}, le a b → op a → op b) :
    OperationalFormalTopology
      (FormalTopology.ofPresentation S le le_refl le_trans basicCov) where
  IsOperational := op
  basicCov := basicCov
  op_preserved_by_le := op_le

-- ============================================================
-- Section 6: Mode A theorems — operational status preservation
-- ============================================================

namespace OperationalFormalTopology

variable {T : FormalTopology} [self : OperationalFormalTopology T]

/-- Operational cover is monotone in the cover family: enlarging an
operational cover to a describable operational superset preserves
operational cover status.  Proof: invoke `OpCoverGen.trans` with the
trivial `mem`-cover at each smaller element. -/
theorem isOperationalCov_mono
    {a : T.S} {U V : Set T.S}
    (hUV : U ⊆ V)
    (opV : ∀ x ∈ V, self.IsOperational x)
    (descV : IsDescribable V)
    (hopU : IsOperationalCov a U) :
    IsOperationalCov a V := by
  refine .trans hopU (fun b hb => ?_)
  exact .mem (opV b (hUV hb)) opV descV (hUV hb)

end OperationalFormalTopology

-- ============================================================
-- Section 7: Operational instances for smoke-test examples
-- ============================================================

namespace Examples

/-- Trivial operational structure on the unit formal topology:
every element is operational, the basic cover is the trivial relation. -/
instance Unit.operationalFormalTopology :
    OperationalFormalTopology Unit.formalTopology where
  IsOperational _ := True
  basicCov _ _ := True
  op_preserved_by_le _ _ := trivial

/-- Trivial operational structure on the discrete two-element formal
topology: every element is operational, the basic cover is the
membership relation (matching Stage 1's `Bool.formalTopology`). -/
instance Bool.operationalFormalTopology :
    OperationalFormalTopology Bool.formalTopology where
  IsOperational _ := True
  basicCov a U := a ∈ U
  op_preserved_by_le _ _ := trivial

end Examples

end VRCycle.Topology
