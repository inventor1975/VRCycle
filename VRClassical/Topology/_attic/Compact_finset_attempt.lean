-- VRCycle/Topology/Compact.lean
-- VR-Topology v1.0.0 — Stage 5: Operational compact formal topology.
--
-- Vickers F-witness compactness for formal topology (Vickers 2005/2007,
-- "Some Constructive Roads to Tychonoff", Theorem 0.4).  Constructive,
-- predicative; no `Classical.choice` required.
--
-- Plan corrections (Stage 5):
--
-- * Finding T11: PLAN_5 §6 Bool F-witness `{S | S = ∅ ∨ true ∈ S ∨ false ∈ S}`
--   is incorrect.  `generators_covered` requires `T.cov g ↑S` for every
--   generator `g`; for Bool's discrete topology, only `{true, false}`
--   covers both generators.  Corrected to `F := {{true, false}}`.
--
-- * `CompactWitness` takes `basicCov` as a parameter rather than reading
--   from `T.basicCov` — `FormalTopology` doesn't carry the basic-cover
--   presentation, only `OperationalFormalTopology` does.  `OperationalCompact`
--   instantiates `basicCov := self.basicCov` from the operational instance.

import VRCycle.Topology.Product
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 1: lowerOrder on Finset
-- ============================================================

namespace FormalTopology

/-- The **lower order** on finite sets: `lowerOrder le A B` iff every
element of `A` is refined by some element of `B`.  Vickers's `vL`. -/
def lowerOrder {S : Type*} (le : S → S → Prop) (A B : Finset S) : Prop :=
  ∀ a ∈ A, ∃ b ∈ B, le a b

theorem lowerOrder_refl {S : Type*} (le : S → S → Prop)
    (refl : ∀ a, le a a) (A : Finset S) : lowerOrder le A A := by
  intro a ha
  exact ⟨a, ha, refl a⟩

theorem lowerOrder_trans {S : Type*} (le : S → S → Prop)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (A B C : Finset S) (hAB : lowerOrder le A B) (hBC : lowerOrder le B C) :
    lowerOrder le A C := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := hAB a ha
  obtain ⟨c, hc, hbc⟩ := hBC b hb
  exact ⟨c, hc, trans _ _ _ hab hbc⟩

end FormalTopology

-- ============================================================
-- Section 2: CompactWitness structure
-- ============================================================

/-- **Vickers's compactness witness** for a formal topology with a given
basic cover presentation.  `F : Set (Finset T.S)` is a set of finite covers
satisfying four closure conditions (Vickers's Theorem 0.4):

1. `upper_closed`: closed under `lowerOrder` refinement.
2. `inhabited`: at least one cover.
3. `cover_closure`: refinement of basic covers preserves membership in F.
4. `generators_covered`: every cover in F actually covers every generator. -/
structure CompactWitness (T : FormalTopology) (basicCov : T.S → Set T.S → Prop)
    [DecidableEq T.S] where
  F : Set (Finset T.S)
  upper_closed : ∀ A ∈ F, ∀ B : Finset T.S,
                  FormalTopology.lowerOrder T.le A B → B ∈ F
  inhabited : F.Nonempty
  cover_closure : ∀ {a : T.S} {U : Set T.S} {T' : Finset T.S},
                   basicCov a U →
                   insert a T' ∈ F →
                   ∃ U₀ : Finset T.S, (↑U₀ : Set T.S) ⊆ U ∧ (U₀ ∪ T') ∈ F
  generators_covered : ∀ S ∈ F, ∀ g : T.S, T.cov g ↑S

-- ============================================================
-- Section 3: OperationalCompact class
-- ============================================================

/-- **Operational compactness** combines Vickers's `CompactWitness` (using
the operational presentation's basic cover) with two invariants:

* `witness_operational`: every element of every F-cover is operational.
* `witness_describable`: every F-cover is describable.

Together these ensure that compactness is operationally accessible — the
key property for the Stage 6 Mode B audit (binary Tychonoff). -/
class OperationalCompact (T : FormalTopology)
    [self : OperationalFormalTopology T] [DecidableEq T.S] where
  witness : CompactWitness T self.basicCov
  witness_operational : ∀ S ∈ witness.F, ∀ x ∈ S,
                         OperationalFormalTopology.IsOperational x
  witness_describable : ∀ S ∈ witness.F,
                         IsDescribable (↑S : Set T.S)

-- ============================================================
-- Section 4: Apparatus placeholder
-- ============================================================

/-- Placeholder marker: `OperationalCompact` is the Mode B audit target.
Full apparatus integration (via `IsModeBOp`-style certificates) deferred
to Stage 6, when concrete use cases reveal the integration shape. -/
theorem OperationalCompact.markedAsModeBTarget
    (T : FormalTopology)
    [OperationalFormalTopology T] [DecidableEq T.S] [OperationalCompact T] :
    True := trivial

-- ============================================================
-- Section 5: skipped — generic Finset.toDescribable dropped
-- ============================================================
--
-- Finding T12 (plan correction): PLAN_5 §5 planned a generic
-- `Finset.toDescribable` instance via `Finset.toList`.  But `Finset.toList`
-- is `noncomputable` in mathlib (uses `Classical.choice` via
-- `Multiset.toList`'s `Quot.unquot`).  This would violate Stage 5's
-- halt-condition ("Classical.choice through Finset → halt").
--
-- A `LinearOrder`-based version via `Finset.sort` is computable, but
-- requires a stronger typeclass than `DecidableEq` and isn't needed for
-- Stage 5's trivial instances.  Generic version deferred; describability
-- provided inline per instance below.

-- ============================================================
-- Section 6: Trivial instances
-- ============================================================

-- `Unit.formalTopology` and `Bool.formalTopology` are `@[reducible]` (Stage 1
-- retroactive amendment), but Lean's typeclass synthesis doesn't reduce `.S`
-- through `ofPresentation` automatically.  Provide explicit `DecidableEq`
-- instances for these specific cases.

instance instDecEqUnitFormalTopologyS :
    DecidableEq Examples.Unit.formalTopology.S :=
  (inferInstance : DecidableEq Unit)

instance instDecEqBoolFormalTopologyS :
    DecidableEq Examples.Bool.formalTopology.S :=
  (inferInstance : DecidableEq Bool)

/-- The unit formal topology is operationally compact.  F-witness: all
finite subsets of `Unit` (which has only `∅` and `{()}`).
Declared outside `namespace Examples` with qualified `Examples.Unit.formalTopology`
to avoid Lean's namespace-resolution ambiguity with dotted instance names. -/
instance Examples.instUnitOperationalCompact :
    OperationalCompact Examples.Unit.formalTopology where
  witness := {
    F := (Set.univ : Set (Finset Unit))
    upper_closed := by
      intros A _ B _
      trivial
    inhabited := ⟨∅, trivial⟩
    cover_closure := by
      intro a U T' _ _
      refine ⟨∅, ?_, ?_⟩
      · simp
      · trivial
    generators_covered := by
      intro S _ g
      -- Unit's basic cov is `fun _ _ => True`, so any set is a basic cover.
      exact CoverGen.basic True.intro
  }
  witness_operational := by
    intros S _ x _
    trivial  -- Unit's IsOperational is `fun _ => True`
  witness_describable := by
    intro S _
    -- ↑S : Set Unit.formalTopology.S. Case on whether () ∈ S.
    by_cases h : () ∈ S
    · have heq : (↑S : Set Unit.formalTopology.S) =
                  ({()} : Set Unit.formalTopology.S) := by
        ext x; cases x
        exact ⟨fun _ => rfl, fun _ => h⟩
      rw [heq]
      exact IsDescribable.instSingleton _
    · have heq : (↑S : Set Unit.formalTopology.S) =
                  (∅ : Set Unit.formalTopology.S) := by
        ext x; cases x
        exact ⟨fun hx => h hx, fun hx => hx.elim⟩
      rw [heq]
      exact IsDescribable.instEmpty

/-- The discrete two-element formal topology `Bool` is operationally
compact.  F-witness: only `{true, false}` (the full set) — this is the
unique cover that contains every generator.  PLAN_5 §6 suggestion
`{S | S = ∅ ∨ true ∈ S ∨ false ∈ S}` was incorrect (Finding T11):
singletons `{true}` and `{false}` do not cover both generators in the
discrete topology. -/
instance Examples.instBoolOperationalCompact :
    OperationalCompact Examples.Bool.formalTopology where
  witness := {
    F := ({({true, false} : Finset Bool)} : Set (Finset Bool))
    upper_closed := by
      intro A hA B hAB
      have hA_eq : A = ({true, false} : Finset Bool) := hA
      subst hA_eq
      -- lowerOrder Eq {true, false} B: ∀ a ∈ {true, false}, ∃ b ∈ B, a = b
      have htrue : true ∈ B := by
        obtain ⟨b, hb, hab⟩ := hAB true (by decide)
        have heq : true = b := hab
        rw [heq]; exact hb
      have hfalse : false ∈ B := by
        obtain ⟨b, hb, hab⟩ := hAB false (by decide)
        have heq : false = b := hab
        rw [heq]; exact hb
      change B ∈ ({({true, false} : Finset Bool)} : Set (Finset Bool))
      have hB_eq : B = ({true, false} : Finset Bool) := by
        apply Finset.ext
        intro x
        constructor
        · intro _; cases x <;> decide
        · intro _; cases x; exacts [hfalse, htrue]
      exact hB_eq
    inhabited := ⟨({true, false} : Finset Bool), rfl⟩
    cover_closure := by
      intro a U T' hbasic hins
      have hins_eq : insert a T' = ({true, false} : Finset Bool) := hins
      refine ⟨({a} : Finset Bool), ?_, ?_⟩
      · -- ↑({a} : Finset Bool) ⊆ U: a ∈ U from hbasic
        intro x hx
        have hxa : x ∈ ({a} : Finset Bool.formalTopology.S) := hx
        rw [Finset.mem_singleton] at hxa
        rw [hxa]; exact hbasic
      · -- ({a} : Finset Bool) ∪ T' ∈ {{true, false}}
        change ({a} : Finset Bool) ∪ T' ∈ ({({true, false} : Finset Bool)} : Set _)
        have h_eq : ({a} : Finset Bool) ∪ T' = insert a T' :=
          (Finset.insert_eq a T').symm
        rw [h_eq, hins_eq]
        rfl
    generators_covered := by
      intro S hS g
      have hS_eq : S = ({true, false} : Finset Bool) := hS
      subst hS_eq
      apply CoverGen.basic
      change g ∈ (↑({true, false} : Finset Bool) : Set Bool)
      cases g <;> decide
  }
  witness_operational := by
    intros S _ x _
    trivial
  witness_describable := by
    intro S hS
    have hS_eq : S = ({true, false} : Finset Bool) := hS
    subst hS_eq
    -- Change goal to expose Set Bool form
    change IsDescribable (↑({true, false} : Finset Bool) : Set Bool)
    have h_eq : (↑({true, false} : Finset Bool) : Set Bool) = (Set.univ : Set Bool) := by
      ext x
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      cases x <;> decide
    rw [h_eq]
    exact IsDescribable.instBoolUniv

-- ============================================================
-- Section 7: Classical-compactness bridge (declarative placeholder)
-- ============================================================

/-- Declarative marker: F-witness compactness is the constructive form of
classical "every cover has finite subcover".  Full equivalence theorem
deferred to Stage 7 (bridge to mathlib) if needed. -/
theorem CompactWitness.implies_classical_compact
    (T : FormalTopology) (basicCov : T.S → Set T.S → Prop)
    [DecidableEq T.S] (_w : CompactWitness T basicCov) : True := trivial

end VRCycle.Topology
