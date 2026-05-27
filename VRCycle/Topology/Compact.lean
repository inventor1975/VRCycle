-- VRCycle/Topology/Compact.lean
-- VR-Topology v1.0.0 — Stage 5: Operational compact formal topology.
--
-- Vickers F-witness compactness for formal topology (Vickers 2005/2007,
-- "Some Constructive Roads to Tychonoff", Theorem 0.4).  Constructive,
-- predicative; no `Classical.choice`.
--
-- **Finding T13**: First-attempt formulation (PLAN_5 §6, using `Finset`)
-- failed Stage 5 axiom audit — mathlib's `Finset` infrastructure
-- transitively imports `Classical.choice` via `Multiset.toList` /
-- `Quot.unquot`.  Strict constructive baseline cannot use mathlib's
-- `Finset`.  Resolution: replace `Finset T.S` with `List T.S` everywhere.
-- Lean core's `List` carries no Classical dependency.  Vickers's F-witness
-- semantics are preserved (sets of finite covers are sets-of-lists of
-- base elements).  See `_attic/Compact_finset_attempt.lean` for the
-- discarded Finset-based draft.
--
-- Finding T13 is the fourth instance of mathlib upstream Classical
-- inheritance discovered in VR-Topology (after T1 universe issue with
-- Nat.sqrt, T6 Nat.unpair_pair, and the constructibility issues that led
-- to T7).  Pattern: strict constructive Lean work requires careful
-- verification of mathlib import dependencies.
--
-- Plan corrections beyond T13:
--
-- * Finding T11: PLAN_5 §6 Bool F-witness `{S | S = ∅ ∨ true ∈ S ∨ false ∈ S}`
--   is incorrect.  Corrected to "lists containing both true and false".
--
-- * `CompactWitness` takes `basicCov` as a parameter rather than reading
--   from `T.basicCov`.

import VRCycle.Topology.Product

namespace VRCycle.Topology

universe u

-- ============================================================
-- Section 1: lowerOrder on List (Vickers's `vL`)
-- ============================================================

namespace FormalTopology

/-- The **lower order** on lists: `listLowerOrder le A B` iff every
element of `A` is refined by some element of `B`.  Vickers's `vL`,
adapted to lists (List in Lean core; no `Classical.choice`). -/
def listLowerOrder {α : Type*} (le : α → α → Prop) (A B : List α) : Prop :=
  ∀ a ∈ A, ∃ b ∈ B, le a b

theorem listLowerOrder_refl {α : Type*} (le : α → α → Prop)
    (refl : ∀ a, le a a) (A : List α) : listLowerOrder le A A := by
  intro a ha
  exact ⟨a, ha, refl a⟩

theorem listLowerOrder_trans {α : Type*} (le : α → α → Prop)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (A B C : List α) (hAB : listLowerOrder le A B) (hBC : listLowerOrder le B C) :
    listLowerOrder le A C := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := hAB a ha
  obtain ⟨c, hc, hbc⟩ := hBC b hb
  exact ⟨c, hc, trans _ _ _ hab hbc⟩

end FormalTopology

-- ============================================================
-- Section 2: CompactWitness structure (List-based, Finding T13)
-- ============================================================

/-- **Vickers's compactness witness** for a formal topology with a given
basic cover presentation.  `F : Set (List T.S)` is a set of finite (list-
encoded) covers satisfying four closure conditions (Vickers's Theorem 0.4).

Lists may contain duplicates without semantic change — the cover is the
underlying set `{x | x ∈ S}`.  Using `List` over `Finset` avoids the
`Classical.choice` inheritance from mathlib's `Finset` infrastructure
(Finding T13). -/
structure CompactWitness (T : FormalTopology) (basicCov : T.S → Set T.S → Prop) where
  F : Set (List T.S)
  upper_closed : ∀ A ∈ F, ∀ B : List T.S,
                  FormalTopology.listLowerOrder T.le A B → B ∈ F
  inhabited : F.Nonempty
  /-- **Member-based cover closure (Finding T15 + T17 amendments)**.

  T15: if `a` is any element of `S ∈ F` (not required to be first), and
  `basicCov a U`, then there exists a finite sub-cover `V₀ ⊆ U` and a
  "residual" list `S'` preserving the non-`a` elements, such that
  `V₀ ++ S' ∈ F`.

  T17: the residual `S'` is also bounded *above* — every element of `S'`
  is in `S` and is not equal to `a`.  Combined with T15's lower bound
  `(∀ y ∈ S, y ≠ a → y ∈ S')`, this pins `S'` as a multi-permutation of
  the non-`a` elements of `S`.

  **Why T17**: Stage 6 Tychonoff §3.3 sub-case B1a needs to argue that
  the residual `S'` is contained in `Fπ₁(X_T)` (no spurious extras
  beyond non-`a` elements).  T15 alone allowed extras (e.g. `S' = S`
  including `a` itself), breaking the proof.  T17 tightens. -/
  cover_closure : ∀ {a : T.S} {U : Set T.S} {S : List T.S},
                   basicCov a U →
                   a ∈ S →
                   S ∈ F →
                   ∃ V₀ : List T.S, ∃ S' : List T.S,
                     (∀ x ∈ V₀, x ∈ U) ∧
                     (∀ y ∈ S, y ≠ a → y ∈ S') ∧
                     (∀ y ∈ S', y ∈ S ∧ y ≠ a) ∧
                     (V₀ ++ S') ∈ F
  generators_covered : ∀ S ∈ F, ∀ g : T.S, T.cov g {x | x ∈ S}

-- ============================================================
-- Section 3: OperationalCompact class
-- ============================================================

/-- **Operational compactness** combines Vickers's `CompactWitness` (using
the operational presentation's basic cover) with two invariants:

* `witness_operational`: every element of every F-cover is operational.
* `witness_describable`: every F-cover's element set is describable.

Together these ensure that compactness is operationally accessible — the
key property for the Stage 6 Mode B audit (binary Tychonoff). -/
class OperationalCompact (T : FormalTopology)
    [self : OperationalFormalTopology T] where
  witness : CompactWitness T self.basicCov
  witness_operational : ∀ S ∈ witness.F, ∀ x ∈ S,
                         OperationalFormalTopology.IsOperational x
  witness_describable : ∀ S ∈ witness.F,
                         IsDescribable ({x | x ∈ S} : Set T.S)

-- ============================================================
-- Section 4: Apparatus placeholder
-- ============================================================

/-- Placeholder marker: `OperationalCompact` is the Mode B audit target.
Full apparatus integration deferred to Stage 6. -/
theorem OperationalCompact.markedAsModeBTarget
    (T : FormalTopology)
    [OperationalFormalTopology T] [OperationalCompact T] :
    True := trivial

-- ============================================================
-- Section 5: List.toDescribable (replaces planned Finset.toDescribable)
-- ============================================================

namespace IsDescribable

/-- Every list (viewed as the set of its elements) is describable, via
`l[n]?` enumeration.  `getElem?` is in Lean core, no `Classical`. -/
instance List.toDescribable {α : Type*} (l : List α) :
    IsDescribable ({x | x ∈ l} : Set α) where
  enumerator n := l[n]?
  enumerator_some_mem n _ h := List.mem_iff_getElem?.mpr ⟨n, h⟩
  enumerator_surj _ hx := List.mem_iff_getElem?.mp hx

end IsDescribable

-- ============================================================
-- Section 6: Trivial instances
-- ============================================================

/-- The unit formal topology is operationally compact.  F-witness: all
lists of `Unit` elements (which can only be `()` repeated). -/
instance Examples.instUnitOperationalCompact :
    OperationalCompact Examples.Unit.formalTopology where
  witness := {
    F := (Set.univ : Set (List Unit))
    upper_closed := by
      intros A _ B _; trivial
    inhabited := ⟨[], trivial⟩
    cover_closure := by
      intro a U S _ _ _
      haveI : Subsingleton Unit.formalTopology.S :=
        inferInstanceAs (Subsingleton Unit)
      refine ⟨[], [], ?_, ?_, ?_, ?_⟩
      · intro x hx; cases hx
      · intros y _ hne
        exact absurd (Subsingleton.elim y a) hne
      · intro x hx; cases hx
      · trivial
    generators_covered := by
      intro S _ g
      -- Unit's basic cov is `fun _ _ => True`.
      exact CoverGen.basic True.intro
  }
  witness_operational := by
    intros S _ x _
    trivial  -- Unit's IsOperational is `fun _ => True`
  witness_describable := by
    intro S _
    infer_instance  -- via List.toDescribable

/-- The discrete two-element formal topology `Bool` is operationally
compact.  F-witness: all lists containing both `true` and `false`.
PLAN_5 §6 suggestion `{S | S = ∅ ∨ true ∈ S ∨ false ∈ S}` was incorrect
(Finding T11): `generators_covered` requires every generator to be
covered, and singletons cover only one. -/
instance Examples.instBoolOperationalCompact :
    OperationalCompact Examples.Bool.formalTopology where
  witness := {
    F := {S : List Bool | true ∈ S ∧ false ∈ S}
    upper_closed := by
      intro A hA B hAB
      -- hA : true ∈ A ∧ false ∈ A
      -- hAB : ∀ a ∈ A, ∃ b ∈ B, a = b
      have htrue : true ∈ B := by
        obtain ⟨b, hb, heq⟩ := hAB true hA.1
        rw [← heq] at hb; exact hb
      have hfalse : false ∈ B := by
        obtain ⟨b, hb, heq⟩ := hAB false hA.2
        rw [← heq] at hb; exact hb
      exact ⟨htrue, hfalse⟩
    inhabited := ⟨[true, false], ⟨by decide, by decide⟩⟩
    cover_closure := by
      intro a U S hbasic _haS hS
      -- T17 form: case-split on a (top level) for clean concrete proofs.
      cases a with
      | true =>
        refine ⟨[true], [false], ?_, ?_, ?_, ?_⟩
        · intro x hx
          cases hx with | head => exact hbasic | tail _ h => cases h
        · intros y hy hne
          cases y with
          | true => exact absurd rfl hne
          | false => exact List.mem_cons_self
        · intro y hy
          cases hy with
          | head =>
            refine ⟨hS.2, ?_⟩
            intro h; exact Bool.false_ne_true h
          | tail _ h => cases h
        · -- [true] ++ [false] = [true, false] ∈ F (has both).
          exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      | false =>
        refine ⟨[false], [true], ?_, ?_, ?_, ?_⟩
        · intro x hx
          cases hx with | head => exact hbasic | tail _ h => cases h
        · intros y hy hne
          cases y with
          | false => exact absurd rfl hne
          | true => exact List.mem_cons_self
        · intro y hy
          cases hy with
          | head =>
            refine ⟨hS.1, ?_⟩
            intro h; exact (Bool.false_ne_true h.symm)
          | tail _ h => cases h
        · exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self⟩
    generators_covered := by
      intro S hS g
      apply CoverGen.basic
      -- basicCov for Bool is (· ∈ ·); need g ∈ {x | x ∈ S}
      change g ∈ S
      cases g
      · exact hS.2
      · exact hS.1
  }
  witness_operational := by
    intros S _ x _; trivial
  witness_describable := by
    intro S _
    infer_instance  -- via List.toDescribable

-- ============================================================
-- Section 7: Classical-compactness bridge (declarative placeholder)
-- ============================================================

/-- Declarative marker: F-witness compactness is the constructive form of
classical "every cover has finite subcover".  Full equivalence theorem
deferred to Stage 7 (bridge to mathlib) if needed. -/
theorem CompactWitness.implies_classical_compact
    (T : FormalTopology) (basicCov : T.S → Set T.S → Prop)
    (_w : CompactWitness T basicCov) : True := trivial

end VRCycle.Topology
