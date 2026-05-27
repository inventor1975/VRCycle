-- VRCycle/Topology/FormalTopology.lean
-- VR-Topology v1.0.0 — Stage 1: Formal topology infrastructure.
--
-- Coverage-based pointfree topology (Coquand 1992; Sambin 1987).  A formal
-- topology is a poset `S` together with a coverage relation `◁ : S → Set S → Prop`
-- satisfying four axioms (reflexivity, transitivity, refinement-monotonicity,
-- locality).  The coverage relation is the primary datum; the frame of
-- formal opens is derived (Lindenbaum-Tarski quotient, deferred to Stage 7).
--
-- This file is the foundation for the entire VR-Topology tower.  Subsequent
-- stages add the operational predicate layer (Stage 2), continuous maps as
-- relators (Stage 3), product of formal topologies (Stage 4), operational
-- compactness (Stage 5), Mode B audit Tychonoff (Stage 6), and bridges to
-- mathlib `Frm` / `TopCat` (Stage 7).
--
-- Design notes (Stage 1 / Option G pivot — see CLAUDE.md "Architectural history"):
--
-- * `cov : S → Set S → Prop` lives in `Prop`, not `Type`.  This is the
--   structural reason formal topology avoids the universe-inflation problem
--   that blocked the original free-frame construction (see `_attic/`).
--
-- * The coverage axioms are Coquand-style (refl / trans / refinement-mono /
--   locality), not classical Sambin-style (refl / trans / left).  The Coquand
--   formulation is what supports constructive Tychonoff by structural
--   induction on cover derivations.
--
-- * `CoverGen` (Section 2) is the inductive closure of a presentation
--   (preorder + basic covers) under the four axioms.  It is parametric in
--   the preorder.  Most formal topologies are built via `ofPresentation`,
--   not by directly providing all coverage data.

import Mathlib.Data.Set.Basic

namespace VRCycle.Topology

-- ============================================================
-- Section 0: Helper — common refinement (introduced for Finding T7)
-- ============================================================

/-- The set of **common refinements** of two cover families `U` and `V`:
elements `c` that refine some `u ∈ U` and some `v ∈ V`.  Used in the
`cov_meet` axiom (Finding T7 — needed for product universal property
via pairing).  Standard Sambin "meeting" set. -/
def commonRefinement {S : Type*} (le : S → S → Prop) (U V : Set S) : Set S :=
  {c | ∃ u ∈ U, ∃ v ∈ V, le c u ∧ le c v}

-- ============================================================
-- Section 1: Formal topology structure
-- ============================================================

/-- A **formal topology** consists of a preordered set `(S, ≤)` together with
a coverage relation `cov : S → Set S → Prop` satisfying the five coverage
axioms — reflexivity, transitivity, refinement-monotonicity, locality
(Coquand 1992) — plus **meet** (Sambin extension; Finding T7).

We use `structure` (not `class`): formal topologies are typically given as
concrete data, not synthesised by instance inference.  A typeclass variant
`[IsFormalTopology S]` may be added later if convenient. -/
structure FormalTopology where
  /-- The underlying type of basic elements (formal opens). -/
  S : Type*
  /-- The preorder on `S`. -/
  le : S → S → Prop
  /-- The coverage relation: `cov a U` means "`a` is covered by `U`". -/
  cov : S → Set S → Prop
  -- Preorder axioms
  le_refl  : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  -- Coverage axioms (Coquand 1992)
  /-- Reflexivity of coverage: membership implies cover. -/
  cov_refl     : ∀ a U, a ∈ U → cov a U
  /-- Transitivity of coverage: if `a ◁ U` and every element of `U` covers `V`,
  then `a ◁ V`. -/
  cov_trans    : ∀ a U V, cov a U → (∀ b ∈ U, cov b V) → cov a V
  /-- Refinement-monotonicity: if `a ≤ b` and `b ◁ U`, then `a ◁ U`. -/
  cov_ref_mono : ∀ a b U, le a b → cov b U → cov a U
  /-- Locality: if `a ≤ b` and `a ◁ U`, then `a ◁ {c ∈ U | c ≤ b}`. -/
  cov_local    : ∀ a b U, le a b → cov a U → cov a {c ∈ U | le c b}
  /-- Meet (Sambin extension; Finding T7).  If `a ◁ U` and `a ◁ V`, then `a`
  is covered by the common refinements of `U` and `V`.  Needed for product
  universal property: pre-image of rectangular cover under pairing relator
  is set-intersection, which requires this axiom to remain covered. -/
  cov_meet     : ∀ a U V, cov a U → cov a V → cov a (commonRefinement le U V)

-- ============================================================
-- Section 2: Inductively generated coverage relation
-- ============================================================

/-- The **inductively generated coverage relation** from a preorder `le` and
a relation `basicCov` of basic covers.  Six constructors:

* `basic` — import a basic cover.
* `mem`   — element membership implies cover (reflexivity).
* `trans` — composition of covers (transitivity).
* `ref_mono` — refinement under `≤` (refinement-monotonicity).
* `local_` — restriction to downset (locality).
* `meet`  — common-refinement of two covers (Finding T7; Sambin extension).

The relation is `Prop`-valued: for `S : Type u`, `CoverGen le basicCov` lives
in `S → Set S → Prop`, in the same universe as `S` (since `Prop` is
impredicative).  No `Type`-level recursive substructure — the universe
problem that blocked the original free-frame construction does not arise. -/
inductive CoverGen {S : Type*} (le : S → S → Prop) (basicCov : S → Set S → Prop) :
    S → Set S → Prop where
  | basic    {a : S} {U : Set S} : basicCov a U → CoverGen le basicCov a U
  | mem      {a : S} {U : Set S} : a ∈ U → CoverGen le basicCov a U
  | trans    {a : S} {U V : Set S} :
      CoverGen le basicCov a U →
      (∀ b ∈ U, CoverGen le basicCov b V) →
      CoverGen le basicCov a V
  | ref_mono {a b : S} {U : Set S} :
      le a b → CoverGen le basicCov b U → CoverGen le basicCov a U
  | local_   {a b : S} {U : Set S} :
      le a b → CoverGen le basicCov a U →
      CoverGen le basicCov a {c ∈ U | le c b}
  | meet     {a : S} {U V : Set S} :
      CoverGen le basicCov a U → CoverGen le basicCov a V →
      CoverGen le basicCov a (commonRefinement le U V)

-- ============================================================
-- Section 3: Coverage axioms hold for CoverGen
-- ============================================================

namespace CoverGen

variable {S : Type*} {le : S → S → Prop} {basicCov : S → Set S → Prop}

/-- `CoverGen` satisfies the reflexivity coverage axiom. -/
theorem cov_refl (a : S) (U : Set S) (h : a ∈ U) : CoverGen le basicCov a U :=
  .mem h

/-- `CoverGen` satisfies the transitivity coverage axiom. -/
theorem cov_trans (a : S) (U V : Set S)
    (hU : CoverGen le basicCov a U)
    (hV : ∀ b ∈ U, CoverGen le basicCov b V) :
    CoverGen le basicCov a V :=
  .trans hU hV

/-- `CoverGen` satisfies the refinement-monotonicity coverage axiom. -/
theorem cov_ref_mono (a b : S) (U : Set S)
    (hab : le a b) (hU : CoverGen le basicCov b U) :
    CoverGen le basicCov a U :=
  .ref_mono hab hU

/-- `CoverGen` satisfies the locality coverage axiom. -/
theorem cov_local (a b : S) (U : Set S)
    (hab : le a b) (hU : CoverGen le basicCov a U) :
    CoverGen le basicCov a {c ∈ U | le c b} :=
  .local_ hab hU

/-- `CoverGen` satisfies the meet coverage axiom (Finding T7). -/
theorem cov_meet (a : S) (U V : Set S)
    (hU : CoverGen le basicCov a U) (hV : CoverGen le basicCov a V) :
    CoverGen le basicCov a (commonRefinement le U V) :=
  .meet hU hV

end CoverGen

-- ============================================================
-- Section 4: Building a FormalTopology from a presentation
-- ============================================================

/-- Build a `FormalTopology` from a presentation: a preorder `(S, ≤)`
together with a basic-cover relation `basicCov : S → Set S → Prop`.

The coverage is the inductive closure `CoverGen le basicCov`.  All four
coverage axioms are inherited from `CoverGen`'s constructors via the
theorems in Section 3. -/
def FormalTopology.ofPresentation
    (S : Type*)
    (le : S → S → Prop)
    (le_refl : ∀ a, le a a)
    (le_trans : ∀ a b c, le a b → le b c → le a c)
    (basicCov : S → Set S → Prop) : FormalTopology where
  S := S
  le := le
  cov := CoverGen le basicCov
  le_refl := le_refl
  le_trans := le_trans
  cov_refl := CoverGen.cov_refl
  cov_trans := CoverGen.cov_trans
  cov_ref_mono := CoverGen.cov_ref_mono
  cov_local := CoverGen.cov_local
  cov_meet := CoverGen.cov_meet

-- ============================================================
-- Section 5: Smoke-test examples
-- ============================================================

namespace Examples

/-- The unit formal topology: one element, trivial preorder, trivial basic
cover.  Used as a sanity check that the infrastructure compiles.
Marked `@[reducible]` so downstream typeclass synthesis can see `.S = Unit`. -/
@[reducible] def Unit.formalTopology : FormalTopology :=
  FormalTopology.ofPresentation
    (S := Unit)
    (le := fun _ _ => True)
    (le_refl := fun _ => trivial)
    (le_trans := fun _ _ _ _ _ => trivial)
    (basicCov := fun _ _ => True)

/-- The discrete two-element formal topology: `Bool` with equality as
preorder and membership as basic cover.  Smoke-test for the basic cover
mechanism.  Marked `@[reducible]` so downstream typeclass synthesis can
see `.S = Bool`. -/
@[reducible] def Bool.formalTopology : FormalTopology :=
  FormalTopology.ofPresentation
    (S := Bool)
    (le := fun a b => a = b)
    (le_refl := fun _ => rfl)
    (le_trans := fun _ _ _ hab hbc => hab.trans hbc)
    (basicCov := fun a U => a ∈ U)

end Examples

-- ============================================================
-- Section 6: Basic structural lemmas
-- ============================================================

namespace FormalTopology

variable (T : FormalTopology)

/-- Coverage is monotone in the cover family: enlarging the cover preserves
cover.  Proved via transitivity, with the larger family used pointwise as a
cover of each smaller element. -/
theorem cov_mono (a : T.S) (U V : Set T.S) (hUV : U ⊆ V) (h : T.cov a U) :
    T.cov a V :=
  T.cov_trans a U V h (fun b hbU => T.cov_refl b V (hUV hbU))

/-- Every element is covered by its own singleton. -/
theorem cov_singleton (a : T.S) : T.cov a {a} :=
  T.cov_refl a {a} rfl

/-- Singleton-mediated transitivity: if `a ◁ {b}` and `b ◁ U`, then `a ◁ U`. -/
theorem cov_trans_singleton (a b : T.S) (U : Set T.S)
    (hab : T.cov a {b}) (hbU : T.cov b U) : T.cov a U :=
  T.cov_trans a {b} U hab (fun c hcb => by
    -- c ∈ {b} means c = b; replace and finish
    cases hcb
    exact hbU)

end FormalTopology

end VRCycle.Topology
