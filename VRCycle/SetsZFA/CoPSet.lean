-- VR-Sets-ZFA: Coinductive pre-sets
-- Stage 1: CoPSet — greatest fixpoint of CoPSetFunctor.
--
-- CoPSet is the coinductive parallel of PSet (mathlib's pre-sets).
-- Constructed as PFunctor.M CoPSetFunctor where
--   CoPSetFunctor := ⟨Type u, id⟩.
-- This is a direct application of Avigad–Carneiro–Hudon's M-type
-- infrastructure (mathlib Data.PFunctor.Univariate.M).
--
-- Universe: CoPSet.{u} : Type (u+1), matching PSet.{u} : Type (u+1).
-- Potentially non-well-founded: contains Quine atoms, cyclic sets, etc.
--
-- Connection to VR-Sets:
--   - VRCycle.Sets.Conjectures.Conjecture_IV_2_Statement asks for a type U
--     with extensional membership satisfying classical AFA (Aczel 1988).
--   - OSetZFA (cobisimulation quotient of CoPSet, Stage 3) is that type U.
--   - AFA holds in OSetZFA as a theorem (Stage 5), not an axiom.
--
-- Source: Aczel 1988 §6; PFunctor.M (mathlib).

import Mathlib.Data.PFunctor.Univariate.M

namespace VR.SetsZFA

universe u v

-- ============================================================
-- §1. CoPSetFunctor
-- ============================================================

/-- The polynomial functor whose greatest fixpoint is CoPSet.

Shape: `A = Type u` (the branching type); `B = id` (children indexed
by the branching type itself, so a node with branching type `α` has
children indexed by `α`).

This is the direct coinductive parallel of the PSet functor:

    PSet.mk (α : Type u) (A : α → PSet)     — inductive
    CoPSet.mk (α : Type u) (A : α → CoPSet) — coinductive (greatest fixpoint)

Universe: `PFunctor.{u+1, u}` — the shape type lives in `Type (u+1)`,
children live in `Type u`. -/
def CoPSetFunctor : PFunctor.{u + 1, u} where
  A := Type u
  B := id

-- ============================================================
-- §2. CoPSet
-- ============================================================

/-- CoPSet.{u}: the type of potentially non-well-founded pre-sets.

Greatest fixpoint of `CoPSetFunctor` via mathlib's `PFunctor.M`
(Avigad–Carneiro–Hudon 2019, `Mathlib.Data.PFunctor.Univariate.M`).

**Structural parallel with PSet:**
- `PSet.{u}` (inductive, mathlib) has universe `Type (u+1)`.
  Elements are well-founded trees: finite ranks, no cycles.
- `CoPSet.{u}` (greatest fixpoint) has universe `Type (u+1)`.
  Elements are potentially infinite/cyclic trees.

Both use the same branching structure `(α : Type u, A : α → ·)`.
The difference is inductive vs coinductive generation.

**AFA connection (Stages 3–5):**
`OSetZFA` (cobisimulation quotient of CoPSet) answers
`Conjecture_IV_2_Statement` (VRCycle.Sets.Conjectures): it is the
type `U` with extensional membership satisfying classical AFA.
AFA is a theorem in OSetZFA, not an axiom.

**Axiom profile:** inherits `[propext, Classical.choice, Quot.sound]`
from `PFunctor.M.bisim` (used in Stage 2 proofs). -/
def CoPSet : Type (u + 1) :=
  PFunctor.M CoPSetFunctor.{u}

-- ============================================================
-- §3. dest — destructor (Sigma form, primary)
-- ============================================================

/-- Destructor: unfolds one level of a CoPSet into its branching type
and children map.

`CoPSet.dest x = ⟨α, A⟩` where:
- `α : Type u` is the branching type (the "arity" of the root node),
- `A : α → CoPSet` is the children map.

**Sigma form is primary.** Downstream proofs (cobisimulation, AFA)
operate on `Σ α : Type u, α → CoPSet` without dependent casts.
The `shape` and `children` projections (§4) are derived from `dest`. -/
def CoPSet.dest (x : CoPSet.{u}) : Σ α : Type u, α → CoPSet.{u} :=
  PFunctor.M.dest x

-- ============================================================
-- §4. shape and children — projections
-- ============================================================

/-- The branching type of a CoPSet: the "arity" of its root node.

`CoPSet.shape x = (CoPSet.dest x).1 : Type u`.

Parallel to `PSet.type : PSet → Type*` (mathlib, `Mathlib.SetTheory.ZFC.Basic`). -/
def CoPSet.shape (x : CoPSet.{u}) : Type u :=
  x.dest.1

/-- The children map: sends each index to the corresponding sub-pre-set.

`CoPSet.children x : x.shape → CoPSet`

`CoPSet.children x i` is the `i`-th direct child of `x`.

Parallel to `PSet.func : ∀ (x : PSet), x.type → PSet`. -/
def CoPSet.children (x : CoPSet.{u}) : x.shape → CoPSet.{u} :=
  x.dest.2

-- ============================================================
-- §5. mk — constructor
-- ============================================================

/-- Constructor: assembles a CoPSet from a branching type and children.

`CoPSet.mk α A : CoPSet` represents the pre-set whose "members" are
indexed by `α : Type u`, with the `i`-th member being `A i : CoPSet`.

**Direct parallel to PSet.mk:**

    PSet.mk (α : Type u) (A : α → PSet) : PSet      — inductive
    CoPSet.mk (α : Type u) (A : α → CoPSet) : CoPSet — coinductive

**Universe:** `α : Type u`, `A : α → CoPSet.{u}`, result `: CoPSet.{u} : Type (u+1)`.

`CoPSet.mk` and `CoPSet.dest` are inverse to each other:
`dest_mk` (§6) and `mk_dest` (§6). -/
def CoPSet.mk (α : Type u) (A : α → CoPSet.{u}) : CoPSet.{u} :=
  PFunctor.M.mk ⟨α, A⟩

-- ============================================================
-- §6. Roundtrip lemmas
-- ============================================================

/-- **Roundtrip I**: `dest` inverts `mk` (Sigma form, primary).

`CoPSet.dest (CoPSet.mk α A) = ⟨α, A⟩`

**Proof:** Direct corollary of `PFunctor.M.dest_mk`, which holds by
`rfl` in mathlib — the approximation structure unfolds definitionally
(`sMk` followed by `dest` reduces to the original sigma). -/
@[simp]
theorem CoPSet.dest_mk (α : Type u) (A : α → CoPSet.{u}) :
    CoPSet.dest (CoPSet.mk α A) = ⟨α, A⟩ := rfl

/-- **Roundtrip II**: `mk` inverts `dest`.

`CoPSet.mk x.shape x.children = x` for any `x : CoPSet`.

**Proof:** `PFunctor.M.mk_dest`. -/
@[simp]
theorem CoPSet.mk_dest (x : CoPSet.{u}) :
    CoPSet.mk x.shape x.children = x :=
  PFunctor.M.mk_dest x

/-- **shape projection**: the shape of `CoPSet.mk α A` is `α`.

`(CoPSet.mk α A).shape = α`

**Proof:** First component of `dest_mk`. -/
@[simp]
theorem CoPSet.shape_mk (α : Type u) (A : α → CoPSet.{u}) :
    (CoPSet.mk α A).shape = α :=
  congrArg Sigma.fst (CoPSet.dest_mk α A)

/-- **children projection** (HEq form): children of `CoPSet.mk α A` are
heterogeneously equal to `A`.

`HEq (CoPSet.mk α A).children A`

**Why HEq?** `(CoPSet.mk α A).children` has type
`(CoPSet.mk α A).shape → CoPSet`, while `A` has type `α → CoPSet`.
These types are propositionally equal (via `shape_mk`) but not
syntactically identical, so heterogeneous equality is required.

**Proof:** Second component of `dest_mk` via `Sigma.mk.inj`. -/
theorem CoPSet.children_mk (α : Type u) (A : α → CoPSet.{u}) :
    HEq (CoPSet.mk α A).children A :=
  (Sigma.mk.inj (CoPSet.dest_mk α A)).2

-- ============================================================
-- §7. Corecursor
-- ============================================================

/-- Corecursor for CoPSet: the unique coalgebra morphism into the
final coalgebra.

Given `f : X → CoPSetFunctor X` (equivalently, `f : X → Σ α : Type u, α → X`),
`CoPSet.corec f : X → CoPSet` is the unique function such that:

    CoPSet.dest (CoPSet.corec f x) = CoPSetFunctor.map (CoPSet.corec f) (f x)

i.e., `CoPSet.corec f` is a coalgebra morphism from `(X, f)` to
`(CoPSet, dest)`.

**AFA preview (Stage 5):** For any graph `(V, E)`, define
`f v = ⟨{w // E v w}, Subtype.val⟩ : CoPSetFunctor V`. Then
`CoPSet.corec f : V → CoPSet` is the AFA decoration of `(V, E)`.
Uniqueness follows from `PFunctor.M.corec_unique`.

Delegates to `PFunctor.M.corec`. -/
def CoPSet.corec {X : Type v} (f : X → CoPSetFunctor.{u} X) : X → CoPSet.{u} :=
  PFunctor.M.corec f

/-- **Coalgebra morphism property of `corec`**: `corec f` intertwines
`f` and `dest`.

`CoPSet.dest (CoPSet.corec f x) = CoPSetFunctor.map (CoPSet.corec f) (f x)`

This is the defining equation of the corecursor: applying `dest` after
`corec f` is the same as applying `f` first, then functorially mapping
`corec f` over the children.

Used in Stage 5 to show the AFA decoration satisfies the decoration equation.
Delegates to `PFunctor.M.dest_corec`. -/
theorem CoPSet.dest_corec {X : Type v} (f : X → CoPSetFunctor.{u} X) (x : X) :
    CoPSet.dest (CoPSet.corec f x) =
      CoPSetFunctor.map (CoPSet.corec f) (f x) :=
  PFunctor.M.dest_corec f x

-- ============================================================
-- §8. Bisimulation
-- ============================================================

/-- **Bisimulation principle**: a bisimulation implies equality.

If `R` is a bisimulation on `CoPSet` (i.e., whenever `R x y`, the
roots of `x` and `y` have the same branching type and pairwise
`R`-related children), then `R x y → x = y`.

**Formal statement:**
A relation `R : CoPSet → CoPSet → Prop` is a bisimulation if:
    ∀ x y, R x y →
      ∃ α (fx fy : α → CoPSet),
          dest x = ⟨α, fx⟩ ∧ dest y = ⟨α, fy⟩ ∧ ∀ i, R (fx i) (fy i)

**Stage 2 connection:** `CoPSet.cobisim` (Stage 2) is the greatest
bisimulation. By this theorem, `cobisim x y → x = y` in OSetZFA
(where cobisimulation becomes equality via the quotient).

**Stage 5 connection:** `corec_unique` (uniqueness of AFA decoration)
also follows from this principle.

**Axiom note:** Delegates to `PFunctor.M.bisim`, which internally uses
`Classical.choice` (via `inhabit` in `eq_of_bisim`). This is within
the ceiling `[propext, Classical.choice, Quot.sound]`. -/
theorem CoPSet.bisim (R : CoPSet.{u} → CoPSet.{u} → Prop)
    (h : ∀ x y, R x y →
          ∃ (α : Type u) (fx fy : α → CoPSet.{u}),
            CoPSet.dest x = ⟨α, fx⟩ ∧
            CoPSet.dest y = ⟨α, fy⟩ ∧
            ∀ i : α, R (fx i) (fy i)) :
    ∀ x y, R x y → x = y := by
  apply PFunctor.M.bisim
  intro x y hxy
  obtain ⟨α, fx, fy, hx, hy, hR⟩ := h x y hxy
  exact ⟨α, fx, fy, hx, hy, hR⟩

end VR.SetsZFA
