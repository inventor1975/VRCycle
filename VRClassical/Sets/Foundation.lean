-- VR-Sets: Foundation (DOI 10.5281/zenodo.20303536)
-- Part II. The Operational Construction of Sets.
--
-- Stage 1: type OSet, empty set osetEmpty, operational identity ≡.
-- Stage 2: Lemma 1 (extensionality), Lemma 2 (uniqueness of ∅), Lemma 3 (operational depth).
-- Source: Part II §II.1–§II.2.
--
-- Architectural note (Stages 1–9 vs Stage 10):
-- OSet := ZFSet is the ZFC-mode base. ZFSet is well-founded by construction,
-- so all of Stages 1-9 and 11-12 use OSet directly. Stage 10 (ZFA-mode,
-- Modes.lean) requires PSet (before the quotient), as cyclic sets like Quine
-- atoms cannot be represented in ZFSet.

import Mathlib.SetTheory.ZFC.Rank   -- subsumes ZFC.Basic; adds ZFSet.rank

namespace VR.Sets

-- ============================================================
-- §II.1, Definition 1 — The type of operational sets
-- ============================================================

/-- # Operational sets (VR-Sets preprint, DOI 10.5281/zenodo.20303536)
Part II §II.1, Definition 1.

## Definition 1 (set) — verbatim
«A **set** in VR-Sets is an operational entity given by its membership
functionality: upon a query, the functionality either reveals an element
(which is itself a set, possibly the same set as the one being queried)
or reveals nothing. The order in which elements are revealed is an
artefact of observation and does not enter into the identity of the set.
A set has no internal structure beyond its functionality; it *is* its
functionality.»

## Implementation
`OSet` is defined as `ZFSet` — mathlib's type of well-founded sets,
constructed as the quotient of pre-sets (`PSet`) by extensional
equivalence (bisimulation). The ZFC axioms are theorems on `ZFSet`,
not postulates of a model (see `Mathlib.SetTheory.ZFC.Basic`).

Construction chain:
```
PSet  := inductive mk (α : Type u) (A : α → PSet) -- a set IS its index family
PSet.Equiv x y := mutual simulation of membership  -- bisimulation (= Def. 4 ≡)
ZFSet := Quotient PSet.setoid                      -- bisimulation collapsed to Eq
OSet  := ZFSet                                     -- our name for the preprint
```

## Why ZFSet realises the preprint semantics
The `PSet` constructor `mk (α : Type u) (A : α → PSet)` captures Definition 1
directly: a set is given by its indexing type `α` (the collection of queries
that produce an element) and its response function `A` (which element each
query reveals). «The functionality either reveals an element or reveals
nothing» corresponds to: a query either lies in `α` (reveals `A i`) or does
not. «Order of revelation is an artefact of observation»: `A : α → PSet` is
a function, not a sequence — order is invisible.

`PSet.Equiv` (bisimulation) identifies sets with the same membership graph,
which is exactly the operational identity ≡ of Definition 4. The quotient
`ZFSet` promotes this to Lean's `Eq`, so `a ≡ b` reduces to `a = b`
(see `notation` below).

## `abbrev` vs `def`
This is `abbrev` (not `def`), marking `OSet` as `@[reducible]`. All mathlib
operations on `ZFSet` (`ZFSet.pair`, `ZFSet.sUnion`, `ZFSet.powerset`, …)
therefore apply directly to `OSet` without wrapping. Contrast with
VR-Numbers where base types (`IntVR`, `RatVR`, `RealVR`) used `def` with
explicit wrappers — there arithmetic was built independently; here we rely
on mathlib's ZFSet infrastructure completely (CLAUDE.md, Decision 1).

## ZFC-mode and the well-foundedness boundary
The preprint distinguishes two modes (Part IV): the **ZFC-mode**, where all
set unfolding terminates at ∅ (foundation holds), and the **ZFA-mode**,
where cyclic sets such as the Quine atom A = {A} are allowed. `ZFSet` — and
therefore `OSet` — is **well-founded by construction**: `PSet` is an
inductive type, so membership is globally well-founded
(`instance : IsWellFounded ZFSet (· ∈ ·)`, Mathlib Basic.lean). Stage 1
therefore formalises the **ZFC-mode base**. The ZFA-mode (Stage 10,
`Modes.lean`) cannot be realised via `ZFSet`: non-well-founded sets cannot
be constructed in this type since mathlib contains no AFA or coinductive
set infrastructure. This is the structural boundary documented at Stage 10
(parallel to the ℝ_VR inexpressibility boundary of VR-Numbers §VIII.6).

## Closure principle (metatheoretic)
The preprint's closure principle (§II.3): «if a functionality is
operationally describable, then there exists a set A such that A is F» is
**not** a Lean-expressible statement (CLAUDE.md, Decision 4). Individual
closure theorems (pairing, union, power, infinity, replacement, choice) are
proved in `ZF.lean` (Stages 3–8), each as a wrapper over the corresponding
mathlib lemma on `ZFSet`.

## Reference
Aczel, P. (1988). *Non-well-founded sets*. CSLI Lecture Notes 14.
Operational identity ≡ (Definition 4) is structurally the same relation as
bisimulation in Aczel's AFA framework; the direct connection is discussed
in the preprint Part IV §IV.8. In mathlib, `PSet.Equiv` is this bisimulation;
`ZFSet` makes it definitional equality. -/
abbrev OSet := ZFSet


-- ============================================================
-- §II.1, Definition 2 — The empty operational set
-- ============================================================

/-- §II.1, Definition 2 (∅) — verbatim:
«∅ is the unique set whose functionality reveals nothing:
∅ is the empty operationality.»

Implemented as `ZFSet.empty` via the `EmptyCollection ZFSet` instance.
Uniqueness is Lemma 2 (Stage 2). -/
def osetEmpty : OSet := ∅


-- ============================================================
-- §II.1, Definition 4 — Operational identity ≡
-- ============================================================

/-- §II.1, Definition 4 (operational identity ≡) — verbatim:
«Sets A and B are *operationally identical* (A ≡ B) if their
functionalities coincide: for every element x of A there exists an
element y of B with x ≡ y, and conversely. ∅ ≡ ∅.»

**Bridge to Lean.** `OSet = ZFSet = Quotient PSet.setoid`. By
`Quotient.sound` and `Quotient.exact`,

    ⟦x⟧ = ⟦y⟧  ↔  PSet.Equiv x y

`PSet.Equiv` is the bisimulation relation (PSet.lean): «for every element
of x there is an equivalent element of y, and conversely» — exactly
Definition 4. Therefore `a ≡ b` holds iff `a = b : OSet`.

**Commentary (4) from §II.1** (verbatim): «In the AFA literature (Aczel
1988) the analogous relation is known as bisimulation: sets are equivalent
if their graphs of membership are isomorphic (allowing cycles). In VR-Sets
≡ is structurally the same relation, expressed operationally.»

Implemented as `notation` (not `def`) so that `rfl`, `rw`, `simp`, and
`ext` apply to `≡` directly without unfolding. -/
notation:50 a " ≡ " b => @Eq OSet a b

-- ============================================================
-- §II.2. Three lemmas
-- ============================================================

-- --------------------------------------------------------
-- Lemma 1 — Extensionality
-- --------------------------------------------------------

/-- §II.2, Lemma 1 (extensionality) — verbatim:
«If A and B have the same elements (up to ≡), then A ≡ B.»

Proof (preprint): «This is a direct reading of Definition 4: the condition
of coincidence of functionalities in Definition 4 is precisely "for every
element x of A there exists y of B with x ≡ y, and conversely."»

In Lean: since ≡ = Eq on OSet, «same elements up to ≡» reduces to
«same elements», i.e. `∀ x, x ∈ a ↔ x ∈ b`. This is exactly
`ZFSet.ext`. The preprint's remark that «extensionality is built into
the definition» (it is a reading of Def 4, not a separate axiom) is
confirmed: `ZFSet.ext` follows from `Quotient.sound` + `Quot.sound`,
no additional axioms. -/
theorem Lemma_II_1_Extensionality (a b : OSet) (h : ∀ x : OSet, x ∈ a ↔ x ∈ b) :
    a ≡ b :=
  ZFSet.ext h


-- --------------------------------------------------------
-- Lemma 2 — Uniqueness of ∅
-- --------------------------------------------------------

/-- §II.2, Lemma 2 (uniqueness of ∅) — verbatim:
«There exists exactly one set with an empty functionality.»

Proof (preprint): «If two functionalities both reveal nothing, the
coincidence condition of Definition 4 holds vacuously on both sides:
"for every element x of A there exists y of B with x ≡ y" — the premise
is false, the implication is true; and conversely. Therefore A ≡ B.»

In Lean: uniqueness follows from Lemma 1 — two sets with no members
have the same (empty) membership relation, hence are equal. Existence
is `osetEmpty`. `ZFSet.notMem_empty` provides `∀ x, x ∉ ∅`. -/
theorem Lemma_II_2_UniquenessEmpty : ∃! (a : OSet), ∀ x : OSet, x ∉ a := by
  refine ⟨osetEmpty, ZFSet.notMem_empty, fun a ha => ?_⟩
  exact ZFSet.ext fun x => iff_of_false (ha x) (ZFSet.notMem_empty x)


-- --------------------------------------------------------
-- Lemma 3 — Operational depth
-- --------------------------------------------------------

/-- Operational depth of an operational set: the ordinal rank of its
membership tree.

§II.2, Lemma 3 (operational depth) — paraphrase:
«Every set has an operational depth — the least number of unfolding
steps after which ∅ is reached. The depth of ∅ is 0. Finite sets have
finite depth. Infinite and cyclic sets do not have finite depth.»

**Note on status** (from preprint): «Lemma 3 is not an existence theorem
but a definition of a property of a functionality. Every set A has its
depth: a number (or "infinity" with the qualification "non-cyclic") — a
structural characteristic of A.»

**Implementation.** `operationalDepth` is `ZFSet.rank`: the unique ordinal
satisfying `rank(a) = sup { rank(b) + 1 | b ∈ a }` (Rank.lean). This is
the Von Neumann rank of the membership tree.

**Mapping of the three preprint cases to this formalisation:**

| Preprint case  | Condition           | Status in OSet = ZFSet |
|----------------|---------------------|------------------------|
| Finite         | `rank a < ω`        | ✓ fully represented    |
| Infinite, non-cyclic (e.g. ω) | `rank a ≥ ω` | ✓ fully represented |
| Cyclic (e.g. Quine atom A = {A}) | depth undefined | ✗ **does not exist** |

**The cyclic case and the ZFC-mode boundary.** `OSet = ZFSet = Quotient
PSet.setoid`, and `PSet` is an *inductive* Lean type — membership is
well-founded by construction (`instance : IsWellFounded ZFSet (· ∈ ·)`).
Therefore cyclic sets (the third case) simply do not exist as elements of
`OSet`. This is a structural boundary: Stage 1 formalises the **ZFC-mode
base**, which is the only mode `ZFSet` supports. The ZFA-mode (Stage 10,
`Modes.lean`), which allows cyclic sets, will require working with `PSet`
directly (before the quotient is taken), not with `OSet`. In that mode,
`operationalDepth` as defined here would not apply to cyclic objects; a
separate treatment (or a `WithTop`-valued variant) would be needed.

**Finite-depth characterisation.** Mathlib provides no ready `ZFSet.IsFinite`
predicate connecting finiteness to `rank < ω` over `ZFSet`. This connection
will be addressed at Stage 10 when the ZFA/ZFC-mode boundary is revisited.

The induction instrument mentioned in the preprint («the analogue of
axiom A4 from VR, lifted to the level of sets») is `Lemma_II_3_DepthMono`
below: membership is strictly depth-decreasing, enabling well-founded
recursion on `OSet`. -/
noncomputable def operationalDepth (a : OSet) : Ordinal :=
  ZFSet.rank a

/-- §II.2, Lemma 3 — depth of ∅ is 0.
Formally: `rank ∅ = 0`. Proof: `ZFSet.rank_empty`. -/
theorem Lemma_II_3_DepthEmpty : operationalDepth osetEmpty = 0 :=
  ZFSet.rank_empty

/-- §II.2, Lemma 3 — depth is strictly monotone on membership.
If `b ∈ a` then `operationalDepth b < operationalDepth a`.
This is the **induction instrument** for VR-Sets: any well-founded
recursion on `OSet` terminates because depth decreases at each step.
Formally: `ZFSet.rank_lt_of_mem`. -/
theorem Lemma_II_3_DepthMono {a b : OSet} (h : b ∈ a) :
    operationalDepth b < operationalDepth a :=
  ZFSet.rank_lt_of_mem h

end VR.Sets
