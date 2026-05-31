-- VR-Sets: Modes (DOI 10.5281/zenodo.20303536)
-- Part IV. ZFC-Mode and ZFA-Mode.
--
-- Stage 9: ZFC-mode predicate (isZFCmode), universality theorem
--           (isZFCmode_all), and Theorem IV.1 (structural collector:
--           all nine ZFC axioms hold on OSet = ZFSet = ZFC-mode).
-- Source: Part IV §IV.2–§IV.3.
--
-- Stage 10 (ZFA-mode, Quine atoms, Theorem IV.2) — TODO: requires
-- switching base type from ZFSet to PSet; the well-foundedness boundary
-- is documented in Foundation.lean (§ operationalDepth, cyclic case).

import VRCycle.Sets.ZF

namespace VR.Sets

-- ============================================================
-- §IV.2 — ZFC-mode predicate
-- ============================================================

/-- ZFC-mode: an operational set s is in ZFC-mode if its membership tree
is well-founded — every descending chain x₁ ∋ x₂ ∋ x₃ ∋ … into s
is finite (ultimately reaches ∅).

## §IV.2 (VR-Sets preprint, verbatim)
«The ZFC-mode of VR-Sets consists of all sets whose operational unfolding
terminates: every descending membership chain x₁ ∋ x₂ ∋ … ∋ xₙ ∋ … is
finite.»

## Lean implementation: `Acc (· ∈ ·) s`

`Acc r s` (accessibility of s in r) is the standard Lean predicate for
well-foundedness at a single element: s is accessible iff every r-chain
descending into s terminates. This is precisely the preprint's
«operational unfolding terminates».

Choice of `Acc` over alternatives:
- `True` — loses all conceptual content; makes the predicate meaningless.
- `WellFounded (· ∈ · : OSet → OSet → Prop)` — a global fact about the
  whole type; not a per-element predicate; cannot serve as a hypothesis
  that distinguishes elements.
- `Acc (· ∈ ·) s` — per-element, unfolds with `Acc.intro`, semantically
  exact, and creates the correct syntactic template for Stage 10.

## Architectural role: template for Stage 10

On `OSet := ZFSet`, `isZFCmode` is universally true (see `isZFCmode_all`):
every ZFSet element is accessible because PSet is inductive. The predicate
has real discriminating power only at Stage 10, when working with `PSet`
directly.

At Stage 10, the analogous predicate `def isPSetZFCmode (p : PSet) : Prop
:= Acc PSet.Mem p` is **non-trivial**: PSet elements representing the
Quine atom A = {A} are constructed via `PSet.mk Unit (fun _ => A)` and
do not satisfy `Acc PSet.Mem` (the membership chain A ∋ A ∋ A ∋ … does
not terminate). Those elements are precisely the ZFA-mode objects excluded
from ZFC-mode. The ZFC/ZFA boundary is visible only at the PSet level;
at the ZFSet level it has already been collapsed. -/
def isZFCmode (s : OSet) : Prop := Acc (· ∈ ·) s

/-- Every element of OSet is in ZFC-mode.

`OSet = ZFSet = Quotient PSet.setoid`, and `PSet` is an inductive Lean
type, so membership is globally well-founded:
`instance : IsWellFounded ZFSet (· ∈ ·)` (Mathlib ZFC.Basic).
Hence `Acc (· ∈ ·) s` holds for every `s : OSet` via `WellFounded.apply`.

This theorem formally records that `OSet := ZFSet` lies entirely within
ZFC-mode — the structural consequence of the architectural choice at
Stage 1. Contrast with Stage 10: on `PSet`, not every element satisfies
the analogous predicate; only well-founded PSet elements are in ZFC-mode. -/
theorem isZFCmode_all (s : OSet) : isZFCmode s :=
  IsWellFounded.wf.apply s

-- ============================================================
-- §IV.3 — Theorem IV.1: ZFC axioms hold in ZFC-mode
-- ============================================================

/-- §IV.3, Theorem IV.1 — verbatim:
«In the ZFC-mode of VR-Sets, all nine classical ZFC axioms are
theorems: Extensionality, Empty, Foundation, Pairing, Union, Power,
Infinity, Replacement, Choice.»

## Status: structural collector

This theorem introduces no new content. Each conjunct is a theorem
already proved in Stages 1–9:

| Conjunct | ZFC axiom         | Lean theorem                    | Stage |
|----------|-------------------|---------------------------------|-------|
| (1) | Extensionality         | `Lemma_II_1_Extensionality`     | 2     |
| (2) | Empty set              | `Lemma_II_2_UniquenessEmpty`    | 2     |
| (3) | Foundation/Regularity  | `Theorem_III_8_Foundation`      | 9     |
| (4) | Pairing                | `Theorem_III_3_Pairing`         | 3     |
| (5) | Union                  | `Theorem_III_4_Union`           | 4     |
| (6) | Power set              | `Theorem_III_5_Power`           | 5     |
| (7) | Infinity               | `Theorem_III_6_Infinity`        | 6     |
| (8) | Replacement            | `Theorem_III_7_Replacement`     | 7     |
| (9) | Choice                 | `Theorem_III_9_Choice`          | 8     |

## Unconditional vs. conditional form

The theorem is stated **unconditionally** on OSet — without the guard
`∀ s : OSet, isZFCmode s → …` — because `isZFCmode` is universally true
(`isZFCmode_all`). The conditional form would be:

```
∀ s : OSet, isZFCmode s →
    (∀ a b, (∀ x, x ∈ a ↔ x ∈ b) → a = b) ∧ … ∧ Foundation ∧ …
```

This conditional form is the **syntactic template** for Stage 10:
the analogous ZFA theorem on PSet will omit Foundation (which fails in
ZFA-mode for cyclic sets) and require the `isPSetZFCmode` guard only on
the Foundation conjunct. The guard is vacuous here; it is non-vacuous at
Stage 10.

## Architectural significance

`Theorem_IV_1_ZFCAxioms` is the formal record that the Lean formalisation
of VR-Sets Part III covers all nine ZFC axioms. It creates the collection
point between Part III (individual closure theorems) and Part IV (modal
analysis). No theorem in this file is new; the new knowledge is their
*joint assembly*. -/
theorem Theorem_IV_1_ZFCAxioms :
    -- (1) Extensionality (§II.2 Lemma 1)
    (∀ a b : OSet, (∀ x, x ∈ a ↔ x ∈ b) → a = b) ∧
    -- (2) Empty set (§II.2 Lemma 2)
    (∃! a : OSet, ∀ x, x ∉ a) ∧
    -- (3) Foundation / Regularity (§III.8)
    (∀ a : OSet, a ≠ ∅ → ∃ x ∈ a, ∀ y ∈ x, y ∉ a) ∧
    -- (4) Pairing (§III.3)
    (∀ a b : OSet, ∀ x, x ∈ osetPair a b ↔ x = a ∨ x = b) ∧
    -- (5) Union (§III.4)
    (∀ a : OSet, ∀ x, x ∈ osetUnion a ↔ ∃ c ∈ a, x ∈ c) ∧
    -- (6) Power set (§III.5)
    (∀ a : OSet, ∀ x, x ∈ osetPower a ↔ x ⊆ a) ∧
    -- (7) Infinity (§III.6)
    ((∅ : OSet) ∈ omega_OSet ∧ ∀ n ∈ omega_OSet, insert n n ∈ omega_OSet) ∧
    -- (8) Replacement (§III.7)
    (∀ (F : OSet → OSet) (a : OSet), ∀ x, x ∈ osetReplacement F a ↔ ∃ y ∈ a, F y = x) ∧
    -- (9) Choice (§III.9)
    (∀ a : OSet, (∀ x ∈ a, (x : OSet) ≠ ∅) → ∃ f : OSet → OSet, ∀ x ∈ a, f x ∈ x) :=
  ⟨Lemma_II_1_Extensionality,
   Lemma_II_2_UniquenessEmpty,
   Theorem_III_8_Foundation,
   Theorem_III_3_Pairing,
   Theorem_III_4_Union,
   Theorem_III_5_Power,
   Theorem_III_6_Infinity,
   Theorem_III_7_Replacement,
   Theorem_III_9_Choice⟩

-- ============================================================
-- §IV.5-§IV.7 — ZFA-mode and Anti-Foundation Axiom (Stage 10)
-- ============================================================

/-- ZFA-mode predicate: an operational PSet is in ZFA-mode if it belongs
to the extended universe that admits non-well-founded sets — Quine atoms
A = {A}, cyclic structures, and self-referential sets.

## §IV.5 (VR-Sets preprint, verbatim)
«The ZFA-mode of VR-Sets consists of ALL operationally specifiable sets,
including those whose operational unfolding does not terminate in the
sense of producing a fixed point: the Quine atom A, whose functionality
reveals exactly A itself, is a valid ZFA-set. ZFA-mode is the maximal
universe; ZFC-mode is the well-founded restriction obtained by adding the
Foundation axiom.»

## §IV.7 (VR-Sets preprint, verbatim — Quine atom)
«The Quine atom A is the unique set satisfying A = {A}: its functionality
reveals exactly one element, which is A itself. A is the simplest cyclic
set in ZFA-mode. AFA guarantees existence and uniqueness of A.»

## Lean implementation: `True`

`isZFAmode` is `True` — every PSet is **declared** to be in ZFA-mode
conceptually. This is not a vacuous or trivial statement: it records the
preprint's foundational decision that ZFA-mode is the maximal universe
(no element is excluded). On OSet = ZFSet, `isZFCmode` was also
universally true (by the inductive structure of ZFSet). The crucial
difference appears not in the predicate value but in the **underlying
type**: ZFSet is well-founded (Quine atoms do not exist), whereas the
preprint's ZFA-mode requires a non-well-founded type.

## The Stage 10 structural boundary: ZFA-mode is ABSENT from mathlib

The preprint's ZFA-mode requires objects that are **provably absent** from
mathlib's PSet and ZFSet. This is the **total structural boundary** of the
VR-Sets Lean formalisation:

### mathlib search result
A systematic search of the full mathlib4 library for terms
`AFA`, `AntiFoundation`, `non-well-founded`, `coinductive` (for sets),
`NonWellFounded`, and `Quine` returned **zero results**. mathlib contains
no AFA or coinductive set infrastructure whatsoever.

### Why PSet cannot represent Quine atoms
`PSet` in mathlib is defined as:
```
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet
```
This is an **inductive** type — not coinductive. Lean's inductive types
generate a **well-founded recursion principle** as their elimination rule.
The direct consequence is `PSet.mem_irrefl : ∀ x : PSet, x ∉ x` (proved
at Mathlib/SetTheory/ZFC/PSet.lean, line 251) and `PSet.mem_wf :
WellFounded (· ∈ · : PSet → PSet → Prop)` (line 239). The Quine atom
would require a PSet value Q satisfying Q ∈ Q, which contradicts
`PSet.mem_irrefl`. So the Quine atom is **provably impossible** in PSet,
not merely hard to construct.

The Lean 4 keyword `coinductive` exists (used for stream-like structures),
but mathlib builds no coinductive set type on it. Implementing ZFA-mode
would require either (a) a coinductive `CoPSet` with an AFA-based quotient,
or (b) taking AFA as a new axiom (which would violate the axiom ceiling
`[propext, Classical.choice, Quot.sound]` of this project). Neither option
is available in the current project.

### The four-level boundary hierarchy
| Stage | Direction | Mechanism |
|-------|-----------|-----------|
| 5, 7, 8 | Lean **wider** | preprint restricts to describable; Lean admits all |
| 9 §III.8 | Lean **narrower** | ZFSet pre-commits to ZFC-mode only |
| 10 | **Total absence** | ZFA-mode objects provably do not exist in PSet/ZFSet |

Stage 10 is stronger than the previous boundaries: at Stages 5/7/8/9 the
preprint concept was at least *expressible* in Lean (as a classical object
or a predicate), even if the operational restriction was lost. At Stage 10,
the ZFA-mode universe itself is **not representable**: the AFA
Statement is provably false in mathlib (see `AFA_Refuted`).

This is also stronger than the VR-Numbers §VIII.6 boundary (ℝ_VR vs ℝ):
there, the classical ℝ existed and computability was metatheoretic. Here,
the ZFA-mode universe simply does not exist in the mathlib type hierarchy.

### Contrast with Conjectures IV.1 and IV.2 (Stage 11)
- Conjectures IV.1/IV.2: open questions — cannot prove or disprove in Lean.
- `AFA_Statement` (Stage 10): **can prove the negation** in Lean
  (`AFA_Refuted`). Not an open question but a provable boundary.

### Theorem IV.2: partial inexpressibility
§IV.6 (preprint): «In ZFA-mode, all ZFC axioms except Foundation hold,
and additionally AFA holds.»
The «all ZFC axioms except Foundation» part holds vacuously on PSet (all 9
axioms, including Foundation, hold on PSet — since PSet is well-founded).
The «AFA holds» part is provably false (`AFA_Refuted`). Therefore Theorem
IV.2 as a **positive statement about ZFA-mode** requires a universe that
does not exist in mathlib; only its negation (= the boundary theorem
`AFA_Refuted`) is formalisable. Theorem IV.2 content is documented here as
a comment; the Lean code records the boundary. -/
def isZFAmode (_ : PSet) : Prop := True

/-- Every PSet element is (trivially) in ZFA-mode.
`isZFAmode` is universally `True` — ZFA-mode is the maximal universe. -/
theorem isZFAmode_all (p : PSet) : isZFAmode p := trivial

-- ============================================================
-- §IV.7 — Quine atom specification and impossibility
-- ============================================================

/-- The Quine-atom specification: the existence of a self-membered PSet.

§IV.7 (VR-Sets preprint, verbatim — the Quine atom A):
«The Quine atom A is the unique set satisfying A = {A}. Its membership
functionality reveals exactly one element: A itself. A ∈ A holds.»

## Lean status: PROVABLY FALSE

`quineAtomSpec` is provably false in mathlib's PSet, as demonstrated by
`quineAtom_impossible`. This is not a formulation of an open question
(contrast with Conjectures IV.1/IV.2 at Stage 11) but a **formal proof
that the preprint's ZFA extension is absent** from mathlib.

`PSet.mem_irrefl : ∀ (x : PSet), x ∉ x` (Mathlib ZFC.PSet, line 251)
is the direct witness. -/
def quineAtomSpec : Prop := ∃ p : PSet.{0}, p ∈ p

/-- The Quine atom is impossible in mathlib's PSet.

`PSet` is an inductive type; membership is well-founded
(`PSet.mem_irrefl`). Therefore no PSet element can be a member of itself.
This is the formal proof that Stage 10's ZFA-mode (which requires Quine
atoms) has no representation in mathlib. -/
theorem quineAtom_impossible : ¬quineAtomSpec :=
  fun ⟨p, h⟩ => PSet.mem_irrefl p h

-- ============================================================
-- §IV.6 — Anti-Foundation Axiom: formulation and refutation
-- ============================================================

/-- The Anti-Foundation Axiom (AFA, Aczel 1988): for every graph (V, E),
there exists a unique function `f : V → PSet` such that for each vertex v,
`f(v)` is PSet-equivalent to the set of images of v's outgoing neighbours.

§IV.6 (VR-Sets preprint, verbatim — AFA):
«For every graph G = (V, E) there exists a unique function f : V → Sets
such that for each v ∈ V, f(v) = {f(w) | (v, w) ∈ E}. This is the
Anti-Foundation Axiom in its graph-decoration form (Aczel 1988, §3).»

## Classical vs. Operational AFA

This `AFA_Statement` formalises **classical AFA** (Aczel 1988, full
generality): the graph (V, E) ranges over all Lean types and functions.
This is the standard formulation used in classical set theory.

The preprint §IV.7 discusses **operational AFA**: AFA restricted to
operationally describable graphs (finite algorithms over finite alphabets).
Operational AFA is a strictly weaker statement (describable graphs are a
countable subset of all graphs). The refutation `AFA_Refuted` below
applies to classical AFA; the status of operational AFA is metatheoretic
(parallel to the Stage 5/7/8 describability boundary) and not formalisable
in Lean.

## PSet.Equiv, not propositional equality

The statement uses `PSet.Equiv` (extensional bisimulation equality) rather
than Lean's propositional `=`. This is the correct notion: in the ZFA
universe, sets with the same members (up to bisimulation) are identical.
Propositional equality would be too strong (requiring syntactic identity
of PSet constructors). -/
def AFA_Statement : Prop :=
    ∀ (V : Type) (E : V → V → Prop),
    ∃! f : V → PSet, ∀ v : V,
        PSet.Equiv (f v) (PSet.mk {w : V // E v w} (fun ⟨w, _⟩ => f w))

/-- The Anti-Foundation Axiom is provably false in mathlib's PSet.

## Proof sketch

Apply `AFA_Statement` to the **universal self-loop** graph: V = Unit
(one vertex), E _ _ = True (one self-loop edge). The assumed decoration
`f : Unit → PSet` would satisfy `PSet.Equiv (f ()) (PSet.mk Unit (fun _ =>
f ()))` — i.e., `f()` is equivalent to the singleton `{f()}`. Since
`{f()} ∋ f()`, by `PSet.Equiv` backward membership: `f () ∈ f ()`.
This contradicts `PSet.mem_irrefl`.

## Methodological note

`AFA_Refuted` is the formal **boundary witness** for Stage 10. It
demonstrates that the mathlib type hierarchy is structurally incompatible
with ZFA-mode: adding AFA as an axiom would make the system inconsistent
over PSet (since PSet already satisfies `¬AFA_Statement`). The only path
to ZFA-mode in Lean 4 is a new coinductive type outside mathlib. -/
theorem AFA_Refuted : ¬AFA_Statement := by
  intro h
  -- Apply AFA to the universal self-loop: V = Unit, every vertex points to itself.
  obtain ⟨f, hf, _⟩ := h Unit (fun _ _ => True)
  -- hf () : PSet.Equiv (f ()) (PSet.mk {w : Unit // True} (fun ⟨w, _⟩ => f w))
  -- The set PSet.mk {_ : Unit // True} (fun ⟨_, _⟩ => f ()) has f () as a member:
  have hmem : f () ∈ PSet.mk {w : Unit // True} (fun ⟨w, _⟩ => f w) :=
    PSet.Mem.mk _ ⟨(), trivial⟩
  -- By PSet.Equiv (hf ()), membership transfers: f () ∈ f ().
  -- PSet.Mem.congr_right (h : Equiv x y) : {z} → z ∈ x ↔ z ∈ y
  exact PSet.mem_irrefl _ ((PSet.Mem.congr_right (hf ())).mpr hmem)

end VR.Sets
