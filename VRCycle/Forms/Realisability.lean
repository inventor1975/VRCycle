-- VR-Forms: Realisability (DOI 10.5281/zenodo.20313735)
-- Part II §II.7. Operationally Realisable Formal Terms.
--
-- Stage 2: isRealisable predicate and three base lemmas.
-- Source: Part II §II.7, Definition II.3.
--
-- Stage 4 retroactive extension (Bridge.lean):
--   Added cases for Conjecture_IV_1_Statement, Conjecture_IV_2_Statement.
--   These are open-realisability cases: formal terms whose realisability
--   is undecided in this Lean cycle (neither proved nor refuted).
--   Extension was planned in Stage 2 doc-comment:
--   «The list extends in Bridge.lean (Stage 4) when new realisable
--   formal terms are added.» — executed here.
--
-- Architectural stage (CLAUDE.md): plan-before-code protocol applied.
-- Plan accepted by Opus before this code was written.
--
-- Imports:
--   VRCycle.Forms.Language     — FormalTerm, Register, ⌜·⌝ notation
--   VRCycle.Sets.Modes         — OSet, osetEmpty, osetPair, omega_OSet,
--                                  Theorem_III_3_Pairing, Theorem_III_6_Infinity,
--                                  AFA_Statement, AFA_Refuted
--                                  (via chain: Modes → ZF → Foundation)
--   VRCycle.Sets.Conjectures   — Conjecture_IV_1_Statement,
--                                  Conjecture_IV_2_Statement
--                                  (Stage 4 addition; Conjectures → Modes)
--
-- This file defines the realisability predicate (isRealisable) and
-- proves it for the three base formal terms of Stage 2.
-- Transit pattern is Stage 3 (Transit.lean).
-- Bridge witnesses to VR-Sets are Stage 4 (Bridge.lean).

import VRCycle.Forms.Language
import VRCycle.Sets.Modes
import VRCycle.Sets.Conjectures

namespace VR.Forms

open VR.Sets


-- ============================================================
-- §II.7 — Operational realisability predicate
-- ============================================================

/-- Operational realisability of a formal term.

## §II.7, Definition II.3 (operational realisability) — verbatim

«A formal term ⌜τ⌝ is called **operationally realisable** if in the
operational register there exists an operational set A such that the
description τ corresponds to the functionality A.

Equivalently: ⌜τ⌝ is operationally realisable if τ (without the
formal-register marker) is an admissible description in VR-Sets
satisfying the closure principle.»

**Clarification on register language (added 2026-05-26):**
The two-register language describes modes of description, not separate
operational levels. All descriptions are operational acts; the registers
distinguish whether the described referent has an operational correlate
(operational register) or is a formal term referring to a non-operational
concept such as actual infinity (formal register). This clarification
aligns with the expanded operational position recorded in VR-UNIQUENESS.md.

§II.7 continues (verbatim): «The distinction «realisable / non-realisable»
is a property of the formal term as a pair (description, register). It only
tells whether the formal term has an operational correlate. The formal term
itself does not become «better» or «worse» from the presence or absence of
realisation; in the formal register all terms are equal.»

## Lean implementation — match function with characteristic propositions

`isRealisable` is a `def`-function mapping each `FormalTerm` to a Lean `Prop`.
For the formal terms in this Lean cycle, the Prop is the **characteristic
operational statement** associated with the description:

| Formal term                       | `isRealisable t` reduces to                               |
|-----------------------------------|-----------------------------------------------------------|
| `⌜"∅"⌝`                          | `∃ s : OSet, ∀ x, x ∉ s`                                |
| `⌜"omega_OSet"⌝`                 | `∃ s : OSet, ∅ ∈ s ∧ ∀ n ∈ s, insert n n ∈ s`          |
| `⌜"osetPair"⌝`                   | `∀ a b : OSet, ∃ s : OSet, ∀ x, x ∈ s ↔ x = a ∨ x = b` |
| `⌜"Conjecture_IV_1_Statement"⌝`  | `VR.Sets.Conjecture_IV_1_Statement` (open; Stage 4)      |
| `⌜"Conjecture_IV_2_Statement"⌝`  | `VR.Sets.Conjecture_IV_2_Statement` (open; Stage 4)      |
| `⌜"AFA_Statement"⌝`              | `VR.Sets.AFA_Statement` (provably False; Stage 4)        |
| any other term                    | `False`                                                   |

Each realisable case maps to an existential (or universal-existential) Lean
Prop, not to `True`. This preserves the mathematical content of the proof:
`isRealisable_empty` does not hold trivially — it holds by `⟨osetEmpty, _⟩`;
`isRealisable_osetPair` holds by `fun a b => ⟨osetPair a b, _⟩`.

## Three-category structure of formal terms (Stage 4, Bridge.lean)

The `match` function embodies a **triadic classification** of formal terms
by their realisability status in this Lean cycle:

**Category (a) — Provably realisable** (Stages 2–3):
  `⌜"∅"⌝`, `⌜"omega_OSet"⌝`, `⌜"osetPair"⌝`.
  Proved by concrete witnesses from VR-Sets. Stage 2 lemmas.

**Category (b) — Open realisability** (Stage 4 retroactive extension):
  `⌜"Conjecture_IV_1_Statement"⌝`, `⌜"Conjecture_IV_2_Statement"⌝`.
  Realisability status undecided: `isRealisable ⌜"Conjecture_IV_X"⌝ ↔`
  `Conjecture_IV_X_Statement`. Since the Conjectures are open in VR-Sets
  (§IX.1, Stage 11), their formal terms' realisability is also open.
  Bridge theorems: `bridge_Conjecture_IV_1`, `bridge_Conjecture_IV_2`
  (Stage 4, Bridge.lean).

**Category (c) — Provably non-realisable** (Stage 4 bridge):
  `⌜"AFA_Statement"⌝`.
  `isRealisable ⌜"AFA_Statement"⌝ = AFA_Statement`, which is provably
  False in mathlib's PSet (`AFA_Refuted`, VR-Sets Stage 10).
  Bridge theorem: `bridge_AFA := AFA_Refuted` (Stage 4, Bridge.lean).

**Catch-all** — metatheoretically non-realisable:
  ⌜"Vitali"⌝, ⌜"Russell_class"⌝, ⌜"dragon"⌝, ⌜"classical_R"⌝, …
  Reduce to `False` by the catch-all; `¬isRealisable` is trivial (`id`).
  Non-realisability is metatheoretic (no VR-Sets theorem needed).

This triadic architecture mirrors VR-Sets Stage 11's three-tier structure
(proved theorems, refuted claims, open formulations) but **localised at
the level of formal terms** in the formal register.

## Closed-world assumption — `| _ => False`

The catch-all `| _ => False` is a **closed-world assumption**: the list of
named cases in the `match` is the explicit enumeration of formal terms
with non-trivial realisability status in this Lean cycle.

**Extended in Stage 4** (planned in the original Stage 2 doc-comment):
`⌜"Conjecture_IV_1_Statement"⌝` and `⌜"Conjecture_IV_2_Statement"⌝` were
added by retroactive extension in Bridge.lean (Stage 4, executed here).
`import VRCycle.Sets.Conjectures` was added at that time.

Equivalently (§II.7, verbatim): «Those [formal terms with an operational
correlate] form a distinguished subfamily of formal terms — let us call it
the **operationally realisable** formal terms.» This Lean `match` function is
the explicit enumeration of that subfamily within the scope of this cycle.

## Boundary reminder — §II.7, AFA vs. Conjectures vs. Vitali/Russell

`⌜"AFA_Statement"⌝`: **Lean-decidable non-realisable**.
  `VR.Sets.AFA_Statement` is provably false (`AFA_Refuted`, VR-Sets Stage 10).
  `¬isRealisable ⌜"AFA_Statement"⌝` requires `AFA_Refuted` — a genuine
  VR-Sets theorem. This is a **provable boundary**.

`⌜"Conjecture_IV_X_Statement"⌝`: **Lean-open**.
  `VR.Sets.Conjecture_IV_X_Statement` is open (neither proved nor refuted).
  `isRealisable ⌜"Conjecture_IV_X_Statement"⌝` is therefore also open.
  Bridge iff is proved trivially (definitional equality); its mathematical
  content is open. This is an **open boundary**.

`⌜"Vitali"⌝`, ⌜"Russell_class"⌝`, ⌜"dragon"⌝, ⌜"classical_R"⌝:
  **Metatheoretically non-realisable** (catch-all → `False`).
  Non-realisability documented metatheoretically. No VR-Sets theorem needed.
  Parallel to the countability of ℘_VR(ω) vs. ℘(ω) — not Lean-expressible.

## Technical note — `OSet.{0}` universe annotation

This `def` lives in `namespace VR.Forms` with `open VR.Sets`. Unlike
definitions inside `namespace VR.Sets` (where `OSet` is universe-pinned by
surrounding context), here `OSet` inside `match`-induced quantifications
requires explicit `.{0}` annotation. Without it, Lean cannot infer the
universe level for the quantified variable. This is the first cross-namespace
universe management point in the VR-Forms cycle, analogous to `PSet.{0}`
in VR-Sets Stage 10's `quineAtomSpec`. See Methodological Notes (future
Part IX) for discussion of the shallow-embedding/cross-namespace interaction.

## What this file does and does not do

**Does**:
  - Defines `isRealisable : FormalTerm → Prop` (the central predicate of
    VR-Forms Part II §II.7).
  - Proves `isRealisable_empty`, `isRealisable_omega`, `isRealisable_osetPair`
    — the three base realisable formal terms of this cycle.
  - Includes the `AFA_Statement` case in `isRealisable` for use by Stage 4.

**Does not**:
  - Define `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝` — Stage 4 object.
  - Define translation π or the transit pattern — Stage 3, `Transit.lean`.
  - Handle `⌜"Conjecture_IV_1_Statement"⌝`, `⌜"OSet"⌝`, etc. — Stage 4. -/
def isRealisable (t : FormalTerm) : Prop :=
  match t with
  -- §II.7 Examples of realisable formal terms:
  -- §II.7: «⌜∅⌝, ⌜{∅}⌝, ⌜ω⌝, ⌜℘_VR(ω)⌝, ⌜ℝ_VR⌝ — all of these are realisable.
  -- Each corresponds to an operational set of VR-Sets.»
  | ⟨"∅",          .formal⟩ =>
      -- Realisability: there exists an OSet with empty functionality.
      -- Witness (Stage 2): osetEmpty.
      ∃ s : OSet.{0}, ∀ x : OSet.{0}, x ∉ s
  | ⟨"omega_OSet", .formal⟩ =>
      -- Realisability: there exists an OSet satisfying the infinity axiom.
      -- Witness (Stage 2): omega_OSet.
      ∃ s : OSet.{0},
        (∅ : OSet.{0}) ∈ s ∧ ∀ n : OSet.{0}, n ∈ s → insert n n ∈ s
  | ⟨"osetPair",   .formal⟩ =>
      -- Realisability: the pair operation is universally realisable —
      -- for any two OSet elements a, b, there exists a pair set {a, b}.
      -- Witness (Stage 2): fun a b => ⟨osetPair a b, Theorem_III_3_Pairing a b⟩.
      -- NOTE: closed Prop (∀ quantifies a b internally); theorem isRealisable_osetPair
      -- has no (a b : OSet) parameters — see doc below.
      ∀ a b : OSet.{0},
        ∃ s : OSet.{0}, ∀ x : OSet.{0}, x ∈ s ↔ x = a ∨ x = b
  | ⟨"Conjecture_IV_1_Statement", .formal⟩ =>
      -- Open-realisability case: isRealisable ⌜"Conjecture_IV_1_Statement"⌝
      --   ↔ Conjecture_IV_1_Statement (bridge_Conjecture_IV_1, Stage 4).
      -- Conjecture_IV_1_Statement is open in VR-Sets (§IX.1 Question 1).
      -- Neither proved nor refuted in this Lean cycle.
      -- Stage 4 retroactive extension — planned in Stage 2 doc-comment.
      Conjecture_IV_1_Statement
  | ⟨"Conjecture_IV_2_Statement", .formal⟩ =>
      -- Open-realisability case: isRealisable ⌜"Conjecture_IV_2_Statement"⌝
      --   ↔ Conjecture_IV_2_Statement (bridge_Conjecture_IV_2, Stage 4).
      -- Conjecture_IV_2_Statement is open in VR-Sets (§IX.1 Question 2).
      -- Neither proved nor refuted in this Lean cycle.
      -- Stage 4 retroactive extension — planned in Stage 2 doc-comment.
      Conjecture_IV_2_Statement
  | ⟨"AFA_Statement", .formal⟩ =>
      -- VR-Sets-refutable case: isRealisable ⌜"AFA_Statement"⌝ ↔ AFA_Statement.
      -- AFA_Statement is provably False in mathlib (AFA_Refuted, Stage 10).
      -- Therefore ¬isRealisable ⌜"AFA_Statement"⌝ requires AFA_Refuted — not trivial.
      -- Used by bridge_AFA in Bridge.lean (Stage 4).
      -- BOUNDARY NOTE: this is the VR-Sets structural boundary appearing inside
      -- the Forms realisability predicate. The formal register admits ⌜AFA_Statement⌝
      -- as a formal term (Principle of Forms, §II.4); it is non-realisable because
      -- the corresponding operational claim is refuted in VR-Sets Lean.
      AFA_Statement
  | _ =>
      -- Catch-all: all other formal terms are non-realisable.
      -- Level 1 negative cases (trivially False):
      --   ⌜"Vitali"⌝, ⌜"Russell_class"⌝, ⌜"dragon"⌝, ⌜"classical_R"⌝, …
      -- Their non-realisability is metatheoretic (no VR-Sets theorem needed).
      -- ¬isRealisable ⌜"Vitali"⌝ := id  (False.elim, no math content required).
      -- See doc-comment above for the two-level boundary structure.
      False


-- ============================================================
-- §II.7 — Base lemmas: realisable cases
-- ============================================================

/-- §II.7 base lemma: the formal term ⌜∅⌝ is operationally realisable.

## Preprint (§II.7, Examples of realisable formal terms) — verbatim
«⌜∅⌝ ... all of these are realisable. Each corresponds to an operational
set of VR-Sets. ∅ is the empty set in the operational register. By Lemma 2
of VR-Sets it is the unique operational object with empty functionality.»

## Lean proof
`isRealisable ⌜"∅"⌝` reduces to `∃ s : OSet, ∀ x, x ∉ s`.
Witness: `osetEmpty` (VR-Sets Stage 1, Foundation.lean).
Proof of `∀ x : OSet, x ∉ osetEmpty`: `ZFSet.notMem_empty`.

## Axiom profile: [propext, Quot.sound] -/
theorem isRealisable_empty : isRealisable ⌜"∅"⌝ :=
  ⟨osetEmpty, ZFSet.notMem_empty⟩


/-- §II.7 base lemma: the formal term ⌜omega_OSet⌝ is operationally realisable.

## Preprint (§II.7, Examples of realisable formal terms) — verbatim
«⌜ω⌝ ... all of these are realisable. Each corresponds to an operational
set of VR-Sets.»

## Lean proof
`isRealisable ⌜"omega_OSet"⌝` reduces to
  `∃ s : OSet, ∅ ∈ s ∧ ∀ n ∈ s, insert n n ∈ s`.
Witness: `omega_OSet` (VR-Sets Stage 6, ZF.lean).
Proof: `Theorem_III_6_Infinity` from VR-Sets ZF.lean (Stage 6):
  `(∅ : OSet) ∈ omega_OSet ∧ ∀ n, n ∈ omega_OSet → insert n n ∈ omega_OSet`.

## Axiom profile: [propext, Quot.sound] -/
theorem isRealisable_omega : isRealisable ⌜"omega_OSet"⌝ :=
  ⟨omega_OSet, Theorem_III_6_Infinity⟩


/-- §II.7 base lemma: the formal term ⌜osetPair⌝ is operationally realisable.

## Preprint (§II.7) — verbatim
«Any description of a computable functionality is an operationally realisable
formal term.» The pair operation {a, b} is a computable functionality (for any
operationally given a and b, {a, b} is constructible — VR-Sets Theorem III.3).

## Lean proof
`isRealisable ⌜"osetPair"⌝` reduces to the **closed** proposition
  `∀ a b : OSet, ∃ s : OSet, ∀ x, x ∈ s ↔ x = a ∨ x = b`.
This is a closed Prop: the universal quantifiers over `a b` are internal to the
type of `isRealisable ⌜"osetPair"⌝`. There are no free `(a b : OSet)` parameters
in this theorem's signature.

Witness: `fun a b => ⟨osetPair a b, Theorem_III_3_Pairing a b⟩`.
- `osetPair a b : OSet` is the pair set {a, b} (VR-Sets Stage 3, ZF.lean).
- `Theorem_III_3_Pairing a b : ∀ x, x ∈ osetPair a b ↔ x = a ∨ x = b`.

## Note on PLAN.md notation
PLAN.md writes `isRealisable_pair (a b : OSet) : isRealisable ⌜osetPair a b⌝`.
The notation `⌜osetPair a b⌝` was schematic — `⌜·⌝` accepts a single ident or
str (Language.lean, Stage 1). The actual Lean theorem is `isRealisable_osetPair`
with no free parameters; `a b` are bound by the ∀ inside `isRealisable ⌜"osetPair"⌝`.

## Axiom profile: [propext, Quot.sound] -/
theorem isRealisable_osetPair : isRealisable ⌜"osetPair"⌝ :=
  fun a b => ⟨osetPair a b, Theorem_III_3_Pairing a b⟩


-- ============================================================
-- Axiom audit — Stage 2
-- ============================================================

-- STAGE 2. SOURCE: Part II §II.7, Definition II.3.
-- LEAN OBJECTS: isRealisable (def), isRealisable_empty, isRealisable_omega,
--               isRealisable_osetPair (theorems).
-- AXIOM AUDIT:
--   Expected for all: [propext, Quot.sound].
--   Note: no Classical.choice — pairing and infinity theorems from VR-Sets
--   use ZFSet quotient structure (Quot.sound + propext for iff-reasoning)
--   but not classical choice.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms isRealisable
#print axioms isRealisable_empty
#print axioms isRealisable_omega
#print axioms isRealisable_osetPair

end VR.Forms
