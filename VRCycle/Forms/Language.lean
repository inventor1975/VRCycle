-- VR-Forms: Language (DOI 10.5281/zenodo.20313735)
-- Part II. The Formal Language.
--
-- Stage 1: Register inductive, FormalTerm structure, ⌜·⌝ notation.
-- Source: Part II §II.1–§II.4.
--
-- Architectural stage (CLAUDE.md): plan-before-code protocol applied.
-- Plan accepted by Opus before this code was written.
--
-- This file defines the syntactic skeleton of formal terms only.
-- Realisability is Stage 2 (Realisability.lean).
-- Transit pattern and translation π are Stage 3 (Transit.lean).
-- Bridge to VR-Sets is Stage 4 (Bridge.lean).
--
-- No imports: Register and FormalTerm are pure Lean 4 structures;
-- String and inductive/structure are built into the Lean 4 prelude.
-- Language.lean does not import VRCycle.Sets.

namespace VR.Forms

-- ============================================================
-- §II.2 — The two registers
-- ============================================================
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
-- ============================================================

/-- The two registers of the VR-Forms two-register system.

## §II.2, Definition II.1 (register-separator) — verbatim

«For any term τ, the notation ⌜τ⌝ means: the term τ is considered
in the formal register. The notation τ without brackets means: the
term is considered in the operational register.

⌜·⌝ is not a function or operation. It is a sign of the **mode of
consideration**. It indicates in which of the two registers a given
term is read.»

## Lean implementation

`Register` is a two-constructor inductive type marking the mode
of consideration:

- `.operational` — the operational register (L₀): the term denotes
  an operational set in the sense of VR-Sets. In VR-Sets notation:
  the term τ is read as an object — an action upon ∅.
- `.formal` — the formal register (L₁): the term is a syntactic
  record, considered as a formula. No operational load is imposed;
  the term may be contradictory, non-operational, or paradoxical.

The `⌜·⌝` notation (below) always produces register `.formal`.
Operational register objects are the `OSet` elements of VR-Sets;
they do not appear as `FormalTerm.mk _ .operational` in this cycle.

## Why no `.mixed` constructor

Mixed formulas (Part VII §VII.2) combine OSet quantifiers with
`isRealisable` predicates on formal terms. They are Lean `Prop`
objects at the meta-level — not a third register for `FormalTerm`.

A `.mixed` constructor would be a category error: mixed formulas
are a third kind of *formula in the two-register theory*, not a
third register for individual terms. The register of a term is
always `.operational` or `.formal`; the mixed character is a
property of the *formula* combining them. See `Examples.lean`
(Stage 5) for the Lean formalisation of mixed formulas. -/
inductive Register where
  | operational
  | formal
  deriving DecidableEq, Repr


-- ============================================================
-- §II.3 — Definition of a formal term
-- ============================================================

/-- A formal term in the sense of VR-Forms Part II §II.3.

## §II.3, Definition II.2 (formal term) — verbatim

«A **formal term** is any correctly built syntactic record of a
description, considered in the formal register.

Formally: a formal term is a pair (τ, F), where τ is a syntactically
correct term of the language of VR-Forms, and F is the register-marker
indicating «formal». The notation ⌜τ⌝ denotes this pair.»

## Commentary on Definition II.2 (§II.3) — verbatim

(1) «A formal term is a **pair**: syntax plus indication of mode.
The same τ specifies different entities depending on the register:
an operational set (in the operational) or a formal term (in the
formal).»

(2) «**Correctly built syntactic record** means: the term is built
according to the rules of §II.1. No other conditions — operationality,
consistency, constructivity — are imposed. A formal term may be
contradictory, non-operational, refer to uncountable collections,
describe the impossible. All this is permitted.»

(3) «In the formal register there is no distinction between «existing»
and «non-existing» formal terms. The differences in their content
(countable, paradoxical, non-mathematical) are properties of
**the description**, not properties of being.»

## §II.4, Principle of forms — verbatim

«**Every syntactically correct record of a description specifies
a formal term.**
No restrictions: operationality is not required, consistency is not
required, describability in any special sense is not required. It
suffices that the record is syntactically correct by §II.1.»

In Lean this principle is a structural fact: `FormalTerm.mk s r` is
well-typed for any `s : String` and `r : Register`. No side conditions.

## Lean implementation — CLAUDE.md Decision 1: shallow embedding

`FormalTerm` is a Lean structure with two fields:

- `description : String` — the human-readable name of the description.
  This is **metadata only**: Lean reasoning does not inspect the string.
  The description identifies the formal term for the human reader;
  `isRealisable` (Stage 2) is defined by case analysis on the whole
  `FormalTerm` via `DecidableEq`, not by parsing the description string.

- `register : Register` — the mode of consideration; defaults to
  `.formal`. All terms produced by the `⌜·⌝` notation have `.formal`
  register.

`DecidableEq FormalTerm` (derived from computable `String.decEq` and
`Register`-equality) enables case analysis in `isRealisable` (Stage 2)
with `#print axioms FormalTerm → []`: no classical axioms needed.

## Shallow vs. deep embedding — CLAUDE.md Decision 1

In a **deep embedding**, `FormalTerm` would be an inductive type
representing the full syntactic structure of descriptions in §II.1:
constructors for ∅, t(·), {x : φ(x)}, ∈, ≡, ¬, ∧, ∀, etc. The
shallow embedding deliberately avoids this:

- Building the deep syntactic structure is the proof-theory layer
  (Part III). It would require a separate `Formula L₁`, `Derivation`
  infrastructure — a project larger than the whole VR-Forms preprint
  cycle, and out of scope.
- `description : String` serves as an **identifier** for the formal
  term, not a parseable formula. It is sufficient for Stages 1–5 of
  this cycle, which treat formal terms as named objects, not as parsed
  syntax trees.
- The shallow choice is consistent with CLAUDE.md Decision 1 and with
  the VR cycle methodology of documenting boundaries explicitly.

## Structural boundary — conservativity — CLAUDE.md Decision 5

The central result of VR-Forms is **Theorem III.1 (conservativity)**:
VR-Forms (the two-register theory T₁) is conservative over VR-Sets
(the operational theory T₀) in the operational register: the formal
register does not allow new statements about operational sets to be
proved (§II.8, «Conservative extensions»).

This theorem is **not formalised** in this Lean cycle. Full
formalisation would require deep-embedded `Formula L₀`, `Formula L₁`,
`Derivation T₀`, `Derivation T₁` types, and an induction proof over
derivations — a proof-theory project beyond the scope of one preprint
cycle. This is the **explicit structural boundary** of VR-Forms Lean,
parallel to (but methodologically different from) the five boundaries
of VR-Sets Lean.

The boundary here is shallow-vs-deep embedding (a gap in proof-theory
infrastructure), not a gap in mathlib's set-theoretic infrastructure.
The transit pattern (Part IV §IV.2) operates by external reference to
the preprint's proof of conservativity; see `Transit.lean` (Stage 3).

## What this file does and does not do

**Does**: defines the syntactic skeleton —
  `Register`, `FormalTerm`, and the `⌜·⌝` notation.

**Does not**:
  - Define `isRealisable` — Stage 2, `Realisability.lean` (§II.7).
  - Define translation π or the transit pattern — Stage 3, `Transit.lean`.
  - Reference VR-Sets objects (`OSet`, `AFA_Statement`, …) — this file
    has no import from `VRCycle.Sets`; it is self-contained. -/
structure FormalTerm where
  /-- Human-readable description of the formal term (metadata only).
      Lean reasoning uses `DecidableEq FormalTerm`, not string inspection.
      See `Realisability.lean` (Stage 2) for how `isRealisable` is defined
      by case analysis on known `FormalTerm` values. -/
  description : String
  /-- Register marker. Defaults to `.formal`; all `⌜·⌝` terms are formal.
      Operational-register objects are `OSet` elements (VR-Sets), not
      `FormalTerm.mk _ .operational` values. -/
  register : Register := .formal
  deriving DecidableEq, Repr


-- ============================================================
-- §II.2, Definition II.1 — The ⌜·⌝ notation
-- ============================================================

-- Identifier form: ⌜OSet⌝, ⌜osetEmpty⌝, ⌜AFA_Statement⌝, …
--   Produces FormalTerm.mk "OSet" .formal (description = identifier name).
--   Used when the description is a valid Lean identifier.
macro "⌜" n:ident "⌝" : term =>
  `(FormalTerm.mk $(Lean.quote n.getId.toString) .formal)

-- String form: ⌜"∅"⌝, ⌜"ω"⌝, ⌜"osetPair"⌝, …
--   Produces FormalTerm.mk "∅" .formal (description = string literal).
--   Used when the description contains special Unicode characters
--   (∅, ω, ℝ, …) or when a string literal is more precise.
--   Both forms are equal when they encode the same string:
--     ⌜OSet⌝ = ⌜"OSet"⌝  (DecidableEq confirms at #eval).
macro "⌜" s:str "⌝" : term =>
  `(FormalTerm.mk $s .formal)


-- ============================================================
-- Axiom audit — Stage 1
-- ============================================================

-- STAGE 1. SOURCE: Part II §II.1–§II.4.
-- LEAN OBJECTS: Register (inductive), FormalTerm (structure), ⌜·⌝ (macro).
-- AXIOM AUDIT:
--   Expected: 'VR.Forms.Register'   does not depend on any axioms.
--   Expected: 'VR.Forms.FormalTerm' does not depend on any axioms.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms Register
#print axioms FormalTerm

end VR.Forms
