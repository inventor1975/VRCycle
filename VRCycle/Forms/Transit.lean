-- VR-Forms: Transit (DOI 10.5281/zenodo.20313735)
-- Part III §III.2. The π translation and transit pattern.
--
-- Stage 3: translate_pi (def), three direct-proof theorems,
--          translate_implies_realisable, transit pattern documentation.
-- Source: Part III §III.2, Part IV §IV.2.
--
-- Architectural stage (CLAUDE.md): plan-before-code protocol applied.
-- Plan accepted by Opus before this code was written.
--
-- Imports:
--   VRCycle.Forms.Realisability   — isRealisable, FormalTerm, ⌜·⌝,
--                                    OSet, osetEmpty, osetPair, omega_OSet,
--                                    ZFSet.notMem_empty, Theorem_III_3_Pairing,
--                                    Theorem_III_6_Infinity, AFA_Statement
--                                    (via chain: Realisability → Language + Sets.Modes)
--
-- ## Two-layer structure of this file (Methodological Observation 4)
--
-- Stage 2 (`Realisability.lean`) introduced `isRealisable : FormalTerm → Prop`
-- as the **existential** layer: a formal term is realisable if there EXISTS some
-- operational set with the corresponding functionality (Definition II.3, §II.7).
--
-- Stage 3 introduces `translate_pi : FormalTerm → Prop` as the **specific** layer:
-- the direct operational predicate referencing concrete named VR-Sets objects.
-- For ⌜"∅"⌝, this is `∀ x, x ∉ osetEmpty` (not `∃ s, ∀ x, x ∉ s`).
-- For ⌜"omega_OSet"⌝, this is `∅ ∈ omega_OSet ∧ …` (not `∃ s, ∅ ∈ s ∧ …`).
--
-- The relation `translate_implies_realisable : ∀ t, translate_pi t → isRealisable t`
-- connects the two layers via existential introduction with the named witness.
-- The **converse does not hold**: from `∃ s, ∀ x, x ∉ s` one cannot recover
-- `∀ x, x ∉ osetEmpty` — no Skolemisation across the existential.
-- The preprint (§II.7 / §III.2) conflates the two levels; Lean separates them,
-- and the forward implication `translate_pi t → isRealisable t` is the
-- formal content of the transit pattern in this cycle.
-- (See Part IX §IX.? for methodological discussion; Part X of VR-Sets v1.0.1
-- documents the parallel for `isZFCmode` vs concrete theorem application.)

import VRCycle.Forms.Realisability

namespace VR.Forms

open VR.Sets


-- ============================================================
-- §III.2 — Translation π (shallow implementation)
-- ============================================================

/-- Translation π: the shallow-embedding map from formal terms to their
defining operational predicates.

## §III.2 (VR-Forms preprint) — verbatim statement of π

«The translation π maps every L₁-formula to an L₀-formula by the
following rules:

  (i)  For ψ ∈ L₀ (an ontological formula): π(ψ) = ψ.
       (π is identity on the ontological register.)

**Clarification on register language (added 2026-05-26):**
The two-register language describes modes of description, not separate
ontological levels. All descriptions are operational acts; the registers
distinguish whether the described referent has an operational correlate
(operational register) or is a formal term referring to a non-operational
concept such as actual infinity (formal register). This clarification
aligns with the expanded operational position recorded in VR-UNIQUENESS.md.

  (ii) For a formal term ⌜τ⌝ with description τ:
       π(⌜τ⌝) = δ_τ, where δ_τ is the defining predicate of τ
       in the operational register — the characterisation of the
       operational set that τ describes.

  (iii) Connectives and quantifiers are preserved:
        π(¬φ) = ¬π(φ),  π(φ ∧ ψ) = π(φ) ∧ π(ψ),
        π(∀x, φ) = ∀x, π(φ),  etc.»

## §III.2, Theorem III.1 (conservativity) — verbatim

«**Theorem III.1.** The theory T₁ (VR-Forms) is conservative over T₀
(VR-Sets) in the ontological register: any formula φ in the language L₀
of the ontological register that is derivable in T₁ is already derivable
in T₀.

Equivalently: formal terms do not produce new ontological theorems.
Any proof in T₁ using formal-register formulas can be translated,
via π, into a proof in T₀ not mentioning formal terms.»

## Why Theorem III.1 is not formalised here

Full formalisation requires deep-embedded `Formula L₀`, `Formula L₁`,
`Derivation T₀`, `Derivation T₁` types (not in mathlib at production
quality) and an induction proof over derivations on the structure of π.
This is the **explicit structural boundary** of VR-Forms Lean (CLAUDE.md
Decision 5). The transit pattern (§IV.2) is documented below as a comment
template; see the `TransitPattern` section.

## Lean implementation — shallow π

In the shallow embedding, π is implemented as a **total function**
`translate_pi : FormalTerm → Prop` mapping each formal term to its
defining operational predicate. This corresponds to rule (ii) of π above.

Difference from `isRealisable` (§II.7, Stage 2):

| | `isRealisable t` | `translate_pi t` |
|---|---|---|
| Layer | existential | specific |
| `⌜"∅"⌝` | `∃ s, ∀ x, x ∉ s` | `∀ x, x ∉ osetEmpty` |
| `⌜"omega_OSet"⌝` | `∃ s, ∅ ∈ s ∧ …` | `∅ ∈ omega_OSet ∧ …` |
| `⌜"osetPair"⌝` | `∀ a b, ∃ s, x ∈ s ↔ …` | `∀ a b x, x ∈ osetPair a b ↔ …` |
| `⌜"AFA_Statement"⌝` | `AFA_Statement` | `AFA_Statement` |
| catch-all | `False` | `False` |

`translate_pi` is total (no `Option` wrapper): π is total in the preprint;
the catch-all `| _ => False` mirrors `isRealisable`'s catch-all exactly.
Connection: `translate_implies_realisable : ∀ t, translate_pi t → isRealisable t`.

## Universe annotation `OSet.{0}`

Same cross-namespace universe management as Stage 2 (Realisability.lean):
`OSet` requires `.{0}` in match-induced quantifications inside
`namespace VR.Forms`. See Stage 2 doc-comment for full discussion.

## What this file does and does not do

**Does**:
  - Defines `translate_pi : FormalTerm → Prop` (§III.2 π, shallow).
  - Proves `translate_pi_empty`, `translate_pi_omega`,
    `translate_pi_osetPair` (direct VR-Sets theorems).
  - Proves `translate_implies_realisable` (two-layer connection).
  - Documents the transit pattern as a comment template (§IV.2).

**Does not**:
  - Formalise Theorem III.1 (conservativity) — structural boundary.
  - Define Formula L₁ or Derivation T₁ — proof-theory layer, out of scope.
  - Handle `⌜"AFA_Statement"⌝` operationally: `translate_pi ⌜"AFA_Statement"⌝`
    = `AFA_Statement`, which is provably False (Stage 4, Bridge.lean).
  - Define bridge theorems — Stage 4. -/
def translate_pi (t : FormalTerm) : Prop :=
  match t with
  -- §III.2 (ii): defining predicate of each formal term in the VR-Sets
  -- language. The predicate references the specific VR-Sets object by name.
  | ⟨"∅",             .formal⟩ =>
      -- π(⌜"∅"⌝) = «∅ has empty functionality»:
      --   ∀ x : OSet, x ∉ osetEmpty
      -- Specific, not existential. (∃ s, ∀ x, x ∉ s) is isRealisable.
      ∀ x : OSet.{0}, x ∉ osetEmpty
  | ⟨"omega_OSet",    .formal⟩ =>
      -- π(⌜"omega_OSet"⌝) = «omega_OSet satisfies the infinity predicate»:
      --   ∅ ∈ omega_OSet ∧ ∀ n ∈ omega_OSet, insert n n ∈ omega_OSet
      (∅ : OSet.{0}) ∈ omega_OSet ∧
      ∀ n : OSet.{0}, n ∈ omega_OSet → insert n n ∈ omega_OSet
  | ⟨"osetPair",      .formal⟩ =>
      -- π(⌜"osetPair"⌝) = «osetPair a b contains exactly {a, b}»:
      --   ∀ a b x, x ∈ osetPair a b ↔ x = a ∨ x = b
      -- NOTE: the universals over a b x are INSIDE translate_pi;
      -- contrast isRealisable ⌜"osetPair"⌝ = ∀ a b, ∃ s, ∀ x, x ∈ s ↔ …
      ∀ (a b x : OSet.{0}), x ∈ osetPair a b ↔ x = a ∨ x = b
  | ⟨"AFA_Statement", .formal⟩ =>
      -- π(⌜"AFA_Statement"⌝) = AFA_Statement (the VR-Sets refutable claim).
      -- AFA_Statement is provably False in mathlib (AFA_Refuted, VR-Sets Stage 10).
      -- `¬translate_pi ⌜"AFA_Statement"⌝` requires AFA_Refuted — Stage 4.
      AFA_Statement
  | _ =>
      -- π is total; catch-all maps to False (no operational predicate).
      -- Parallel to isRealisable's catch-all. See translate_implies_realisable.
      False


-- ============================================================
-- §IV.2 — Transit pattern (documented, NOT a Lean theorem)
-- ============================================================

-- SOURCE: VR-Forms preprint Part III §III.2, Part IV §IV.2.
--
-- ## Theorem III.1 (conservativity) — BOUNDARY
--
-- Theorem III.1 is the central result of VR-Forms: T₁ is conservative
-- over T₀. Its proof is metalogical (induction over derivations in T₁;
-- π maps each derivation step to T₀). Full formalisation requires
-- deep-embedded Formula L₀, Formula L₁, Derivation T₀, Derivation T₁
-- types and the π-preservation proof — a proof-theory project beyond the
-- scope of this Lean cycle (CLAUDE.md Decision 5).
--
-- STATUS: Theorem III.1 is documented here by external reference to the
-- preprint. This is an honest boundary: the conservativity theorem is
-- *proved* in the preprint (metalogically), but *not formalisable* at
-- this depth in shallow-Lean. A `def : Prop` would misrepresent it as
-- open (Conjectures IV.1/IV.2 pattern); it is not open.
--
-- ## Transit pattern — application template (§IV.2)
--
-- Given a proof:
--   h : translate_pi ⌜τ⌝
--   (a direct operational truth about the VR-Sets correlate of τ)
--
-- Obtain:
--   translate_implies_realisable h : isRealisable ⌜τ⌝
--   (the formal term ⌜τ⌝ has an operational correlate)
--
-- Justification: by Theorem III.1 (preprint §III.2, external reference),
-- any T₁-proof using formal terms that yields an operational conclusion
-- is already a T₀-proof. In this Lean cycle, h IS already a VR-Sets
-- theorem (T₀-proof); the transit step is existential introduction via
-- translate_implies_realisable.
--
-- ## Concrete instances
--
--   isRealisable ⌜"∅"⌝  ←  translate_implies_realisable translate_pi_empty
--     (translate_pi_empty : translate_pi ⌜"∅"⌝ := ZFSet.notMem_empty)
--
--   isRealisable ⌜"omega_OSet"⌝  ←  translate_implies_realisable translate_pi_omega
--     (translate_pi_omega : translate_pi ⌜"omega_OSet"⌝ := Theorem_III_6_Infinity)
--
--   isRealisable ⌜"osetPair"⌝  ←  translate_implies_realisable translate_pi_osetPair
--     (translate_pi_osetPair : translate_pi ⌜"osetPair"⌝ := Theorem_III_3_Pairing)
--
-- ## What this pattern is not
--
-- This is NOT the full conservativity theorem. In the preprint, the transit
-- rule applies to *any* T₁-derivation; here, it applies only to the three
-- named formal terms. The general case (arbitrary T₁-derivation → T₀-proof)
-- is the structural boundary. The three instances above are direct VR-Sets
-- theorems that happen to also appear as translate_pi facts.


-- ============================================================
-- §III.2 — Direct-proof theorems (translate_pi instances)
-- ============================================================

/-- §III.2 direct proof: π(⌜"∅"⌝) holds in VR-Sets.

## Lean proof
`translate_pi ⌜"∅"⌝` reduces to `∀ x : OSet, x ∉ osetEmpty`.
This is exactly `ZFSet.notMem_empty` (mathlib).

## Connection to isRealisable
`translate_implies_realisable translate_pi_empty : isRealisable ⌜"∅"⌝`.
Existential witness: `osetEmpty`. This is how the transit pattern
is instantiated for ⌜"∅"⌝.

## Axiom profile: [propext, Quot.sound] -/
theorem translate_pi_empty : translate_pi ⌜"∅"⌝ :=
  ZFSet.notMem_empty


/-- §III.2 direct proof: π(⌜"omega_OSet"⌝) holds in VR-Sets.

## Lean proof
`translate_pi ⌜"omega_OSet"⌝` reduces to
  `∅ ∈ omega_OSet ∧ ∀ n, n ∈ omega_OSet → insert n n ∈ omega_OSet`.
This is exactly `Theorem_III_6_Infinity` (VR-Sets Stage 6, ZF.lean).

## Connection to isRealisable
`translate_implies_realisable translate_pi_omega : isRealisable ⌜"omega_OSet"⌝`.
Existential witness: `omega_OSet`.

## Axiom profile: [propext, Quot.sound] -/
theorem translate_pi_omega : translate_pi ⌜"omega_OSet"⌝ :=
  Theorem_III_6_Infinity


/-- §III.2 direct proof: π(⌜"osetPair"⌝) holds in VR-Sets.

## Lean proof
`translate_pi ⌜"osetPair"⌝` reduces to
  `∀ a b x : OSet, x ∈ osetPair a b ↔ x = a ∨ x = b`.
This is exactly `Theorem_III_3_Pairing` (VR-Sets Stage 3, ZF.lean),
which has signature `∀ (a b : OSet), ∀ x, x ∈ osetPair a b ↔ x = a ∨ x = b`.
The two are definitionally equal: `Theorem_III_3_Pairing` is `fun a b x => ...`.

## Connection to isRealisable
`translate_implies_realisable translate_pi_osetPair : isRealisable ⌜"osetPair"⌝`.
Existential introduction: `fun a b => ⟨osetPair a b, Theorem_III_3_Pairing a b⟩`.
(Stage 2's `isRealisable_osetPair` used this directly.)

## Axiom profile: [propext, Quot.sound] -/
theorem translate_pi_osetPair : translate_pi ⌜"osetPair"⌝ :=
  Theorem_III_3_Pairing


-- ============================================================
-- §III.2 — Two-layer connection theorem
-- ============================================================

/-- Connection theorem: `translate_pi t → isRealisable t` for all formal terms.

## Mathematical content (§III.2 / §II.7 relationship)

The **specific** predicate `translate_pi t` (defining predicate of τ in the
operational language, referencing a named VR-Sets object) implies the
**existential** predicate `isRealisable t` (operational correlate exists):

| `t` | `translate_pi t` | witness | `isRealisable t` |
|-----|-----------------|---------|-----------------|
| `⌜"∅"⌝` | `∀ x, x ∉ osetEmpty` | `osetEmpty` | `∃ s, ∀ x, x ∉ s` |
| `⌜"omega_OSet"⌝` | `∅ ∈ omega_OSet ∧ …` | `omega_OSet` | `∃ s, ∅ ∈ s ∧ …` |
| `⌜"osetPair"⌝` | `∀ a b x, x ∈ osetPair a b ↔ …` | `osetPair` | `∀ a b, ∃ s, …` |
| `⌜"AFA_Statement"⌝` | `AFA_Statement` | identity | `AFA_Statement` |
| catch-all | `False` | `False.elim` | `False` |

The converse (`isRealisable t → translate_pi t`) does **not** hold: from
`∃ s, ∀ x, x ∉ s` one cannot recover `∀ x, x ∉ osetEmpty` without
knowing the witness is `osetEmpty`. The forward direction is the formal
content of the transit pattern in this Lean cycle.

## Lean proof — equation compiler + by_cases catch-all

The named cases use the equation compiler's pattern matching directly;
the catch-all case requires `by_cases` + `unfold translate_pi` + `split`.

### Equation-compiler catch-all: why `h.elim` fails in term mode

**Technical note (Lean 4 specificity)**:

In term mode, `| _, h => h.elim` and `| _, h => (h : False).elim` both
fail with:
  `Invalid field 'elim': The environment does not contain
   'VR.Forms.translate_pi.match_1.elim'`

The root cause: Lean 4's equation compiler represents the catch-all
branch via a **schematic variable** (`x✝`). In **term mode**, the kernel
does NOT reduce `translate_pi x✝` to `False` for this schematic variable
— the match is left unreduced because the kernel cannot evaluate it
without a concrete value.

**Working fix**: use `by_cases` to explicitly enumerate the four named
formal terms (using `DecidableEq FormalTerm`, which requires no Classical
axiom). In the residual branch (t ≠ all four named terms), prove
`translate_pi t = False` via `unfold translate_pi; split <;> simp_all
[FormalTerm.mk.injEq]`. After `unfold`, the goal shows the match
expression explicitly; `split` case-analyses it; in each named-pattern
case, `simp_all` finds the contradiction with the `by_cases` disequality
hypotheses; in the catch-all case, the goal is `False = False` by `rfl`.

**Cost**: zero new axioms. `by_cases h : t = ⌜τ⌝` uses `DecidableEq
FormalTerm` (derived from `DecidableEq String × DecidableEq Register`),
not `Classical.propDecidable`.

## Axiom profile: [propext, Quot.sound] (no Classical.choice) -/
theorem translate_implies_realisable (t : FormalTerm) (h : translate_pi t) :
    isRealisable t := by
  -- Named cases: pattern-match on t; each uses existential introduction.
  by_cases h1 : t = ⌜"∅"⌝
  · subst h1; exact ⟨osetEmpty, h⟩
  by_cases h2 : t = ⌜"omega_OSet"⌝
  · subst h2; exact ⟨omega_OSet, h⟩
  by_cases h3 : t = ⌜"osetPair"⌝
  · subst h3; exact fun a b => ⟨osetPair a b, h a b⟩
  by_cases h4 : t = ⌜"AFA_Statement"⌝
  · subst h4; exact h
  · -- Catch-all: t ≠ all four named terms ⟹ translate_pi t = False.
    -- Derive False from h via explicit unfold + split.
    -- (See doc-comment above for why direct h.elim fails in term mode.)
    exfalso
    have hf : translate_pi t = False := by
      unfold translate_pi
      split <;> simp_all [FormalTerm.mk.injEq]
    rw [hf] at h; exact h


-- ============================================================
-- Axiom audit — Stage 3
-- ============================================================

-- STAGE 3. SOURCE: Part III §III.2, Part IV §IV.2.
-- LEAN OBJECTS: translate_pi (def), translate_pi_empty, translate_pi_omega,
--               translate_pi_osetPair, translate_implies_realisable (theorems).
-- AXIOM AUDIT:
--   Expected for all: [propext, Quot.sound].
--   Note: no Classical.choice — by_cases in translate_implies_realisable
--   uses DecidableEq FormalTerm (derived), not Classical.propDecidable.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms translate_pi
#print axioms translate_pi_empty
#print axioms translate_pi_omega
#print axioms translate_pi_osetPair
#print axioms translate_implies_realisable

end VR.Forms
