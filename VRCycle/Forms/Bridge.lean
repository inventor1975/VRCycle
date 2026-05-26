-- VR-Forms: Bridge (DOI 10.5281/zenodo.20313735)
-- Part V §V.1–§V.5 (selected items), Part VII §VII.2.
-- Bridge theorems from formal terms to VR-Sets Lean objects.
--
-- Stage 4: bridge_AFA (negative bridge), bridge_Conjecture_IV_1,
--          bridge_Conjecture_IV_2 (open conditional bridges).
-- Source: Part V §V.4 (AFA as non-realisable), Part IV §IV.6,
--         Part IX §IX.1 (open questions).
--
-- Architectural stage (CLAUDE.md): plan-before-code protocol applied.
-- Plan accepted by Opus before this code was written.
--
-- Imports:
--   VRCycle.Forms.Transit   — translate_pi, isRealisable, translate_implies_realisable,
--                              FormalTerm, ⌜·⌝, OSet, AFA_Statement, AFA_Refuted,
--                              Conjecture_IV_1_Statement, Conjecture_IV_2_Statement
--                              (via chain: Transit → Realisability → Modes + Conjectures)
--
-- ## Bridge module purpose
--
-- A bridge theorem has the form:
--   `isRealisable ⌜τ⌝ ↔ P`   (P is a VR-Sets Lean proposition)
-- or
--   `¬isRealisable ⌜τ⌝`      (the formal term is non-realisable in Lean)
--
-- By connecting formal terms in the formal register (Part II) to concrete
-- objects in VR-Sets Lean (the operational register), bridge theorems make
-- the two-register structure explicit in Lean.
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- ontological levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- ## Cross-cycle dependency chain
--
-- `bridge_AFA` uses `AFA_Refuted` from VR-Sets Stage 10 (Modes.lean).
-- `bridge_Conjecture_IV_1` uses `Conjecture_IV_1_Statement` from VR-Sets Stage 11
-- `bridge_Conjecture_IV_2` uses `Conjecture_IV_2_Statement` from VR-Sets Stage 11
--
-- This makes the bridge module the **junction point** between two Lean cycles:
--   VR-Sets (Stages 1–13, ~22 public theorems) → VR-Forms (Stages 1–5).
-- Bridge.lean is where VR-Forms imports content proved in VR-Sets and uses
-- it to determine the realisability status of formal terms.
--
-- ## Triadic classification (Methodological Observation 5)
--
-- The three bridge theorems surface the triadic classification of formal terms:
--
-- (a) **Provably realisable** — Stages 2–3:
--     `⌜"∅"⌝`, `⌜"omega_OSet"⌝`, `⌜"osetPair"⌝`.
--     Proved by concrete VR-Sets witnesses. No bridge theorems needed —
--     `isRealisable_empty`, `isRealisable_omega`, `isRealisable_osetPair`
--     already establish these (Stage 2).
--
-- (b) **Open realisability** — this file:
--     `⌜"Conjecture_IV_1_Statement"⌝`, `⌜"Conjecture_IV_2_Statement"⌝`.
--     Realisability is undecided: `isRealisable ⌜τ⌝ ↔ Conjecture`. Since
--     the Conjectures are open in VR-Sets (Stage 11, §IX.1), the formal
--     terms' realisability is also open. The bridge iff is PROVED (trivially,
--     by definitional equality); its mathematical CONTENT is open.
--
-- (c) **Provably non-realisable** — this file:
--     `⌜"AFA_Statement"⌝`.
--     `¬isRealisable ⌜"AFA_Statement"⌝` proved via `AFA_Refuted`
--     (VR-Sets Stage 10). This is the ZFA-mode boundary of VR-Sets
--     appearing as a realisability theorem in VR-Forms.
--
-- This triadic architecture mirrors VR-Sets Stage 11's three-tier structure
-- (proved theorems / refuted claims / open formulations), but localised
-- at the level of **formal terms** in the formal register. See Part IX §IX.?
-- for the methodological discussion.
--
-- ## What this file does and does not do
--
-- **Does**:
--   - Proves `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝`
--     (provably non-realisable; requires VR-Sets theorem `AFA_Refuted`).
--   - Proves `bridge_Conjecture_IV_1`, `bridge_Conjecture_IV_2`
--     (open conditional bridges; iff is trivially proved by reduction).
--
-- **Does not**:
--   - Alias Stage 2 positive lemmas (isRealisable_empty etc. already proved).
--   - Prove `bridge_Vitali`, `bridge_Russell_class` — metatheoretic
--     non-realisability (catch-all → False; trivial by `id`; no VR-Sets theorem).
--   - Prove either Conjecture (they are open questions in VR-Sets Stage 11).

import VRCycle.Forms.Transit

namespace VR.Forms

open VR.Sets


-- ============================================================
-- §V.4 — Negative bridge: AFA_Statement is non-realisable
-- ============================================================

/-- Negative bridge: the formal term ⌜"AFA_Statement"⌝ is not operationally
realisable.

## Preprint (Part V §V.4) — verbatim

«The Anti-Foundation Axiom, formalised as the requirement that every
directed graph has a unique «decoration» as a set-system, is not
operationally realisable. The operational register of VR-Sets admits
only well-founded sets (built by iterated application of the pairing
and union operations). A universe satisfying AFA would require
self-membered sets, which are excluded by the foundation structure
of VR-Sets (Theorem VI.1).»

## §V.4, commentary on the formal register

«In the **formal** register, ⌜AFA_Statement⌝ is a perfectly legitimate
formal term — it records a syntactically correct description (§II.1).
The formal register places no restrictions on the content of descriptions.
⌜AFA_Statement⌝ exists as a formal term; it is simply not operationally
realisable. The formal term and its non-realisability are not in conflict.»

## Lean proof

`isRealisable ⌜"AFA_Statement"⌝` reduces definitionally to
`VR.Sets.AFA_Statement` (by the Stage 2/Stage 4 match case).
`¬isRealisable ⌜"AFA_Statement"⌝` = `¬AFA_Statement`.
`AFA_Refuted : ¬AFA_Statement` (VR-Sets Stage 10, Modes.lean).
Direct application: `bridge_AFA := AFA_Refuted`.

The kernel evaluates `isRealisable ⟨"AFA_Statement", .formal⟩` by
iota-reduction (concrete match scrutinee; all `String.decEq` calls are
ground) to `AFA_Statement`. No `simp`/`rw` needed.

## Cross-cycle chain

`bridge_AFA` is the first theorem in VR-Forms that uses a VR-Sets
**refutation theorem** (as opposed to a VR-Sets existence theorem
like `osetEmpty` or `omega_OSet`). The chain:
  VR-Sets Stage 10 `AFA_Refuted` → VR-Forms Stage 4 `bridge_AFA`.

## Axiom profile: [propext, Quot.sound] -/
theorem bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝ := AFA_Refuted


-- ============================================================
-- §IX.1 — Open conditional bridges: Conjectures IV.1 and IV.2
-- ============================================================

/-- Open conditional bridge: realisability of ⌜"Conjecture_IV_1_Statement"⌝
is equivalent to Conjecture IV.1 of VR-Sets.

## Preprint (Part IX §IX.1, Question 1) — verbatim

«Is the ZFC-mode of VR-Sets (Part IV §IV.2) mutually interpretable with
a countable model of classical ZFC? Specifically: does there exist a
countable set M, closed under all ZFC operations, such that the ZFC
axioms hold when quantified over M?»

## Status in VR-Sets Lean

`Conjecture_IV_1_Statement` is a `def : Prop` in VR-Sets Stage 11
(Conjectures.lean) with axiom profile `[]`. It is an **open question**:
neither proved nor refuted in mathlib or in the VR-Sets Lean cycle.

Compare with `AFA_Statement` / `AFA_Refuted` (VR-Sets Stage 10):
there, the statement is provably false. Here, the statement is genuinely
open — no proof direction is available.

## Lean proof

`isRealisable ⌜"Conjecture_IV_1_Statement"⌝` reduces definitionally to
`Conjecture_IV_1_Statement` (by the Stage 4 extension to the isRealisable
match). The iff is proved by `⟨id, id⟩`: both sides ARE the same Prop.

## Mathematical content of the bridge iff

The bridge theorem `bridge_Conjecture_IV_1` says:
  ⌜"Conjecture_IV_1_Statement"⌝ is operationally realisable
  **if and only if** the countable-model conjecture holds in VR-Sets.

The iff proof is trivial (definitional equality); the CONTENT is open.
Neither direction of the iff can be discharged without proving or
refuting Conjecture IV.1 itself.

## Axiom profile: [propext, Quot.sound] -/
theorem bridge_Conjecture_IV_1 :
    isRealisable ⌜"Conjecture_IV_1_Statement"⌝ ↔ Conjecture_IV_1_Statement :=
  ⟨id, id⟩


/-- Open conditional bridge: realisability of ⌜"Conjecture_IV_2_Statement"⌝
is equivalent to Conjecture IV.2 of VR-Sets.

## Preprint (Part IV §IV.6, Part IX §IX.1 Question 2) — verbatim

«Is the ZFA-mode of VR-Sets (Part IV §IV.5) mutually interpretable with
a type-theoretic universe satisfying the Anti-Foundation Axiom (AFA)?
Specifically: does there exist a type U with a membership relation
admitting cyclic sets — in particular, the Quine atom — and satisfying
AFA in its graph-decoration form?»

## Status in VR-Sets Lean

`Conjecture_IV_2_Statement` is a `def : Prop` in VR-Sets Stage 11
(Conjectures.lean). Open question; compare with `AFA_Statement`:

| Object | Stage | Status |
|--------|-------|--------|
| `AFA_Statement` | VR-Sets Stage 10 | Provably false in PSet (`AFA_Refuted`) |
| `Conjecture_IV_2_Statement` | VR-Sets Stage 11 | Open: asks for a *different* type U |

Stages 10 and 11 are logically compatible: Stage 10 proves AFA is false
*in mathlib's PSet*; Conjecture IV.2 asks whether there exists *some* type
U (possibly outside mathlib) with AFA-compatible membership.

## Lean proof

`isRealisable ⌜"Conjecture_IV_2_Statement"⌝` reduces definitionally to
`Conjecture_IV_2_Statement` (Stage 4 extension). Bridge iff: `⟨id, id⟩`.

## Mathematical content of the bridge iff

⌜"Conjecture_IV_2_Statement"⌝ is operationally realisable if and only
if the AFA-compatible type-universe conjecture holds. Open status mirrors
Conjecture IV.2's open status in VR-Sets Stage 11.

## Axiom profile: [propext, Quot.sound] -/
theorem bridge_Conjecture_IV_2 :
    isRealisable ⌜"Conjecture_IV_2_Statement"⌝ ↔ Conjecture_IV_2_Statement :=
  ⟨id, id⟩


-- ============================================================
-- Axiom audit — Stage 4
-- ============================================================

-- STAGE 4. SOURCE: Part V §V.4; Part IV §IV.6; Part IX §IX.1.
-- LEAN OBJECTS: bridge_AFA, bridge_Conjecture_IV_1, bridge_Conjecture_IV_2.
-- RETROACTIVE EXTENSION: isRealisable in Realisability.lean got two new
--   cases (Conjecture_IV_1_Statement, Conjecture_IV_2_Statement);
--   import VRCycle.Sets.Conjectures was added to Realisability.lean.
-- AXIOM AUDIT:
--   Expected for all: [propext, Quot.sound].
--   Note: no Classical.choice — bridge_AFA := AFA_Refuted (direct application);
--   bridge_Conjecture_IV_X use ⟨id, id⟩ (definitional equality).
-- CHECKS: no sorry, no admit; lake build passes; Transit.lean unchanged.

#print axioms bridge_AFA
#print axioms bridge_Conjecture_IV_1
#print axioms bridge_Conjecture_IV_2

end VR.Forms
