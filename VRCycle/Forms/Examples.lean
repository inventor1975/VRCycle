-- VR-Forms: Examples (DOI 10.5281/zenodo.20313735)
-- Part V §V.2–§V.4, Part VI §VI.1, Part VII §VII.2.
-- Applications of the two-register apparatus.
--
-- Stage 5: non-realisable examples (Russell, Vitali, classical ℝ, ℘(ℕ))
--          and mixed formulas (§VII.2) demonstrating cross-register coherence.
-- Source: Part V §V.2–§V.4; Part VI §VI.1; Part VII §VII.2.
--
-- Plan accepted by Opus before this code was written.
--
-- Imports:
--   VRCycle.Forms.Bridge   — all prior stages transitively:
--     Language (Stage 1), Realisability (Stage 2), Transit (Stage 3),
--     Bridge (Stage 4), Sets.Modes, Sets.Conjectures, ZFSet.mem_irrefl
--
-- ## Purpose of this file
--
-- Examples.lean applies the two-register apparatus built in Stages 1–4 to
-- demonstrate its coverage across three areas of the preprint:
--
-- **(a) Non-realisable formal terms** (Part V §V.2–§V.4, Part VI §VI.1):
--   Formal terms for Russell's class, the Vitali set, classical ℝ, and the
--   classical powerset of ℕ. All non-realisable (catch-all → False). The
--   mathematical content resides in the preprint citations; the Lean proofs
--   are trivial (`id`). This is correct: metatheoretic non-realisability
--   (paradoxical descriptions, uncountable collections) is documented by
--   the catch-all, not proved by VR-Sets theorems.
--
-- **(b) Skolem's paradox — two-register reading** (Part V §V.2, §VII.2):
--   The formal-register half of Skolem's paradox IS a Lean theorem
--   (`not_isRealisable_classical_powerset_N := id`). The ontological half
--   («℘_VR(ω) is countable») is metatheoretic — documented in comments,
--   not formalised as a Lean theorem. This is the honest two-level treatment.
--
-- **(c) Mixed formulas** (Part VII §VII.2):
--   Lean Props combining OSet quantification (ontological register) with
--   `isRealisable` predicates (formal register). Two concrete examples:
--   - `mixed_omega_two_register`: positive — both registers affirm ω.
--   - `mixed_AFA_boundary`: the ZFA structural boundary surfaces in both
--     registers simultaneously (Part X §X.3 B.5 cross-register reading).
--
-- ## Relationship to Stages 1–4
--
-- Stage 1 defined the language (FormalTerm, ⌜·⌝).
-- Stage 2 proved realisability for ⌜∅⌝, ⌜omega_OSet⌝, ⌜osetPair⌝.
-- Stage 3 proved the π-translation and transit pattern.
-- Stage 4 proved bridge theorems (bridge_AFA, bridge_Conjecture_IV_X).
-- Stage 5 applies all of the above to concrete formal terms from the
-- preprint, demonstrating that the two-register apparatus is coherent
-- and covers the range of examples discussed in Parts V–VII.
--
-- ## Technical observation — universe handling (cross-cycle boundary)
--
-- `mixed_omega_two_register` uses `translate_pi_omega.1` (not `Theorem_III_6_Infinity.1`)
-- because `Theorem_III_6_Infinity` has a two-universe signature {u v} from the
-- ZFSet/PSet interaction, generating metavariables when `.1` is projected outside
-- its defining namespace. `translate_pi_omega` has `OSet.{0}` pinned in its match
-- case. This is the second universe-handling observation in VR-Forms Lean (after
-- Stage 2's OSet.{0} annotation requirement), both reflecting the same fact:
-- VR-Forms is a cross-cycle module, and universe inference does not propagate
-- automatically across cycle boundaries without explicit annotation.

import VRCycle.Forms.Bridge

namespace VR.Forms

open VR.Sets


-- ============================================================
-- §V.2 / §VII.2 — Skolem's paradox: two-register reading
-- (documented, partially formalised)
-- ============================================================

-- SOURCE: Part V §V.2, Part VII §VII.2.
--
-- ## Skolem's paradox in the two-register framework
--
-- Skolem's paradox (1922): classical set theory proves the existence of an
-- uncountable set ℘(ℕ), but the Löwenheim–Skolem theorem guarantees a
-- countable model of set theory exists. The paradox dissolves in the VR
-- framework via the two-register reading:
--
-- **Ontological register**: ℘_VR(ω) is the operational power set — the
-- set of all operationally describable subsets of ω. In VR-Sets Lean,
-- `ZFSet.powerset omega_OSet` is the classical powerset (full mathlib
-- powerset, NOT restricted to describable subsets). The countability of
-- ℘_VR(ω) is a **metatheoretic** claim: only finitely-describable
-- operations are admitted in the operational register (§II.3), making
-- the operational ℘_VR(ω) countable. This claim is NOT a Lean theorem —
-- it belongs to the same metatheoretic boundary as VR-Numbers §VIII.6
-- (countability of ℝ_VR is metatheoretic, not Lean-expressible).
--
-- **Formal register**: ⌜"classical_powerset_N"⌝ is the formal term for the
-- classical (uncountable) ℘(ℕ). It is non-realisable: there is no
-- operational set in VR-Sets corresponding to the full classical powerset.
-- THIS half IS a Lean theorem (below): `not_isRealisable_classical_powerset_N`.
--
-- ## Two-level Lean treatment
--
-- | Side | Claim | Lean status |
-- |------|-------|------------|
-- | Formal | ⌜℘(ℕ)⌝ non-realisable | Lean theorem (trivial, id) |
-- | Ontological | ℘_VR(ω) countable | Comment only (metatheoretic) |
--
-- This is the honest treatment. Composing both into a single `def : Prop`
-- would misrepresent the ontological claim as Lean-provable.
-- See the discussion at the transit pattern boundary (Stage 3, §III.2).


-- ============================================================
-- §V.2–§V.4, §VI.1 — Non-realisable formal terms
-- ============================================================

/-- Part V §V.3 — The Russell class formal term is not realisable.

## Part V §V.3 — verbatim

«The Russell class R = {x : x ∉ x} is a classical formal description.
In the formal register, ⌜R⌝ is a well-formed formal term (§II.1): the
description «the set of all sets not containing themselves» is
syntactically correct. However, ⌜R⌝ is not operationally realisable:
no operational set A exists in VR-Sets such that the description R
corresponds to the functionality A. The formal term ⌜R⌝ exists in
the formal register without any ontological correlate.»

## Lean proof

`isRealisable ⌜"Russell_class"⌝` hits the catch-all `| _ => False`.
`¬isRealisable ⌜"Russell_class"⌝ = False → False = id`.

Non-realisability is **metatheoretic** here: no VR-Sets theorem states
«no operational set satisfies the Russell description». The catch-all
documents this fact by construction. `id` requires no VR-Sets proof.

Contrast with `bridge_AFA` (Stage 4): AFA non-realisability IS provable
from a VR-Sets theorem (`AFA_Refuted`). Russell non-realisability is
documented, not proved. Both are honest treatments of their respective
non-realisabilities.

## Axiom profile: [propext, Quot.sound] -/
theorem not_isRealisable_Russell : ¬isRealisable ⌜"Russell_class"⌝ := id


/-- Part VI §VI.1 — The Vitali set formal term is not realisable.

## Part VI §VI.1 — verbatim

«The Vitali set V ⊂ [0,1] (constructed by selecting one representative
from each equivalence class under rational translations) requires the
Axiom of Choice at an uncountable level. VR-Sets does not admit
uncountable choice: the operational register is restricted to finitely-
describable operations (§II.3). Therefore ⌜"Vitali"⌝ is not operationally
realisable. The formal term ⌜"Vitali"⌝ exists; its non-realisability
reflects the metatheoretic countability constraint on VR-Sets.»

## Lean proof

`isRealisable ⌜"Vitali"⌝` hits the catch-all → `False`.
`¬isRealisable ⌜"Vitali"⌝ := id`.

Non-realisability is metatheoretic: the Vitali set requires uncountable
Choice, which is not expressible as a VR-Sets Lean theorem (boundary
parallel to VR-Numbers §VIII.6). The catch-all documents this.

## Axiom profile: [propext, Quot.sound] -/
theorem not_isRealisable_Vitali : ¬isRealisable ⌜"Vitali"⌝ := id


/-- Part V §V.2, VR-Numbers §VIII.6 — The classical ℝ formal term is not realisable.

## Part V §V.2 — verbatim

«The classical real line ℝ (Dedekind cuts or Cauchy sequences over all
rational sequences) is not operationally realisable. The operational
real line ℝ_VR consists only of the operationally describable reals —
a countable subset. ⌜ℝ⌝ (classical) and ℝ_VR (operational) are distinct
objects: the first is a formal term, the second an operational set.
The distinction between ℝ_VR and ⌜ℝ⌝ illustrates the core thesis of
VR-Forms: the formal register accommodates uncountable descriptions that
have no operational correlate.»

## Lean proof

`isRealisable ⌜"classical_R"⌝` hits the catch-all → `False`.
`¬isRealisable ⌜"classical_R"⌝ := id`.

The operational ℝ_VR is not formalised in VR-Sets Lean either (VR-Numbers
§VIII.6 boundary: operational countability of ℝ_VR is metatheoretic).
The distinction between ⌜"classical_R"⌝ (non-realisable, this theorem)
and whatever operational analogue exists (metatheoretic, not in Lean)
is documented in comments, not in proofs.

## Axiom profile: [propext, Quot.sound] -/
theorem not_isRealisable_classical_R : ¬isRealisable ⌜"classical_R"⌝ := id


/-- Part V §V.2 — The classical powerset ℘(ℕ) formal term is not realisable.

## Part V §V.2 — verbatim (Skolem-related)

«The classical powerset ℘(ℕ) is not operationally realisable. The
operational power set ℘_VR(ω) is countable (metatheoretically): only
finitely-describable subsets of ω are operational. ⌜℘(ℕ)⌝ (classical,
uncountable) has no operational correlate. This is the VR reading of
Skolem's paradox: in the ontological register, ℘_VR(ω) is countable;
in the formal register, ⌜℘(ℕ)⌝ is non-realisable. Both registers give
a coherent picture without contradiction.»

## Lean proof

`isRealisable ⌜"classical_powerset_N"⌝` hits the catch-all → `False`.
`¬isRealisable ⌜"classical_powerset_N"⌝ := id`.

This is the **formal-register half** of the two-register Skolem reading.
The ontological half («℘_VR(ω) is countable») is metatheoretic — see
the Skolem documentation block above. Only this half is a Lean theorem.

## Axiom profile: [propext, Quot.sound] -/
theorem not_isRealisable_classical_powerset_N :
    ¬isRealisable ⌜"classical_powerset_N"⌝ := id


-- ============================================================
-- §VII.2 — Mixed formulas
-- ============================================================

-- SOURCE: Part VII §VII.2.
--
-- ## §VII.2, Mixed formulas — verbatim
--
-- «A **mixed formula** is a formula that combines quantification over
-- operational sets (the ontological register L₀) with assertions about
-- formal terms (the formal register L₁). Mixed formulas have the form:
--
--   Φ(x₁, …, xₙ, ⌜τ₁⌝, …, ⌜τₖ⌝)
--
-- where xᵢ : OSet (ontological variables) and ⌜τⱼ⌝ are formal terms.
-- Mixed formulas are legitimate formulas of the two-register theory T₁
-- (Part III §III.1). By Theorem III.1 (conservativity), if a mixed
-- formula Φ is provable in T₁ and Φ ∈ L₀ (ontological register), it
-- is already provable in T₀ without formal terms.»
--
-- ## Lean implementation of mixed formulas
--
-- In shallow embedding, a mixed formula is a Lean `Prop` that mentions
-- both `OSet` quantification and `isRealisable` (or `translate_pi`)
-- predicates. The two mixed theorems below demonstrate this structure.
--
-- Note: by Theorem III.1 (conservativity, §III.2, external reference),
-- if a mixed formula is purely operational (∈ L₀), it is already provable
-- without the formal-register components. In both theorems below, the
-- operational component IS a standalone VR-Sets theorem; the formal
-- component adds the two-register layer.


/-- §VII.2 mixed formula: the operational ω and the formal ⌜omega_OSet⌝ agree.

## §VII.2 — positive mixed formula (realisable case)

Both registers affirm ω's existence and properties:
- Ontological: `∅ ∈ omega_OSet` — the empty set is a member of the
  operational ω (VR-Sets Theorem III.6, infinity axiom).
- Formal: `isRealisable ⌜"omega_OSet"⌝` — the formal term for ω has an
  operational correlate (Stage 2 lemma `isRealisable_omega`).

Together: the operational ω exists and is confirmed at the formal level.

## Lean proof

Left component: `translate_pi_omega.1 : (∅ : OSet) ∈ omega_OSet`.
  (Use `translate_pi_omega.1`, NOT `Theorem_III_6_Infinity.1`:
   `Theorem_III_6_Infinity` has a two-universe signature {u v} from the
   ZFSet/PSet boundary; projecting `.1` outside its namespace generates
   universe metavariables. `translate_pi_omega` has `OSet.{0}` pinned.)
Right component: `isRealisable_omega : isRealisable ⌜"omega_OSet"⌝`.

## Axiom profile: [propext, Quot.sound] -/
theorem mixed_omega_two_register :
    (∅ : OSet.{0}) ∈ omega_OSet ∧ isRealisable ⌜"omega_OSet"⌝ :=
  ⟨translate_pi_omega.1, isRealisable_omega⟩


/-- §VII.2 mixed formula: the ZFA boundary appears in both registers.

## §VII.2 — structural mixed formula (ZFA boundary cross-register)

The most mathematically substantive mixed formula of this cycle. It
expresses — in a single Lean Prop — the parallel manifestation of the
ZFA structural boundary across both registers:

- Ontological: `∀ x : OSet, x ∉ x` — no operational set is self-membered.
  This is the foundation / regularity property of VR-Sets. In Lean:
  `ZFSet.mem_irrefl : ∀ x : ZFSet, ¬(x ∈ x)`.

- Formal: `¬isRealisable ⌜"AFA_Statement"⌝` — the AFA formal term has no
  operational correlate. In Lean: `bridge_AFA := AFA_Refuted` (Stage 4).

Together: the same structural fact (well-foundedness of set membership)
manifests in the ontological register as the `mem_irrefl` property of OSet,
and in the formal register as the non-realisability of the AFA claim.

## §V.4 preprint reference — verbatim

«The Anti-Foundation Axiom is not operationally realisable. The operational
register of VR-Sets admits only well-founded sets. A universe satisfying
AFA would require self-membered sets (x ∈ x), excluded by the foundation
structure (Theorem VI.1). This is not merely a limitation of VR-Sets —
it reflects the foundational structure of the entire operational apparatus.»

## Methodological note (for Part IX)

Both components derive from the inductive nature of `PSet` (mathlib's
pre-sets) and from the ZFSet quotient. `ZFSet.mem_irrefl` comes from
the PSet foundation axiom. `AFA_Refuted` uses `PSet.mem_irrefl` directly.
Both reach the same root:

```
PSet.mem_irrefl  ──→  ZFSet.mem_irrefl  ──→  mixed_AFA_boundary.left
                  └──→  AFA_Refuted  ──→  bridge_AFA  ──→  mixed_AFA_boundary.right
```

`mixed_AFA_boundary` is thus the **junction theorem** of the VR-Forms
cycle: it is where the ZFA boundary of VR-Sets (Part X §X.3 B.5) enters
the two-register apparatus of VR-Forms and is expressed across both
registers simultaneously. This cross-register coherence is the formal
content of Part VII §VII.2's claim that the two-register framework gives
a coherent (not contradictory) treatment of self-membership impossibility.

## Lean proof

Left: `ZFSet.mem_irrefl : ∀ x : ZFSet, ¬(x ∈ x)` — OSet = ZFSet (abbrev).
Right: `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝` (Stage 4).

## Axiom profile: [propext, Quot.sound] -/
theorem mixed_AFA_boundary :
    (∀ x : OSet.{0}, x ∉ x) ∧ ¬isRealisable ⌜"AFA_Statement"⌝ :=
  ⟨ZFSet.mem_irrefl, bridge_AFA⟩


-- ============================================================
-- Axiom audit — Stage 5
-- ============================================================

-- STAGE 5. SOURCE: Part V §V.2–§V.4; Part VI §VI.1; Part VII §VII.2.
-- LEAN OBJECTS: not_isRealisable_Russell, not_isRealisable_Vitali,
--               not_isRealisable_classical_R,
--               not_isRealisable_classical_powerset_N,
--               mixed_omega_two_register, mixed_AFA_boundary.
-- AXIOM AUDIT:
--   Expected for all six: [propext, Quot.sound].
--   Note: non-realisable theorems proved by `id`; mixed theorems proved by
--   ⟨translate_pi_omega.1, isRealisable_omega⟩ and ⟨ZFSet.mem_irrefl, bridge_AFA⟩.
--   No Classical.choice anywhere in this file.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms not_isRealisable_Russell
#print axioms not_isRealisable_Vitali
#print axioms not_isRealisable_classical_R
#print axioms not_isRealisable_classical_powerset_N
#print axioms mixed_omega_two_register
#print axioms mixed_AFA_boundary

end VR.Forms
