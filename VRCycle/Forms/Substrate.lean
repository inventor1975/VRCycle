-- VR-Forms: Substrate (DOI 10.5281/zenodo.20313735)
-- Operational Substrate Totality.
--
-- Stage 6: Carrier inductive, Operational predicate, substrate totality.
-- Source: Frozen statement (curator-architect, 2026-05-28).
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- **What Stage 6 does:**
-- Promotes the register-language clarification from prose in a comment
-- (Stages 1-5 headers) to a machine-checked theorem. The frozen statement:
--
--   «Operationality is a total substrate. Every operand (operational object
--   or formal term) and every result — including the empty result ∅ —
--   carries operational substrate. The *content* (value of a result) is not
--   invariant under application; the *presence* of operational substrate is
--   invariant.»
--
-- Stage 6 proves **presence-invariance** (substrate totality on operands).
-- Content-invariance is false and is not claimed.
--
-- **Note on .term branch (Operational (.term _) := True):**
-- Intentional — see doc-comment on `Operational` and `operational_total`.
-- The gate-report (2026-05-28) proved that no content-ful non-trivial
-- predicate exists that is both total over all FormalTerm and non-trivial.
-- `True` is chosen over `∃ s r, t = ⟨s,r⟩` which says the same thing
-- while pretending to say more. See gate-report §3.2 for full argument.
--
-- Imports:
--   VRCycle.Forms.Examples   — top of Forms chain (Stages 1-5 transitive):
--     Language (Register, FormalTerm, ⌜·⌝), Realisability (isRealisable),
--     Transit (translate_pi), Bridge (bridge_AFA, bridge_Conjectures),
--     Examples (mixed_omega_two_register, mixed_AFA_boundary)
--     VRCycle.Sets.Modes (OSet, osetEmpty, omega_OSet, ...)
--
-- **ZFSet.mem_wf** (Mathlib.SetTheory.ZFC.Basic):
--   `theorem ZFSet.mem_wf : @WellFounded ZFSet (· ∈ ·)`
--   Proved from PSet.mem_wf by structural recursion — NO Classical.choice.
--   Axiom profile: [propext, Quot.sound]. This underpins the .obj branch.

import VRCycle.Forms.Examples

namespace VR.Forms

open VR.Sets


-- ============================================================
-- Carrier — the type over which the substrate thesis ranges
-- ============================================================

/-- Carrier of the substrate thesis: anything appearing as operand or
result in the two-register system.

## Frozen statement (curator-architect, 2026-05-28)

«Operationality is a total substrate. Every operand (operational object
or formal term) and every result — including the empty result ∅ —
carries operational substrate.»

Stage 6 proves this over `Carrier`: the minimal honest type covering
both modes of the two-register system.

## Two constructors

- `.obj a` — an operational object (operational mode): `a : OSet.{0}`
  (= `ZFSet`). This is any set reachable by the operational closure
  principle: ∅, {∅}, ω, etc. The `.obj` constructor carries the
  well-foundedness content of the substrate predicate.

- `.term t` — a formal term (formal mode): `t : FormalTerm`
  (= `⟨description : String, register : Register⟩`). This includes
  realisable terms (`⌜"∅"⌝`, `⌜"omega_OSet"⌝`) and non-realisable
  terms (`⌜"Russell_class"⌝`, `⌜"AFA_Statement"⌝`, AC, AD, ...).
  By the Principle of Forms (Language.lean §II.4), any syntactically
  correct record is a formal term — no further conditions.

## Universe note

`OSet.{0}` is pinned (as throughout Forms Stages 2-5) to avoid the
cross-namespace universe inference friction documented in Realisability.lean
and Examples.lean. `FormalTerm` has no universe parameter (String, Register
are in Type 0). The resulting `Carrier` is in Type 0 — no friction.

## Stage 7 note

Application acts (`apply : Carrier → Carrier → Carrier` or relation) are
Stage 7. The `.term` constructor is kept in `Carrier` for Stage 7: AC, AD,
Power Set are formal terms; Stage 7 will range over them to prove that
the application act is operational and that content (not substrate) is
what contradicts. Removing `.term` (Variant II at gate) would make those
Stage 7 claims inexpressible. -/
inductive Carrier where
  | obj  : OSet.{0} → Carrier
  | term : FormalTerm → Carrier


-- ============================================================
-- Operational — the substrate predicate
-- ============================================================

/-- A carrier element carries operational substrate.

## Design (gate-report, 2026-05-28, Variant I — curator/architect sign-off)

**`.obj a => Acc (· ∈ ·) a`** — the operational object `a` is accessible
under set membership. Content-ful by the decision rule: a non-well-founded
set (e.g. an AFA-universe element `x` with `x ∈ x`) would make this false.
Such objects exist formally (VRCycle.Sets.ZFA) but not in `OSet = ZFSet`
(which is well-founded by construction). The predicate discriminates between
well-founded and non-well-founded carriers — it is not `True` in disguise.

Proof via `ZFSet.mem_wf : @WellFounded ZFSet (· ∈ ·)` (choice-free).
Axiom ceiling: `[propext, Quot.sound]`.

**`.term _ => True`** — a formal term carries operational substrate
unconditionally. This is intentionally `True` for four reasons:

1. **Principle of Forms (Language.lean §II.4)**: any syntactically correct
   record is a formal term, without further conditions. The `FormalTerm`
   type is a Lean structure `⟨description : String, register : Register⟩`,
   and any value of this type already satisfies whatever "being a formal
   term" could mean. There is no non-trivial property that holds for all
   `FormalTerm` values but could fail for some — any such property collapses
   to `True`. Gate-report §3.2 proved this via the logical pinch: any
   discriminating predicate (like `isRealisable t`) fails totality because
   non-realisable terms exist; any total predicate is trivial.

2. **Honest over false-content**: `∃ s r, t = ⟨s,r⟩` holds for every
   `FormalTerm` by `⟨t.description, t.register, rfl⟩`. It says nothing
   more than `True`. Bare `True` is the honest choice.

3. **Stage 7 connector**: the non-trivial substrate claim about formal
   terms lives in the APPLICATION ACT — "AC applied to ∅ yields ∅, ∅ is
   still operational; contradiction is in content (AC+AD co-assertion),
   not in substrate". This requires `apply : Carrier → Carrier → Carrier`,
   which is Stage 7. Stage 6 only establishes the static carrier.

4. **AC/AD accessibility**: formal terms (AC, AD, Power Set) must remain
   in `Carrier` for Stage 7. `.term _ => True` keeps them operational
   at the substrate level; Stage 7 will show their APPLICATION produces
   contradiction in content while the substrate ∅ remains operational.

## What `operational_total` proves

The genuine mathematical content of Stage 6 is in the `.obj` branch:
`∀ a : OSet, Acc (· ∈ ·) a` — a real well-foundedness theorem.
The `.term` branch is philosophically grounded (Principle of Forms)
but Lean-trivial. The asymmetry is expected and documented. -/
def Operational : Carrier → Prop
  | .obj a  => Acc (· ∈ ·) a
  | .term _ => True


-- ============================================================
-- operational_total — substrate totality
-- ============================================================

/-- Totality of the operational substrate: every carrier element carries
operational substrate.

## Proof

- `.obj a`: `ZFSet.mem_wf.apply a : Acc (· ∈ ·) a`.
  `ZFSet.mem_wf : @WellFounded ZFSet (· ∈ ·)` is proved in mathlib
  (ZFC/Basic.lean) constructively: `PSet.mem_wf` uses structural
  recursion on the `PSet` inductive (`PSet.mem_wf_aux : ∀ {x y}, Equiv x y → Acc (· ∈ ·) y`,
  proved by structural recursion without choice), lifted through the
  ZFSet quotient using `wellFounded_lift₂_iff` (propext + Quot.sound,
  no Classical.choice). `WellFounded.apply : WellFounded r → ∀ a, Acc r a`
  gives the witness.

- `.term _`: `trivial : True` — intentional. See `Operational` doc-comment.

## The .obj/.term asymmetry

Content-ful for `.obj` (genuine well-foundedness), trivial for `.term`
(Principle of Forms). This asymmetry does not weaken the frozen statement:
the statement says every operand *carries* operational substrate, not that
the substrate predicate is *hard to prove* for every operand. For operational
objects, the substrate is well-foundedness; for formal terms, it is the act
of inscription — which is precisely what the Principle of Forms encodes.

## Axiom profile (expected)

`[propext, Quot.sound]` — from `ZFSet.mem_wf` on the `.obj` branch.
`Classical.choice` must NOT appear. Its absence is confirmed by the mathlib
proof chain: `PSet.mem_wf` (structural recursion) → `ZFSet.mem_wf`
(quotient lift via propext + Quot.sound). -/
theorem operational_total : ∀ c : Carrier, Operational c
  | .obj a  => ZFSet.mem_wf.apply a
  | .term _ => trivial


-- ============================================================
-- operational_empty — the limit case
-- ============================================================

/-- The empty set carries operational substrate.

## The curator's insisted-upon limit case

`Operational (.obj osetEmpty)` = `Acc (· ∈ ·) (∅ : ZFSet)`.

∅ has rank 0 (`Lemma_II_3_DepthEmpty : operationalDepth osetEmpty = 0`,
Foundation.lean): zero construction steps, no elements, the operational
floor. Stage 6 machine-checks that even this limit case — the primordial
object held by the positing of «nothing» — carries operational substrate.

## Why this is not trivial

`ZFSet.mem_wf.apply osetEmpty : Acc (· ∈ ·) osetEmpty` requires the
full well-foundedness theorem for ZFSet membership. The proof is NOT:
  - "∅ has no members, so accessibility is vacuous" (this is the intuition,
    not the proof — the proof goes through the general `WellFounded.apply`,
    which delivers `Acc` via the induction principle of `WellFounded`).
  - `trivial` — this is not `True`, it is a genuine `Acc` term.

The proof term is: `⟨fun y hy => (ZFSet.notMem_empty y hy).elim⟩`
at the Acc level (the induction unpacking), but delivered cleanly by
`ZFSet.mem_wf.apply osetEmpty` without spelling out the vacuous case.

## Substrate vs. content

Content of ∅: zero elements, rank 0 — the minimal result. Content CAN
change under application (eating all apples yields ∅ — the same ∅ that
was already the floor). Stage 7 formalizes this. Here: ∅ as an operand
carries substrate. The PRESENCE of substrate is invariant; content is not.

## Axiom profile (expected): [propext, Quot.sound] -/
theorem operational_empty : Operational (.obj osetEmpty) :=
  ZFSet.mem_wf.apply osetEmpty


-- ============================================================
-- omega_substrate — §3.4 connection to mixed_omega_two_register
-- ============================================================

/-- Both registers of ω carry operational substrate (§3.4).

## Connection to mixed_omega_two_register

This corollary links Stage 6 to `mixed_omega_two_register` (Examples.lean,
Stage 5), showing it is a special case of substrate totality: the referent ω,
appearing in both registers, is operational in both modes.

`mixed_omega_two_register : (∅ : OSet) ∈ omega_OSet ∧ isRealisable ⌜"omega_OSet"⌝`
— the Stage 5 cross-register formula affirming ω in both registers.

`omega_substrate` adds the substrate layer: not only does ω exist in both
registers (as `mixed_omega_two_register` shows), but each of those carriers
*bears* operational substrate.

## The .obj/.term asymmetry (as expected)

- `Operational (.obj omega_OSet)` = `Acc (· ∈ ·) omega_OSet`.
  **Content-ful**: omega_OSet = {∅, {∅}, {∅,{∅}}, …}; each element has
  strictly smaller rank. Proved by `ZFSet.mem_wf.apply omega_OSet`.

- `Operational (.term ⌜"omega_OSet"⌝)` = `True`.
  **Trivial**: Principle of Forms. The formal-register holder of the ω
  description carries substrate by inscription — there is no further
  Lean-expressible criterion (gate-report §3.2).

The asymmetry is the same as in `operational_total` and is expected.
It does not signal incoherence: the two components express different things.

## What this shows about the promotion

Every Forms Stage 1-5 file carries the comment «all descriptions are
operational acts». `omega_substrate` is the first machine-checked instance
of that thesis: for ω, both the operational object (`.obj omega_OSet`)
and the formal term (`.term ⌜"omega_OSet"⌝`) provably carry substrate.
The comment is now a theorem — for this case.

## Axiom profile (expected): [propext, Quot.sound] -/
theorem omega_substrate :
    Operational (.obj omega_OSet) ∧ Operational (.term ⌜"omega_OSet"⌝) :=
  ⟨ZFSet.mem_wf.apply omega_OSet, trivial⟩


-- ============================================================
-- Axiom audit — Stage 6
-- ============================================================

-- STAGE 6. SOURCE: Frozen statement (curator-architect, 2026-05-28).
-- LEAN OBJECTS: Carrier (inductive), Operational (def),
--               operational_total, operational_empty, omega_substrate (theorems).
--
-- AXIOM AUDIT EXPECTATIONS:
--   Carrier:             []
--     (pure inductive — OSet.{0} and FormalTerm have no axioms at the
--      type level; Carrier itself introduces no new axioms)
--   Operational:         []
--     (def by pattern match; Acc is in Lean core prelude (no classical axioms);
--     True has no axioms; no ZFSet.mem_wf used at definition level)
--   operational_total:   [propext, Quot.sound]
--     (ZFSet.mem_wf path: PSet.mem_wf [structural recursion] →
--      ZFSet.mem_wf [propext + Quot.sound via wellFounded_lift₂_iff])
--   operational_empty:   [propext, Quot.sound]
--     (same: ZFSet.mem_wf.apply osetEmpty)
--   omega_substrate:     [propext, Quot.sound]
--     (ZFSet.mem_wf.apply omega_OSet on left; trivial on right)
--
-- HALT CONDITION: Classical.choice MUST NOT APPEAR.
--   ZFSet.mem_wf is choice-free (confirmed at gate reconnaissance).
--   If Classical.choice appears, this signals a non-constructive backdoor —
--   halt and diagnose before proceeding.
--
-- CHECKS: no sorry, no admit; lake build passes (all of Forms Stages 1-6).

#print axioms Carrier
#print axioms Operational
#print axioms operational_total
#print axioms operational_empty
#print axioms omega_substrate


-- ============================================================
-- ## The application act (documentation, not a theorem)
-- ============================================================
--
-- **Frozen statement (curator-architect, 2026-05-28):**
-- The application act produces a result-Carrier from operands. Two facts:
--
-- 1. The substrate of the result is always intact. Application cannot
--    produce a result without operational substrate. The act of applying
--    is itself operational (by the fact of being performed); the result
--    carries substrate — no matter what the result's content is.
--
-- 2. The operational correlate of the result (its realisability) varies by
--    content, not by sort. Application can yield a realisable result (one
--    with an operational correlate) or a non-realisable one (a formal term
--    without correlate), depending on what the operands describe. This is
--    content-variance: realisability is not invariant under application,
--    while substrate is.
--
-- **Where this is already proved in VR-Forms Lean:**
--
-- Substrate-invariance (fact 1):
--   `operational_total : ∀ c : Carrier, Operational c`     (this file, Stage 6)
--   `operational_empty : Operational (.obj osetEmpty)`      (this file, Stage 6)
--   Every carrier — operand or result — provably carries operational substrate.
--   The result of any application is a Carrier, and every Carrier is covered
--   by `operational_total`. No new theorem about apply is needed to establish
--   this: Stage 6 already made substrate universally total.
--
-- Content-variance (fact 2):
--   `isRealisable` is non-total (Stage 2, Realisability.lean):
--     `isRealisable_empty : isRealisable ⌜"∅"⌝`               (realisable)
--     `isRealisable_omega : isRealisable ⌜"omega_OSet"⌝`       (realisable)
--     `not_isRealisable_Russell : ¬isRealisable ⌜"Russell_class"⌝`  (non-realisable)
--     catch-all `| _ => False` covers ⌜"dragon"⌝ and all unnamed terms
--   Content-variance is a property of `isRealisable`, not of apply. The
--   predicate already discriminates between realisable and non-realisable
--   formal terms; that discrimination is the formal content of fact 2.
--
-- **Why `apply` is not formalised as a separate relation:**
--
-- Gate analysis (implementer, 2026-05-28) showed that the minimal honest
-- `apply` relation — `inductive apply ... | act (hz : Operational z)` — is
-- vacuous: since `operational_total` supplies `hz` for every `z : Carrier`,
-- the relation holds for ALL (x, y, z) triples, collapsing to `True`. Every
-- theorem provable about it (`apply_preserves_substrate`, `apply_can_realise`,
-- `apply_can_fail`) is already provable from Stage 2 + Stage 6 without the
-- relation. Content-variance is a property of `isRealisable` (Stage 2);
-- substrate-invariance is a property of `operational_total` (Stage 6). The
-- `apply` relation adds no machine-content of its own.
--
-- This is the same structural-boundary discipline applied in `Transit.lean`
-- (Stage 3) for Conservativity (Theorem III.1): a claim the preprint asserts
-- and that is correct, but whose full formalisation requires infrastructure
-- beyond the current scope — here, a non-vacuous model of application that
-- would require freezing specific content-rules not yet decided. Named in
-- words; the machine-content lives in Stages 2 and 6.
--
-- **Forward note:**
-- Concrete contentful applications — where specific operands determine
-- specific result-realisability (e.g. incompatibility of AC+AD, or formal
-- descriptions of number-theoretic operations) — are the subject of
-- VR-Audit (the audit cycle), not VR-Forms. VR-Forms establishes the
-- two-register substrate; VR-Audit ranges over the mathematical content
-- within that substrate. `apply` remains a documented concept here, not a
-- formalised relation.

end VR.Forms
