# T_FINDINGS.md — VR-Topology v1.0.0 architectural amendments catalog

**Cycle**: VR-Topology v1.0.0.
**Cycle dates**: 2026-05-27 to 2026-05-28.
**Workflow**: Variant A (architect / implementer).
**Recognition discipline gate**: word-first phase + pre-implementation paper sketch.

**Total findings**: 18 distinct (T0-T21 with T18 skipped, T4/T10 absorbed).

---

## T0 — Free frame infeasibility (reconnaissance)

**Stage**: pre-1 reconnaissance.
**Caught at**: initial Stage 1 attempt before any code committed.
**Root cause**: original CLAUDE.md plan called for `FreeFrame` construction
(free frame on generators-and-relations).  Lean 4's positivity check
rejects `Set (FreeFramePre G) → FreeFramePre G` — universe inflation.
**Resolution**: pivot to formal topology (Coquand 1992, Sambin 1987) —
coverage relations on posets, not frames as complete lattices.  `cov : S → Set S → Prop` lives in `Prop`, no universe issue.
**Impact**: cycle's foundational re-architecture before any Lean code.

---

## T1 — Universe inflation confirmed

**Stage**: 1 (Lean verification of T0).
**Caught at**: Stage 1 reconnaissance proved infeasibility formally.
**Root cause**: Lean 4 positivity check.
**Resolution**: T0 pivot validated.  Stage 1 proceeds with formal topology.

---

## T2 — Bridge insufficient (Stage 2 to Stage 1)

**Stage**: 2.
**Caught at**: Stage 2 implementation of `OperationalCov → CoverGen`.
**Root cause**: structural induction on `CoverGen` cannot carry
operational+describability witnesses through `trans` constructor.
**Resolution**: introduce parallel inductive `OpCoverGen` carrying these
witnesses by construction.  ~30 lines.

---

## T3 — `IsDescribable` data class

**Stage**: 2.
**Caught at**: design phase of operational layer.
**Root cause**: original plan had `IsDescribable` as `Prop`, but
`enumerator : ℕ → Option α` cannot be propositional (carries data).
**Resolution**: redesign as class with `enumerator` field (data class).
Standard Tier 2 structure per VR-Apparatus terminology.

---

## T5 — `respects_le` direction error

**Stage**: 3.
**Caught at**: Stage 3 paper sketch with Eq relator (dry-run).
**Root cause**: architect's PLAN_3 §1 specified wrong direction for
`respects_le` in `ContinuousMap` structure; identity map proof failed.
**Resolution**: flip direction.  Detected pre-coding, no Lean code lost.

---

## T6 — `Nat.unpair_pair` Classical inheritance

**Stage**: 3.
**Caught at**: Stage 3 axiom audit showed unexpected `Classical.choice`.
**Root cause**: mathlib's `Nat.unpair_pair` lemma pulls Classical via
`Nat.sqrt` infrastructure.
**Resolution**: implement custom bit-interleaving `Nat` pairing in
`IsDescribable` namespace.  ~80 lines isolated.

---

## T7 — Coquand minimal insufficient for product universal property

**Stage**: 4.
**Caught at**: Stage 4 paper sketch for product construction.
**Root cause**: architect's PLAN assumed Coquand's minimal 4-axiom
coverage condition suffices.  Vickers's product universal property
requires `cov_meet` (Sambin's meet axiom) as additional axiom —
`V₁ ∩ V₂` covered by intersection of covers not derivable from minimal.
**Resolution**: T7 amendment — added `cov_meet` field to `FormalTopology`
class.  Trivial for `ofPresentation`-built topologies (via
`CoverGen.meet` constructor).  ~35 lines.
**Downstream payoff**: T7 was the **critical infrastructure** for Stage 6
frame distributivity in Stage 7 (architectural capital).

---

## T8 — `rel_op` direction withdrawn

**Stage**: 4.
**Caught at**: implementer's deeper analysis of architect's `rel_op` proposal.
**Root cause**: architect proposed flipping `rel_op` direction.  Implementer
verified that forward direction breaks `comp.preserves_op_cov`.
**Resolution**: withdraw the flip.  Operational morphisms scope-narrowed
from Stage 4; deferred.

---

## T9 — Relator monotonicity gap

**Stage**: 4.
**Caught at**: Stage 4 design phase, pair construction.
**Root cause**: `ContinuousMap.pair`'s `preserves_cov` for `CoverGen
ref_mono` case requires relator monotonicity in target argument, which
is not present in Stage 3 axioms.
**Resolution**: defer `pair` construction.  Recognition discipline:
abstraction removed because no concrete instance emerged within scope.

---

## T11 — Bool F-witness math error

**Stage**: 5.
**Caught at**: Stage 5 paper sketch verification.
**Root cause**: architect's PLAN_5 §6 specified Bool F-witness as
`{S | S = ∅ ∨ true ∈ S ∨ false ∈ S}`.  Mathematical error: singletons
don't cover both generators.
**Resolution**: corrected to `{S | true ∈ S ∧ false ∈ S}` — lists
containing both elements.

---

## T12 — Drop generic `Finset.toDescribable`

**Stage**: 5.
**Caught at**: implementation of describability.
**Root cause**: generic instance pulled Classical via mathlib's Finset.
**Resolution**: keep specific instances (Empty, Singleton, BoolUniv,
UnitUniv, binaryUnion).  No generic `Finset.toDescribable`.

---

## T13 — Finset Classical inheritance (CompactWitness)

**Stage**: 5.
**Caught at**: Stage 5 axiom audit.
**Root cause**: mathlib's `Finset` transitively imports `Classical.choice`
via `Multiset.toList` / `Quot.unquot`.  Original `CompactWitness.F :
Set (Finset T.S)` design polluted.
**Resolution**: replace `Finset T.S` with `List T.S` everywhere in
Stage 5.  ~268 lines discarded, ~245 lines rewritten.  Lean core's
`List` carries no Classical dependency.

---

## T14 — `prodBasicCov` layer collapse

**Stage**: pre-6 (during PLAN_6 reconnaissance).
**Caught at**: implementer's pre-Stage-6 verification of `prodBasicCov`
interface for `CompactWitness.cover_closure`.
**Root cause**: Stage 4's `prodBasicCov` used full `T.cov` of components;
PLAN_6 §2C assumed it exposed component `basicCov`.  Interface mismatch.
**Resolution**: add `opProdBasicCov` using component `basicCov`;
redirect `instProd.basicCov` to it.  Keep `FormalTopology.prodBasicCov`
untouched for projections.  ~15 lines.

---

## T15 — `cover_closure` head-only form generalization

**Stage**: pre-6.
**Caught at**: implementer's pre-Stage-6 review.
**Root cause**: original Stage 5 `cover_closure` used `(a :: T') ∈ F`
form (head only).  Stage 6 Tychonoff requires applying `cover_closure`
to elements inside lists, not only at head.
**Resolution**: generalize to member-based form `a ∈ S → S ∈ F → ...`.
Strictly stronger over PLAN_5 form's DOMAIN.

---

## T16 — Decidability hypotheses (Stage 6 signature)

**Stage**: pre-6.
**Caught at**: implementer's paper sketch of Stage 6 proof structure.
**Root cause**: PLAN_6 didn't explicitly include decidability
hypotheses, but proofs need them for filtering and case analysis.
Vickers's classical-style proof relied on Kuratowski-finite implicit
decidability; Lean 4 with `List` needs explicit instances.
**Resolution**: add `[DecidableEq T₁.S] [DecidableEq T₂.S]
[DecidableRel T₁.le] [DecidableRel T₂.le] [DecidablePred (· ∈ w₁.F)]
[DecidablePred (· ∈ w₂.F)]` to `tychonoff_binary` signature.  Honest
hypothesis exposition.

---

## T17 — `cover_closure` S' upper bound

**Stage**: pre-6 (during Stage 6 §3.3 paper sketch).
**Caught at**: implementer's paper sketch of §3.3 case B sub-case B1a.
**Root cause**: T15 generalized DOMAIN but inadvertently weakened
CONCLUSION — S' may contain extras beyond non-a elements of S.  Bool
instance's `S' = S` includes `a` itself, breaking upper_closed
shrink-step in §3.3.
**Resolution**: T17 amendment — add upper bound `∀ y ∈ S', y ∈ S ∧
y ≠ a` to `cover_closure` field.  Pins `S'` as multi-subset of non-a
elements of S.  ~35 lines spec + Bool/Unit instances rewritten.

---

## T19 — Operational preservation under refinement

**Stage**: pre-6b.
**Caught at**: PLAN_6b §1.2 design.
**Root cause**: `OperationalFormalTopology` didn't include
`op_preserved_by_le` field; needed for prospective abstract
`prodF_op_upper_closed`.  Conceptually natural in Sambin-style settings.
**Resolution**: add `op_preserved_by_le : T.le a b → IsOperational a →
IsOperational b` to `OperationalFormalTopology` class.  Trivial for
`IsOperational := True` instances.  Retained as conceptually sound
even after T20 made it not directly needed for v1.0.0.

---

## T20 — `listLowerOrder` direction mismatch (Stage 6b)

**Stage**: 6b.
**Caught at**: implementer's paper sketch of `prodF_op_upper_closed`.
**Root cause**: PLAN_6b §1.2(A) assumed `A vL B → ∀ b ∈ B, ∃ a ∈ A,
prodLe a b` (per-B-element preimage in A).  Actual definition:
`A vL B := ∀ a ∈ A, ∃ b ∈ B, le a b` (opposite direction — A bounded
by B).
**Resolution**: R3 (concrete-only) — provide
`Examples.instUnitBoolProductOperationalCompact` directly.  Defer
abstract `instProdOperationalCompact` to v1.1.0.  No retroactive Stage
5/6 amendments.

---

## T21 — Mathlib `iSup` notation bridging via `iSup_pos`

**Stage**: 7.
**Caught at**: implementer's frame distributivity proof — multiple
attempts.
**Root cause**: mathlib's `⨆ b ∈ S, A ⊓ b` notation elaborates to nested
`iSup` with conditional `iSup (_ : b ∈ S)`.  Our explicit `sSup S' :=
saturate (⋃ U ∈ S', U.1)` definition produced unions in a different
syntactic form.  Bridging required identifying `iSup_pos` lemma:
`(⨆ h : p, f h) = f hp` (given `hp : p`).
**Resolution**: rewrite via `iSup_pos hUS` to align the conditional iSup
with explicit `A ⊓ U`.  ~5 lines once identified, but took multiple
elaboration attempts to find.
**Methodological note**: T21 is a notation/elaboration finding, not a
mathematical one.  The paper proof closes; Lean's mathlib infrastructure
requires specific tactic to bridge.

---

## Patterns observed

**Pattern 1 — Architect direction errors caught by implementer paper sketch**:
T5, T8, T9, T11, T15, T17, T20.  All caught at word-first/paper-sketch
phase BEFORE Lean code committed.  Validates `§6.(2) pre-implementation
paper sketch` workflow as recognition-discipline gate.

**Pattern 2 — Classical inheritance from mathlib**:
T6, T13.  Required custom isolated reimplementations to maintain
`Classical.choice`-free baseline.

**Pattern 3 — Word-first under-specification of technical requirements**:
T7, T14, T16, T19.  Architect's plans implicitly assumed properties
that needed explicit axiomatization.  Recognition discipline made them
explicit.

**Pattern 4 — Notation/elaboration bridging at integration boundaries**:
T21.  Mathlib's notation has elaboration semantics that require
specific bridging tactics.  Not mathematical but technical.

**Pattern 5 — Scope discipline under fatigue**:
T20 R3 resolution.  Architect chose concrete-only path over forcing
abstract closure, preserving cycle stability.

---

## Methodological significance

The cycle accumulated **19 distinct architectural amendments** (T0-T21)
through nine sessions of Variant A workflow.  Each represents a
word-first design gap caught at recognition-discipline gate.

**Key methodological result**: at no point did an architect direction
error propagate into committed Lean code.  The pre-implementation
paper sketch + halt-and-report workflow consistently caught issues
before code commitment.

This data is substantial **Part VIII** content demonstrating the
recognition discipline working at workflow level across a complete
non-trivial Lean 4 formalization project.

---

**End of T_FINDINGS.md.**
