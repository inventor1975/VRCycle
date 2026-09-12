# Changelog

## Integrity programme, step 1a: `csr_ring` and the witnessed rationals — 2026-09-12

The curator's programme (2026-09-12): VR must stand on itself from arithmetic to the top — numbers
on `[]` as witnessed layers, then sets = `SetsZTL`/`SetsOp`, forms over them, topology over them,
apparatus with witnessed identity. Step 1 is the number floor.

* **New instrument `Meta/CSRNorm.lean` — `csr_ring`, a `ring` on `[]` up to an equivalence.**
  A structure `CSR α` (an equivalence `r` that is a congruence for `add`/`mul`/`neg`, and the
  commutative-ring laws up to `r`); polynomial expressions reified into `PE`, normalised into
  sorted signed monomials by a computable `norm`; `norm_sound` proved once from the fields;
  `eq_of_norm` closes `r lhs rhs` when the normal forms coincide (equality decided by kernel
  evaluation, `Nat.decEq`/`instDecidableEqList`, both on `[]`). Measured: the four-pair identity
  that `simp`-driven AC-rewriting could not finish in 300 s closes in the blink of an eye, whole
  test file 1.6 s; `#print axioms` empty. No cancellation `m + (−m) = 0` (done by hand where
  needed). Found on the way: `List.getD` and overlapping-pattern `match` splitters carry `propext`.
  Instances: `VRObj.csr` (`vr_ring`), `IntExpr.csr` up to `intEq` (`int_ring` — pairs as atoms,
  no unfolding), `QExpr.csr` up to `qEq` (`rat_ring`).
* **`Numbers/IntegersOp.lean` extended:** `vmul_right_cancel` (through `O`/`O_inv` and
  `Nat.eq_of_mul_eq_mul_right`), canonical-form products, `imul_ne_zero`, **`imul_cancel_right`**
  (`e·g ≈ f·g`, `g ≉ 0` ⟹ `e ≈ f`), `imul_eq_zero`, decidable equality of `VRObj` and of `intEq`.
* **New `Numbers/RationalsOp.lean` — ℚ_VR with witnessed identity on `[]`:** `QExpr` (numerator
  and denominator as integer pairs, denominator `≉ 0`), `qEq` by cross-multiplication, `qEq_trans`
  by cancellation, `qadd`/`qneg`/`qmul`/`qinv`/`qofInt` with their congruences (`num_nz_respects`:
  a non-zero numerator is a property of the class), the field laws up to `qEq`, `qzero_ne_one`,
  the embedding `qofInt` a ring homomorphism. Every theorem on `[]` (offenders 0/0/0). Still to
  come for this floor: the order (positive denominators, `qle`/`qlt`, trichotomy, decidability) and
  ℝ_VR; then the continuum's `Qop`/`Real` are moved onto these.

## Empty-list sweep, waves 4–8 — 2026-09-12

Census: modules with no axiom at all 36 → **43** (of 107; 47 carry `Classical.choice` through
Mathlib's ℚ/ℝ/ZFSet and are the declared limit; 17 remain cleanable). Each wave was measured with
`#axiom_offenders_all` over the touched modules → 0 / 0 / 0 before its commit.

* **Wave 4 — `Forms/ConservativityComprehension.lean`.** All de Bruijn lemmas (`subst_lift`,
  `lift_lift`, `lift_subst`, `subst_subst`, `lift_subst'`), the π-commutation lemmas and
  `conservativity` / `conservativity_comprehension_concrete` on `[]`: `omega` and `simp only`
  closures replaced by a local `NatAux` (five hand lemmas) and `show`/`rw`; `genInjectivity` off.
  The third storey of conservativity is now axiom-free like the first two.
* **Wave 5 — `SetsZTL/Stages.lean`.** `ListCore` gains `nth`, `nth_ext`, `nth_append_*`,
  `take_length'`, `take_append_of_le`, `length_append'` (all by induction); the stage court
  (`through_mono`, `pad_through`, `stage_eq_super`, `through_pointwise`, `apart_earned`) no longer
  reaches propext through `List.ext_getElem` / `getElem?` / `take_range`.
* **Wave 6 — `Topology/{Operational,Compact,Continuous}.lean`.** `binaryUnion` interleaves by
  `ListCore.halve` (no `%`, `/`, `omega`); `List.toDescribable` enumerates by `ListCore.nth`
  (`mem_of_nth` / `nth_of_mem` on `List.Mem`); the pairing function behind `preimage_of_relator` is
  rebuilt on `halve` with fuel, every inequality by hand; `OpContinuous.id` / `comp` use
  `isOperationalCov_mono` and direct `IsDescribable` instances instead of `Set.ext` rewrites; the
  `Bool` compactness witness is inhabited by `List.Mem`, not `decide`.
* **Wave 7 — new `Numbers/IntegersOp.lean`.** The ring laws of ℤ_VR restated where VR performs
  them: on `IntExpr` up to the witnessed identity `intEq`, proved from `T1`/`T2`/`T3` and hand
  `vmul_comm` / `vmul_assoc` — no quotient, no Mathlib `Int`, no `ring`; every theorem on `[]`.
  `Integers.lean` (the quotient + the isomorphism with `Int`) stays as the bridge to Mathlib.
* **Wave 8 — `Topology/Tychonoff.lean`.** `ListCore` gains `mem_cons_iff`, `mem_append_iff`,
  `mem_map_iff`, `mem_filter_iff`, `mem_flatMap_iff`, `bnot_decide_eq_true_iff`, `decMem` (decidable
  membership by structural recursion) and `subl`/`filter_mem_subl` (the only fact about
  `List.sublists` the proof used). Tychonoff uses them through `.mp`/`.mpr` only — `rw` with an
  `Iff` goes through `propext` — and drops core's `LawfulBEq` membership instance for the file.
  `tychonoff_binary`, `prodWitness` and the four `prodF_*` theorems carry no axioms.

**Measured, and left to the curator.** The class-2 plan ("replace the `Quotient` carriers of
`Qop`/`Real` by witnessed identity") does not by itself reach `[]`: `PreQ` and `Pre` are built over
Mathlib's `ℤ`, and the core lemmas `Int.add_comm`, `Int.add_assoc`, `Int.mul_comm`, `Int.mul_add`,
`Int.zero_add`, … each carry `propext` (checked with `#print axioms`); only `Int.natCast_add/mul`,
`Int.sub_eq_add_neg`, `Int.add_zero`, `Int.one_mul`, `Int.neg_neg` are free. Dropping the quotient
removes `Quot.sound` and leaves `propext`. Reaching `[]` for the operational continuum's arithmetic
floor means rebuilding its integer substrate (ℤ_VR / Nat pairs with hand lemmas, as `IntegersOp`
does) under `Rational.lean` (468 lines), `Real.lean` (1087), `GaussianRational.lean`, `UnitInterval.lean`
— a rebuild, not a wave. Also found: `ac_rfl` carries `[propext, Quot.sound]`; `Nat.mul_assoc`,
`Nat.right_distrib`, `Nat.add_left_cancel`, `Nat.sub_add_cancel` carry `propext` while
`Nat.add_comm/assoc`, `Nat.mul_comm`, `Nat.left_distrib` are free.

Remaining cleanable (propext/Quot.sound counts): `Continuum.Real` 70/53, `GaussianRational` 39/39,
`UnitInterval` 18/18 (all on the ℤ substrate above); `Sets.VRNumbers` 18/23 (ZFSet — class 3);
`Numbers.Integers` 16/34 (the bridge); `Algebra.*`, `Forms.*` bridges, `Apparatus.Composition` 0/3
(generic theorems about `Quotient`), `Transit.FiniteWitness` (Finset) — class 3. Class 1 is now
exhausted: every remaining `propext`/`Quot.sound` is either the ℤ substrate (class 2) or a statement
about a Mathlib object (class 3) — see VR-LOGIC §1, "three kinds of axiom in Lean, three verdicts".

## Empty-list sweep, waves 1–3 — 2026-09-12

The curator set the bar for the whole cycle at the EMPTY axiom list: an axiom is a thing posited,
VR is acts; where the cycle cannot reach `[]` that is a declared limit of operationalism, to be
named, not accommodated. Three instruments in `Meta/DependsOn.lean` measure it: `#axiom_census`
(per module: how many constants carry propext / Quot.sound / Classical.choice, and through which
external lemma each first arrives), `#axiom_offenders_all` (the constants, one by one, with the
lemma they inherit the axiom from) and `#axiom_frontier` (where an axiom enters one constant's
closure). Census before: 20 modules with no axiom at all; after waves 1–3: **36** (of 106).

What propext turned out to be, module by module, and what replaced it:
* auto-generated `injEq` lemmas (`Eq.propIntro`) for every inductive — never used by the cycle;
  `set_option genInjectivity false` after the namespace line in 12 files (an `… in` form cannot sit
  between a doc comment and its declaration). `Transit.lean` named one; the hand `Iff`
  `FormalTerm.mk_eq_iff` replaces it on `[]`;
* `simp only` closing goals through `eq_self`: `piTr_embed`, `piTr_subst` (two storeys), Cantor's
  diagonal, `no_node_surjection` — rewritten with `show`/`rw`/`Bool.noConfusion`;
* core list and division lemmas (`List.range_succ`, `map_append`, `length_map`, `length_range`,
  `append_inj_left'`, `prefix_refl`, every `Nat` `/` and `%` lemma) — all reach propext through
  `simp`; `Continuum/ListCore.lean` proves the needed ones by induction on `[]`, and `decodeNode`
  is now structural (fuel + `halve`), no well-founded recursion, no division;
* `Nat.find_le` / `le_find_iff` in `continuity_of_nbhd` — `find_spec`/`find_min` are axiom-free, the
  antisymmetry is argued from them;
* `omega` (Int simp lemmas) in `trEmpty_closed` — `Nat.noConfusion`, `Nat.not_lt_zero`.

Now on the empty axiom list, among others: `Theorem_11_VR_PA` (as before), all three storeys'
central theorems — `Conservativity.conservativity`, `ConservativityFOL.conservativity`,
`conservativity_empty_concrete` — and the operational continuum's `operational_cantor`,
`powerset_diagonal`, `no_node_surjection`, `nodes_describable`, `cover_sound`,
`uniform_continuity`, `NbhdFun.continuity_of_nbhd`, `operational_choice_available`.
`ConservativityComprehension.conservativity` still carries `[propext, Quot.sound]` (de Bruijn
lemmas proved with `omega`) — next wave.

Not yet done, by kind (census of 2026-09-12): tactic artefacts in `Continuum.Real`/`GaussianRational`/
`UnitInterval`, `Numbers.Integers`, `Sets.VRNumbers` (`ring`, mathlib `Int.instMonoid`),
`ConservativityComprehension`, `SetsZTL.Stages`, `Topology.Tychonoff` — mechanical, sizeable;
carrier `Quotient` (`Quot.sound` via `Quotient.sound`/`funext`) in `Qop`/`Real`/`Apparatus.Composition`
— a redesign after the `SetsOp` pattern (witnessed identity, no quotient; `OpSet.ext` is on `[]`);
statements about mathlib objects (`ZFSet` in VR-Forms' realisability, `AddSubgroup`, `Finset`,
`Set.ext` in Topology) — a declared limit unless the referent is moved to the cycle's own universe.
The per-module tier tables in `README.md` predate this sweep; the census is the current truth.

## Preprint 12: "Choice as an Act" v1.0.0 — 2026-07-17

Twelfth work of the preprint line (`preprints/12_VR-Choice_EN_v1_0_0.pdf`,
6 pp). Russell's socks, cardinals as becomings, and the productive
continuum — the rule/act split of choice, cardinal comparison as a
witnessed act (order partial by design; trichotomy priced at full AC,
declined), the uniform Cantor–Lawvere ladder, uncountability re-signed
from wall to generator (Post productivity), the anonymous-symmetry
impossibility (Angluin, machine-checked), and the DC demarcation. Ten
central theorems on the EMPTY axiom list. Written to be verified from
zero: a single mathlib-free file `Verify_Choice_standalone.lean` reproves
all ten in under a second (`lean Verify_Choice_standalone.lean`). Zenodo
sheet: `preprints/12_VR-Choice_ZENODO.md`. Tag: `choice-v1.0.0`.

## Continuum: operational cardinals — 2026-07-17

`Continuum/Cardinal.lean`: the cardinal as a type of BECOMING (the curator's
definition). A comparison is an ACT — the witness is data: **`natIntoBranch`**
(an explicit injection ℕ ↪ Branch); **`cantor_ladder`** — the
Cantor–Lawvere diagonal, uniform over every floor, on the **empty axiom
list**: no type surjects onto its power floor — the doubling ladder never
closes from below; **`nat_strictly_below_branch`** — the first step fully
earned (injection up + `branches_not_enumerable` back). TIER PASS same day:
the whole module AND the branch diagonal (`branches_not_enumerable`, which
had carried `[propext]` since June via a `simp` on a Bool hypothesis) now
stand on the **empty axiom list** — own-recursion `beq` lemmas, explicit
`Bool.noConfusion`; `selectors_not_enumerable` cleared by cascade. The order
is partial
by design: trichotomy of cardinals ⟺ AC — cited, not claimed. Choice-free
throughout. Full build green.

## Continuum: Russell's socks — 2026-07-17

`Continuum/Choice.lean` §Socks: selection over indistinguishable pairs split
into rule and act. **`no_symmetric_selector`** — no swap-symmetric selection
rule exists (the Fraenkel–Mostowski sock statement in miniature) — on the
**empty axiom list**; **`selectors_not_enumerable`** — the selectors are
exactly the branches, so the acts are a continuum (`[propext]`, inherits the
branch diagonal). Rules: zero. Acts: uncountable. `Classical.choice` nowhere
in the section: theorems about choice that borrowed none. Full build green,
8369 jobs. Companion runs and the act/object reading live in the ZTL
workspace (dilemmas, 2026-07-17).

## VR-Transit v1.0.0 — 2026-05-29

Tenth work: transit conservativity (the apparatus is axiom-neutral) plus a
bounded, predicate-track witness library. Git tag `v1.15-vr-transit-v1.0.0`.
Zero `sorry`/`admit`; full build 3366 jobs. A clarity result, not new power.

### Witness library — two new providers (four total, counting the inherited one)

New in VR-Transit:

- **`finiteGen_provides_factorisable`** — pointwise finite-generator bridge, `[]`.
- **`finiteSpan_provides_factorisable`** — aggregating bridge over an explicit
  `Finset`, choice-free `[propext, Quot.sound]`.
- **`located_witness_operational` / `located_provides_factorisable`** — the located
  subspace structure supplies the witness `f ∘ P_M` (realised Level-B),
  `[propext, Classical.choice, Quot.sound]` (source: the operation, not the apparatus).

Inherited: the **separability** provider (VR-Apparatus, Stage 6) completes the
spanning set — density, projection, finiteness — all predicate-track.

### Conservativity (I), exhibited

- **`Conservativity.lean`** — no public objects; `#print axioms` attribution shows the
  apparatus column empty across representatives. Four-source cost decomposition:
  operation ⊕ pointwise-witness ⊕ aggregation ⊕ carrier-encoding ⊕ apparatus ∅.
  The universal form is meta (kernel-level), exhibited on representatives.

### Findings (`T_FINDINGS_TRANSIT.md`)

- **TR-FW1** — finite-transit cost lives in the carrier encoding, not the algebra
  (two removable faces: `Fintype`/`Finset.univ` inflation; `Finset`-in-class contamination).
- **TR-C1** — the operation source is a spectrum (`[propext]` algebraic ↔ `[P,C,Q]` analytic).
- **TR-R1** (headline) — the witness method reaches as far as the obstacle is
  witnessable; the reference track reduces to `Classical.choice` (unwitnessable),
  so its provider was dropped (recognition discipline).

### Stages

| Stage | Content | File |
|---|---|---|
| 1 | Finite-generator providers (pointwise + aggregating) | `Transit/FiniteWitness.lean` |
| 2 | Conservativity exhibited (axiom attribution) | `Transit/Conservativity.lean` |
| 3 | Located provider (structural witness) | `Transit/Located.lean` |
| 4 | Reference-track recon → drop (TR-R1) | — |
| 5 | Blueprint Chapter 11 | `blueprint/src/chapters/10_transit.tex` |

## v1.0.0 — 2026-05-28

### Mode B audit object delivered

- **`tychonoff_binary`** — binary Tychonoff for compact formal topologies,
  multistep constructive proof via Vickers 2006 Theorem 19.
- Axiom profile `[propext, Quot.sound]` — **zero `Classical.choice`**.

### Bridge to mathlib

- **`instFrame (SatSet T)`** — `FormalTopology` produces `Order.Frame`
  constructively, without acquiring `Classical.choice` through mathlib's
  classical infrastructure (positive deviation from PLAN_7 expectation).

### Stages completed

| Stage | Content | File |
|---|---|---|
| 1 | `FormalTopology`, `CoverGen`, foundational structure | `FormalTopology.lean` |
| 2 | `OperationalFormalTopology`, `OpCoverGen` | `Operational.lean` |
| 3 | Continuous maps via relators | `Continuous.lean` |
| 4 | Binary products | `Product.lean` |
| 5 | `CompactWitness`, `OperationalCompact` | `Compact.lean` |
| 6 | Binary Tychonoff (Mode B audit object) | `Tychonoff.lean` |
| 6b | Concrete `Unit × Bool` operational compactness | `Tychonoff.lean` |
| 7 | Bridge to `Order.Frame` | `Bridge.lean` |

### T-findings catalogued

**18 distinct architectural amendments** through cycle (T0-T21 with T18
skipped, T4/T10 absorbed).  Full catalog in `T_FINDINGS.md`.

### Cumulative statistics

- **~85+ public objects**.
- **~2700 active lines** of Lean.
- **3296 build jobs** successful.
- **Zero `Classical.choice`** across all stages.
- Build dependencies: Lean 4.29.1, mathlib (as pinned).

### Files (this release)

Root:
- `README.md` — project entry document, audit summary, reproducibility.
- `CHANGELOG.md` — this file.
- `T_FINDINGS.md` — 18-finding methodology catalog.
- `FINAL_AXIOM_AUDIT.md` — `#print axioms` verification artifact.
- `VERSION` — `1.0.0`.
- `STAGE_*_REPORT.md` — per-stage completion reports.
- `T*_AMENDMENT_REPORT.md` — retroactive amendment reports.
- `PLAN_*.md` — word-first PLAN documents per stage.
- `RELEASE_PREP_v1.0.0.md` — release preparation instructions.

Lean code:
- `VRCycle/Topology.lean` — top-level module.
- `VRCycle/Topology/*.lean` — six stage files.
- `VRCycle/Topology/_attic/*.lean` — historical artifacts.

### Deferred to v1.1.0

- **Bridge B** (`FormalTopology → TopCat` via formal points).
- **Compactness payoff** (`OperationalCompact → CompactSpace`).
- **Frame functoriality** (continuous maps lift to frame homomorphisms).
- **Abstract `instProdOperationalCompact`** (currently concrete-only
  for `Unit × Bool`; requires architectural amendment per
  `STAGE_6b_HALT_DIRECTION.md` analysis).
- **Additional concrete examples** beyond `Unit × Bool`.
- **Operational `pair` continuous map** (Finding T9 territory).

### Methodological highlights

- **Recognition discipline at workflow level**: 18 architectural
  amendments all caught at word-first phase or pre-implementation paper
  sketch.  No architect direction error propagated into committed Lean code.
- **Three Classical-avoidance techniques** deployed in Stage 6
  (constructive proof of binary Tychonoff):
  1. List induction extraction (replaces `push_neg`'s Classical fallback).
  2. Direct lambda De Morgan for `¬(A ∧ B)` cases.
  3. Explicit `haveI` typeclass cascades (replaces `by_cases` Classical fallback).
- **Boundary-crossing surprise**: Stage 7's bridge to mathlib's
  `Order.Frame` remained constructive (anticipated to acquire Classical).

### License

As per the VR cycle's standard license.

---

*This is the first major release of VR-Topology.*
