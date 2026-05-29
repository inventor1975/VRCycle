# T_FINDINGS_TRANSIT.md — VR-Transit architectural amendments catalog

**Cycle**: VR-Transit (tenth piece of the VR cycle).
**Cycle dates**: 2026-05-29 — (in progress).
**Workflow**: Variant A (architect / implementer).
**Findings prefix**: `TR-` (kept off the bare `T#` numbering of VR-Topology's
`T_FINDINGS.md`, which is a separate per-work catalog).

**Total findings so far**: 3 (TR-FW1, TR-C1, TR-R1).

---

## TR-FW1 — Finite-dimensional transit cost lives in the carrier encoding, not in the algebra

**Stage**: 1 (`VRCycle/Transit/FiniteWitness.lean`).
**Caught at**: Stage 1 axiom audit, then again at the Stage 1 amendment re-audit.
**Target**: `finiteSpan_provides_factorisable` was first targeted `[]`; revised to
choice-free `[propext, Quot.sound]` after this finding (see "Calibration" below).

### Statement
The axiom cost of finitely-generated additive transit is **not** in the linear
algebra (`AddMonoidHom` evaluation) and **not** in the apparatus (`Factorisable` is
`[]`). It is entirely in **how the finiteness of the carrier is encoded**. The
finding has two faces, both reducible to encoding choices, both eliminable.

### Face 1 — index encoding (`Fin card` / `Fintype` / `Finset.univ` pulls `Classical.choice`)
Summing an explicit combination over `Finset.univ` of a `Fin card` index drags in the
`Fintype (Fin n)` / `Finset.univ` infrastructure, which in mathlib v4.29.1 is the full
standard ceiling. Bisection (`#print axioms`, isolated terms):

| Term | Profile |
|---|---|
| `map_zsmul` (additive integer scaling) | `[propext]` |
| `map_sum` (the `AddMonoidHom`-sum lemma) | `[propext, Quot.sound]` |
| `∑ i ∈ (s : Finset ι)` + `map_sum` (abstract `Finset`) | `[propext, Quot.sound]` |
| `Finset.univ : Finset (Fin n)` / `Fintype (Fin n)` | `[propext, Classical.choice, Quot.sound]` |
| `(∑ i : Fin 3, w i) = (∑ i, w i) := rfl` | `[propext, Classical.choice, Quot.sound]` |

`Classical.choice` is injected by `Finset.univ` / `Fintype (Fin card)` — the *index* —
not by additivity and not by the explicit-coordinate (operand-not-operation) design.
**Resolution**: index the explicit combination by an *abstract* `Finset ι` supplied as
data, not by `Finset.univ` of `Fin card`. The aggregating bridge is then
`[propext, Quot.sound]` — choice-free. In-file reproducer:
`tFW1_exhibit_univ_pulls_choice` (`FiniteWitness.lean` §4), kept `private` and printed
with `#print axioms` (not `example`).

### Face 2 — field placement (a `Finset` class field contaminates the pointwise tier)
The first fix for Face 1 put the explicit `carrier : Finset ι` *as a field of the
Tier-2 class* `HasFiniteGeneratorStructure`. That re-introduced cost in a new place: a
`Finset` field makes the **class type itself** depend on `[propext, Quot.sound]`
(`Finset = Multiset` quotient ⇒ `Quot.sound`; set-extensionality ⇒ `propext`), and the
**pointwise** bridge `finiteGen_provides_factorisable` inherited `[propext, Quot.sound]`
merely by referencing the class — even though its proof `⟨g, hg_op, hg_agree i⟩`
introduces no axiom and it does no summation. The `[]` pointwise tier collapsed.

**Resolution (option b, applied)**: keep the Tier-2 class carrying **only** the
axiom-free generator map `gens : ι → T` (exactly as `HasSeparabilityStructure` carries
`denseSeq : ℕ → T`), and pass the finite index set `s : Finset ι` and coefficients
`c : ι → ℤ` as **explicit arguments to the aggregating bridge** `finiteSpan_…`, where
they are operand data. Final audit:

| Object | Profile |
|---|---|
| `HasFiniteGeneratorStructure` (class, 1 field) | `[]` |
| `finiteGen_provides_factorisable` (pointwise) | `[]` |
| `finiteSpan_provides_factorisable` (aggregating) | `[propext, Quot.sound]` |

### Calibration (architect, recorded)
The original Stage-1b target `[]` was wrong, and not because of choice: `[]` is
reachable only by **non-aggregating** (pointwise) bridges (separability, 1a), which
evaluate the witness at a single named operand and touch no `Finset.sum`. Any bridge
that **aggregates over a carrier** necessarily touches `propext` / `Quot.sound` through
`Finset.sum`. The honest achievable target for an aggregating bridge is therefore
**choice-free** `[propext, Quot.sound]`, and the load-bearing check is the absence of
`Classical.choice`. The Stage-1 experiment asked whether finite-dimensional additive
transit can be choice-free; the answer is **yes**.

### Rule canonised
Added to CLAUDE.md §5: axiom-bearing data (whose *type* carries `propext`/`Quot.sound`,
e.g. `Finset`, `Quotient`) must not be a field of a Tier-2 class shared with pointwise
bridges; it is passed as an aggregating-bridge argument. Tier-2 classes carry only
axiom-free data (a generator map). Pointwise bridges target `[]`; aggregating bridges
target choice-free `[propext, Quot.sound]`.

### Impact
- Second clean witness-library provider after separability, of a **different tier**
  (aggregating, choice-free) — strengthens thesis (II) without duplicating
  separability.
- Sharpens thesis (I): cost is now attributable by source — apparatus `[]`, pointwise
  witness `[]`, aggregation `propext`/`Quot.sound`, classical operation `Classical.choice`
  — and the apparatus is clean in every case.
- Relation to A15 (VR-Algebra import-context ceiling escalation): TR-FW1 is a
  *removable* ceiling escalation at the level of **carrier encoding** (both faces were
  eliminated), in contrast to A15's import-chain escalation which could not be removed.

---

## TR-C1 — The operation source is itself a spectrum (algebraic propext vs analytic choice)

**Stage**: 2 (`VRCycle/Transit/Conservativity.lean`).
**Caught at**: Stage 2 name/profile verification (CLAUDE.md §7) before writing the file.

### Statement
The Stage-2 brief annotated `image_isOperationalAddSubgroup_isModeBOp` (VR.Algebra) as
`[]`. Its **actual** profile is `[propext]`. The discrepancy does **not** break the
conservativity gate: the `propext` attributes to the *operation's own algebraic
infrastructure* (`OperationalAddGroup` / `AddSubgroup` membership, set-extensionality),
not to the apparatus. The apparatus column stays empty.

The lesson is a refinement of the attribution model: the **OPERATION** source is not a
single tier but a **spectrum**, and the cycle's Mode B representatives exhibit two ends
of it:

| Representative | Profile | Operation flavour |
|---|---|---|
| `image_isOperationalAddSubgroup_isModeBOp` | `[propext]` | algebraic infrastructure |
| `riesz_extension_isModeBOp` | `[propext, Classical.choice, Quot.sound]` | analytic (Hahn–Banach / choice) |

Both are operation-side; neither is apparatus. So the four-source decomposition
(OPERATION ⊕ POINTWISE-WITNESS ⊕ AGGREGATION ⊕ CARRIER-ENCODING) holds, with the
OPERATION term ranging over its own sub-spectrum.

### Gate verdict
Apparatus column empty in every audited representative (Conservativity.lean §5).
Thesis (I) holds, exhibited on real cycle data. The library may grow (Stage 3) on this
confirmed footing.

### Impact
- Confirms thesis (I) empirically before investing in Stage-3 providers (the ordering
  rationale: cheap gate first).
- Sharpens the exhibited classification: cost is attributable by source at finer grain
  than the brief assumed; the apparatus remains inert throughout.

---

## TR-R1 — No clean reference-track Mode-B instance: the witness library is a predicate-track phenomenon

**Stage**: 4.0 (recon-first; no module created — abstraction dropped).
**Caught at**: Stage 4 reconnaissance, before defining `RefFactorisable` (per the
recon-first brief and recognition discipline A0/S1-A: no abstraction without a
nontrivial instance).

### Question
The four existing providers (separability, finiteGen, finiteSpan, located) all live in
the **predicate track**. The apparatus has a second, **reference** track
(`ReferenceOperationality`, setoids/quotients: `ZFSet = Quotient PSet.setoid`,
`OSetZFA`). Reference-track operationality is *descent* (a map `f : Q → Quotient s`
respects `≈`, i.e. `ReferenceOperationality.IsModeAOp`). Stage 4 asked: is there a
genuine reference-track **Mode B** — an operation that globally does NOT descend (not
Mode A) but descends on a structurally-distinguished subset — to carry a reference
`Factorisable` and extend conservativity (thesis I) to both tracks?

### Finding: no clean nontrivial instance exists
A natural non-descending selection operation (e.g. "select the child at a given
index") is **not totally and purely expressible** on `PSet`:
- **Totality wall.** `PSet.Func x : x.Type → PSet`; to select a child one needs an
  element of `x.Type`, an arbitrary `Type`. `example (x : PSet) : x.Type` is not
  provable — there is no pure total inhabitant extractor.
- **Choice is opaque.** The only way to make selection total is `Classical.choice` on
  `Nonempty x.Type` (plus a default for the empty case). But that selection is opaque:
  for two representatives of the same set the chosen indices are unidentifiable, so the
  defining non-descent `f a ≠ f b` is **not provable** (it may not even hold). Mode B
  here coincides with choice-selection, which is unwitnessable.
- **The only witnessable non-descent is artificial.** A total operation that *is*
  provably non-descending must be a gerrymandered indicator (e.g. a classical decidable
  test `x = thisExactRepresentative`), which is merely a re-skin of "structural
  equality ⊋ `≈`" — true but trivial, not a natural/nontrivial instance. Per A0/S1-A it
  does not justify the `RefFactorisable` abstraction.

### Grounding (Lean, verified in recon scratch — not committed)
Two representatives of the set `{∅, {∅}}` with a `Bool` index in opposite order:
`repA := ⟨Bool, fun b => bif b then {∅} else ∅⟩`, `repB := ⟨Bool, fun b => bif b then ∅
else {∅}⟩`.
- `repA ≈ repB` — provable (same set; only representation order differs).
- `repA.Func true = {∅}` and `repB.Func true = ∅` by `rfl`; `({∅} : ZFSet) ≠ ∅`.
So non-descent is REAL at the representative level — but it is reachable only by reading
a representation-specific index (`true`), which is not a uniform total pure operation
over all `PSet` (the totality wall). There is no operation to lift.

### Outcome — drop (recognition discipline)
`RefFactorisable` and `Reference.lean` are **not** introduced. The drop is the correct
recognition outcome (cf. three abstractions dropped in VR-Apparatus; `OperationalGroup`
deferred until `ℚˣ`, A0/A12), not a failure.

### Relation to S3-A and the thesis
This refines Finding S3-A (two parallel tracks, no natural cross-track bridge). S3-A was
about Mode A composition; TR-R1 is about Mode B / Factorisable: the **witness library
and transit conservativity are a predicate-track phenomenon**. On the reference track,
failure of descent coincides exactly with `Classical.choice` representative selection,
which is opaque and therefore unwitnessable — so no clean reference `Factorisable`
exists. This is an honest cross-track boundary: thesis (I) and the witness library are
exhibited for the predicate track (Conservativity.lean §5); the reference track admits
no witnessable Mode B to extend them to. The set-theoretic reading is that the
non-descending content is exactly choice, and choice is precisely what cannot be
witnessed.

### Impact
- Closes the breadth question honestly: the spanning set is the four predicate-track
  providers (two analytic: density + located; one algebraic: finiteness; the
  computability/arithmetic and reference-track candidates were both examined and dropped
  with reasons). No vapour.
- Sharpens the programme's scope claim for the write-up: bounded leverage, predicate
  track, with the reference-track boundary stated rather than papered over.

---

**End of T_FINDINGS_TRANSIT.md.**
