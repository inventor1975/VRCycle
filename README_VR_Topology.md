# VR-Topology v1.0.0

Constructive predicative formal topology in Lean 4, with binary
Tychonoff theorem and bridge to mathlib's `Order.Frame`.

The ninth work in the VR cycle (formal-system development by Vitaly
Reznik).  Builds on VR-Apparatus (DOI 10.5281/zenodo.20381417).

## Mode B audit object

`tychonoff_binary` — binary Tychonoff for compact formal topologies,
proved constructively via Vickers (2006) Theorem 19.

**Axiom profile**: `[propext, Quot.sound]`. **Zero `Classical.choice`**.

```lean
def tychonoff_binary
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    CompactWitness (FormalTopology.prod T₁ T₂)
                   (OperationalFormalTopology.instProd T₁ T₂).basicCov
```

## Cumulative audit (final)

- ~2700 lines Lean across 6 files (FormalTopology, Operational,
  Continuous, Product, Compact, Tychonoff, Bridge).
- ~85+ public objects.
- Axiom distribution (see `FINAL_AXIOM_AUDIT.md`):
  - `[]` axiom-free: ~50
  - `[propext]`: 3
  - `[propext, Quot.sound]`: ~22
  - `[propext, Classical.choice, Quot.sound]`: **0**

**Zero `Classical.choice` across the entire VR-Topology v1.0.0 tower**,
including the bridge to mathlib's classical `Order.Frame` infrastructure
(an unexpected positive deviation from PLAN_7's expectation).

## Repository structure

```
VRCycle/
  Topology.lean              -- top-level module (imports all)
  Topology/
    FormalTopology.lean      -- Stage 1: FormalTopology, CoverGen
    Operational.lean         -- Stage 2: OperationalFormalTopology, OpCoverGen
    Continuous.lean          -- Stage 3: continuous maps (relators)
    Product.lean             -- Stage 4: binary products
    Compact.lean             -- Stage 5: CompactWitness, OperationalCompact
    Tychonoff.lean           -- Stages 6 + 6b: binary Tychonoff + concrete instance
    Bridge.lean              -- Stage 7: bridge to Order.Frame
    Examples/                -- (reserved; current examples inline)
    _attic/                  -- historical artifacts (Stage 0 frame attempt, etc.)
```

## Mode B audit position in the VR cycle

| Audit | Achievement |
|---|---|
| VR-Hahn-Banach (VR-Audit) | multistep classical, `[propext, Classical.choice, Quot.sound]` |
| VR-Algebra image of subgroup | onestep constructive, `[propext]` |
| **VR-Topology Tychonoff** | **multistep constructive structural induction, `[propext, Quot.sound]`**, with constructive bridge to mathlib `Order.Frame` |

VR-Topology v1.0.0 occupies the **multistep constructive** position on
the Mode B spectrum, with the additional unprecedented property of a
constructive bridge to mainstream classical infrastructure.

## Reproducibility

```bash
cd VRCycle
lake update
lake build
```

Expected: 3296 build jobs successful, no errors, no warnings.

Verify the central axiom claim:

```lean
#print axioms VRCycle.Topology.tychonoff_binary
-- 'VRCycle.Topology.tychonoff_binary' depends on axioms:
--   [propext, Quot.sound]

#print axioms VRCycle.Topology.instFrame
-- 'VRCycle.Topology.instFrame' depends on axioms:
--   [propext, Quot.sound]

#print axioms VRCycle.Topology.Examples.instUnitBoolProductOperationalCompact
-- 'VRCycle.Topology.Examples.instUnitBoolProductOperationalCompact' depends on
-- axioms: [propext, Quot.sound]
```

Full audit per object: see `FINAL_AXIOM_AUDIT.md`.

## Key theorems

- `VRCycle.Topology.tychonoff_binary` — binary Tychonoff (Stage 6, Mode B
  audit object).
- `VRCycle.Topology.Examples.instUnitBoolProductOperationalCompact` —
  concrete compactness for `Unit × Bool` (Stage 6b).
- `VRCycle.Topology.instFrame` — bridge from `SatSet T` to mathlib's
  `Order.Frame` (Stage 7).

## T-findings (architectural amendments through cycle)

18 distinct T-findings catalogued (T0-T21 with T18 skipped, T4/T10
absorbed). Each represents a word-first architectural gap caught at
recognition-discipline pre-implementation paper sketch. Full catalog
in `T_FINDINGS.md`.

## Methodological notes

- **Variant A workflow**: architect (word-first PLAN documents) and
  implementer (Lean code), iterating via halts and reports.
- **Recognition discipline**: bidirectional, applied to code and plans.
- **Word-first phase**: all PLAN documents written before Lean.
- **Axiom audit per public object**: every theorem/def/instance has
  `#print axioms` verified.
- **Honest scope discipline**: where abstract closure was infeasible
  (Stage 6b R3), concrete-only path was chosen; documented honestly.

## Deferred to v1.1.0

- Bridge B (`FormalTopology → TopCat` via formal points).
- Compactness payoff theorem (`OperationalCompact → CompactSpace`).
- Frame functoriality (continuous maps lift to frame homomorphisms).
- Abstract `instProdOperationalCompact` (Stage 6b R3 gap — currently
  concrete-only for `Unit × Bool`; requires bidirectional
  `listLowerOrder` or restructured `OperationalCompact` class).

## References

- Vickers, S. (2006). *Compactness in locales and in formal topology*.
  Annals of Pure and Applied Logic 137, 413-438.
- Vickers, S. (2005). *Some constructive roads to Tychonoff*. In *From
  Sets and Types to Topology and Analysis*, Oxford Univ. Press.
- Coquand, T., Sambin, G., Smith, J., Valentini, S. (2003).
  *Inductively generated formal topologies*. Annals of Pure and
  Applied Logic 124, 71-106.

## VR cycle context

This is the ninth work in the VR cycle by Vitaly Reznik:

1. VR. A Formal System (DOI 10.5281/zenodo.20212092)
2. VR-Numbers (DOI 10.5281/zenodo.20272743)
3. VR-Sets (DOI 10.5281/zenodo.20303536)
4. VR-Forms (DOI 10.5281/zenodo.20355939)
5. VR-Audit (DOI 10.5281/zenodo.20364111)
6. VR-Sets-ZFA (DOI 10.5281/zenodo.20369346)
7. VR-Apparatus (DOI 10.5281/zenodo.20381417)
8. VR-Algebra (DOI 10.5281/zenodo.20398300)
9. **VR-Topology (this work)**

## Citation

[BibTeX entry to be added after Zenodo deposit assigns DOI.]

## License

As per the VR cycle's standard license (see project root or upstream).

## Acknowledgements

This work was conducted using Claude Opus 4.7 in the Variant A workflow
(architect-implementer split).  Claude Code (implementer) and Claude
Opus (architect) collaborated under human curator Vitaly Reznik through
multiple sessions.  All Lean code is machine-verified.

The cycle's recognition-discipline workflow — word-first PLAN documents
+ pre-implementation paper sketch + axiom audit per public object —
proved essential for catching 19 architectural amendments before any
incorrect code was committed.
