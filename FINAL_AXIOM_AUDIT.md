# FINAL_AXIOM_AUDIT.md — VR-Topology v1.0.0 verification

**Generated**: 2026-05-28 via `#print axioms` on every public object.
**Build**: `lake build` clean, 3296 jobs successful.
**Lean**: 4.29.1.
**Mathlib**: as pinned in `lakefile.toml`.

## Summary

**Zero `Classical.choice` across ALL public objects in VR-Topology v1.0.0.**

Axiom profile distribution:
- `[]` axiom-free
- `[propext]`
- `[propext, Quot.sound]`

**No object depends on `Classical.choice`**.

---

## Stage 1 — `FormalTopology.lean` (foundational)

| Object | Kind | Axioms |
|---|---|---|
| `commonRefinement` | def | `[]` |
| `FormalTopology` | structure | `[]` |
| `CoverGen` | inductive | `[]` |
| `CoverGen.cov_refl` | theorem | `[]` |
| `CoverGen.cov_trans` | theorem | `[]` |
| `CoverGen.cov_ref_mono` | theorem | `[]` |
| `CoverGen.cov_local` | theorem | `[]` |
| `CoverGen.cov_meet` | theorem | `[]` |
| `FormalTopology.ofPresentation` | def | `[]` |
| `Examples.Unit.formalTopology` | def | `[]` |
| `Examples.Bool.formalTopology` | def | `[]` |
| `FormalTopology.cov_mono` | theorem | `[]` |
| `FormalTopology.cov_singleton` | theorem | `[]` |
| `FormalTopology.cov_trans_singleton` | theorem | `[]` |

**14 objects, all `[]`.**

---

## Stage 2 — `Operational.lean`

| Object | Kind | Axioms |
|---|---|---|
| `IsDescribable` | class | `[]` |
| `IsDescribable.instEmpty` | instance | `[]` |
| `IsDescribable.instSingleton` | instance | `[propext]` |
| `IsDescribable.instBoolUniv` | instance | `[]` |
| `IsDescribable.instUnitUniv` | instance | `[]` |
| `IsDescribable.binaryUnion` | instance | `[propext, Quot.sound]` |
| `OpCoverGen` | inductive | `[]` |
| `OperationalFormalTopology` | class | `[]` |
| `OperationalFormalTopology.IsOperationalCov` | abbrev | `[]` |
| `opFormalTopologyPredicate` | instance | `[]` |
| `OpCoverGen.toCoverGen` | def | `[]` |
| `OpCoverGen.toOpCov` | def | `[]` |
| `OperationalFormalTopology.ofPresentation` | def | `[]` |
| `OperationalFormalTopology.isOperationalCov_mono` | theorem | `[]` |
| `Examples.Unit.operationalFormalTopology` | instance | `[]` |
| `Examples.Bool.operationalFormalTopology` | instance | `[]` |

**16 objects, mostly `[]`, two `[propext]`/`[propext, Quot.sound]`.**

---

## Stage 3 — `Continuous.lean`

| Object | Kind | Axioms |
|---|---|---|
| `IsDescribable.preimage_of_relator` | reducible def | `[propext, Quot.sound]` |
| `ContinuousMap` | structure | `[]` |
| `ContinuousMap.preimage` | def | `[]` |
| `OpContinuous` | structure | `[]` |
| `ContinuousMap.id` | def | `[]` |
| `OpContinuous.id` | def | `[propext, Quot.sound]` |
| `ContinuousMap.comp` | def | `[]` |
| `OpContinuous.comp` | def | `[propext, Quot.sound]` |
| `OpContinuous.id_isModeAOp` | theorem | `[]` |
| `OpContinuous.comp_isModeAOp` | theorem | `[]` |

**10 objects.**

---

## Stage 4 — `Product.lean`

| Object | Kind | Axioms |
|---|---|---|
| `FormalTopology.prodBase` | def | `[]` |
| `FormalTopology.prodLe` | def | `[]` |
| `FormalTopology.prodLe_refl` | theorem | `[]` |
| `FormalTopology.prodLe_trans` | theorem | `[]` |
| `FormalTopology.prodBasicCov` | def | `[]` |
| `FormalTopology.prod` | def | `[]` |
| `OperationalFormalTopology.prodIsOperational` | def | `[]` |
| `OperationalFormalTopology.opProdBasicCov` | def | `[]` |
| `OperationalFormalTopology.instProd` | instance | `[]` |
| `ContinuousMap.proj₁` | def | `[]` |
| `ContinuousMap.proj₂` | def | `[]` |

**11 objects, all `[]`.**

---

## Stage 5 — `Compact.lean`

| Object | Kind | Axioms |
|---|---|---|
| `FormalTopology.listLowerOrder` | def | `[]` |
| `FormalTopology.listLowerOrder_refl` | theorem | `[]` |
| `FormalTopology.listLowerOrder_trans` | theorem | `[]` |
| `CompactWitness` | structure | `[]` |
| `OperationalCompact` | class | `[]` |
| `OperationalCompact.markedAsModeBTarget` | theorem | `[]` |
| `IsDescribable.List.toDescribable` | instance | `[propext, Quot.sound]` |
| `Examples.instUnitOperationalCompact` | instance | `[propext, Quot.sound]` |
| `Examples.instBoolOperationalCompact` | instance | `[propext, Quot.sound]` |
| `CompactWitness.implies_classical_compact` | theorem | `[]` |

**10 objects.**

---

## Stage 6 — `Tychonoff.lean` (Mode B audit object)

| Object | Kind | Axioms |
|---|---|---|
| `prodF` | def | `[]` |
| `prodF_inhabited` | theorem | `[propext, Quot.sound]` |
| `prodF_upper_closed` | theorem | `[propext, Quot.sound]` |
| `manyMeet` | def | `[]` |
| `cov_meet_iter` | theorem | `[propext]` |
| `cov_product_of_components` | theorem | `[]` |
| `product_decomposition_lemma` | theorem | `[propext]` |
| `cov_via_vL` | theorem | `[]` |
| `prodF_generators_covered` | theorem | `[propext, Quot.sound]` |
| `prodF_cover_closure_head` | theorem | `[propext, Quot.sound]` |
| `prodF_set_invariant` | lemma | `[propext]` |
| `prodF_cover_closure` | theorem | `[propext, Quot.sound]` |
| `prodWitness` | def | `[propext, Quot.sound]` |
| **`tychonoff_binary`** | **def (Mode B audit)** | **`[propext, Quot.sound]`** |

**14 objects.  Mode B audit object highlighted.**

---

## Stage 6b — concrete operational instance

| Object | Kind | Axioms |
|---|---|---|
| `Examples.unitWitness` | def | `[propext, Quot.sound]` |
| `Examples.boolWitness` | def | `[propext, Quot.sound]` |
| **`Examples.instUnitBoolProductOperationalCompact`** | **instance** | **`[propext, Quot.sound]`** |
| 6 supporting decidability instances | instance | mostly `[]` |

---

## Stage 7 — `Bridge.lean` (mathlib bridge)

| Object | Kind | Axioms |
|---|---|---|
| `IsSaturated` | def | `[]` |
| `SatSet` | def | `[]` |
| `SatSet.saturate` | def | `[]` |
| `SatSet.saturate_isSaturated` | theorem | `[]` |
| `SatSet.subset_saturate` | theorem | `[]` |
| `SatSet.le_mem` | theorem | `[]` |
| `instLE` | instance | `[]` |
| `instCompleteLattice` | instance | `[propext, Quot.sound]` |
| `frameMinAx` | instance | `[propext, Quot.sound]` |
| **`instFrame`** | **instance (Order.Frame)** | **`[propext, Quot.sound]`** |

**10 objects.**

---

## Cumulative distribution

Across **~85+ public objects** in VR-Topology v1.0.0:

- `[]` axiom-free: **~50**
- `[propext]`: **3** (cov_meet_iter, product_decomposition_lemma, prodF_set_invariant, IsDescribable.instSingleton)
- `[propext, Quot.sound]`: **~22**
- `[propext, Classical.choice, Quot.sound]`: **0**

**Verification: NO object in VR-Topology v1.0.0 depends on `Classical.choice`.**

This audit is the verification artifact for the v1.0.0 claim "zero
`Classical.choice` across entire tower including bridge to mathlib's
classical `Order.Frame` infrastructure".

---

## How to reproduce this audit

```bash
cd VRCycle
lake update
lake build  # ~3296 jobs, must complete clean

# Then for each object listed above:
echo "import VRCycle.Topology
#print axioms VRCycle.Topology.<OBJECT_NAME>" | lake env lean /dev/stdin
```

Or use the bundled audit script (run all at once):
```bash
# See /tmp scripts used during audit; the comprehensive set of
# #print axioms commands was run across files in this report.
```

---

**End of FINAL_AXIOM_AUDIT.md.**
