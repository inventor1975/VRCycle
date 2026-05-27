# Changelog

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
