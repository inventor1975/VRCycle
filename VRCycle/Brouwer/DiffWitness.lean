-- VR-Brouwer — the DIFFERENTIAL WITNESS, machine-checked.
-- Findings B-1/B-2 showed absolute `#print axioms` cannot discriminate constructivity over the
-- mathlib substrate (ℝ / `Fin.fintype` saturate the tier). The honest replacement is a *dependency*
-- claim: the constructive layer (Stages 2-3) does not transitively invoke the choice-driven
-- extraction `IsCompact.tendsto_subseq` (nor continuity); the classical layer (Stage 4) does.
-- The generic engine lives in `VRCycle.Meta.DependsOn`; this file is just the Brouwer-specific
-- assertions that gate the build.

import VRCycle.Meta.DependsOn
import VRCycle.Brouwer.Fixed
import VRCycle.Brouwer.Convex

open Brouwer.KuhnGen

/-! ### The differential witness, certified at build time

The boundary between the two layers is a build invariant along two independent markers — the
compactness extraction `IsCompact.tendsto_subseq` and continuity `Continuous`:

| layer | `tendsto_subseq` | `Continuous` |
|-------|------------------|--------------|
| Stage 2 `exists_rainbow_cell` (Sperner) | free | free |
| Stage 3 `exists_approx_fixed` (approximate) | free | free |
| Stage 4 `brouwer_stdSimplex` (exact) | **depends** | **depends** |

Each assertion fails the build if violated; the `depends` rows certify the boundary is genuine, not
vacuous. -/

-- Stage 2 — the Sperner combinatorics is entirely free of analysis:
#assert_not_depends_on exists_rainbow_cell on IsCompact.tendsto_subseq
#assert_not_depends_on exists_rainbow_cell on Continuous

-- Stage 3 — the approximate fixed point evaluates `f` but uses neither extraction nor continuity:
#assert_not_depends_on exists_approx_fixed on IsCompact.tendsto_subseq
#assert_not_depends_on exists_approx_fixed on Continuous

-- Stage 4 — the exact theorem genuinely needs both (the boundary is real):
#assert_depends_on brouwer_stdSimplex on IsCompact.tendsto_subseq
#assert_depends_on brouwer_stdSimplex on Continuous

-- Stage 5 — the general (compact convex) theorem inherits the classical extraction:
#assert_depends_on Brouwer.Convex.brouwer_compact_convex on IsCompact.tendsto_subseq

-- The whole layer table in one command (the citable form of the differential witness):
#dependency_matrix [exists_rainbow_cell, exists_approx_fixed, brouwer_stdSimplex,
  Brouwer.Convex.brouwer_compact_convex] vs [IsCompact.tendsto_subseq, Continuous]
