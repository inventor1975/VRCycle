-- VR-Brouwer — top-level module index.
--
-- Brouwer fixed-point theorem via the Sperner route (mathlib-bound), decision (C):
-- concrete Kuhn–Freudenthal / grid model. Per findings B-1/B-2 (CLAUDE.md §5 v3),
-- constructivity is witnessed differentially (no choice-driven extraction), not by the
-- absolute axiom tier (Tier-3 from the ℝ / `Fin.fintype` substrate is accepted).
--
-- Stage 2 (Sperner, in progress):
--   Skeleton  — ℝ-free `Equiv.Perm`/flag machinery (kept; reused if the general pivot
--               form of pseudomanifold (b) is pursued; currently orphaned under the
--               explicit n = 2 encoding).
--   Sperner   — 1-D parity core (`odd_doors`), the induction base case.
--   Grid      — grid realization `gridToSimplex` + mesh ≤ 1/k.
--   Handshake — encoding-independent handshake parity kernel.
--   Kuhn      — link (a) `rainbow_iff_odd_doors` + explicit n = 2 grid cells.
--
-- The barycentric realization (Stage-1a `Subdivision.lean`) was pruned: orphaned under
-- decision (C) (the grid model supersedes barycentric subdivision; Stage 1b dropped).

import VRClassical.Brouwer.Skeleton
import VRClassical.Brouwer.Sperner
import VRClassical.Brouwer.Grid
import VRClassical.Brouwer.Handshake
import VRClassical.Brouwer.Kuhn
import VRClassical.Brouwer.KuhnGen
import VRClassical.Brouwer.Approx
import VRClassical.Brouwer.Fixed
import VRClassical.Brouwer.Convex
import VRClassical.Brouwer.DiffWitness
