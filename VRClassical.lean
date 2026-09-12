-- VRClassical.lean — the CLASSICAL REGISTER and the BRIDGES around the VR core.
--
-- Split from the VR core on 2026-09-12 (integrity programme). `VRCycle` (the other library of this
-- package) is VR proper: numbers, ZTL/operational sets, forms, topology, continuum, apparatus — every
-- declaration with `#print axioms = []` (guarded at build time by `VRCycle/Guard.lean`).
-- `VRClassical` is everything that is stated ABOUT Mathlib objects or lifted to Lean's `Quotient`:
-- the old ℤ/ℚ/ℝ/ℂ over Mathlib and their isomorphisms, the ZFC/ZFA universes (`Sets`, `SetsZFA`),
-- Brouwer's fixed point over Mathlib's ℝ, the Hilbert/Hahn–Banach audit, the algebra instances,
-- the transit examples, the quotient bridges of the continuum (`Qop`, `GaussQ`, `Real`), the
-- Mathlib Frame bridge of the topology, the ZFC reading of the forms, and the apparatus instances
-- over ℝ/PSet. It depends on `VRCycle`; nothing in `VRCycle` depends on it.
-- Axiom profiles here are the standard Lean/Mathlib ones and are declared per object.

import VRClassical.Numbers
import VRClassical.Sets
import VRClassical.SetsZFA
import VRClassical.Algebra
import VRClassical.Audit
import VRClassical.Brouwer
import VRClassical.Transit
import VRClassical.Continuum
import VRClassical.Forms
import VRClassical.Topology
import VRClassical.Apparatus
import VRClassical.Meta
