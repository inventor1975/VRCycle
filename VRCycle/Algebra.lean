-- VRCycle: Algebra.lean
-- Module index for the VR Operational Algebra cycle — v0.1.0.
--
-- ## What this module is
--
-- The eighth work in the VR Cycle: **Operational Algebra**.
--
-- Demonstrates that the VR-Apparatus framework (meta-formalised in v1.0.0,
-- DOI 10.5281/zenodo.20380344) extends naturally to algebraic structures.
-- Specifically: the predicate-wrapping apparatus (PredicateOperationality)
-- applies to additive groups, with subgroups and a Mode B skeleton example.
--
-- ## Architecture
--
-- VRCycle/Algebra/AddGroup.lean     — OperationalAddGroup typeclass (Stage 1)
-- VRCycle/Algebra/Instances.lean    — ℤ and ZMod n instances (Stages 2, 4)
-- VRCycle/Algebra/ModeA.lean        — Mode A closure theorems + PredicateOperationality (Stage 3)
-- VRCycle/Algebra/Subgroups.lean    — Operational subgroups (Stage 5)
-- VRCycle/Algebra/ModeBExample.lean — Mode B skeleton (intentional sorry, Stage 6)
--
-- ## Stage index
--
-- Stage 1 (complete): OperationalAddGroup typeclass. Finding A0: multiplicative
--   typeclass removed — no v0.1.0 multiplicative instances (recognition discipline).
-- Stage 2: ℤ instance (Instances.lean, OperationalAddGroup ℤ).
-- Stage 3: Mode A theorems + PredicateOperationality instance (ModeA.lean).
-- Stage 4: ZMod n instance (Instances.lean extension).
-- Stage 5: Operational subgroups (Subgroups.lean).
-- Stage 6: Mode B skeleton example (ModeBExample.lean). Findings A7, A8.
-- Stage 7: Polish, full audit, git.

import VRCycle.Algebra.AddGroup
import VRCycle.Algebra.Instances
import VRCycle.Algebra.ModeA
import VRCycle.Algebra.Subgroups
import VRCycle.Algebra.ModeBExample
