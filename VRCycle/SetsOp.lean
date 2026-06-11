-- VRCycle.SetsOp — VR-Sets, Brouwer edition: the OPERATIONAL set universe.
-- Built FROM SCRATCH (no mathlib PFunctor.M) to stay below the Classical.choice floor:
-- a set is a pointed graph (a revealing functionality), identity is witnessed bisimulation
-- (a setoid — NO quotient, which is what would re-pull choice).  ZFC (grounded) and ZFA
-- (cyclic, e.g. the Quine atom) are NOT axioms here but a PREDICATE on the graph.
-- The classical CoPSet/OSetZFA/ZFSet universes are the FORMAL register (Tier-3).
import VRCycle.SetsOp.Pointed
import VRCycle.SetsOp.Builder
import VRCycle.SetsOp.Closure
import VRCycle.SetsOp.Omega
import VRCycle.SetsOp.Extensionality
import VRCycle.SetsOp.Congruence
import VRCycle.SetsOp.Becoming
import VRCycle.SetsOp.Describable
import VRCycle.SetsOp.Schemas
import VRCycle.SetsOp.Grounded
import VRCycle.SetsOp.Power
import VRCycle.SetsOp.AFA
