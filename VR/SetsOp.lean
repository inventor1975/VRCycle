-- VRCycle.SetsOp — VR-Sets, Brouwer edition: the OPERATIONAL set universe.
-- Built FROM SCRATCH (no mathlib PFunctor.M) to stay below the Classical.choice floor:
-- a set is a pointed graph (a revealing functionality), identity is witnessed bisimulation
-- (a setoid — NO quotient, which is what would re-pull choice).  ZFC (grounded) and ZFA
-- (cyclic, e.g. the Quine atom) are NOT axioms here but a PREDICATE on the graph.
-- The classical CoPSet/OSetZFA/ZFSet universes are the FORMAL register (Tier-3).
import VR.SetsOp.Pointed
import VR.SetsOp.Builder
import VR.SetsOp.Closure
import VR.SetsOp.Omega
import VR.SetsOp.Extensionality
import VR.SetsOp.Congruence
import VR.SetsOp.Becoming
import VR.SetsOp.Describable
import VR.SetsOp.Schemas
import VR.SetsOp.Grounded
import VR.SetsOp.Power
import VR.SetsOp.AFA
