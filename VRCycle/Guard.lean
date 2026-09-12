-- VRCycle/Guard.lean — the build-time axiom guard of the VR core.
--
-- `lake build VRCycle` fails if ANY declaration of the `VRCycle.*` modules (the VR core: numbers,
-- ZTL/operational sets, forms, topology, continuum, apparatus) carries `propext`, `Quot.sound`,
-- `Classical.choice` or `sorryAx`. Meta code (tactics, census commands) is skipped — instruments, not
-- theorems. This is the sentence "VR is formalised in Lean 4 with an empty axiom list" turned into a
-- build invariant, not a claim. The classical register and the Mathlib bridges live in the other
-- library of this package, `VRClassical`, which depends on the core and is not covered by this guard.

import VRCycle.Meta.DependsOn
import VRCycle.VR
import VRCycle.Numbers
import VRCycle.Forms
import VRCycle.Apparatus
import VRCycle.Topology
import VRCycle.Continuum
import VRCycle.SetsOp
import VRCycle.SetsZTL

#assert_axiom_free_library VRCycle
