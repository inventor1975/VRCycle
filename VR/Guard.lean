-- VR/Guard.lean — the build-time axiom guard of the VR core.
--
-- `lake build VR` fails if ANY declaration of the `VR.*` modules (the VR core: numbers,
-- ZTL/operational sets, forms, topology, continuum, apparatus) carries `propext`, `Quot.sound`,
-- `Classical.choice` or `sorryAx`. Meta code (tactics, census commands) is skipped — instruments, not
-- theorems. This is the sentence "VR is formalised in Lean 4 with an empty axiom list" turned into a
-- build invariant, not a claim. The classical register and the Mathlib bridges live in the other
-- library of this package, `VRClassical`, which depends on the core and is not covered by this guard.

import VR.Meta.DependsOn
import VR.VRArithmetic
import VR.Numbers
import VR.Forms
import VR.Apparatus
import VR.Topology
import VR.Continuum
import VR.SetsOp
import VR.SetsZTL

#assert_axiom_free_library VR
