-- VR/Guard.lean — the build-time axiom guard of the VR core.
--
-- `lake build VR` fails if ANY declaration of the `VR.*` modules (the VR core: numbers,
-- ZTL/operational sets, forms, topology, continuum, apparatus) carries `propext`, `Quot.sound`,
-- `Classical.choice` or `sorryAx`. Every constant is checked — private, compiler-generated, structural
-- and meta ones included (2026-10-30; before, internal and meta constants were skipped unchecked). The
-- one exemption is tool code of the two instrument modules listed below (tactic metaprograms and
-- elaborators: `VR.CSR.reify`, `ringCore`, `DependsOn.transitiveDeps`, …), and not their theorems.
-- This is the sentence "VR is formalised in Lean 4 with an empty axiom list" turned into a
-- build invariant, not a claim. The classical register and the Mathlib bridges live in the other
-- library of this package, `VRClassical`, which depends on the core and is not covered by this guard.

import VR.Meta.DependsOn
import VR.Arithmetic
import VR.Numbers
import VR.Forms
import VR.Apparatus
import VR.Topology
import VR.Continuum
import VR.SetsOp
import VR.ZTL

#assert_axiom_free_library VR tools [VR.Meta.CSRNorm, VR.Meta.DependsOn]
