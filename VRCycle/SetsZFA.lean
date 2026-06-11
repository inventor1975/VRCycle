-- VR-Sets-ZFA (DOI placeholder)
-- Operational reference semantics for non-well-founded sets.
-- Lean 4 formalisation extending VR-Sets with coinductive type theory
-- and Aczel's Anti-Foundation Axiom as a theorem.
--
-- Stage layout:
--   Stage 1: CoPSet.lean       — coinductive pre-set type
--   Stage 2: Cobisimulation.lean — equivalence relation (planned)
--   Stage 3: OSetZFA.lean      — quotient type (planned)
--   Stage 4: Membership.lean   — ∈ on OSetZFA (planned)
--   Stage 5: AFA.lean          — AFA theorem (planned)
--   Stage 6: Embedding.lean    — OSet → OSetZFA (planned)
--   Stage 7: Examples.lean     — Quine atom + demonstrations (planned)
--   Stage 8: API.lean          — helper lemmas, polish (planned)

import VRCycle.SetsZFA.CoPSet
import VRCycle.SetsZFA.Cobisimulation
import VRCycle.SetsZFA.OSetZFA
import VRCycle.SetsZFA.Membership
import VRCycle.SetsZFA.AFA
import VRCycle.SetsZFA.Embedding
import VRCycle.SetsZFA.Examples
import VRCycle.SetsZFA.API
import VRCycle.SetsZFA.ZFAxioms
