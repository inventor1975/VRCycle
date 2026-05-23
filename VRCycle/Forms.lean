-- VR-Forms (DOI 10.5281/zenodo.20313735)
-- Two-register system with formal terms
--
-- Stage 1: Language.lean       — Register, FormalTerm, ⌜·⌝ notation
-- Stage 2: Realisability.lean  — isRealisable predicate, base lemmas
--                                (extended Stage 4: +Conjecture cases)
-- Stage 3: Transit.lean        — translate_pi, transit pattern, two-layer connection
-- Stage 4: Bridge.lean         — bridge_AFA, bridge_Conjecture_IV_1/IV_2
-- Stage 5: Examples.lean       — non-realisable examples, mixed formulas

import VRCycle.Forms.Language
import VRCycle.Forms.Realisability
import VRCycle.Forms.Transit
import VRCycle.Forms.Bridge
import VRCycle.Forms.Examples
