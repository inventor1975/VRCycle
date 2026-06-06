-- VR-Forms (DOI 10.5281/zenodo.20313735)
-- Two-register system with formal terms
--
-- **Clarification on register language (added 2026-05-26):**
-- The two-register language describes modes of description, not separate
-- operational levels. All descriptions are operational acts; the registers
-- distinguish whether the described referent has an operational correlate
-- (operational register) or is a formal term referring to a non-operational
-- concept such as actual infinity (formal register). This clarification
-- aligns with the expanded operational position recorded in VR-UNIQUENESS.md.
--
-- Stage 1: Language.lean       — Register, FormalTerm, ⌜·⌝ notation
-- Stage 2: Realisability.lean  — isRealisable predicate, base lemmas
--                                (extended Stage 4: +Conjecture cases)
-- Stage 3: Transit.lean        — translate_pi, transit pattern, two-layer connection
-- Stage 4: Bridge.lean         — bridge_AFA, bridge_Conjecture_IV_1/IV_2
-- Stage 5: Examples.lean       — non-realisable examples, mixed formulas
-- Stage 6: Substrate.lean      — Carrier, Operational, substrate totality

import VRCycle.Forms.Language
import VRCycle.Forms.Realisability
import VRCycle.Forms.Transit
import VRCycle.Forms.Bridge
import VRCycle.Forms.Examples
import VRCycle.Forms.Substrate
import VRCycle.Forms.Conservativity
import VRCycle.Forms.ConservativityFOL
