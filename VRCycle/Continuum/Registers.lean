-- VRCycle/Continuum/Registers.lean
-- Operational Continuum (Path 1) — Stage B (file 6): the register gap (unconditional payoff).
--
-- STAGE: B. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md.
--
-- ## What this file does — the unconditional, choice-light payoff of Path 1
-- `no_node_surjection` : there is NO surjection from the (countable) node space
-- `List Bool` onto the branch space.  Combining `nodes_describable` (the operational
-- register is enumerable — Spread.lean) with `branches_not_enumerable` (the becoming
-- register is not — Branch.lean): the countable register of performed acts cannot
-- exhaust the becoming register.  This is the operational-continuum thesis as a theorem,
-- and unlike the Brouwerian results (which assume `Continuity`, classically false — see
-- ClassicalBoundary.lean and Finding CONT-4) it is UNCONDITIONAL.

import VRCycle.Continuum.Branch

namespace VRCycle.Continuum

/-- **The operational register cannot exhaust the becoming register.**  No function from
the countable node space `List Bool` is onto the branch space: composing such a surjection
with the node enumeration `decodeNode` would surject `ℕ` onto branches, contradicting
`branches_not_enumerable`.  Unconditional (no Brouwerian hypothesis); the structural
witness that "becoming" strictly exceeds "done". -/
theorem no_node_surjection : ¬ ∃ f : List Bool → Branch, Function.Surjective f := by
  rintro ⟨f, hf⟩
  refine branches_not_enumerable ⟨f ∘ decodeNode, ?_⟩
  intro α
  obtain ⟨s, hs⟩ := hf α
  exact ⟨encodeNode s, by simp [Function.comp, decodeNode_encodeNode, hs]⟩

-- ============================================================
-- Axiom audit — Stage B (file 6)
-- ============================================================
#print axioms no_node_surjection

end VRCycle.Continuum
