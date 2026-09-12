-- VRCycle/Forms/Substrate.lean — the substrate thesis (Stage 6), over `OpSet`.
--
-- Frozen statement (curator-architect, 2026-05-28): «Operationality is a total substrate.  Every
-- operand (operational object or formal term) and every result — including the empty result ∅ —
-- carries operational substrate.»
--
-- Integrity programme, step 3 (2026-09-12).  The 2026-05-28 gate chose `Acc (· ∈ ·)` as the
-- substrate predicate on `OSet = ZFSet`, where it is total because Mathlib's universe is
-- well-founded by construction.  On the operational universe `OpSet` that choice is REFUTED as a
-- substrate: AFA holds there (`OpSet.afa`), so groundedness (`OpSet.IsGrounded`) is not total —
-- it is a MODE (ZFC-mode), separately available.  The substrate of an operational set is the act it
-- IS: its revealing functionality, witnessed minimally by the identity bisimulation `Equiv.refl`
-- (the diagonal relation with its two simulation proofs — a construction, not `True`).  For a
-- formal term the substrate is the act of inscription (Principle of Forms, §II.4): `True`.
-- Every theorem on `[]`.
import VRCycle.Forms.Examples

namespace VR.Forms

open VRCycle.SetsOp

set_option genInjectivity false

/-- Carrier of the substrate thesis: anything appearing as operand or result. -/
inductive Carrier where
  | obj  : OpSet.{0} → Carrier
  | term : FormalTerm → Carrier

/-- Operational substrate: an operational set witnesses its own functionality (the identity
bisimulation); a formal term is inscribed. -/
def Operational : Carrier → Prop
  | .obj a  => a.Equiv a
  | .term _ => True

/-- Totality of the operational substrate. -/
theorem operational_total : ∀ c : Carrier, Operational c
  | .obj a  => OpSet.Equiv.refl a
  | .term _ => trivial

/-- The empty set — the limit case the curator insisted on — carries operational substrate. -/
theorem operational_empty : Operational (.obj OpSet.empty) := OpSet.Equiv.refl _

/-- Both registers of ω carry operational substrate (§3.4). -/
theorem omega_substrate : Operational (.obj OpSet.omega) ∧ Operational (.term ⌜"omega"⌝) :=
  ⟨OpSet.Equiv.refl _, trivial⟩

#print axioms Carrier
#print axioms Operational
#print axioms operational_total
#print axioms operational_empty
#print axioms omega_substrate

end VR.Forms
