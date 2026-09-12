-- VRCycle/Forms/Bridge.lean — the ZFC-register reading of realisability, and the bridges to the
-- statements about Mathlib's universes (kind 3 of VR-LOGIC §1: named limits, not accommodated).
--
-- `isRealisableZFC` is the reading VR-Forms had until 2026-09-12: the operational register taken
-- to be `OSet = ZFSet` (Mathlib's well-founded ZFC universe).  There ⌜AFA_Statement⌝ (Mathlib's
-- `PSet`) is REFUTED (`AFA_Refuted`, VR-Sets Stage 10) and the Conjectures IV.1–2 are open.  In the
-- operational universe `OpSet` (`Realisability.lean`) ⌜AFA⌝ is REALISED (`OpSet.afa`).  Both are
-- theorems; they speak of different universes — that is the two-register picture, and
-- `afa_two_registers` states it in one line.  Axioms here are Mathlib's (`ZFSet`/`PSet`): the
-- bridge's, not VR's.
import VRCycle.Forms.Transit
import VRClassical.Sets.ZF
import VRClassical.Sets.Modes
import VRClassical.Sets.Conjectures

namespace VR.Forms

open VR.Sets

/-- Realisability read in Mathlib's ZFC universe (`OSet = ZFSet`): the pre-integrity reading. -/
def isRealisableZFC (t : FormalTerm) : Prop :=
  match t with
  | ⟨"∅", .formal⟩ => ∃ s : OSet.{0}, ∀ x : OSet.{0}, x ∉ s
  | ⟨"omega_OSet", .formal⟩ =>
      ∃ s : OSet.{0}, (∅ : OSet.{0}) ∈ s ∧ ∀ n : OSet.{0}, n ∈ s → insert n n ∈ s
  | ⟨"osetPair", .formal⟩ =>
      ∀ a b : OSet.{0}, ∃ s : OSet.{0}, ∀ x : OSet.{0}, x ∈ s ↔ x = a ∨ x = b
  | ⟨"Conjecture_IV_1_Statement", .formal⟩ => Conjecture_IV_1_Statement
  | ⟨"Conjecture_IV_2_Statement", .formal⟩ => Conjecture_IV_2_Statement
  | ⟨"AFA_Statement", .formal⟩ => AFA_Statement
  | _ => False

theorem isRealisableZFC_empty : isRealisableZFC ⌜"∅"⌝ := ⟨osetEmpty, ZFSet.notMem_empty⟩
theorem isRealisableZFC_omega : isRealisableZFC ⌜"omega_OSet"⌝ :=
  ⟨omega_OSet, Theorem_III_6_Infinity⟩
theorem isRealisableZFC_osetPair : isRealisableZFC ⌜"osetPair"⌝ :=
  fun a b => ⟨osetPair a b, Theorem_III_3_Pairing a b⟩

/-- Negative bridge (§V.4): in Mathlib's well-founded universe, ⌜AFA_Statement⌝ is not
realisable — `AFA_Refuted` (VR-Sets Stage 10). -/
theorem bridge_AFA : ¬isRealisableZFC ⌜"AFA_Statement"⌝ := AFA_Refuted

/-- Open conditional bridge (§IX.1, Question 1): realisability of ⌜Conjecture_IV_1_Statement⌝
in the ZFC register is Conjecture IV.1 itself (open). -/
theorem bridge_Conjecture_IV_1 :
    isRealisableZFC ⌜"Conjecture_IV_1_Statement"⌝ ↔ Conjecture_IV_1_Statement := ⟨id, id⟩

/-- Open conditional bridge (§IX.1, Question 2). -/
theorem bridge_Conjecture_IV_2 :
    isRealisableZFC ⌜"Conjecture_IV_2_Statement"⌝ ↔ Conjecture_IV_2_Statement := ⟨id, id⟩

/-- **AFA in two registers**: realised in the operational universe (`OpSet`, every graph has a
decoration), refuted in Mathlib's well-founded one (`PSet`).  The ZFA boundary of VR-Sets is a
boundary of a MODE (groundedness), not of operationality. -/
theorem afa_two_registers : isRealisable ⌜"AFA"⌝ ∧ ¬isRealisableZFC ⌜"AFA_Statement"⌝ :=
  ⟨isRealisable_AFA, bridge_AFA⟩

#print axioms isRealisableZFC
#print axioms bridge_AFA
#print axioms bridge_Conjecture_IV_1
#print axioms bridge_Conjecture_IV_2
#print axioms afa_two_registers

/-- §VII.2 junction formula, corrected by the operational universe: ⌜AFA⌝ is realised in `OpSet`
(the formal register's anti-foundation description has an operational correlate — `OpSet.afa`),
while its ZFC-register reading is refuted in Mathlib's well-founded universe.  The ZFA boundary of
VR-Sets (Part X §X.3 B.5) is thereby located: a boundary of groundedness (a mode), not of
operationality. -/
theorem mixed_AFA_two_registers :
    isRealisable ⌜"AFA"⌝ ∧ ¬isRealisableZFC ⌜"AFA_Statement"⌝ := afa_two_registers

#print axioms mixed_AFA_two_registers

end VR.Forms
