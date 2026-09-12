-- VRCycle/Forms/Transit.lean — the translation π (§III.2) in the shallow embedding, over `OpSet`.
--
-- «The translation π maps every L₁-formula to an L₀-formula: (i) π is the identity on the
-- operational register; (ii) for a formal term ⌜τ⌝, π(⌜τ⌝) = δ_τ, the defining predicate of τ in
-- the operational register; (iii) connectives and quantifiers are preserved.»  (§III.2, verbatim.)
-- «Theorem III.1. T₁ (VR-Forms) is conservative over T₀ (VR-Sets) in the operational register.»
--
-- The shallow π is the total function `translate_pi : FormalTerm → Prop`, rule (ii): the SPECIFIC
-- defining predicate naming the operational set (`OpSet.empty`, `OpSet.omega`, `OpSet.pair`,
-- `OpSet.decorate`); `isRealisable` is the EXISTENTIAL one.  `translate_implies_realisable` is the
-- transit pattern (§IV.2) in this cycle: specific ⟹ existential; the converse fails (a witness
-- cannot be recovered from an existential — the T→O asymmetry, TR-R1).  Theorem III.1 itself is
-- formalised in the three storeys `Conservativity{,FOL,Comprehension}.lean`, all on `[]`.
-- Integrity programme, step 3 (2026-09-12): operational register = `OpSet`; every theorem on `[]`.
import VR.Forms.Realisability

namespace VR.Forms

open VRCycle.SetsOp

set_option genInjectivity false

/-- The specific defining predicate per class. -/
def translateN : Named → Prop
  | .empty => ∀ x : OpSet.{0}, ¬ x.Mem OpSet.empty
  | .omega => (OpSet.vn 0).Mem OpSet.omega ∧
      ∀ n : OpSet.{0}, n.Mem OpSet.omega → (OpSet.succ n).Mem OpSet.omega
  | .pair => ∀ a b x : OpSet.{0}, x.Mem (OpSet.pair a b) ↔ x.Equiv a ∨ x.Equiv b
  | .afa => ∀ (V : Type) (E : V → V → Prop), IsDecoration E (OpSet.decorate E)
  | .other => False

/-- **The translation π** (shallow, rule (ii)). -/
def translate_pi (t : FormalTerm) : Prop := translateN (named t)

theorem translate_pi_empty : translate_pi ⌜"∅"⌝ := OpSet.not_mem_empty
theorem translate_pi_omega : translate_pi ⌜"omega"⌝ :=
  ⟨OpSet.empty_mem_omega, fun _ hn => OpSet.omega_succ_closed hn⟩
theorem translate_pi_pair : translate_pi ⌜"pair"⌝ := fun a b x => OpSet.mem_pair x a b
theorem translate_pi_AFA : translate_pi ⌜"AFA"⌝ := fun _ E => OpSet.decorate_isDecoration E

theorem translateN_implies_realisableN : ∀ n : Named, translateN n → isRealisableN n
  | .empty, h => ⟨OpSet.empty, h⟩
  | .omega, h => ⟨OpSet.omega, h⟩
  | .pair, h => fun a b => ⟨OpSet.pair a b, h a b⟩
  | .afa, h => fun V E => ⟨OpSet.decorate E, h V E⟩
  | .other, h => h.elim

/-- **The transit pattern, specific ⟹ existential**: `π(⌜τ⌝)` gives realisability of ⌜τ⌝. -/
theorem translate_implies_realisable (t : FormalTerm) (h : translate_pi t) : isRealisable t :=
  translateN_implies_realisableN (named t) h

#print axioms translate_pi
#print axioms translate_pi_empty
#print axioms translate_pi_omega
#print axioms translate_pi_pair
#print axioms translate_pi_AFA
#print axioms translate_implies_realisable

end VR.Forms
