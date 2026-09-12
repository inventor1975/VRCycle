-- VRCycle/Forms/Examples.lean — Parts V–VII: non-realisable formal terms and mixed formulas.
--
-- «The Russell class R = {x : x ∉ x} is a classical formal description.  In the formal register
-- ⌜R⌝ is a well-formed formal term; it is not operationally realisable» (§V.3).  Likewise the
-- Vitali set (uncountable choice, §VI.1), the classical real line and ℘(Nat) (§V.2, Skolem's
-- paradox read in two registers).  Their non-realisability is metatheoretic: the closed world of
-- `isRealisable` sends them to `False`, and `¬isRealisable ⌜τ⌝` is `id`.
--
-- Mixed formulas (§VII.2) combine operational statements about `OpSet` with realisability
-- predicates on formal terms — Lean `Prop`s at the meta level, not a third register.
-- Integrity programme, step 3 (2026-09-12): operational register = `OpSet`; the ZFC-register
-- junction (`mixed_AFA_two_registers`) reads the ZFA boundary correctly as a MODE boundary.
import VR.Forms.Transit

namespace VR.Forms

open VRCycle.SetsOp

theorem not_isRealisable_Russell : ¬isRealisable ⌜"Russell_class"⌝ := id
theorem not_isRealisable_Vitali : ¬isRealisable ⌜"Vitali"⌝ := id
theorem not_isRealisable_classical_R : ¬isRealisable ⌜"classical_R"⌝ := id
theorem not_isRealisable_classical_powerset_N : ¬isRealisable ⌜"classical_powerset_N"⌝ := id

/-- §VII.2 positive mixed formula: the operational ω contains ∅, and the formal ⌜ω⌝ has an
operational correlate. -/
theorem mixed_omega_two_register : (OpSet.vn 0).Mem OpSet.omega ∧ isRealisable ⌜"omega"⌝ :=
  ⟨OpSet.empty_mem_omega, isRealisable_omega⟩

#print axioms not_isRealisable_Russell
#print axioms not_isRealisable_Vitali
#print axioms not_isRealisable_classical_R
#print axioms not_isRealisable_classical_powerset_N
#print axioms mixed_omega_two_register

end VR.Forms
