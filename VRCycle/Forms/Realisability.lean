-- VRCycle/Forms/Realisability.lean — operational realisability of formal terms (§II.7), over the
-- operational set universe `OpSet` (VR-SetsOp).
--
-- Integrity programme, step 3 (2026-09-12).  Until today the operational register of VR-Forms was
-- `OSet = ZFSet` (Mathlib's well-founded ZFC universe, `[propext, Quot.sound]`); it is now `OpSet`
-- — set = revealing functionality, identity = witnessed bisimulation `Equiv`, on `[]`.  The
-- characteristic propositions read membership as `Mem` and identity as `Equiv`: the pair
-- `{a, b}` has members *identical to* `a` or `b` by witness, not by extension.  The ZFC-register
-- reading (Mathlib's `ZFSet`/`PSet`, AFA refuted, the open Conjectures IV.1–2) lives in
-- `Bridge.lean` as `isRealisableZFC` — kind 3 of VR-LOGIC §1, named as such.
import VRCycle.Forms.Language
import VRCycle.SetsOp

namespace VR.Forms

open VRCycle.SetsOp

set_option genInjectivity false

/-- The formal terms with a non-trivial realisability status in this cycle (closed world). -/
inductive Named where
  | empty | omega | pair | afa | other

/-- Classification of a formal term by its description — by `DecidableEq FormalTerm` (a `match`
on string literals compiles to a splitter that reaches `propext`; decidable tests do not). -/
def named (t : FormalTerm) : Named :=
  if t = ⌜"∅"⌝ then .empty
  else if t = ⌜"omega"⌝ then .omega
  else if t = ⌜"pair"⌝ then .pair
  else if t = ⌜"AFA"⌝ then .afa
  else .other

/-- The existential predicate per class: «there is an operational set whose functionality the
description names». -/
def isRealisableN : Named → Prop
  | .empty => ∃ s : OpSet.{0}, ∀ x : OpSet.{0}, ¬ x.Mem s
  | .omega => ∃ s : OpSet.{0}, (OpSet.vn 0).Mem s ∧ ∀ n : OpSet.{0}, n.Mem s → (OpSet.succ n).Mem s
  | .pair => ∀ a b : OpSet.{0}, ∃ s : OpSet.{0}, ∀ x : OpSet.{0}, x.Mem s ↔ x.Equiv a ∨ x.Equiv b
  | .afa => ∀ (V : Type) (E : V → V → Prop), ∃ d : V → OpSet.{0}, IsDecoration E d
  | .other => False

/-- **Operational realisability** (§II.7, Definition II.3): «a formal term ⌜τ⌝ is operationally
realisable if in the operational register there exists an operational set A such that the
description τ corresponds to the functionality A.»  Closed world: unnamed descriptions are
metatheoretically non-realisable (`False`). -/
def isRealisable (t : FormalTerm) : Prop := isRealisableN (named t)

/-- ⌜∅⌝ is realisable: `OpSet.empty` reveals nothing. -/
theorem isRealisable_empty : isRealisable ⌜"∅"⌝ := ⟨OpSet.empty, OpSet.not_mem_empty⟩

/-- ⌜ω⌝ is realisable: `OpSet.omega` contains `∅` and is closed under successor. -/
theorem isRealisable_omega : isRealisable ⌜"omega"⌝ :=
  ⟨OpSet.omega, OpSet.empty_mem_omega, fun _ hn => OpSet.omega_succ_closed hn⟩

/-- ⌜pair⌝ is realisable: `OpSet.pair a b` has as members exactly the sets *identical to* `a`
or `b` (`Equiv` — witnessed identity, the operational reading of extensionality). -/
theorem isRealisable_pair : isRealisable ⌜"pair"⌝ :=
  fun a b => ⟨OpSet.pair a b, fun x => OpSet.mem_pair x a b⟩

/-- ⌜AFA⌝ is realisable in the operational universe: every graph has a decoration
(`OpSet.decorate`, VR-SetsOp).  Contrast `Bridge.lean`: in Mathlib's well-founded universe the
same description is refuted — two registers, one honest picture. -/
theorem isRealisable_AFA : isRealisable ⌜"AFA"⌝ :=
  fun _ E => ⟨OpSet.decorate E, OpSet.decorate_isDecoration E⟩

#print axioms isRealisable
#print axioms isRealisable_empty
#print axioms isRealisable_omega
#print axioms isRealisable_pair
#print axioms isRealisable_AFA

end VR.Forms
