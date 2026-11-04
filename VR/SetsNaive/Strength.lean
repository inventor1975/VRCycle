-- VR/SetsNaive/Strength.lean
-- VR-Sets, naive edition — Stage N6: how strong is the CLEAN part?  A first, negative,
-- machine-checked measure: TOTAL cleanliness is trivial.
--
-- The dirty set `D = {x : R∈R}` carries no information at all: not one membership `a ∈ D`
-- is grounded either way.  So the co-extensionality condition between `D` and ANY object is
-- met vacuously, and by the congruence theorem of N5 whatever is grounded about `D` is
-- grounded, the same way, about every object (`D_bottom`).  Consequence (`total_trivial`): a
-- set that decides the dirty probe `D` decides every object the same way — it is extensionally
-- ∅ or V.  Every NONTRIVIAL naive set (one earned member, one earned non-member) is therefore
-- necessarily quarantined at `D` (`nontrivial_dirty_at_D`) — the set of empty sets `Empt` is
-- the witness.
--
-- Reading (ZTL): this is not a defect of the naive layer but ZTL's own rule "dirty by input =
-- not checked": a probe that carries only the mark cannot be judged, by any set.  It does mean
-- that the strength of the clean part must be measured RELATIVE TO CLEAN PROBES (a set clean
-- on clean arguments), never by totality.  Not yet checked against the literature.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Ext

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-- `D` carries no grounded membership at all. -/
theorem D_no_value (a : Tm) (b : Bool) : ¬ Val b (.mem a D) := by
  intro h
  cases b with
  | true => exact D_no_member a h
  | false => cases h with | memF h => exact russell_quarantine false h

theorem D_closed : Cl D := rfl

/-- **The dirty probe is the bottom of information**: whatever is grounded about `D` (in any
context) is grounded, the same way, about every object. -/
theorem D_bottom {t : Tm} (ht : Cl t) (χ : Fm) (b : Bool) :
    Val b (χ.inst D) → Val b (χ.inst t) := by
  have hρ : Inert (fun x y => x = D ∧ y = t) := by
    intro s s' h k c
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨Cl.subst D_closed k c, Cl.subst ht k c⟩
  have H : Ext (fun x y => x = D ∧ y = t) := by
    intro s s' h a a' _ b hv
    obtain ⟨h1, _⟩ := h; subst h1
    exact absurd hv (D_no_value a b)
  exact indiscernible hρ H ⟨rfl, rfl⟩ χ b

theorem inst_mem_closed {X : Tm} (hX : Cl X) (t : Tm) :
    Fm.inst (.mem x0 X) t = .mem t X := by
  show Fm.mem (Tm.subst 0 t x0) (Tm.subst 0 t X) = .mem t X
  rw [Cl.subst hX 0 t]
  rfl

/-- **Total cleanliness is trivial**: a set that decides the dirty probe `D` decides every
object the same way — extensionally it is ∅ (b = false) or V (b = true). -/
theorem total_trivial {X : Tm} (hX : Cl X) (b : Bool) (h : Val b (.mem D X)) :
    ∀ t, Cl t → Val b (.mem t X) := by
  intro t ht
  have h' : Val b ((Fm.mem x0 X).inst D) := by rw [inst_mem_closed hX D]; exact h
  have := D_bottom ht (.mem x0 X) b h'
  rw [inst_mem_closed hX t] at this
  exact this

/-- **Every nontrivial naive set is quarantined at the dirty probe.** -/
theorem nontrivial_dirty_at_D {X s t : Tm} (hX : Cl X) (hs : Cl s) (ht : Cl t)
    (hin : Val true (.mem s X)) (hout : Val false (.mem t X)) (b : Bool) :
    ¬ Val b (.mem D X) := by
  intro h
  cases b with
  | true => exact consistent (total_trivial hX true h t ht) hout
  | false => exact consistent (total_trivial hX false h s hs) hin

theorem Empt_closed : Cl Empt := rfl

/-- V is earned NOT empty (E is in it). -/
theorem V_not_in_Empt : Val false (.mem V Empt) :=
  .memF (.allF E rfl (.negF (.memT .top)))

/-- The witness: the set of empty sets is nontrivial, hence dirty at `D` — rederived from the
general theorem (Bridge proved it by hand). -/
theorem Empt_dirty_at_D (b : Bool) : ¬ Val b (.mem D Empt) :=
  nontrivial_dirty_at_D (s := E) (t := V) Empt_closed rfl rfl E_in_Empt V_not_in_Empt b

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.D_bottom
#print axioms VRCycle.SetsNaive.total_trivial
#print axioms VRCycle.SetsNaive.nontrivial_dirty_at_D
#print axioms VRCycle.SetsNaive.Empt_dirty_at_D
