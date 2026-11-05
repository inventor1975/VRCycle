-- VR/SetsNaive/Curry.lean
-- VR-Sets, naive edition — Stage N14 (path 1, "Weber inside ZTL"), first milestone: can a STRONG
-- conditional — `p → p` valid at every value, as Weber's naive set theory needs — live inside
-- ZTL's three values together with naive comprehension?
--
-- Answer, machine-checked: NO.  Take any truth-functional conditional `f` on {T, F, Z} that is
-- classical on the clean values (ZTL's own requirement: the classical laws hold in every clean
-- cell) and validates identity at the mark, `f Z Z = T`.  Then the Curry sets
--   C₁ = {x : x∈x → ⊥},   C₂ = {x : x∈x → (x∈x → ⊥)}
-- have no consistent value: a transparent valuation (naive comprehension) must solve
-- `v = f v F` and `w = f w (f w F)` simultaneously, and no table allows it (`curry_two`).  Modus
-- ponens is not even needed.  So path 1 must LEAVE three-valued truth-functionality: infinitely
-- many values (Łukasiewicz, where arithmetic is known to misbehave — Hájek) or a non-truth-
-- functional conditional (Weber/Brady worlds, Field's revision) — that is the next milestone.
-- (This is the three-valued case of a classical observation — Moh Shaw-Kwei 1954 for Łukasiewicz;
-- not a new theorem, a measured door closed.)
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Residue
import VR.ZTL.Kernel

namespace VRCycle.SetsNaive.Cur

abbrev V3 := VRCycle.ZTL.V

set_option genInjectivity false

/-- The value equations: any 3-valued conditional, classical on clean values, with `Z → Z = T`,
admits no simultaneous solution of the two Curry equations. -/
theorem curry_two (f : V3 → V3 → V3)
    (hTF : f .T .F = .F) (hFF : f .F .F = .T) (hFT : f .F .T = .T) (hZZ : f .Z .Z = .T)
    (v w : V3) (hv : v = f v .F) (hw : w = f w (f w .F)) : False := by
  cases v with
  | T => rw [hTF] at hv; exact VRCycle.ZTL.V.noConfusion hv
  | F => rw [hFF] at hv; exact VRCycle.ZTL.V.noConfusion hv
  | Z =>
    have hZF : f .Z .F = .Z := hv.symm
    cases w with
    | T => rw [hTF, hTF] at hw; exact VRCycle.ZTL.V.noConfusion hw
    | F => rw [hFF, hFT] at hw; exact VRCycle.ZTL.V.noConfusion hw
    | Z => rw [hZF, hZZ] at hw; exact VRCycle.ZTL.V.noConfusion hw

/-! ## The language with a conditional, and transparent valuations -/

mutual
inductive CTm where
  | var : Nat → CTm
  | abs : CFm → CTm
inductive CFm where
  | bot : CFm
  | mem : CTm → CTm → CFm
  | imp : CFm → CFm → CFm
end

mutual
def CTm.subst (k : Nat) (c : CTm) : CTm → CTm
  | .var n => if n = k then c else .var n
  | .abs φ => .abs (CFm.subst (k + 1) c φ)
def CFm.subst (k : Nat) (c : CTm) : CFm → CFm
  | .bot => .bot
  | .mem a b => .mem (CTm.subst k c a) (CTm.subst k c b)
  | .imp φ ψ => .imp (CFm.subst k c φ) (CFm.subst k c ψ)
end

/-- A model of naive comprehension with a truth-functional conditional `f`: a compositional,
TRANSPARENT valuation (`a ∈ {x : φ}` has exactly the value of `φ(a)`). -/
structure Transparent (f : V3 → V3 → V3) where
  val : CFm → V3
  bot : val .bot = .F
  imp : ∀ φ ψ, val (.imp φ ψ) = f (val φ) (val ψ)
  comp : ∀ a φ, val (.mem a (.abs φ)) = val (φ.subst 0 a)

def x0 : CTm := .var 0
/-- `C₁ = {x : x∈x → ⊥}`. -/
def C1 : CTm := .abs (.imp (.mem x0 x0) .bot)
/-- `C₂ = {x : x∈x → (x∈x → ⊥)}`. -/
def C2 : CTm := .abs (.imp (.mem x0 x0) (.imp (.mem x0 x0) .bot))

/-- **No three-valued model**: no conditional that is classical on clean values and validates
`Z → Z` supports naive comprehension. -/
theorem no_transparent (f : V3 → V3 → V3)
    (hTF : f .T .F = .F) (hFF : f .F .F = .T) (hFT : f .F .T = .T) (hZZ : f .Z .Z = .T)
    (M : Transparent f) : False := by
  have h1 : M.val (.mem C1 C1) = f (M.val (.mem C1 C1)) .F :=
    (M.comp C1 (.imp (.mem x0 x0) .bot)).trans (by
      show M.val (.imp (.mem C1 C1) .bot) = _; rw [M.imp, M.bot])
  have h2 : M.val (.mem C2 C2) = f (M.val (.mem C2 C2)) (f (M.val (.mem C2 C2)) .F) :=
    (M.comp C2 (.imp (.mem x0 x0) (.imp (.mem x0 x0) .bot))).trans (by
      show M.val (.imp (.mem C2 C2) (.imp (.mem C2 C2) .bot)) = _
      rw [M.imp, M.imp, M.bot])
  exact curry_two f hTF hFF hFT hZZ _ _ h1 h2

/-- The K3 material conditional (`Z → Z = Z`) escapes — and pays with `p → p` failing at the
mark: exactly the weakness measured in N10. -/
theorem k3_escapes : VRCycle.ZTL.V.zimp .Z .Z = .F ∧
    VRCycle.ZTL.V.zor (VRCycle.ZTL.V.znot .Z) .Z = .F := by decide

end VRCycle.SetsNaive.Cur

#print axioms VRCycle.SetsNaive.Cur.curry_two
#print axioms VRCycle.SetsNaive.Cur.no_transparent
