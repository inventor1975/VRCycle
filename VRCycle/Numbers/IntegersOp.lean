-- VRCycle/Numbers/IntegersOp.lean
-- The operational integers with WITNESSED identity, on the empty axiom list.
--
-- Empty-list sweep, wave 7 (2026-09-12).  `Numbers/Integers.lean` takes the quotient
-- `ℤ_VR := Quotient intEqSetoid` and proves its ring laws through the isomorphism with
-- Mathlib's `Int` (`forward_injective` + `ring`) — every one of those theorems carries
-- `[propext, Quot.sound]`: the quotient contributes `Quot.sound`, Mathlib's `Int` lemmas and
-- `ring` contribute `propext`.  Neither is an act of VR.
--
-- Here the same laws are stated where VR actually performs them: on the pairs `IntExpr`
-- (a difference `a − b` of two VR numbers) up to the witnessed identity `intEq`
-- (`a + d = b + c`, a decidable equation of VR numbers).  Every proof is a finite
-- computation with `T1_vadd_comm`, `T2_vadd_assoc`, `T3_vmul_distrib` and their
-- multiplicative companions proved below — no quotient, no Mathlib `Int`, no `ring`.
-- `#print axioms` on every theorem of this file returns `[]`.  The quotient file remains as
-- the bridge to Mathlib (its axioms are the bridge's, the acknowledged limit — VR-LOGIC §1).
import VRCycle.Numbers.Integers

namespace VR.Numbers

open VR

-- ============================================================
-- §1. Multiplication laws on VR numbers (VR.lean has T3 = left distributivity;
--     `Integers.lean` has right distributivity).  All by structural induction.
-- ============================================================

theorem vmul_zero_left : ∀ b : VRObj, vmul VRObj.base b = VRObj.base
  | VRObj.base => rfl
  | VRObj.succ d => by
      show vadd (vmul VRObj.base d) VRObj.base = VRObj.base
      exact vmul_zero_left d

theorem vmul_succ_left : ∀ a b : VRObj, vmul (VRObj.succ a) b = vadd (vmul a b) b
  | _, VRObj.base => rfl
  | a, VRObj.succ d => by
      show VRObj.succ (vadd (vmul (VRObj.succ a) d) a)
          = VRObj.succ (vadd (vadd (vmul a d) a) d)
      rw [vmul_succ_left a d, T2_vadd_assoc, T2_vadd_assoc, T1_vadd_comm d a]

theorem vmul_comm : ∀ a b : VRObj, vmul a b = vmul b a
  | a, VRObj.base => (vmul_zero_left a).symm
  | a, VRObj.succ d => by
      show vadd (vmul a d) a = vmul (VRObj.succ d) a
      rw [vmul_succ_left d a, vmul_comm a d]

theorem vmul_assoc : ∀ a b c : VRObj, vmul (vmul a b) c = vmul a (vmul b c)
  | _, _, VRObj.base => rfl
  | a, b, VRObj.succ d => by
      show vadd (vmul (vmul a b) d) (vmul a b) = vmul a (vadd (vmul b d) b)
      rw [T3_vmul_distrib, vmul_assoc a b d]

/-- `(a + b) + (c + d) = (a + c) + (b + d)`. -/
theorem vadd_swap' (a b c d : VRObj) :
    vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d) := by
  rw [T2_vadd_assoc a b (vadd c d), T2_vadd_assoc a c (vadd b d),
      ← T2_vadd_assoc b c d, T1_vadd_comm b c, T2_vadd_assoc c b d]

-- ============================================================
-- §2. The witnessed layer: `IntExpr` up to `intEq`
-- ============================================================

/-- Zero and one as pairs. -/
def zeroI : IntExpr := .mk VRObj.base VRObj.base
def oneI : IntExpr := .mk (VRObj.succ VRObj.base) VRObj.base

theorem iadd_comm : ∀ e f : IntExpr, intEq (iadd e f) (iadd f e)
  | .mk a b, .mk c d => by
      show vadd (vadd a c) (vadd d b) = vadd (vadd b d) (vadd c a)
      rw [T1_vadd_comm a c, T1_vadd_comm d b]
      exact T1_vadd_comm _ _

theorem iadd_assoc : ∀ e f g : IntExpr, intEq (iadd (iadd e f) g) (iadd e (iadd f g))
  | .mk a b, .mk c d, .mk e f => by
      show vadd (vadd (vadd a c) e) (vadd b (vadd d f))
          = vadd (vadd (vadd b d) f) (vadd a (vadd c e))
      rw [T2_vadd_assoc a c e, T2_vadd_assoc b d f]
      exact T1_vadd_comm _ _

theorem iadd_zero : ∀ e : IntExpr, intEq (iadd e zeroI) e
  | .mk a b => by
      show vadd a b = vadd b a
      exact T1_vadd_comm a b

theorem zero_iadd : ∀ e : IntExpr, intEq (iadd zeroI e) e
  | .mk a b => by
      show vadd (vadd VRObj.base a) b = vadd (vadd VRObj.base b) a
      rw [vadd_zero_left, vadd_zero_left]
      exact T1_vadd_comm a b

theorem iadd_ineg : ∀ e : IntExpr, intEq (iadd e (ineg e)) zeroI
  | .mk a b => by
      show vadd a b = vadd b a
      exact T1_vadd_comm a b

theorem imul_comm : ∀ e f : IntExpr, intEq (imul e f) (imul f e)
  | .mk a b, .mk c d => by
      show vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul c b) (vmul d a))
          = vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul c a) (vmul d b))
      rw [vmul_comm c b, vmul_comm d a, vmul_comm c a, vmul_comm d b,
          T1_vadd_comm (vmul b c) (vmul a d)]
      exact T1_vadd_comm _ _

theorem imul_one : ∀ e : IntExpr, intEq (imul e oneI) e
  | .mk a b => by
      show vadd (vadd (vadd VRObj.base a) VRObj.base) b
          = vadd (vadd VRObj.base (vadd VRObj.base b)) a
      rw [vadd_zero_left, vadd_zero_left, vadd_zero_left]
      exact T1_vadd_comm a b

theorem one_imul (e : IntExpr) : intEq (imul oneI e) e :=
  intEq_trans _ _ _ (imul_comm oneI e) (imul_one e)

theorem imul_assoc : ∀ e f g : IntExpr, intEq (imul (imul e f) g) (imul e (imul f g))
  | .mk a b, .mk c d, .mk e f => by
      show vadd (vadd (vmul (vadd (vmul a c) (vmul b d)) e)
                      (vmul (vadd (vmul a d) (vmul b c)) f))
                (vadd (vmul a (vadd (vmul c f) (vmul d e)))
                      (vmul b (vadd (vmul c e) (vmul d f))))
          = vadd (vadd (vmul (vadd (vmul a c) (vmul b d)) f)
                      (vmul (vadd (vmul a d) (vmul b c)) e))
                (vadd (vmul a (vadd (vmul c e) (vmul d f)))
                      (vmul b (vadd (vmul c f) (vmul d e))))
      simp only [vmul_distrib_right, T3_vmul_distrib, vmul_assoc]
      rw [vadd_swap' (vmul a (vmul c e)) (vmul b (vmul d e))
                     (vmul a (vmul d f)) (vmul b (vmul c f)),
          T1_vadd_comm (vmul b (vmul d e)) (vmul b (vmul c f)),
          T1_vadd_comm (vmul b (vmul c e)) (vmul b (vmul d f)),
          vadd_swap' (vmul a (vmul c f)) (vmul a (vmul d e))
                     (vmul b (vmul d f)) (vmul b (vmul c e))]
      exact T1_vadd_comm _ _

theorem imul_iadd : ∀ e f g : IntExpr, intEq (imul e (iadd f g)) (iadd (imul e f) (imul e g))
  | .mk a b, .mk c d, .mk e f => by
      show vadd (vadd (vmul a (vadd c e)) (vmul b (vadd d f)))
                (vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul a f) (vmul b e)))
          = vadd (vadd (vmul a (vadd d f)) (vmul b (vadd c e)))
                (vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul a e) (vmul b f)))
      simp only [T3_vmul_distrib]
      rw [vadd_swap' (vmul a c) (vmul a e) (vmul b d) (vmul b f),
          vadd_swap' (vmul a d) (vmul b c) (vmul a f) (vmul b e)]
      exact T1_vadd_comm _ _

theorem iadd_imul (e f g : IntExpr) : intEq (imul (iadd e f) g) (iadd (imul e g) (imul f g)) :=
  intEq_trans _ _ _ (imul_comm (iadd e f) g)
    (intEq_trans _ _ _ (imul_iadd g e f)
      (iadd_respects _ _ _ _ (imul_comm g e) (imul_comm g f)))

theorem zero_imul : ∀ e : IntExpr, intEq (imul zeroI e) zeroI
  | .mk a b => by
      show vadd (vadd (vmul VRObj.base a) (vmul VRObj.base b)) VRObj.base
          = vadd (vadd (vmul VRObj.base b) (vmul VRObj.base a)) VRObj.base
      rw [vmul_zero_left, vmul_zero_left]

theorem imul_zero (e : IntExpr) : intEq (imul e zeroI) zeroI :=
  intEq_trans _ _ _ (imul_comm e zeroI) (zero_imul e)

-- ============================================================
-- §3. The audit: every act of this file is on the empty list
-- ============================================================

#print axioms vmul_comm
#print axioms vmul_assoc
#print axioms iadd_comm
#print axioms iadd_assoc
#print axioms iadd_zero
#print axioms iadd_ineg
#print axioms imul_comm
#print axioms imul_assoc
#print axioms imul_one
#print axioms imul_iadd
#print axioms iadd_imul
#print axioms intEq_trans
#print axioms iadd_respects
#print axioms imul_respects

end VR.Numbers
