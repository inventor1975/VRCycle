-- VRCycle/Continuum/Rational.lean — the operational rationals `Qop`: the BRIDGE over the witnessed
-- layer `Numbers/RationalsOp.lean`.
--
-- Integrity programme, step 1d (2026-09-12).  Until today this file built its own `PreQ` over
-- Mathlib's `ℤ` and proved the field laws with `ring` — a second ℚ, on `[propext, Quot.sound]`,
-- and not on VR's own integers.  Now the pre-rationals ARE `QExpr` (integer pairs over VR numbers,
-- identity `qEq`, every law on `[]`), and this file only takes the quotient and packages it with
-- the Mathlib-style instances its consumers use (`CommRing`, `Inv`, `DecidableEq`, `LE`/`LT`,
-- `Nontrivial`) plus the embedding of Mathlib's `ℚ`.  What the quotient costs is exactly
-- `Quot.sound` (and `propext` for the lifted order, `Classical.choice` for `ofRat`): the bridge's
-- axioms, not VR's — VR-LOGIC §1, kind 3.
import VR.Numbers.RationalsOp
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Data.Rat.Defs

namespace VRCycle.Continuum

open VR VR.Numbers

/-- Pre-rationals: the witnessed layer (`Numbers/RationalsOp.lean`). -/
abbrev PreQ := QExpr

/-- The operational-rational setoid: `qEq`. -/
instance PreQ.setoid : Setoid QExpr :=
  ⟨qEq, ⟨qEq_refl, fun h => qEq_symm h, fun h1 h2 => qEq_trans h1 h2⟩⟩

instance PreQ.decidableEquiv (a b : QExpr) : Decidable (a ≈ b) := qEq.decidable a b

/-- The operational rationals: `QExpr` up to `qEq` — the quotient bridge. -/
def Qop : Type := Quotient PreQ.setoid

namespace Qop

/-- Integer pairs into `Qop`. -/
def ofIntExpr (e : IntExpr) : Qop := Quotient.mk PreQ.setoid (qofInt e)

/-- Mathlib's `ℤ` as integer pairs (the bridge's convenience, not an act of VR). -/
def intToPair : Int → IntExpr
  | .ofNat n => .mk (O n) VRObj.base
  | .negSucc n => .mk VRObj.base (O (n + 1))

/-- Integer embedding into `Qop`. -/
def ofInt (z : ℤ) : Qop := ofIntExpr (intToPair z)

instance : Zero Qop := ⟨Quotient.mk PreQ.setoid qzero⟩
instance : One Qop := ⟨Quotient.mk PreQ.setoid qone⟩

def add : Qop → Qop → Qop :=
  Quotient.lift₂ (fun x y => (⟦qadd x y⟧ : Qop))
    (fun _ _ _ _ hx hy => Quotient.sound (qadd_respects hx hy))
def neg : Qop → Qop :=
  Quotient.lift (fun x => (⟦qneg x⟧ : Qop)) (fun _ _ h => Quotient.sound (qneg_respects h))
def mul : Qop → Qop → Qop :=
  Quotient.lift₂ (fun x y => (⟦qmul x y⟧ : Qop))
    (fun _ _ _ _ hx hy => Quotient.sound (qmul_respects hx hy))
/-- Total reciprocal, lifted from `qinv'` (`0⁻¹ = 0`). -/
def inv : Qop → Qop :=
  Quotient.lift (fun x => (⟦qinv' x⟧ : Qop)) (fun _ _ h => Quotient.sound (qinv'_respects h))

instance : Add Qop := ⟨add⟩
instance : Neg Qop := ⟨neg⟩
instance : Mul Qop := ⟨mul⟩
instance : Inv Qop := ⟨inv⟩

theorem add_assoc (a b c : Qop) : a + b + c = a + (b + c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (qadd_assoc x y z))
theorem zero_add (a : Qop) : 0 + a = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (qzero_add x))
theorem add_zero (a : Qop) : a + 0 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (qadd_zero x))
theorem neg_add_cancel (a : Qop) : -a + a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (qEq_trans (qadd_comm _ _) (qadd_neg x)))
theorem add_comm (a b : Qop) : a + b = b + a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (qadd_comm x y))
theorem mul_assoc (a b c : Qop) : a * b * c = a * (b * c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (qmul_assoc x y z))
theorem mul_one (a : Qop) : a * 1 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (qmul_one x))
theorem one_mul (a : Qop) : 1 * a = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (qone_mul x))
theorem mul_comm (a b : Qop) : a * b = b * a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (qmul_comm x y))
theorem left_distrib (a b c : Qop) : a * (b + c) = a * b + a * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (qmul_add x y z))
theorem right_distrib (a b c : Qop) : (a + b) * c = a * c + b * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (qadd_mul x y z))
theorem zero_mul (a : Qop) : 0 * a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (qzero_mul x))
theorem mul_zero (a : Qop) : a * 0 = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (qmul_zero x))

/-- **The operational rationals form a commutative ring** — every law lifted from the witnessed
layer; the quotient adds `Quot.sound` and nothing else. -/
instance instCommRing : CommRing Qop where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  add_comm := add_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

/-- **The reciprocal is a genuine inverse on `Qop`** — total, `a · a⁻¹ = 1` for every `a ≠ 0`
(zero is decidable at this pole of the spectrum; operational `Real` has only a witnessed inverse). -/
theorem mul_inv_cancel : ∀ a : Qop, a ≠ 0 → a * a⁻¹ = 1 := by
  refine Quotient.ind ?_
  intro x h
  have hx : ¬ qEq x qzero := fun e => h (Quotient.sound e)
  exact Quotient.sound (qmul_inv'_cancel hx)

/-- `0⁻¹ = 0` on `Qop`. -/
theorem inv_zero : (0 : Qop)⁻¹ = 0 := Quotient.sound qinv'_zero

/-- **Equality on `Qop` is decidable** — the decidable pole of the operational spectrum. -/
instance : DecidableEq Qop := inferInstanceAs (DecidableEq (Quotient PreQ.setoid))

theorem qle_iff {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') : qle x y ↔ qle x' y' :=
  ⟨qle_respects hx hy, qle_respects (qEq_symm hx) (qEq_symm hy)⟩
theorem qlt_iff {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') : qlt x y ↔ qlt x' y' :=
  ⟨qlt_respects hx hy, qlt_respects (qEq_symm hx) (qEq_symm hy)⟩

/-- `≤` on `Qop`, lifted (the lift of a `Prop` costs `propext` — the bridge's). -/
def le : Qop → Qop → Prop :=
  Quotient.lift₂ qle (fun _ _ _ _ ha hb => propext (qle_iff ha hb))
def lt : Qop → Qop → Prop :=
  Quotient.lift₂ qlt (fun _ _ _ _ ha hb => propext (qlt_iff ha hb))

instance : LE Qop := ⟨le⟩
instance : LT Qop := ⟨lt⟩

/-- **`≤` on `Qop` is decidable.** -/
instance : DecidableLE Qop := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun x y => qle.decidable x y
instance : DecidableLT Qop := fun a b =>
  Quotient.recOnSubsingleton₂ a b fun x y => qlt.decidable x y

/-- **Full trichotomy on `Qop`** — what operational `Real` cannot have. -/
theorem lt_trichotomy (a b : Qop) : a < b ∨ a = b ∨ b < a := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  rcases qlt_trichotomy x y with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Quotient.sound h))
  · exact Or.inr (Or.inr h)

theorem zero_ne_one : (0 : Qop) ≠ 1 := fun h => qzero_ne_one (Quotient.exact h)

instance : Nontrivial Qop := ⟨⟨0, 1, zero_ne_one⟩⟩

theorem mul_self_nonneg (a : Qop) : 0 ≤ a * a :=
  Quotient.inductionOn a (fun x => qmul_self_nonneg x)

theorem mul_self_pos {a : Qop} (h : a ≠ 0) : 0 < a * a := by
  revert h
  refine Quotient.inductionOn a (fun x h => ?_)
  exact qmul_self_pos (fun e => h (Quotient.sound e))

theorem add_pos_of_pos_of_nonneg {A B : Qop} (hA : 0 < A) (hB : 0 ≤ B) : 0 < A + B := by
  revert hA hB
  refine Quotient.inductionOn₂ A B (fun x y hA hB => ?_)
  exact qadd_pos_of_pos_of_nonneg hA hB

/-- Embedding Mathlib's `ℚ` — the `ratCast` any `Field Qop` would be forced to carry.  Reads
`q.num`/`q.den` from Mathlib (`Classical.choice` through Mathlib's `ℚ`): kind 3, the limit. -/
def ofRat (q : ℚ) : Qop :=
  Quotient.mk PreQ.setoid ⟨intToPair q.num, IntExpr.mk (O q.den) VRObj.base, by
    obtain ⟨k, hk⟩ : ∃ k, q.den = k + 1 := ⟨q.den - 1, (Nat.succ_pred_eq_of_pos q.den_pos).symm⟩
    rw [hk]
    exact (intPos_iff _).mpr ⟨O k, intEq_refl _⟩⟩

end Qop

end VRCycle.Continuum

#print axioms VRCycle.Continuum.Qop.instCommRing
#print axioms VRCycle.Continuum.Qop.mul_inv_cancel
#print axioms VRCycle.Continuum.Qop.lt_trichotomy
#print axioms VRCycle.Continuum.Qop.ofRat
