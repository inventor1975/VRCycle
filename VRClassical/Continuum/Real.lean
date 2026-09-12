-- VRCycle/Continuum/Real.lean — the operational reals `Real`: the BRIDGE over the witnessed layer
-- `Numbers/RealsOp.lean`, and the point named by a branch.
--
-- Integrity programme, step 1e (2026-09-12).  Until today this file built its own pre-reals over
-- Mathlib's `ℤ` (dyadic numerators, `omega`/`nlinarith`, 1087 lines on `[propext, Quot.sound]`).
-- Now a pre-real IS `RExpr` (a Cauchy sequence of VR's own pre-rationals with an explicit
-- modulus, every law on `[]`); this file takes the quotient, packages the `CommRing`, and names
-- the `[0,1]` point of a branch: `Real.ofBranch α` is the sequence `intval α n / 2^n`, Cauchy by
-- the binary-prefix bound of `UnitInterval.lean`.  The quotient costs exactly `Quot.sound`.
--
-- The order `le`/`lt`, apartness and the reciprocal of a positive real (`Pre.invPos`, with an
-- explicit positivity witness — Markov's line: no modulus, no inverse) live in the witnessed layer
-- (`RealsOp` §6) and are lifted here.
import VR.Continuum.UnitInterval
import VR.Numbers.RealsOp
import Mathlib.Algebra.Ring.Defs

namespace VRCycle.Continuum

open VR VR.Numbers

set_option genInjectivity false

/-- Pre-reals: the witnessed layer. -/
abbrev Pre := RExpr

instance Pre.setoid : Setoid RExpr :=
  ⟨rEq, ⟨rEq_refl, fun h => rEq_symm h, fun h1 h2 => rEq_trans h1 h2⟩⟩

/-- **The operational reals**: pre-reals up to eventual closeness — the quotient bridge. -/
def Real : Type := Quotient Pre.setoid

-- ============================================================
-- §1. The point named by a branch
-- ============================================================

/-- The `n`-th dyadic approximation `intval α n / 2^n` of the point named by `α`. -/
def dyadic (α : Branch) (n : Nat) : QExpr := ⟨intval α n, pow2 n, pow2_pos n⟩

/-- For `k ≤ n ≤ m` the approximations `m` and `n` are within `ε_k` (from the prefix bound). -/
theorem dyadic_close (α : Branch) {k n m : Nat} (hkn : k ≤ n) (hnm : n ≤ m) :
    qclose (dyadic α m) (dyadic α n) (qeps k) := by
  obtain ⟨hd0, hd1⟩ := intval_diff_bound α hnm
  -- D := intval m · 2^n − intval n · 2^m, 0 ≤ D < 2^m
  obtain ⟨e, he⟩ := Nat.le.dest hkn
  subst he
  have hkn' : pow2 k ≤ᵢ pow2 (k + e) := pow2_le_add k e
  -- products of non-negatives
  have p1 : zeroI ≤ᵢ imul (iadd (pow2 (k + e)) (ineg (pow2 k)))
      (iadd (imul (intval α m) (pow2 (k + e))) (ineg (imul (intval α (k + e)) (pow2 m)))) :=
    intNonneg_mul (by int_linarith) hd0
  have p2 : zeroI ≤ᵢ imul (iadd (pow2 m) (ineg (iadd (imul (intval α m) (pow2 (k + e)))
      (ineg (imul (intval α (k + e)) (pow2 m)))))) (pow2 (k + e)) :=
    intNonneg_mul (by int_linarith) (pow2_nonneg _)
  have p3 : zeroI ≤ᵢ imul (iadd (imul (intval α m) (pow2 (k + e)))
      (ineg (imul (intval α (k + e)) (pow2 m)))) (pow2 k) :=
    intNonneg_mul hd0 (pow2_nonneg _)
  have p4 : zeroI ≤ᵢ imul (pow2 m) (pow2 (k + e)) := intNonneg_mul (pow2_nonneg _) (pow2_nonneg _)
  constructor
  · change intLe (imul (iadd (imul (intval α m) (pow2 (k + e))) (imul (ineg (intval α (k + e))) (pow2 m)))
      (pow2 k)) (imul oneI (imul (pow2 m) (pow2 (k + e))))
    int_linarith
  · change intLe (imul (ineg oneI) (imul (pow2 m) (pow2 (k + e))))
      (imul (iadd (imul (intval α m) (pow2 (k + e))) (imul (ineg (intval α (k + e))) (pow2 m))) (pow2 k))
    int_linarith

/-- Every branch names a pre-real: its dyadic approximations form a Cauchy sequence. -/
def Pre.ofBranch (α : Branch) : Pre where
  seq := dyadic α
  cauchy := fun k => ⟨k, fun m n hm hn => by
    rcases Nat.le_total n m with h | h
    · exact dyadic_close α hn h
    · exact qclose_symm (dyadic_close α hm h)⟩

/-- The operational real named by a branch (its `[0,1]` point). -/
def Real.ofBranch (α : Branch) : Real := Quotient.mk _ (Pre.ofBranch α)

-- ============================================================
-- §2. The ring, lifted
-- ============================================================

namespace Real

def ofQ (q : QExpr) : Real := Quotient.mk Pre.setoid (rofQ q)
def ofIntExpr (e : IntExpr) : Real := ofQ (qofInt e)

instance : Zero Real := ⟨Quotient.mk Pre.setoid rzero⟩
instance : One Real := ⟨Quotient.mk Pre.setoid rone⟩

def add : Real → Real → Real :=
  Quotient.lift₂ (fun x y => (⟦radd x y⟧ : Real))
    (fun _ _ _ _ hx hy => Quotient.sound (radd_respects hx hy))
def neg : Real → Real :=
  Quotient.lift (fun x => (⟦rneg x⟧ : Real)) (fun _ _ h => Quotient.sound (rneg_respects h))
def mul : Real → Real → Real :=
  Quotient.lift₂ (fun x y => (⟦rmul x y⟧ : Real))
    (fun _ _ _ _ hx hy => Quotient.sound (rmul_respects hx hy))

instance : Add Real := ⟨add⟩
instance : Neg Real := ⟨neg⟩
instance : Mul Real := ⟨mul⟩

theorem add_comm (a b : Real) : a + b = b + a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (radd_comm x y))
theorem add_assoc (a b c : Real) : a + b + c = a + (b + c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (radd_assoc x y z))
theorem zero_add (a : Real) : 0 + a = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (rzero_add x))
theorem add_zero (a : Real) : a + 0 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (radd_zero x))
theorem neg_add_cancel (a : Real) : -a + a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (rEq_trans (radd_comm _ _) (radd_neg x)))
theorem mul_comm (a b : Real) : a * b = b * a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (rmul_comm x y))
theorem mul_assoc (a b c : Real) : a * b * c = a * (b * c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (rmul_assoc x y z))
theorem mul_one (a : Real) : a * 1 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (rmul_one x))
theorem one_mul (a : Real) : 1 * a = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (rone_mul x))
theorem left_distrib (a b c : Real) : a * (b + c) = a * b + a * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (rmul_add x y z))
theorem right_distrib (a b c : Real) : (a + b) * c = a * c + b * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (radd_mul x y z))
theorem zero_mul (a : Real) : 0 * a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (rzero_mul x))
theorem mul_zero (a : Real) : a * 0 = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (rmul_zero x))

/-- **The operational reals form a commutative ring** — lifted from the witnessed layer. -/
instance instCommRing : CommRing Real where
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

theorem zero_ne_one : (0 : Real) ≠ 1 := fun h => rzero_ne_one (Quotient.exact h)

-- ============================================================
-- §3. Order and apartness, lifted (lifting a `Prop` costs `propext` — the bridge's)
-- ============================================================

theorem rle_iff {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') : rle x y ↔ rle x' y' :=
  ⟨rle_respects hx hy, rle_respects (rEq_symm hx) (rEq_symm hy)⟩
theorem rlt_iff {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') : rlt x y ↔ rlt x' y' :=
  ⟨rlt_respects hx hy, rlt_respects (rEq_symm hx) (rEq_symm hy)⟩

def le : Real → Real → Prop := Quotient.lift₂ rle (fun _ _ _ _ ha hb => propext (rle_iff ha hb))
def lt : Real → Real → Prop := Quotient.lift₂ rlt (fun _ _ _ _ ha hb => propext (rlt_iff ha hb))
/-- Apartness `x # y`: positive separation one way or the other. -/
def apart (a b : Real) : Prop := lt a b ∨ lt b a

instance : LE Real := ⟨le⟩
instance : LT Real := ⟨lt⟩

theorem le_refl (a : Real) : a ≤ a := Quotient.inductionOn a rle_refl
theorem le_trans {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  revert h1 h2
  exact Quotient.inductionOn₃ a b c (fun x y z h1 h2 => rle_trans h1 h2)
theorem le_antisymm {a b : Real} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  revert h1 h2
  exact Quotient.inductionOn₂ a b (fun x y h1 h2 => Quotient.sound (rle_antisymm h1 h2))
theorem lt_irrefl (a : Real) : ¬ a < a := Quotient.inductionOn a rlt_irrefl
theorem le_of_lt {a b : Real} (h : a < b) : a ≤ b := by
  revert h
  exact Quotient.inductionOn₂ a b (fun x y h => rle_of_rlt h)
theorem apart_irrefl (a : Real) : ¬ apart a a := fun h => h.elim (lt_irrefl a) (lt_irrefl a)

end Real

/-- The reciprocal of a positive pre-real, given its positivity witness (`RealsOp.rinvPos`). -/
abbrev Pre.invPos (x : Pre) (k N : Nat) (hw : PosWitness x k N) : Pre := rinvPos x k N hw
theorem Pre.invPos_mul (x : Pre) (k N : Nat) (hw : PosWitness x k N) :
    rEq (rmul x (Pre.invPos x k N hw)) rone := rinvPos_mul x k N hw

end VRCycle.Continuum

#print axioms VRCycle.Continuum.Pre.ofBranch
#print axioms VRCycle.Continuum.dyadic_close
#print axioms VRCycle.Continuum.Real.instCommRing
#print axioms VRCycle.Continuum.Real.mul_assoc
#print axioms VRCycle.Continuum.Real.zero_ne_one
#print axioms VRCycle.Continuum.Real.le_antisymm
#print axioms VRCycle.Continuum.Pre.invPos_mul
