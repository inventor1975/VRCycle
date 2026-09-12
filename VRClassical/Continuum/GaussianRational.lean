-- VRCycle/Continuum/GaussianRational.lean — the Gaussian rationals ℂ_op = ℚ_op(i).
--
-- Integrity programme, step 1d (2026-09-12).  Witnessed layer first: `GaussE` (a pair of
-- pre-rationals) up to the componentwise identity `gEq`; ring laws by `rat_ring`, the total inverse
-- `z̄ / |z|²` with `|z|² > 0` for `z ≉ 0` (decidable zero at this pole of the spectrum) — every
-- theorem on `[]`.  Then the bridge `GaussQ` (the quotient) with `CommRing`, `Inv`,
-- `DecidableEq` for consumers, costing exactly `Quot.sound`.
import VRClassical.Continuum.Rational

namespace VRCycle.Continuum

open VR VR.Numbers

set_option genInjectivity false

-- ============================================================
-- §1. The witnessed layer
-- ============================================================

/-- A Gaussian pre-rational `re + im·i`. -/
structure GaussE where
  re : QExpr
  im : QExpr

/-- Componentwise identity. -/
def gEq (z w : GaussE) : Prop := qEq z.re w.re ∧ qEq z.im w.im

theorem gEq_refl (z : GaussE) : gEq z z := ⟨qEq_refl _, qEq_refl _⟩
theorem gEq_symm {z w : GaussE} (h : gEq z w) : gEq w z := ⟨qEq_symm h.1, qEq_symm h.2⟩
theorem gEq_trans {z w v : GaussE} (h1 : gEq z w) (h2 : gEq w v) : gEq z v :=
  ⟨qEq_trans h1.1 h2.1, qEq_trans h1.2 h2.2⟩

instance gEq.decidable (z w : GaussE) : Decidable (gEq z w) := instDecidableAnd

def gzero : GaussE := ⟨qzero, qzero⟩
def gone : GaussE := ⟨qone, qzero⟩
def gadd (z w : GaussE) : GaussE := ⟨qadd z.re w.re, qadd z.im w.im⟩
def gneg (z : GaussE) : GaussE := ⟨qneg z.re, qneg z.im⟩
def gmul (z w : GaussE) : GaussE :=
  ⟨qadd (qmul z.re w.re) (qneg (qmul z.im w.im)), qadd (qmul z.re w.im) (qmul z.im w.re)⟩

theorem gadd_respects {z z' w w' : GaussE} (hz : gEq z z') (hw : gEq w w') :
    gEq (gadd z w) (gadd z' w') :=
  ⟨qadd_respects hz.1 hw.1, qadd_respects hz.2 hw.2⟩
theorem gneg_respects {z z' : GaussE} (hz : gEq z z') : gEq (gneg z) (gneg z') :=
  ⟨qneg_respects hz.1, qneg_respects hz.2⟩
theorem gmul_respects {z z' w w' : GaussE} (hz : gEq z z') (hw : gEq w w') :
    gEq (gmul z w) (gmul z' w') :=
  ⟨qadd_respects (qmul_respects hz.1 hw.1) (qneg_respects (qmul_respects hz.2 hw.2)),
   qadd_respects (qmul_respects hz.1 hw.2) (qmul_respects hz.2 hw.1)⟩

/-- `g_ring`: a `gEq` identity, componentwise by `rat_ring`. -/
syntax "g_ring" : tactic
macro_rules
  | `(tactic| g_ring) =>
    `(tactic| (dsimp only [gEq, gadd, gneg, gmul, gzero, gone]; exact ⟨by rat_ring, by rat_ring⟩))

theorem gadd_comm (z w : GaussE) : gEq (gadd z w) (gadd w z) := by g_ring
theorem gadd_assoc (z w v : GaussE) : gEq (gadd (gadd z w) v) (gadd z (gadd w v)) := by g_ring
theorem gzero_add (z : GaussE) : gEq (gadd gzero z) z := by g_ring
theorem gadd_zero (z : GaussE) : gEq (gadd z gzero) z := by g_ring
theorem gadd_neg (z : GaussE) : gEq (gadd z (gneg z)) gzero := ⟨qadd_neg _, qadd_neg _⟩
theorem gmul_comm (z w : GaussE) : gEq (gmul z w) (gmul w z) := by g_ring
theorem gmul_assoc (z w v : GaussE) : gEq (gmul (gmul z w) v) (gmul z (gmul w v)) := by g_ring
theorem gone_mul (z : GaussE) : gEq (gmul gone z) z := by g_ring
theorem gmul_one (z : GaussE) : gEq (gmul z gone) z := by g_ring
theorem gzero_mul (z : GaussE) : gEq (gmul gzero z) gzero := by g_ring
theorem gmul_zero (z : GaussE) : gEq (gmul z gzero) gzero := by g_ring
theorem gmul_add (z w v : GaussE) : gEq (gmul z (gadd w v)) (gadd (gmul z w) (gmul z v)) := by
  g_ring
theorem gadd_mul (z w v : GaussE) : gEq (gmul (gadd z w) v) (gadd (gmul z v) (gmul w v)) := by
  g_ring

/-- Gaussian pre-rationals as a commutative ring up to `gEq`. -/
def GaussE.csr : VR.CSR.CSR GaussE where
  r := gEq
  refl := gEq_refl
  symm := gEq_symm
  trans := gEq_trans
  add := gadd
  mul := gmul
  neg := gneg
  zero := gzero
  one := gone
  add_congr := gadd_respects
  mul_congr := gmul_respects
  neg_congr := gneg_respects
  add_comm := gadd_comm
  add_assoc := gadd_assoc
  zero_add := gzero_add
  mul_comm := gmul_comm
  mul_assoc := gmul_assoc
  one_mul := gone_mul
  zero_mul := gzero_mul
  mul_add := gmul_add
  neg_add := fun z w => by g_ring
  neg_mul := fun z w => by g_ring
  neg_neg := fun z => by g_ring
  neg_zero := by g_ring

def GaussE.cr : VR.CSR.CR GaussE := { GaussE.csr with add_neg := gadd_neg }

/-- `gauss_ring`: ring identities between Gaussian pre-rationals up to `gEq`, with cancellation. -/
syntax "gauss_ring" : tactic
macro_rules
  | `(tactic| gauss_ring) => `(tactic| cr_ring VRCycle.Continuum.GaussE.cr)

/-- `|z|² = re² + im² : QExpr`. -/
def normSq (z : GaussE) : QExpr := qadd (qmul z.re z.re) (qmul z.im z.im)

theorem normSq_respects {z z' : GaussE} (h : gEq z z') : qEq (normSq z) (normSq z') :=
  qadd_respects (qmul_respects h.1 h.1) (qmul_respects h.2 h.2)

/-- For a non-zero Gaussian pre-rational the norm is strictly positive. -/
theorem normSq_pos {z : GaussE} (h : ¬ gEq z gzero) : qlt qzero (normSq z) := by
  by_cases hre : qEq z.re qzero
  · have him : ¬ qEq z.im qzero := fun him => h ⟨hre, him⟩
    have hp := qadd_pos_of_pos_of_nonneg (qmul_self_pos him) (qmul_self_nonneg z.re)
    exact qlt_respects (qEq_refl _) (qadd_comm _ _) hp
  · exact qadd_pos_of_pos_of_nonneg (qmul_self_pos hre) (qmul_self_nonneg z.im)

theorem normSq_ne_zero {z : GaussE} (h : ¬ gEq z gzero) : ¬ qEq (normSq z) qzero :=
  fun e => qlt_irrefl qzero (qlt_respects (qEq_refl _) e (normSq_pos h))

/-- Total reciprocal `z⁻¹ = z̄ / |z|²` (with `qinv'`, so `0⁻¹ = 0` needs no case). -/
def ginv (z : GaussE) : GaussE :=
  ⟨qmul z.re (qinv' (normSq z)), qneg (qmul z.im (qinv' (normSq z)))⟩

theorem ginv_respects {z z' : GaussE} (h : gEq z z') : gEq (ginv z) (ginv z') :=
  ⟨qmul_respects h.1 (qinv'_respects (normSq_respects h)),
   qneg_respects (qmul_respects h.2 (qinv'_respects (normSq_respects h)))⟩

/-- **The Gaussian pre-rationals are a field in content**: `z · z⁻¹ ≈ 1` for `z ≉ 0`, on `[]`. -/
theorem gmul_inv_cancel {z : GaussE} (h : ¬ gEq z gzero) : gEq (gmul z (ginv z)) gone := by
  have hN := qmul_inv'_cancel (normSq_ne_zero h)
  constructor
  · -- re: a·(a·I) − b·(−(b·I)) ≈ (a² + b²)·I ≈ 1
    change qEq (qadd (qmul z.re (qmul z.re (qinv' (normSq z))))
                     (qneg (qmul z.im (qneg (qmul z.im (qinv' (normSq z))))))) qone
    refine qEq_trans ?_ hN
    change qEq _ (qmul (qadd (qmul z.re z.re) (qmul z.im z.im)) (qinv' (normSq z)))
    rat_ring
  · -- im: a·(−(b·I)) + b·(a·I) ≈ −(ab·I) + ab·I ≈ 0
    change qEq (qadd (qmul z.re (qneg (qmul z.im (qinv' (normSq z)))))
                     (qmul z.im (qmul z.re (qinv' (normSq z))))) qzero
    refine qEq_trans (y := qadd (qmul (qmul z.re z.im) (qinv' (normSq z)))
      (qneg (qmul (qmul z.re z.im) (qinv' (normSq z))))) ?_ (qadd_neg _)
    rat_ring

-- ============================================================
-- §2. The bridge: the quotient `GaussQ`
-- ============================================================

instance GaussE.setoid : Setoid GaussE :=
  ⟨gEq, ⟨gEq_refl, fun h => gEq_symm h, fun h1 h2 => gEq_trans h1 h2⟩⟩
instance GaussE.decidableEquiv (a b : GaussE) : Decidable (a ≈ b) := gEq.decidable a b

/-- The Gaussian rationals: `GaussE` up to `gEq`. -/
def GaussQ : Type := Quotient GaussE.setoid

namespace GaussQ

instance : Zero GaussQ := ⟨Quotient.mk GaussE.setoid gzero⟩
instance : One GaussQ := ⟨Quotient.mk GaussE.setoid gone⟩
def add : GaussQ → GaussQ → GaussQ :=
  Quotient.lift₂ (fun x y => (⟦gadd x y⟧ : GaussQ))
    (fun _ _ _ _ hx hy => Quotient.sound (gadd_respects hx hy))
def neg : GaussQ → GaussQ :=
  Quotient.lift (fun x => (⟦gneg x⟧ : GaussQ)) (fun _ _ h => Quotient.sound (gneg_respects h))
def mul : GaussQ → GaussQ → GaussQ :=
  Quotient.lift₂ (fun x y => (⟦gmul x y⟧ : GaussQ))
    (fun _ _ _ _ hx hy => Quotient.sound (gmul_respects hx hy))
def inv : GaussQ → GaussQ :=
  Quotient.lift (fun x => (⟦ginv x⟧ : GaussQ)) (fun _ _ h => Quotient.sound (ginv_respects h))
instance : Add GaussQ := ⟨add⟩
instance : Neg GaussQ := ⟨neg⟩
instance : Mul GaussQ := ⟨mul⟩
instance : Inv GaussQ := ⟨inv⟩

/-- **The Gaussian rationals form a commutative ring** — lifted from the witnessed layer. -/
instance instCommRing : CommRing GaussQ where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (gadd_assoc x y z))
  zero_add a := Quotient.inductionOn a (fun x => Quotient.sound (gzero_add x))
  add_zero a := Quotient.inductionOn a (fun x => Quotient.sound (gadd_zero x))
  neg_add_cancel a := Quotient.inductionOn a
    (fun x => Quotient.sound (gEq_trans (gadd_comm _ _) (gadd_neg x)))
  add_comm a b := Quotient.inductionOn₂ a b (fun x y => Quotient.sound (gadd_comm x y))
  mul_assoc a b c := Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (gmul_assoc x y z))
  one_mul a := Quotient.inductionOn a (fun x => Quotient.sound (gone_mul x))
  mul_one a := Quotient.inductionOn a (fun x => Quotient.sound (gmul_one x))
  left_distrib a b c := Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (gmul_add x y z))
  right_distrib a b c := Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (gadd_mul x y z))
  zero_mul a := Quotient.inductionOn a (fun x => Quotient.sound (gzero_mul x))
  mul_zero a := Quotient.inductionOn a (fun x => Quotient.sound (gmul_zero x))
  mul_comm a b := Quotient.inductionOn₂ a b (fun x y => Quotient.sound (gmul_comm x y))
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance : DecidableEq GaussQ := inferInstanceAs (DecidableEq (Quotient GaussE.setoid))

/-- **ℂ_op is a field in content**: total inverse, `z · z⁻¹ = 1` for `z ≠ 0`. -/
theorem mul_inv_cancel {z : GaussQ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  revert h
  refine Quotient.inductionOn z (fun x h => ?_)
  exact Quotient.sound (gmul_inv_cancel (fun e => h (Quotient.sound e)))

end GaussQ

end VRCycle.Continuum

#print axioms VRCycle.Continuum.gmul_inv_cancel
#print axioms VRCycle.Continuum.GaussE.csr
#print axioms VRCycle.Continuum.GaussQ.instCommRing
#print axioms VRCycle.Continuum.GaussQ.mul_inv_cancel
