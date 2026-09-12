-- VRCycle/Numbers/RationalsOp.lean
-- The operational rationals with WITNESSED identity, on the empty axiom list.
--
-- Integrity programme, step 1 (2026-09-12).  `Numbers/Rationals.lean` builds ℚ_VR as a quotient of
-- pairs of the quotient ℤ_VR and proves its laws through the isomorphism with Mathlib's ℚ;
-- `Continuum/Rational.lean` builds a second ℚ (`Qop`) over Mathlib's ℤ.  Here the rationals are
-- built where VR performs them: a pair of integer pairs (`IntExpr`) with a non-zero denominator,
-- up to the witnessed identity `qEq` (cross-multiplication, an `intEq` — itself an equation of VR
-- numbers).  Every law is decided by `int_ring` (reflection over the ring laws of `IntExpr` up to
-- `intEq`, `Meta/CSRNorm.lean`) plus `imul_cancel_right` for transitivity.  `#print axioms`
-- returns `[]` for every theorem of this file.  No quotient, no Mathlib ℤ or ℚ, no `ring`.
import VRCycle.Numbers.IntegersOp

namespace VR.Numbers

open VR

-- No auto-generated `injEq` lemmas (they carry `propext`).
set_option genInjectivity false

-- ============================================================
-- §1. Pre-rationals and their identity
-- ============================================================

/-- A pre-rational: numerator and denominator as integer pairs, denominator not `≈ 0`. -/
structure QExpr where
  num : IntExpr
  den : IntExpr
  den_nz : ¬ intEq den zeroI

/-- Witnessed identity of pre-rationals: `a/b ≈ c/d ⟺ a·d ≈ c·b` (an `intEq`). -/
def qEq (x y : QExpr) : Prop := intEq (imul x.num y.den) (imul y.num x.den)

theorem qEq_refl (x : QExpr) : qEq x x := intEq_refl _
theorem qEq_symm {x y : QExpr} (h : qEq x y) : qEq y x := intEq_symm _ _ h

instance : Trans intEq intEq intEq := ⟨fun h1 h2 => intEq_trans _ _ _ h1 h2⟩

theorem imul_congr_left {e e' f : IntExpr} (h : e ≈ᵢ e') : imul e f ≈ᵢ imul e' f :=
  imul_respects _ _ _ _ h (intEq_refl f)
theorem imul_congr_right {e f f' : IntExpr} (h : f ≈ᵢ f') : imul e f ≈ᵢ imul e f' :=
  imul_respects _ _ _ _ (intEq_refl e) h
theorem iadd_congr {e e' f f' : IntExpr} (h1 : e ≈ᵢ e') (h2 : f ≈ᵢ f') :
    iadd e f ≈ᵢ iadd e' f' :=
  iadd_respects _ _ _ _ h1 h2

theorem qEq_trans {x y z : QExpr} (hxy : qEq x y) (hyz : qEq y z) : qEq x z := by
  apply imul_cancel_right y.den_nz
  calc imul (imul x.num z.den) y.den
      ≈ᵢ imul (imul x.num y.den) z.den := by int_ring
    _ ≈ᵢ imul (imul y.num x.den) z.den := imul_congr_left hxy
    _ ≈ᵢ imul (imul y.num z.den) x.den := by int_ring
    _ ≈ᵢ imul (imul z.num y.den) x.den := imul_congr_left hyz
    _ ≈ᵢ imul (imul z.num x.den) y.den := by int_ring

theorem qEq_congr_left {x x' y : QExpr} (h : qEq x x') : qEq x y ↔ qEq x' y :=
  ⟨qEq_trans (qEq_symm h), qEq_trans h⟩
theorem qEq_congr_right {x y y' : QExpr} (h : qEq y y') : qEq x y ↔ qEq x y' :=
  ⟨fun h' => qEq_trans h' h, fun h' => qEq_trans h' (qEq_symm h)⟩

-- ============================================================
-- §2. Operations
-- ============================================================

def qzero : QExpr := ⟨zeroI, oneI, one_ne_zero_I⟩
def qone : QExpr := ⟨oneI, oneI, one_ne_zero_I⟩

/-- `a/b + c/d = (a·d + c·b) / (b·d)`. -/
def qadd (x y : QExpr) : QExpr :=
  ⟨iadd (imul x.num y.den) (imul y.num x.den), imul x.den y.den, imul_ne_zero x.den_nz y.den_nz⟩
/-- `-(a/b) = (-a)/b`. -/
def qneg (x : QExpr) : QExpr := ⟨ineg x.num, x.den, x.den_nz⟩
/-- `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul (x y : QExpr) : QExpr :=
  ⟨imul x.num y.num, imul x.den y.den, imul_ne_zero x.den_nz y.den_nz⟩
/-- `(a/b)⁻¹ = b/a`, given a witness that `a ≉ 0`. -/
def qinv (x : QExpr) (h : ¬ intEq x.num zeroI) : QExpr := ⟨x.den, x.num, h⟩
/-- Embedding of integer pairs: `e ↦ e/1`. -/
def qofInt (e : IntExpr) : QExpr := ⟨e, oneI, one_ne_zero_I⟩

/-- `q_ring`: a `qEq` identity, unfolded to an `intEq` and decided by `int_ring`. -/
syntax "q_ring" : tactic
macro_rules
  | `(tactic| q_ring) =>
    `(tactic| (dsimp only [qEq, qadd, qneg, qmul, qinv, qzero, qone, qofInt]; int_ring))

-- ============================================================
-- §3. The operations respect the identity
-- ============================================================

theorem qadd_respects {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') :
    qEq (qadd x y) (qadd x' y') := by
  change imul (iadd (imul x.num y.den) (imul y.num x.den)) (imul x'.den y'.den)
      ≈ᵢ imul (iadd (imul x'.num y'.den) (imul y'.num x'.den)) (imul x.den y.den)
  calc imul (iadd (imul x.num y.den) (imul y.num x.den)) (imul x'.den y'.den)
      ≈ᵢ iadd (imul (imul x.num x'.den) (imul y.den y'.den))
              (imul (imul y.num y'.den) (imul x.den x'.den)) := by int_ring
    _ ≈ᵢ iadd (imul (imul x'.num x.den) (imul y.den y'.den))
              (imul (imul y'.num y.den) (imul x.den x'.den)) :=
        iadd_congr (imul_congr_left hx) (imul_congr_left hy)
    _ ≈ᵢ imul (iadd (imul x'.num y'.den) (imul y'.num x'.den)) (imul x.den y.den) := by int_ring

theorem qneg_respects {x x' : QExpr} (hx : qEq x x') : qEq (qneg x) (qneg x') := by
  change imul (ineg x.num) x'.den ≈ᵢ imul (ineg x'.num) x.den
  calc imul (ineg x.num) x'.den
      ≈ᵢ ineg (imul x.num x'.den) := by int_ring
    _ ≈ᵢ ineg (imul x'.num x.den) := ineg_respects _ _ hx
    _ ≈ᵢ imul (ineg x'.num) x.den := by int_ring

theorem qmul_respects {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') :
    qEq (qmul x y) (qmul x' y') := by
  change imul (imul x.num y.num) (imul x'.den y'.den)
      ≈ᵢ imul (imul x'.num y'.num) (imul x.den y.den)
  calc imul (imul x.num y.num) (imul x'.den y'.den)
      ≈ᵢ imul (imul x.num x'.den) (imul y.num y'.den) := by int_ring
    _ ≈ᵢ imul (imul x'.num x.den) (imul y'.num y.den) := imul_respects _ _ _ _ hx hy
    _ ≈ᵢ imul (imul x'.num y'.num) (imul x.den y.den) := by int_ring

/-- A non-zero numerator is a property of the class. -/
theorem num_nz_respects {x x' : QExpr} (hx : qEq x x') (h : ¬ intEq x.num zeroI) :
    ¬ intEq x'.num zeroI := by
  intro h0
  apply h
  have h1 : imul x.num x'.den ≈ᵢ zeroI :=
    intEq_trans _ _ _ hx (intEq_trans _ _ _ (imul_congr_left h0) (zero_imul _))
  rcases imul_eq_zero h1 with ha | hd
  · exact ha
  · exact absurd hd x'.den_nz

theorem qinv_respects {x x' : QExpr} (hx : qEq x x') (h : ¬ intEq x.num zeroI) :
    qEq (qinv x h) (qinv x' (num_nz_respects hx h)) := by
  change imul x.den x'.num ≈ᵢ imul x'.den x.num
  calc imul x.den x'.num
      ≈ᵢ imul x'.num x.den := by int_ring
    _ ≈ᵢ imul x.num x'.den := intEq_symm _ _ hx
    _ ≈ᵢ imul x'.den x.num := by int_ring

-- ============================================================
-- §4. Field laws, up to `qEq`
-- ============================================================

theorem qadd_comm (x y : QExpr) : qEq (qadd x y) (qadd y x) := by q_ring
theorem qadd_assoc (x y z : QExpr) : qEq (qadd (qadd x y) z) (qadd x (qadd y z)) := by q_ring
theorem qadd_zero (x : QExpr) : qEq (qadd x qzero) x := by q_ring
theorem qzero_add (x : QExpr) : qEq (qadd qzero x) x := by q_ring
theorem qmul_comm (x y : QExpr) : qEq (qmul x y) (qmul y x) := by q_ring
theorem qmul_assoc (x y z : QExpr) : qEq (qmul (qmul x y) z) (qmul x (qmul y z)) := by q_ring
theorem qmul_one (x : QExpr) : qEq (qmul x qone) x := by q_ring
theorem qone_mul (x : QExpr) : qEq (qmul qone x) x := by q_ring
theorem qmul_add (x y z : QExpr) : qEq (qmul x (qadd y z)) (qadd (qmul x y) (qmul x z)) := by
  q_ring
theorem qadd_mul (x y z : QExpr) : qEq (qmul (qadd x y) z) (qadd (qmul x z) (qmul y z)) := by
  q_ring
theorem qzero_mul (x : QExpr) : qEq (qmul qzero x) qzero := by q_ring
theorem qmul_zero (x : QExpr) : qEq (qmul x qzero) qzero := by q_ring
theorem qmul_inv_cancel (x : QExpr) (h : ¬ intEq x.num zeroI) :
    qEq (qmul x (qinv x h)) qone := by q_ring

/-- `x + (−x) ≈ 0` — the one law that needs cancellation (`iadd_ineg`), not just normalisation. -/
theorem qadd_neg (x : QExpr) : qEq (qadd x (qneg x)) qzero := by
  change imul (iadd (imul x.num x.den) (imul (ineg x.num) x.den)) oneI
      ≈ᵢ imul zeroI (imul x.den x.den)
  calc imul (iadd (imul x.num x.den) (imul (ineg x.num) x.den)) oneI
      ≈ᵢ iadd (imul x.num x.den) (ineg (imul x.num x.den)) := by int_ring
    _ ≈ᵢ zeroI := iadd_ineg _
    _ ≈ᵢ imul zeroI (imul x.den x.den) := intEq_symm _ _ (zero_imul _)

theorem qzero_ne_one : ¬ qEq qzero qone := by
  intro h
  change imul zeroI oneI ≈ᵢ imul oneI oneI at h
  exact one_ne_zero_I (intEq_trans _ _ _ (intEq_symm _ _ (imul_one oneI))
    (intEq_trans _ _ _ (intEq_symm _ _ h) (zero_imul oneI)))

/-- The embedding of integer pairs is a ring homomorphism up to the identities. -/
theorem qofInt_add (e f : IntExpr) : qEq (qofInt (iadd e f)) (qadd (qofInt e) (qofInt f)) := by
  q_ring
theorem qofInt_mul (e f : IntExpr) : qEq (qofInt (imul e f)) (qmul (qofInt e) (qofInt f)) := by
  q_ring
theorem qofInt_respects {e f : IntExpr} (h : e ≈ᵢ f) : qEq (qofInt e) (qofInt f) := by
  change imul e oneI ≈ᵢ imul f oneI
  exact imul_congr_left h

/-- Pre-rationals as a commutative ring up to `qEq`, for `csr_ring` at the next floor. -/
def QExpr.csr : VR.CSR.CSR QExpr where
  r := qEq
  refl := qEq_refl
  symm := qEq_symm
  trans := qEq_trans
  add := qadd
  mul := qmul
  neg := qneg
  zero := qzero
  one := qone
  add_congr := qadd_respects
  mul_congr := qmul_respects
  neg_congr := qneg_respects
  add_comm := qadd_comm
  add_assoc := qadd_assoc
  zero_add := qzero_add
  mul_comm := qmul_comm
  mul_assoc := qmul_assoc
  one_mul := qone_mul
  zero_mul := qzero_mul
  mul_add := qmul_add
  neg_add := fun x y => by q_ring
  neg_mul := fun x y => by q_ring
  neg_neg := fun x => by q_ring
  neg_zero := by q_ring

/-- `rat_ring`: ring identities between pre-rationals up to `qEq`, pre-rationals as atoms. -/
syntax "rat_ring" : tactic
macro_rules
  | `(tactic| rat_ring) => `(tactic| csr_ring VR.Numbers.QExpr.csr)

-- ============================================================
-- §5. The audit
-- ============================================================

#print axioms qEq_trans
#print axioms qadd_respects
#print axioms qmul_respects
#print axioms qinv_respects
#print axioms qadd_assoc
#print axioms qmul_assoc
#print axioms qmul_add
#print axioms qadd_neg
#print axioms qmul_inv_cancel
#print axioms qzero_ne_one
#print axioms qofInt_mul
#print axioms QExpr.csr

end VR.Numbers
