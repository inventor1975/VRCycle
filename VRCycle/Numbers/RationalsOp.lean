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
import VRCycle.Numbers.IntegersOrd

namespace VR.Numbers

open VR

-- No auto-generated `injEq` lemmas (they carry `propext`).
set_option genInjectivity false

-- ============================================================
-- §1. Pre-rationals and their identity
-- ============================================================

/-- A pre-rational: numerator and denominator as integer pairs, denominator positive. -/
structure QExpr where
  num : IntExpr
  den : IntExpr
  den_pos : intPos den

theorem QExpr.den_nz (x : QExpr) : ¬ intEq x.den zeroI := ne_zero_of_intPos x.den_pos

/-- Witnessed identity of pre-rationals: `a/b ≈ c/d ⟺ a·d ≈ c·b` (an `intEq`). -/
def qEq (x y : QExpr) : Prop := intEq (imul x.num y.den) (imul y.num x.den)

theorem qEq_refl (x : QExpr) : qEq x x := intEq_refl _
theorem qEq_symm {x y : QExpr} (h : qEq x y) : qEq y x := intEq_symm _ _ h

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

def qzero : QExpr := ⟨zeroI, oneI, intPos_one⟩
def qone : QExpr := ⟨oneI, oneI, intPos_one⟩

/-- `a/b + c/d = (a·d + c·b) / (b·d)`. -/
def qadd (x y : QExpr) : QExpr :=
  ⟨iadd (imul x.num y.den) (imul y.num x.den), imul x.den y.den, intPos_mul x.den_pos y.den_pos⟩
/-- `-(a/b) = (-a)/b`. -/
def qneg (x : QExpr) : QExpr := ⟨ineg x.num, x.den, x.den_pos⟩
/-- `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def qmul (x y : QExpr) : QExpr :=
  ⟨imul x.num y.num, imul x.den y.den, intPos_mul x.den_pos y.den_pos⟩
/-- Embedding of integer pairs: `e ↦ e/1`. -/
def qofInt (e : IntExpr) : QExpr := ⟨e, oneI, intPos_one⟩

-- Signs of integer pairs, for the inverse and the order.
theorem intPos_neg_of_lt_zero {e : IntExpr} (h : e <ᵢ zeroI) : intPos (ineg e) := by
  have h1 := intLe_add_right (ineg e) h
  change intLe (iadd zeroI oneI) (ineg e)
  refine intLe_respects ?_ ?_ h1
  · calc iadd (iadd e oneI) (ineg e)
        ≈ᵢ iadd oneI (iadd e (ineg e)) := by int_ring
      _ ≈ᵢ iadd oneI zeroI := iadd_congr (intEq_refl _) (iadd_ineg e)
      _ ≈ᵢ iadd zeroI oneI := by int_ring
  · exact zero_iadd _

theorem intPos_neg_of_not_pos {e : IntExpr} (hp : ¬ intPos e) (h0 : ¬ e ≈ᵢ zeroI) :
    intPos (ineg e) := by
  rcases intLt_trichotomy e zeroI with h | h | h
  · exact intPos_neg_of_lt_zero h
  · exact absurd h h0
  · exact absurd h hp

theorem not_intPos_zero : ¬ intPos zeroI := by
  intro h
  obtain ⟨n, hn⟩ := (intPos_iff _).mp h
  exact VRObj.noConfusion ((intEq_zero_iff _ _).mp (intEq_symm _ _ hn))

theorem intPos_of_mul_pos_right {e g : IntExpr} (hg : intPos g) (h : intPos (imul e g)) :
    intPos e := by
  rcases intLt_trichotomy e zeroI with hlt | heq | hgt
  · -- e < 0: then e·g < 0, contradiction with e·g > 0
    exfalso
    have hn : intPos (ineg e) := intPos_neg_of_lt_zero hlt
    have hp : intPos (imul (ineg e) g) := intPos_mul hn hg
    -- (−e)·g ≈ −(e·g); both e·g and −(e·g) positive is impossible
    have hp' : intPos (ineg (imul e g)) := intPos_respects (by int_ring) hp
    have hsum : intPos (iadd (imul e g) (ineg (imul e g))) := intPos_add h hp'
    exact not_intPos_zero (intPos_respects (iadd_ineg _) hsum)
  · exfalso
    have : imul e g ≈ᵢ zeroI := intEq_trans _ _ _ (imul_congr_left heq) (zero_imul g)
    exact not_intPos_zero (intPos_respects this h)
  · exact hgt

/-- `(a/b)⁻¹`: `b/a` if `a > 0`, `(−b)/(−a)` if `a < 0` — the denominator stays positive. -/
def qinv (x : QExpr) (h : ¬ intEq x.num zeroI) : QExpr :=
  if hp : intPos x.num then ⟨x.den, x.num, hp⟩
  else ⟨ineg x.den, ineg x.num, intPos_neg_of_not_pos hp h⟩

/-- `q_ring`: a `qEq` identity, unfolded to an `intEq` and decided by `int_ring`. -/
syntax "q_ring" : tactic
macro_rules
  | `(tactic| q_ring) =>
    `(tactic| (dsimp only [qEq, qadd, qneg, qmul, qzero, qone, qofInt]; int_ring))

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

/-- The sign of the numerator is a property of the class (denominators are positive). -/
theorem num_pos_respects {x x' : QExpr} (hx : qEq x x') (h : intPos x.num) : intPos x'.num := by
  have h1 : intPos (imul x.num x'.den) := intPos_mul h x'.den_pos
  have h2 : intPos (imul x'.num x.den) := intPos_respects hx h1
  exact intPos_of_mul_pos_right x.den_pos h2

theorem qinv_respects {x x' : QExpr} (hx : qEq x x') (h : ¬ intEq x.num zeroI) :
    qEq (qinv x h) (qinv x' (num_nz_respects hx h)) := by
  unfold qinv
  by_cases hp : intPos x.num
  · have hp' : intPos x'.num := num_pos_respects hx hp
    rw [dif_pos hp, dif_pos hp']
    change imul x.den x'.num ≈ᵢ imul x'.den x.num
    calc imul x.den x'.num
        ≈ᵢ imul x'.num x.den := by int_ring
      _ ≈ᵢ imul x.num x'.den := intEq_symm _ _ hx
      _ ≈ᵢ imul x'.den x.num := by int_ring
  · have hp' : ¬ intPos x'.num := fun h' => hp (num_pos_respects (qEq_symm hx) h')
    rw [dif_neg hp, dif_neg hp']
    change imul (ineg x.den) (ineg x'.num) ≈ᵢ imul (ineg x'.den) (ineg x.num)
    calc imul (ineg x.den) (ineg x'.num)
        ≈ᵢ imul x'.num x.den := by int_ring
      _ ≈ᵢ imul x.num x'.den := intEq_symm _ _ hx
      _ ≈ᵢ imul (ineg x'.den) (ineg x.num) := by int_ring

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
    qEq (qmul x (qinv x h)) qone := by
  unfold qinv
  by_cases hp : intPos x.num
  · rw [dif_pos hp]; q_ring
  · rw [dif_neg hp]; q_ring

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

-- ============================================================
-- §4b. The order
-- ============================================================

/-- `a/b ≤ c/d ⟺ a·d ≤ c·b` (denominators positive). -/
def qle (x y : QExpr) : Prop := intLe (imul x.num y.den) (imul y.num x.den)
def qlt (x y : QExpr) : Prop := intLt (imul x.num y.den) (imul y.num x.den)

instance qle.decidable (x y : QExpr) : Decidable (qle x y) := intLe.decidable _ _
instance qlt.decidable (x y : QExpr) : Decidable (qlt x y) := intLt.decidable _ _

theorem qle_refl (x : QExpr) : qle x x := intLe_refl _
theorem qle_antisymm {x y : QExpr} (h1 : qle x y) (h2 : qle y x) : qEq x y :=
  intLe_antisymm h1 h2
theorem qle_total (x y : QExpr) : qle x y ∨ qle y x := intLe_total _ _
theorem qle_of_qEq {x y : QExpr} (h : qEq x y) : qle x y := intLe_of_intEq h

theorem qle_trans {x y z : QExpr} (h1 : qle x y) (h2 : qle y z) : qle x z := by
  -- (a·d ≤ c·b)·f  and  (c·f ≤ e·d)·b, then cancel d
  have h1' : imul (imul x.num z.den) y.den ≤ᵢ imul (imul y.num z.den) x.den :=
    intLe_respects (by int_ring) (by int_ring) (intLe_mul_right z.den_pos h1)
  have h2' : imul (imul y.num z.den) x.den ≤ᵢ imul (imul z.num x.den) y.den :=
    intLe_respects (by int_ring) (by int_ring) (intLe_mul_right x.den_pos h2)
  change imul x.num z.den ≤ᵢ imul z.num x.den
  exact intLe_of_mul_le_mul_right y.den_pos (intLe_trans h1' h2')

theorem qle_respects {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') (h : qle x y) :
    qle x' y' := by
  have h1 := intLe_mul_right (intPos_mul x'.den_pos y'.den_pos) h
  -- a·d·(b'·d') ≈ (a·b')·(d·d') ≈ (a'·b)·(d·d') ; c·b·(b'·d') ≈ (c·d')·(b·b') ≈ (c'·d)·(b·b')
  have h2 : imul (imul x'.num y'.den) (imul x.den y.den)
      ≤ᵢ imul (imul y'.num x'.den) (imul x.den y.den) := by
    refine intLe_respects ?_ ?_ h1
    · calc imul (imul x.num y.den) (imul x'.den y'.den)
          ≈ᵢ imul (imul x.num x'.den) (imul y.den y'.den) := by int_ring
        _ ≈ᵢ imul (imul x'.num x.den) (imul y.den y'.den) := imul_congr_left hx
        _ ≈ᵢ imul (imul x'.num y'.den) (imul x.den y.den) := by int_ring
    · calc imul (imul y.num x.den) (imul x'.den y'.den)
          ≈ᵢ imul (imul y.num y'.den) (imul x.den x'.den) := by int_ring
        _ ≈ᵢ imul (imul y'.num y.den) (imul x.den x'.den) := imul_congr_left hy
        _ ≈ᵢ imul (imul y'.num x'.den) (imul x.den y.den) := by int_ring
  exact intLe_of_mul_le_mul_right (intPos_mul x.den_pos y.den_pos) h2

theorem qlt_iff_le_not_le {x y : QExpr} : qlt x y ↔ (qle x y ∧ ¬ qle y x) :=
  intLt_iff_le_not_le

theorem qlt_respects {x x' y y' : QExpr} (hx : qEq x x') (hy : qEq y y') (h : qlt x y) :
    qlt x' y' := by
  obtain ⟨h1, h2⟩ := qlt_iff_le_not_le.mp h
  exact qlt_iff_le_not_le.mpr ⟨qle_respects hx hy h1,
    fun h3 => h2 (qle_respects (qEq_symm hy) (qEq_symm hx) h3)⟩

theorem qlt_trichotomy (x y : QExpr) : qlt x y ∨ qEq x y ∨ qlt y x := by
  by_cases h1 : qle x y
  · by_cases h2 : qle y x
    · exact Or.inr (Or.inl (qle_antisymm h1 h2))
    · exact Or.inl (qlt_iff_le_not_le.mpr ⟨h1, h2⟩)
  · rcases qle_total x y with h | h
    · exact absurd h h1
    · exact Or.inr (Or.inr (qlt_iff_le_not_le.mpr ⟨h, h1⟩))

theorem qlt_irrefl (x : QExpr) : ¬ qlt x x :=
  fun h => (qlt_iff_le_not_le.mp h).2 (qle_refl x)

theorem qle_add_right {x y : QExpr} (z : QExpr) (h : qle x y) : qle (qadd x z) (qadd y z) := by
  -- (a·d ≤ c·b)·(f·f), then add e·b·d·f to both sides
  have h1 := intLe_mul_right (intPos_mul z.den_pos z.den_pos) h
  have h2 := intLe_add_right (imul (imul z.num x.den) (imul y.den z.den)) h1
  change imul (iadd (imul x.num z.den) (imul z.num x.den)) (imul y.den z.den)
      ≤ᵢ imul (iadd (imul y.num z.den) (imul z.num y.den)) (imul x.den z.den)
  exact intLe_respects (by int_ring) (by int_ring) h2

theorem qpos_iff (x : QExpr) : qlt qzero x ↔ intPos x.num := by
  change intLe (iadd (imul zeroI x.den) oneI) (imul x.num oneI) ↔ intLe (iadd zeroI oneI) x.num
  constructor
  · intro h
    exact intLe_respects (by int_ring) (imul_one _) h
  · intro h
    exact intLe_respects (by int_ring) (intEq_symm _ _ (imul_one _)) h

theorem qmul_pos {x y : QExpr} (hx : qlt qzero x) (hy : qlt qzero y) : qlt qzero (qmul x y) :=
  (qpos_iff _).mpr (intPos_mul ((qpos_iff x).mp hx) ((qpos_iff y).mp hy))

theorem qadd_pos {x y : QExpr} (hx : qlt qzero x) (hy : qlt qzero y) : qlt qzero (qadd x y) :=
  (qpos_iff _).mpr (intPos_add (intPos_mul ((qpos_iff x).mp hx) y.den_pos)
    (intPos_mul ((qpos_iff y).mp hy) x.den_pos))

instance qEq.decidable (x y : QExpr) : Decidable (qEq x y) := intEq.decidable _ _

theorem qEq_zero_iff (x : QExpr) : qEq x qzero ↔ x.num ≈ᵢ zeroI := by
  change imul x.num oneI ≈ᵢ imul zeroI x.den ↔ x.num ≈ᵢ zeroI
  constructor
  · intro h
    exact intEq_trans _ _ _ (intEq_symm _ _ (imul_one _)) (intEq_trans _ _ _ h (zero_imul _))
  · intro h
    exact intEq_trans _ _ _ (imul_one _) (intEq_trans _ _ _ h (intEq_symm _ _ (zero_imul _)))

/-- Total inverse: `0⁻¹ = 0`, otherwise `qinv`. -/
def qinv' (x : QExpr) : QExpr :=
  if h : x.num ≈ᵢ zeroI then qzero else qinv x h

theorem qinv'_respects {x x' : QExpr} (hx : qEq x x') : qEq (qinv' x) (qinv' x') := by
  unfold qinv'
  by_cases h : x.num ≈ᵢ zeroI
  · have h' : x'.num ≈ᵢ zeroI := by
      by_contra h''
      exact num_nz_respects (qEq_symm hx) h'' h
    rw [dif_pos h, dif_pos h']; exact qEq_refl _
  · have h' : ¬ x'.num ≈ᵢ zeroI := num_nz_respects hx h
    rw [dif_neg h, dif_neg h']; exact qinv_respects hx h

theorem qmul_inv'_cancel {x : QExpr} (h : ¬ qEq x qzero) : qEq (qmul x (qinv' x)) qone := by
  have h0 : ¬ x.num ≈ᵢ zeroI := fun e => h ((qEq_zero_iff x).mpr e)
  unfold qinv'
  rw [dif_neg h0]
  exact qmul_inv_cancel x h0

theorem qinv'_zero : qEq (qinv' qzero) qzero := by
  unfold qinv'
  change qEq (if h : zeroI ≈ᵢ zeroI then qzero else qinv qzero h) qzero
  rw [dif_pos (intEq_refl zeroI)]; exact qEq_refl _

theorem qle_of_qlt {x y : QExpr} (h : qlt x y) : qle x y := (qlt_iff_le_not_le.mp h).1

theorem qnonneg_iff (x : QExpr) : qle qzero x ↔ zeroI ≤ᵢ x.num := by
  change intLe (imul zeroI x.den) (imul x.num oneI) ↔ intLe zeroI x.num
  constructor
  · intro h; exact intLe_respects (zero_imul _) (imul_one _) h
  · intro h; exact intLe_respects (intEq_symm _ _ (zero_imul _)) (intEq_symm _ _ (imul_one _)) h

theorem qmul_self_nonneg (x : QExpr) : qle qzero (qmul x x) :=
  (qnonneg_iff _).mpr (intNonneg_mul_self x.num)

theorem qmul_self_pos {x : QExpr} (h : ¬ qEq x qzero) : qlt qzero (qmul x x) :=
  (qpos_iff _).mpr (intPos_mul_self (fun e => h ((qEq_zero_iff x).mpr e)))

theorem qadd_pos_of_pos_of_nonneg {x y : QExpr} (hx : qlt qzero x) (hy : qle qzero y) :
    qlt qzero (qadd x y) :=
  (qpos_iff _).mpr (intPos_add_nonneg (intPos_mul ((qpos_iff x).mp hx) y.den_pos)
    (intNonneg_mul ((qnonneg_iff y).mp hy) (intNonneg_of_pos x.den_pos)))

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

def QExpr.cr : VR.CSR.CR QExpr := { QExpr.csr with add_neg := qadd_neg }

theorem qone_pos : qlt qzero qone := (qpos_iff qone).mpr intPos_one

theorem qnumeral_succ_pos : ∀ c : Nat, qlt qzero (VR.CSR.CR.numeral QExpr.cr (c + 1))
  | 0 => qlt_respects (qEq_refl _) (qEq_symm (qadd_zero qone)) qone_pos
  | c + 1 => qadd_pos qone_pos (qnumeral_succ_pos c)

/-- Pre-rationals as an ordered commutative ring up to `qEq` (dense: `lt` is just `le (a+1) b`
here, the genuine `qlt` is handled by `qlt_iff_le_not_le`). -/
def QExpr.ocr : VR.CSR.OCR QExpr :=
  { QExpr.cr with
    le := qle
    lt := fun a b => qle (qadd a qone) b
    lt_def := fun _ _ => Iff.rfl
    le_respects := fun h1 h2 h => qle_respects h1 h2 h
    le_refl := qle_refl
    le_trans := fun h1 h2 => qle_trans h1 h2
    le_add_right := fun c h => qle_add_right c h
    zero_le_one := qle_of_qlt qone_pos
    le_of_smul := fun c x h => by
      have hN : intPos (VR.CSR.CR.numeral QExpr.cr (c + 1)).num :=
        (qpos_iff _).mp (qnumeral_succ_pos c)
      have h1 : zeroI ≤ᵢ imul (VR.CSR.CR.numeral QExpr.cr (c + 1)).num x.num :=
        (qnonneg_iff _).mp h
      have h2 : imul zeroI (VR.CSR.CR.numeral QExpr.cr (c + 1)).num
          ≤ᵢ imul x.num (VR.CSR.CR.numeral QExpr.cr (c + 1)).num :=
        intLe_respects (intEq_symm _ _ (zero_imul _)) (imul_comm _ _) h1
      exact (qnonneg_iff x).mpr (intLe_of_mul_le_mul_right hN h2) }

/-- `rat_linarith`: linear consequences of `qle` hypotheses between pre-rationals (a strict
hypothesis `qlt a b` is fed as `qle a b` by hand: `qle_of_qlt`), on `[]`. -/
syntax "rat_linarith" (" [" term,* "]")? : tactic
macro_rules
  | `(tactic| rat_linarith) => `(tactic| cr_linarith VR.Numbers.QExpr.ocr)
  | `(tactic| rat_linarith [$ts,*]) => `(tactic| cr_linarith VR.Numbers.QExpr.ocr [$ts,*])

/-- `rat_ring`: ring identities between pre-rationals up to `qEq`, pre-rationals as atoms, with
cancellation. -/
syntax "rat_ring" : tactic
macro_rules
  | `(tactic| rat_ring) => `(tactic| cr_ring VR.Numbers.QExpr.cr)

-- ============================================================
-- §5. The audit
-- ============================================================

#print axioms qEq_trans
#print axioms qadd_respects
#print axioms qmul_respects
#print axioms qinv_respects
#print axioms qmul_inv'_cancel
#print axioms qmul_self_pos
#print axioms qadd_pos_of_pos_of_nonneg
#print axioms qadd_assoc
#print axioms qmul_assoc
#print axioms qmul_add
#print axioms qadd_neg
#print axioms qmul_inv_cancel
#print axioms qzero_ne_one
#print axioms qofInt_mul
#print axioms QExpr.csr
#print axioms qle_trans
#print axioms qle_respects
#print axioms qlt_trichotomy
#print axioms qle_add_right
#print axioms qinv_respects

end VR.Numbers
