-- VRCycle/Numbers/RealsOp.lean
-- The operational reals with WITNESSED identity, on the empty axiom list.
--
-- Integrity programme, step 1e (2026-09-12).  A pre-real is a sequence of pre-rationals with an
-- explicit modulus: for every precision `k`, from some `N` on, any two terms are within
-- `ε_k = 1/2^k` of each other (two-sided `qle` bounds — no absolute value, no division at the
-- real level).  Identity `rEq`: the two sequences eventually agree to every precision.  Ring
-- operations are termwise, so every ring law is a termwise `rat_ring` identity; only the Cauchy
-- estimates and the congruences need inequalities, and those are `rat_linarith` certificates over
-- explicit product facts.  Every theorem on `[]`.  The quotient (`Continuum/Real.lean`) is the
-- bridge.
import VR.Numbers.RationalsOp
import VR.Numbers.IntegersOrd

namespace VR.Numbers

open VR

set_option genInjectivity false

instance : Trans qEq qEq qEq := ⟨fun h1 h2 => qEq_trans h1 h2⟩
scoped infix:50 " ≈q " => qEq

-- ============================================================
-- §1. Precisions `ε_k = 1/2^k`, closeness
-- ============================================================

/-- `ε_k = 1 / 2^k`. -/
def qeps (k : Nat) : QExpr := ⟨oneI, pow2 k, pow2_pos k⟩

def qsub (x y : QExpr) : QExpr := qadd x (qneg y)

/-- `|x − y| ≤ e`, as two inequalities. -/
def qclose (x y e : QExpr) : Prop := qle (qsub x y) e ∧ qle (qneg e) (qsub x y)

theorem qeps_pos (k : Nat) : qlt qzero (qeps k) := (qpos_iff _).mpr intPos_one

theorem qeps_nonneg (k : Nat) : qle qzero (qeps k) := qle_of_qlt (qeps_pos k)

/-- `ε_{k+1} + ε_{k+1} ≈ ε_k`. -/
theorem qeps_succ_add (k : Nat) : qEq (qadd (qeps (k + 1)) (qeps (k + 1))) (qeps k) := by
  have h := pow2_succ k
  change imul (iadd (imul oneI (pow2 (k + 1))) (imul oneI (pow2 (k + 1)))) (pow2 k)
      ≈ᵢ imul oneI (imul (pow2 (k + 1)) (pow2 (k + 1)))
  calc imul (iadd (imul oneI (pow2 (k + 1))) (imul oneI (pow2 (k + 1)))) (pow2 k)
      ≈ᵢ imul (iadd (imul oneI (iadd (pow2 k) (pow2 k))) (imul oneI (iadd (pow2 k) (pow2 k)))) (pow2 k) :=
        imul_respects _ _ _ _ (iadd_respects _ _ _ _ (imul_respects _ _ _ _ (intEq_refl _) h)
          (imul_respects _ _ _ _ (intEq_refl _) h)) (intEq_refl _)
    _ ≈ᵢ imul oneI (imul (iadd (pow2 k) (pow2 k)) (iadd (pow2 k) (pow2 k))) := by int_ring
    _ ≈ᵢ imul oneI (imul (pow2 (k + 1)) (pow2 (k + 1))) :=
        imul_respects _ _ _ _ (intEq_refl _) (imul_respects _ _ _ _ (intEq_symm _ _ h) (intEq_symm _ _ h))

theorem qeps_succ_le (k : Nat) : qle (qeps (k + 1)) (qeps k) := by
  have h1 := qeps_succ_add k
  have h2 := qeps_nonneg (k + 1)
  rat_linarith

theorem qeps_le_add : ∀ (k e : Nat), qle (qeps (k + e)) (qeps k)
  | _, 0 => qle_refl _
  | k, e + 1 => qle_trans (qeps_succ_le (k + e)) (qeps_le_add k e)

theorem qeps_zero : qEq (qeps 0) qone := qEq_refl _

/-- `2^B · ε_{k+B} ≈ ε_k`. -/
theorem qpow2_mul_eps (B k : Nat) : qEq (qmul (qofInt (pow2 B)) (qeps (k + B))) (qeps k) := by
  have h := pow2_add k B
  change imul (imul (pow2 B) oneI) (pow2 k) ≈ᵢ imul oneI (imul oneI (pow2 (k + B)))
  calc imul (imul (pow2 B) oneI) (pow2 k)
      ≈ᵢ imul oneI (imul oneI (imul (pow2 k) (pow2 B))) := by int_ring
    _ ≈ᵢ imul oneI (imul oneI (pow2 (k + B))) :=
        imul_respects _ _ _ _ (intEq_refl _) (imul_respects _ _ _ _ (intEq_refl _) (intEq_symm _ _ h))

-- closeness algebra
theorem qclose_refl (x e : QExpr) (he : qle qzero e) : qclose x x e := by
  have h : qEq (qsub x x) qzero := by unfold qsub; exact qadd_neg x
  constructor <;> rat_linarith

theorem qclose_symm {x y e : QExpr} (h : qclose x y e) : qclose y x e := by
  obtain ⟨h1, h2⟩ := h
  have hs : qEq (qsub y x) (qneg (qsub x y)) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem qclose_trans {x y z e₁ e₂ : QExpr} (h1 : qclose x y e₁) (h2 : qclose y z e₂) :
    qclose x z (qadd e₁ e₂) := by
  obtain ⟨h11, h12⟩ := h1
  obtain ⟨h21, h22⟩ := h2
  have hs : qEq (qsub x z) (qadd (qsub x y) (qsub y z)) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem qclose_mono {x y e e' : QExpr} (h : qclose x y e) (he : qle e e') : qclose x y e' := by
  obtain ⟨h1, h2⟩ := h
  constructor <;> rat_linarith

theorem qclose_respects {x x' y y' e e' : QExpr} (hx : qEq x x') (hy : qEq y y') (he : qEq e e')
    (h : qclose x y e) : qclose x' y' e' := by
  obtain ⟨h1, h2⟩ := h
  have hs : qEq (qsub x' y') (qsub x y) := by
    unfold qsub; exact qadd_respects (qEq_symm hx) (qneg_respects (qEq_symm hy))
  constructor <;> rat_linarith

-- ============================================================
-- §2. Pre-reals and their identity
-- ============================================================

/-- A pre-real: a sequence of pre-rationals with an explicit Cauchy modulus. -/
structure RExpr where
  seq : Nat → QExpr
  cauchy : ∀ k : Nat, ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n → qclose (seq m) (seq n) (qeps k)

/-- Witnessed identity: eventually within every `ε_k`. -/
def rEq (x y : RExpr) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → qclose (x.seq n) (y.seq n) (qeps k)

theorem rEq_refl (x : RExpr) : rEq x x :=
  fun k => ⟨0, fun n _ => qclose_refl _ _ (qeps_nonneg k)⟩

theorem rEq_symm {x y : RExpr} (h : rEq x y) : rEq y x := by
  intro k
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => qclose_symm (hN n hn)⟩

theorem rEq_trans {x y z : RExpr} (hxy : rEq x y) (hyz : rEq y z) : rEq x z := by
  intro k
  obtain ⟨N1, h1⟩ := hxy (k + 1)
  obtain ⟨N2, h2⟩ := hyz (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_right N1 N2) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left N2 N1) hn
  exact qclose_mono (qclose_trans (h1 n hn1) (h2 n hn2)) (qle_of_qEq (qeps_succ_add k))

/-- Termwise-identical sequences are identical reals. -/
theorem rEq_of_seq {x y : RExpr} (h : ∀ n, qEq (x.seq n) (y.seq n)) : rEq x y :=
  fun k => ⟨0, fun n _ => qclose_respects (qEq_refl _) (h n) (qEq_refl _)
    (qclose_refl _ _ (qeps_nonneg k))⟩

-- ============================================================
-- §3. Constants, negation, addition
-- ============================================================

/-- A pre-rational as a constant pre-real. -/
def rofQ (q : QExpr) : RExpr :=
  ⟨fun _ => q, fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩⟩

def rzero : RExpr := rofQ qzero
def rone : RExpr := rofQ qone

def rneg (x : RExpr) : RExpr :=
  ⟨fun n => qneg (x.seq n), fun k => by
    obtain ⟨N, hN⟩ := x.cauchy k
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN m n hm hn
    have hs : qEq (qsub (qneg (x.seq m)) (qneg (x.seq n))) (qneg (qsub (x.seq m) (x.seq n))) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith⟩

def radd (x y : RExpr) : RExpr :=
  ⟨fun n => qadd (x.seq n) (y.seq n), fun k => by
    obtain ⟨N1, hX⟩ := x.cauchy (k + 1)
    obtain ⟨N2, hY⟩ := y.cauchy (k + 1)
    refine ⟨N1 + N2, fun m n hm hn => ?_⟩
    have hm1 : N1 ≤ m := Nat.le_trans (Nat.le_add_right N1 N2) hm
    have hm2 : N2 ≤ m := Nat.le_trans (Nat.le_add_left N2 N1) hm
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_right N1 N2) hn
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left N2 N1) hn
    obtain ⟨hx1, hx2⟩ := hX m n hm1 hn1
    obtain ⟨hy1, hy2⟩ := hY m n hm2 hn2
    have he := qeps_succ_add k
    have hs : qEq (qsub (qadd (x.seq m) (y.seq m)) (qadd (x.seq n) (y.seq n)))
        (qadd (qsub (x.seq m) (x.seq n)) (qsub (y.seq m) (y.seq n))) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith⟩

theorem rneg_respects {x x' : RExpr} (h : rEq x x') : rEq (rneg x) (rneg x') := by
  intro k
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  change qclose (qneg (x.seq n)) (qneg (x'.seq n)) (qeps k)
  have hs : qEq (qsub (qneg (x.seq n)) (qneg (x'.seq n))) (qneg (qsub (x.seq n) (x'.seq n))) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem radd_respects {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') :
    rEq (radd x y) (radd x' y') := by
  intro k
  obtain ⟨N1, hX⟩ := hx (k + 1)
  obtain ⟨N2, hY⟩ := hy (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_right N1 N2) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left N2 N1) hn
  obtain ⟨hx1, hx2⟩ := hX n hn1
  obtain ⟨hy1, hy2⟩ := hY n hn2
  have he := qeps_succ_add k
  change qclose (qadd (x.seq n) (y.seq n)) (qadd (x'.seq n) (y'.seq n)) (qeps k)
  have hs : qEq (qsub (qadd (x.seq n) (y.seq n)) (qadd (x'.seq n) (y'.seq n)))
      (qadd (qsub (x.seq n) (x'.seq n)) (qsub (y.seq n) (y'.seq n))) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem radd_comm (x y : RExpr) : rEq (radd x y) (radd y x) :=
  rEq_of_seq (fun _ => qadd_comm _ _)
theorem radd_assoc (x y z : RExpr) : rEq (radd (radd x y) z) (radd x (radd y z)) :=
  rEq_of_seq (fun _ => qadd_assoc _ _ _)
theorem radd_zero (x : RExpr) : rEq (radd x rzero) x := rEq_of_seq (fun _ => qadd_zero _)
theorem rzero_add (x : RExpr) : rEq (radd rzero x) x := rEq_of_seq (fun _ => qzero_add _)
theorem radd_neg (x : RExpr) : rEq (radd x (rneg x)) rzero := rEq_of_seq (fun _ => qadd_neg _)


-- ============================================================
-- §4. Bounds: every pre-rational, every pre-real, is bounded by a power of two
-- ============================================================

theorem vle_O_vpow2 : ∀ k : Nat, vle (O k) (vpow2 k)
  | 0 => vle_zero_left _
  | k + 1 => by
      have ih := vle_O_vpow2 k
      have h1 : vle (VRObj.succ VRObj.base) (vpow2 k) :=
        vle_trans (vlt_of_vle_of_ne (vle_zero_left _) (fun e => by
          have : vlt VRObj.base (vpow2 k) := by
            obtain ⟨n, hn⟩ := (intPos_iff _).mp (pow2_pos k)
            change vadd (vpow2 k) VRObj.base = vadd VRObj.base (VRObj.succ n) at hn
            exact ⟨n, by rw [vadd_zero_left] at hn; rw [vadd_succ_left, vadd_zero_left]; exact hn.symm⟩
          exact vlt_irrefl _ (e ▸ this))) (vle_refl _)
      -- O (k+1) = succ (O k) ≤ vpow2 k + 1 ≤ vpow2 k + vpow2 k
      have h2 : vle (VRObj.succ (O k)) (vadd (vpow2 k) (VRObj.succ VRObj.base)) := by
        have := vle_add_right (VRObj.succ VRObj.base) ih
        exact vle_congr (by vr_ring) rfl this
      have h3 : vle (vadd (vpow2 k) (VRObj.succ VRObj.base)) (vadd (vpow2 k) (vpow2 k)) :=
        vle_congr (T1_vadd_comm _ _) (T1_vadd_comm _ _) (vle_add_right (vpow2 k) h1)
      exact vle_trans h2 h3

/-- Every integer pair lies between `−2^B` and `2^B` for some `B`. -/
theorem intExpr_bound (e : IntExpr) : ∃ B : Nat, e ≤ᵢ pow2 B ∧ ineg (pow2 B) ≤ᵢ e := by
  rcases canonical_form e with ⟨n, hn⟩ | ⟨n, hn⟩
  · refine ⟨O_inv n, ?_, ?_⟩
    · refine intLe_respects (intEq_symm _ _ hn) (intEq_refl _) ?_
      change vle (vadd n VRObj.base) (vadd VRObj.base (vpow2 (O_inv n)))
      have := vle_O_vpow2 (O_inv n)
      rw [O_right_inv] at this
      exact vle_congr rfl (vadd_zero_left _).symm this
    · refine intLe_respects (intEq_refl _) (intEq_symm _ _ hn) ?_
      change vle (vadd VRObj.base VRObj.base) (vadd (vpow2 (O_inv n)) n)
      exact vle_zero_left _
  · refine ⟨O_inv n, ?_, ?_⟩
    · refine intLe_respects (intEq_symm _ _ hn) (intEq_refl _) ?_
      change vle (vadd VRObj.base VRObj.base) (vadd n (vpow2 (O_inv n)))
      exact vle_zero_left _
    · refine intLe_respects (intEq_refl _) (intEq_symm _ _ hn) ?_
      change vle (vadd VRObj.base n) (vadd (vpow2 (O_inv n)) VRObj.base)
      have := vle_O_vpow2 (O_inv n)
      rw [O_right_inv] at this
      exact vle_congr (vadd_zero_left _).symm rfl this

theorem qofInt_le {e f : IntExpr} (h : e ≤ᵢ f) : qle (qofInt e) (qofInt f) := by
  change intLe (imul e oneI) (imul f oneI)
  exact intLe_respects (intEq_symm _ _ (imul_one e)) (intEq_symm _ _ (imul_one f)) h

theorem one_le_den (x : QExpr) : oneI ≤ᵢ x.den := by
  obtain ⟨n, hn⟩ := (intPos_iff _).mp x.den_pos
  refine intLe_respects (intEq_refl _) (intEq_symm _ _ hn) ?_
  change vle (vadd (VRObj.succ VRObj.base) VRObj.base) (vadd VRObj.base (VRObj.succ n))
  exact vle_congr rfl (vadd_zero_left _).symm (vle_succ_succ_iff.mpr (vle_zero_left n))

/-- Every pre-rational lies between `−2^B` and `2^B` for some `B`. -/
theorem qexpr_bound (q : QExpr) : ∃ B : Nat, qclose q qzero (qofInt (pow2 B)) := by
  obtain ⟨B, hu, hl⟩ := intExpr_bound q.num
  refine ⟨B, ?_, ?_⟩
  · -- (num − 0·den)·1 ≤ 2^B·(den·1)
    change intLe (imul (iadd (imul q.num oneI) (imul (ineg zeroI) q.den)) oneI)
                 (imul (pow2 B) (imul q.den oneI))
    have h1 : imul oneI (pow2 B) ≤ᵢ imul q.den (pow2 B) := intLe_mul_right (pow2_pos B) (one_le_den q)
    int_linarith
  · change intLe (imul (ineg (pow2 B)) (imul q.den oneI))
                 (imul (iadd (imul q.num oneI) (imul (ineg zeroI) q.den)) oneI)
    have h1 : imul oneI (pow2 B) ≤ᵢ imul q.den (pow2 B) := intLe_mul_right (pow2_pos B) (one_le_den q)
    int_linarith

/-- Every pre-real is eventually bounded by a power of two. -/
theorem rbounded (x : RExpr) : ∃ B N : Nat, ∀ n, N ≤ n → qclose (x.seq n) qzero (qofInt (pow2 B)) := by
  obtain ⟨N, hN⟩ := x.cauchy 0
  obtain ⟨B0, hb⟩ := qexpr_bound (x.seq N)
  refine ⟨B0 + 1, N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n N hn (Nat.le_refl N)
  obtain ⟨hb1, hb2⟩ := hb
  have hsum : qEq (qofInt (pow2 (B0 + 1))) (qadd (qofInt (pow2 B0)) (qofInt (pow2 B0))) :=
    qEq_trans (qofInt_respects (pow2_succ B0)) (qofInt_add _ _)
  have hone : qle qone (qofInt (pow2 B0)) := qofInt_le (one_le_pow2 B0)
  have he0 : qEq (qeps 0) qone := qeps_zero
  have hs : qEq (qsub (x.seq n) qzero) (qadd (qsub (x.seq n) (x.seq N)) (qsub (x.seq N) qzero)) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

-- ============================================================
-- §5. Multiplication
-- ============================================================

theorem qmul_nonneg {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) : qle qzero (qmul a b) :=
  (qnonneg_iff _).mpr (intNonneg_mul ((qnonneg_iff a).mp ha) ((qnonneg_iff b).mp hb))

/-- `|a| ≤ P`, `|c| ≤ Q` give `|a·c| ≤ P·Q`. -/
theorem qmul_abs_bound {a c P Q : QExpr} (ha : qclose a qzero P) (hc : qclose c qzero Q) :
    qclose (qmul a c) qzero (qmul P Q) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hc1, hc2⟩ := hc
  -- P − a ≥ 0, P + a ≥ 0, Q − c ≥ 0, Q + c ≥ 0
  have hPa : qle qzero (qsub P a) := by unfold qsub at *; rat_linarith
  have hPa' : qle qzero (qadd P a) := by unfold qsub at *; rat_linarith
  have hQc : qle qzero (qsub Q c) := by unfold qsub at *; rat_linarith
  have hQc' : qle qzero (qadd Q c) := by unfold qsub at *; rat_linarith
  have m1 := qmul_nonneg hPa hQc
  have m2 := qmul_nonneg hPa' hQc'
  have m3 := qmul_nonneg hPa hQc'
  have m4 := qmul_nonneg hPa' hQc
  have e1 : qEq (qmul (qsub P a) (qsub Q c)) (qadd (qmul P Q) (qadd (qneg (qmul P c)) (qadd (qneg (qmul a Q)) (qmul a c)))) := by
    unfold qsub; rat_ring
  have e2 : qEq (qmul (qadd P a) (qadd Q c)) (qadd (qmul P Q) (qadd (qmul P c) (qadd (qmul a Q) (qmul a c)))) := by
    rat_ring
  have e3 : qEq (qmul (qsub P a) (qadd Q c)) (qadd (qmul P Q) (qadd (qmul P c) (qadd (qneg (qmul a Q)) (qneg (qmul a c))))) := by
    unfold qsub; rat_ring
  have e4 : qEq (qmul (qadd P a) (qsub Q c)) (qadd (qmul P Q) (qadd (qneg (qmul P c)) (qadd (qmul a Q) (qneg (qmul a c))))) := by
    unfold qsub; rat_ring
  have hs : qEq (qsub (qmul a c) qzero) (qmul a c) := by unfold qsub; rat_ring
  constructor <;> rat_linarith

def rmul (x y : RExpr) : RExpr :=
  ⟨fun n => qmul (x.seq n) (y.seq n), fun k => by
    obtain ⟨Bx, Nx, hbx⟩ := rbounded x
    obtain ⟨By, Ny, hby⟩ := rbounded y
    obtain ⟨N1, hX⟩ := x.cauchy (k + 1 + By)
    obtain ⟨N2, hY⟩ := y.cauchy (k + 1 + Bx)
    refine ⟨Nx + Ny + N1 + N2, fun m n hm hn => ?_⟩
    have hmx : Nx ≤ m := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hm))
    have hny : Ny ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn))
    have hm1 : N1 ≤ m := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) hm)
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) hn)
    have hm2 : N2 ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
    have hxb := hbx m hmx
    have hyb := hby n hny
    have hxc := hX m n hm1 hn1
    have hyc := hY m n hm2 hn2
    -- x_m (y_m − y_n): |x_m| ≤ 2^Bx, |y_m − y_n| ≤ ε_{k+1+Bx} ⟹ ≤ 2^Bx ε_{k+1+Bx} ≈ ε_{k+1}
    have p1 := qmul_abs_bound hxb (show qclose (qsub (y.seq m) (y.seq n)) qzero (qeps (k + 1 + Bx)) from by
      obtain ⟨a1, a2⟩ := hyc
      have hz : qEq (qsub (qsub (y.seq m) (y.seq n)) qzero) (qsub (y.seq m) (y.seq n)) := by
        unfold qsub; rat_ring
      constructor <;> rat_linarith)
    have p2 := qmul_abs_bound hyb (show qclose (qsub (x.seq m) (x.seq n)) qzero (qeps (k + 1 + By)) from by
      obtain ⟨a1, a2⟩ := hxc
      have hz : qEq (qsub (qsub (x.seq m) (x.seq n)) qzero) (qsub (x.seq m) (x.seq n)) := by
        unfold qsub; rat_ring
      constructor <;> rat_linarith)
    have q1 := qpow2_mul_eps Bx (k + 1)
    have q2 := qpow2_mul_eps By (k + 1)
    have he := qeps_succ_add k
    obtain ⟨p11, p12⟩ := p1
    obtain ⟨p21, p22⟩ := p2
    have hs : qEq (qsub (qmul (x.seq m) (y.seq m)) (qmul (x.seq n) (y.seq n)))
        (qadd (qmul (x.seq m) (qsub (y.seq m) (y.seq n))) (qmul (y.seq n) (qsub (x.seq m) (x.seq n)))) := by
      unfold qsub; rat_ring
    have z1 : qEq (qsub (qmul (x.seq m) (qsub (y.seq m) (y.seq n))) qzero)
        (qmul (x.seq m) (qsub (y.seq m) (y.seq n))) := by unfold qsub; rat_ring
    have z2 : qEq (qsub (qmul (y.seq n) (qsub (x.seq m) (x.seq n))) qzero)
        (qmul (y.seq n) (qsub (x.seq m) (x.seq n))) := by unfold qsub; rat_ring
    constructor <;> rat_linarith⟩

theorem rmul_respects {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') :
    rEq (rmul x y) (rmul x' y') := by
  intro k
  obtain ⟨Bx, Nx, hbx⟩ := rbounded x
  obtain ⟨By, Ny, hby⟩ := rbounded y'
  obtain ⟨N1, hX⟩ := hx (k + 1 + By)
  obtain ⟨N2, hY⟩ := hy (k + 1 + Bx)
  refine ⟨Nx + Ny + N1 + N2, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn))
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn))
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) hn)
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have hxb := hbx n hnx
  have hyb := hby n hny
  have hxc := hX n hn1
  have hyc := hY n hn2
  change qclose (qmul (x.seq n) (y.seq n)) (qmul (x'.seq n) (y'.seq n)) (qeps k)
  -- x y − x' y' = x (y − y') + y' (x − x')
  have p1 := qmul_abs_bound hxb (show qclose (qsub (y.seq n) (y'.seq n)) qzero (qeps (k + 1 + Bx)) from by
    obtain ⟨a1, a2⟩ := hyc
    have hz : qEq (qsub (qsub (y.seq n) (y'.seq n)) qzero) (qsub (y.seq n) (y'.seq n)) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith)
  have p2 := qmul_abs_bound hyb (show qclose (qsub (x.seq n) (x'.seq n)) qzero (qeps (k + 1 + By)) from by
    obtain ⟨a1, a2⟩ := hxc
    have hz : qEq (qsub (qsub (x.seq n) (x'.seq n)) qzero) (qsub (x.seq n) (x'.seq n)) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith)
  have q1 := qpow2_mul_eps Bx (k + 1)
  have q2 := qpow2_mul_eps By (k + 1)
  have he := qeps_succ_add k
  obtain ⟨p11, p12⟩ := p1
  obtain ⟨p21, p22⟩ := p2
  have hs : qEq (qsub (qmul (x.seq n) (y.seq n)) (qmul (x'.seq n) (y'.seq n)))
      (qadd (qmul (x.seq n) (qsub (y.seq n) (y'.seq n))) (qmul (y'.seq n) (qsub (x.seq n) (x'.seq n)))) := by
    unfold qsub; rat_ring
  have z1 : qEq (qsub (qmul (x.seq n) (qsub (y.seq n) (y'.seq n))) qzero)
      (qmul (x.seq n) (qsub (y.seq n) (y'.seq n))) := by unfold qsub; rat_ring
  have z2 : qEq (qsub (qmul (y'.seq n) (qsub (x.seq n) (x'.seq n))) qzero)
      (qmul (y'.seq n) (qsub (x.seq n) (x'.seq n))) := by unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem rmul_comm (x y : RExpr) : rEq (rmul x y) (rmul y x) := rEq_of_seq (fun _ => qmul_comm _ _)
theorem rmul_assoc (x y z : RExpr) : rEq (rmul (rmul x y) z) (rmul x (rmul y z)) :=
  rEq_of_seq (fun _ => qmul_assoc _ _ _)
theorem rmul_one (x : RExpr) : rEq (rmul x rone) x := rEq_of_seq (fun _ => qmul_one _)
theorem rone_mul (x : RExpr) : rEq (rmul rone x) x := rEq_of_seq (fun _ => qone_mul _)
theorem rzero_mul (x : RExpr) : rEq (rmul rzero x) rzero := rEq_of_seq (fun _ => qzero_mul _)
theorem rmul_zero (x : RExpr) : rEq (rmul x rzero) rzero := rEq_of_seq (fun _ => qmul_zero _)
theorem rmul_add (x y z : RExpr) : rEq (rmul x (radd y z)) (radd (rmul x y) (rmul x z)) :=
  rEq_of_seq (fun _ => qmul_add _ _ _)
theorem radd_mul (x y z : RExpr) : rEq (rmul (radd x y) z) (radd (rmul x z) (rmul y z)) :=
  rEq_of_seq (fun _ => qadd_mul _ _ _)

/-- `0 ≉ 1`: at precision `1`, `|0 − 1| ≤ 1/2` is refuted. -/
theorem rzero_ne_one : ¬ rEq rzero rone := by
  intro h
  obtain ⟨N, hN⟩ := h 1
  obtain ⟨_, h2⟩ := hN N (Nat.le_refl N)
  change qle (qneg (qeps 1)) (qsub qzero qone) at h2
  have he := qeps_succ_add 0
  have he0 : qEq (qeps 0) qone := qeps_zero
  have hs : qEq (qsub qzero qone) (qneg qone) := by unfold qsub; rat_ring
  have hle : qle qone qzero := by rat_linarith
  exact (qlt_iff_le_not_le.mp qone_pos).2 hle

/-- Pre-reals as a commutative ring up to `rEq`. -/
def RExpr.cr : VR.CSR.CR RExpr where
  r := rEq
  refl := rEq_refl
  symm := rEq_symm
  trans := rEq_trans
  add := radd
  mul := rmul
  neg := rneg
  zero := rzero
  one := rone
  add_congr := radd_respects
  mul_congr := rmul_respects
  neg_congr := rneg_respects
  add_comm := radd_comm
  add_assoc := radd_assoc
  zero_add := rzero_add
  mul_comm := rmul_comm
  mul_assoc := rmul_assoc
  one_mul := rone_mul
  zero_mul := rzero_mul
  mul_add := rmul_add
  neg_add := fun x y => rEq_of_seq (fun n => by
    change qEq (qneg (qadd (x.seq n) (y.seq n))) (qadd (qneg (x.seq n)) (qneg (y.seq n))); rat_ring)
  neg_mul := fun x y => rEq_of_seq (fun n => by
    change qEq (qmul (qneg (x.seq n)) (y.seq n)) (qneg (qmul (x.seq n) (y.seq n))); rat_ring)
  neg_neg := fun x => rEq_of_seq (fun n => by change qEq (qneg (qneg (x.seq n))) (x.seq n); rat_ring)
  neg_zero := rEq_of_seq (fun _ => by change qEq (qneg qzero) qzero; rat_ring)
  add_neg := radd_neg

-- ============================================================
-- §6. Order, apartness, and the reciprocal of a positive real
-- ============================================================

/-- `x ≤ y`: `x_n − y_n ≤ ε_k` eventually, for every `k`. -/
def rle (x y : RExpr) : Prop := ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → qle (qsub (x.seq n) (y.seq n)) (qeps k)
/-- `x < y`: `y_n − x_n ≥ ε_k` eventually, for some `k` — a positive separation with a witness. -/
def rlt (x y : RExpr) : Prop := ∃ k N : Nat, ∀ n : Nat, N ≤ n → qle (qeps k) (qsub (y.seq n) (x.seq n))
/-- Apartness: separated one way or the other. -/
def rapart (x y : RExpr) : Prop := rlt x y ∨ rlt y x

theorem rle_refl (x : RExpr) : rle x x := fun k => ⟨0, fun n _ => by
  have h : qEq (qsub (x.seq n) (x.seq n)) qzero := by unfold qsub; exact qadd_neg _
  have he := qeps_nonneg k
  rat_linarith⟩

theorem rle_trans {x y z : RExpr} (hxy : rle x y) (hyz : rle y z) : rle x z := by
  intro k
  obtain ⟨N1, h1⟩ := hxy (k + 1)
  obtain ⟨N2, h2⟩ := hyz (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have ha := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  have hb := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have he := qeps_succ_add k
  have hs : qEq (qsub (x.seq n) (z.seq n)) (qadd (qsub (x.seq n) (y.seq n)) (qsub (y.seq n) (z.seq n))) := by
    unfold qsub; rat_ring
  rat_linarith

theorem rle_of_rEq {x y : RExpr} (h : rEq x y) : rle x y := fun k => by
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => (hN n hn).1⟩

theorem rle_antisymm {x y : RExpr} (hxy : rle x y) (hyx : rle y x) : rEq x y := by
  intro k
  obtain ⟨N1, h1⟩ := hxy k
  obtain ⟨N2, h2⟩ := hyx k
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have ha := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  have hb := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have hs : qEq (qsub (y.seq n) (x.seq n)) (qneg (qsub (x.seq n) (y.seq n))) := by
    unfold qsub; rat_ring
  constructor <;> rat_linarith

theorem rle_respects {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') (h : rle x y) : rle x' y' :=
  rle_trans (rle_of_rEq (rEq_symm hx)) (rle_trans h (rle_of_rEq hy))

theorem rlt_irrefl (x : RExpr) : ¬ rlt x x := by
  rintro ⟨k, N, h⟩
  have hb := h N (Nat.le_refl N)
  have h0 : qEq (qsub (x.seq N) (x.seq N)) qzero := by unfold qsub; exact qadd_neg _
  have hle : qle qone qzero := by
    -- ε_k ≤ 0 contradicts ε_k > 0: derive 1 ≤ 0 through 2^k·ε_k ≈ 1
    have hm : qEq (qmul (qofInt (pow2 k)) (qeps k)) qone := by
      have := qpow2_mul_eps k 0
      rw [Nat.zero_add] at this
      exact qEq_trans this qeps_zero
    have hp : qle qzero (qofInt (pow2 k)) := qofInt_le (pow2_nonneg k)
    have hprod : qle qzero (qmul (qofInt (pow2 k)) (qneg (qeps k))) :=
      qmul_nonneg hp (by rat_linarith)
    have hneg : qEq (qmul (qofInt (pow2 k)) (qneg (qeps k)))
        (qneg (qmul (qofInt (pow2 k)) (qeps k))) := by
      rat_ring
    rat_linarith
  exact (qlt_iff_le_not_le.mp qone_pos).2 hle

theorem rle_of_rlt {x y : RExpr} (h : rlt x y) : rle x y := by
  obtain ⟨k, N, hN⟩ := h
  intro k'
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  have he := qeps_nonneg k
  have he' := qeps_nonneg k'
  have hs : qEq (qsub (x.seq n) (y.seq n)) (qneg (qsub (y.seq n) (x.seq n))) := by
    unfold qsub; rat_ring
  rat_linarith

theorem rlt_respects {x x' y y' : RExpr} (hx : rEq x x') (hy : rEq y y') (h : rlt x y) : rlt x' y' := by
  obtain ⟨k, N, hN⟩ := h
  obtain ⟨N1, h1⟩ := hx (k + 2)
  obtain ⟨N2, h2⟩ := hy (k + 2)
  refine ⟨k + 1, N + N1 + N2, fun n hn => ?_⟩
  have hn0 : N ≤ n := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hn)
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans (Nat.le_add_right _ _) hn)
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have hb := hN n hn0
  obtain ⟨a1, a2⟩ := h1 n hn1
  obtain ⟨b1, b2⟩ := h2 n hn2
  have he1 := qeps_succ_add k
  have he2 := qeps_succ_add (k + 1)
  have hs : qEq (qsub (y'.seq n) (x'.seq n))
      (qadd (qsub (y.seq n) (x.seq n)) (qadd (qneg (qsub (y.seq n) (y'.seq n))) (qsub (x.seq n) (x'.seq n)))) := by
    unfold qsub; rat_ring
  rat_linarith

theorem rapart_symm {x y : RExpr} (h : rapart x y) : rapart y x := h.symm

theorem rapart_irrefl (x : RExpr) : ¬ rapart x x := fun h => h.elim (rlt_irrefl x) (rlt_irrefl x)

/-- Positivity witness: `ε_k ≤ x_n` for all `n ≥ N`. -/
def PosWitness (x : RExpr) (k N : Nat) : Prop := ∀ n : Nat, N ≤ n → qle (qeps k) (x.seq n)

theorem rlt_zero_iff (x : RExpr) : rlt rzero x ↔ ∃ k N, PosWitness x k N := by
  constructor
  · rintro ⟨k, N, h⟩
    refine ⟨k, N, fun n hn => ?_⟩
    have hb := h n hn
    change qle (qeps k) (qsub (x.seq n) qzero) at hb
    have hs : qEq (qsub (x.seq n) qzero) (x.seq n) := by unfold qsub; rat_ring
    rat_linarith
  · rintro ⟨k, N, h⟩
    refine ⟨k, N, fun n hn => ?_⟩
    have hb := h n hn
    change qle (qeps k) (qsub (x.seq n) qzero)
    have hs : qEq (qsub (x.seq n) qzero) (x.seq n) := by unfold qsub; rat_ring
    rat_linarith

-- inversion of pre-rationals bounded below by ε_k
theorem qmul_le_mul_of_nonneg {a b c : QExpr} (h : qle a b) (hc : qle qzero c) :
    qle (qmul a c) (qmul b c) := by
  have hp : qle qzero (qmul (qsub b a) c) := qmul_nonneg (by unfold qsub; rat_linarith) hc
  have he : qEq (qmul (qsub b a) c) (qadd (qmul b c) (qneg (qmul a c))) := by unfold qsub; rat_ring
  rat_linarith

theorem ne_zero_of_eps_le {x : QExpr} {k : Nat} (h : qle (qeps k) x) : ¬ qEq x qzero := by
  intro h0
  have hle : qle (qeps k) qzero := qle_respects (qEq_refl _) h0 h
  exact (qlt_iff_le_not_le.mp (qeps_pos k)).2 hle

theorem qinv'_nonneg_of_pos {x : QExpr} (h : qlt qzero x) : qle qzero (qinv' x) := by
  have hn : intPos x.num := (qpos_iff x).mp h
  have h0 : ¬ x.num ≈ᵢ zeroI := ne_zero_of_intPos hn
  unfold qinv' qinv
  rw [dif_neg h0, dif_pos hn]
  change intLe (imul zeroI x.num) (imul x.den oneI)
  exact intLe_respects (intEq_symm _ _ (zero_imul _)) (intEq_symm _ _ (imul_one _))
    (intNonneg_of_pos x.den_pos)

/-- `ε_k ≤ x` gives `0 ≤ 1/x ≤ 2^k`. -/
theorem qinv'_bound {x : QExpr} {k : Nat} (h : qle (qeps k) x) :
    qle qzero (qinv' x) ∧ qle (qinv' x) (qofInt (pow2 k)) := by
  have hpos : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans (qeps_nonneg k) h, fun hle =>
    (qlt_iff_le_not_le.mp (qeps_pos k)).2 (qle_trans h hle)⟩
  have hi0 := qinv'_nonneg_of_pos hpos
  have hc := qmul_inv'_cancel (ne_zero_of_eps_le h)
  refine ⟨hi0, ?_⟩
  -- ε_k · inv ≤ x · inv ≈ 1, then multiply by 2^k: (2^k ε_k) inv ≤ 2^k
  have h1 : qle (qmul (qeps k) (qinv' x)) (qmul x (qinv' x)) := qmul_le_mul_of_nonneg h hi0
  have hp : qle qzero (qofInt (pow2 k)) := qofInt_le (pow2_nonneg k)
  have h2 : qle (qmul (qmul (qeps k) (qinv' x)) (qofInt (pow2 k))) (qmul (qmul x (qinv' x)) (qofInt (pow2 k))) :=
    qmul_le_mul_of_nonneg h1 hp
  have hm : qEq (qmul (qofInt (pow2 k)) (qeps k)) qone := by
    have := qpow2_mul_eps k 0
    rw [Nat.zero_add] at this
    exact qEq_trans this qeps_zero
  have hr : qEq (qmul (qmul (qeps k) (qinv' x)) (qofInt (pow2 k)))
      (qmul (qmul (qofInt (pow2 k)) (qeps k)) (qinv' x)) := by rat_ring
  have hr2 : qEq (qmul (qmul x (qinv' x)) (qofInt (pow2 k))) (qmul (qofInt (pow2 k)) (qmul x (qinv' x))) := by
    rat_ring
  have hr3 : qle (qmul (qofInt (pow2 k)) (qmul x (qinv' x))) (qmul (qofInt (pow2 k)) qone) := by
    have := qmul_le_mul_of_nonneg (qle_of_qEq hc) hp
    exact qle_respects (qmul_comm _ _) (qmul_comm _ _) this
  have hr4 : qEq (qmul (qofInt (pow2 k)) qone) (qofInt (pow2 k)) := qmul_one _
  have hr5 : qEq (qmul (qmul (qofInt (pow2 k)) (qeps k)) (qinv' x)) (qmul qone (qinv' x)) :=
    qmul_respects hm (qEq_refl _)
  have hr6 : qEq (qmul qone (qinv' x)) (qinv' x) := qone_mul _
  rat_linarith

/-- **Reciprocal of a positive pre-real**, termwise (`qinv'`), given a positivity witness. -/
def rinvPos (x : RExpr) (k N : Nat) (hw : PosWitness x k N) : RExpr :=
  ⟨fun n => qinv' (x.seq n), fun k' => by
    -- |1/x_m − 1/x_n| = |x_n − x_m| · (1/x_m)(1/x_n) ≤ ε_{k'+2k} · 2^k · 2^k = ε_{k'}
    obtain ⟨Nc, hc⟩ := x.cauchy (k' + (k + k))
    refine ⟨N + Nc, fun m n hm hn => ?_⟩
    have hmN : N ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
    have hnN : N ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
    have hmC : Nc ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
    have hnC : Nc ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
    obtain ⟨im0, im1⟩ := qinv'_bound (hw m hmN)
    obtain ⟨in0, in1⟩ := qinv'_bound (hw n hnN)
    have hcm := qmul_inv'_cancel (ne_zero_of_eps_le (hw m hmN))
    have hcn := qmul_inv'_cancel (ne_zero_of_eps_le (hw n hnN))
    obtain ⟨d1, d2⟩ := hc m n hmC hnC
    -- 1/x_m − 1/x_n ≈ (x_n − x_m)·(1/x_m)·(1/x_n)   (using the two cancellations)
    have hid : qEq (qsub (qinv' (x.seq m)) (qinv' (x.seq n)))
        (qmul (qsub (x.seq n) (x.seq m)) (qmul (qinv' (x.seq m)) (qinv' (x.seq n)))) := by
      have e1 : qEq (qinv' (x.seq m)) (qmul (qinv' (x.seq m)) (qmul (x.seq n) (qinv' (x.seq n)))) :=
        qEq_symm (qEq_trans (qmul_respects (qEq_refl _) hcn) (qmul_one _))
      have e2 : qEq (qinv' (x.seq n)) (qmul (qinv' (x.seq n)) (qmul (x.seq m) (qinv' (x.seq m)))) :=
        qEq_symm (qEq_trans (qmul_respects (qEq_refl _) hcm) (qmul_one _))
      have e3 : qEq (qsub (qinv' (x.seq m)) (qinv' (x.seq n)))
          (qsub (qmul (qinv' (x.seq m)) (qmul (x.seq n) (qinv' (x.seq n))))
                (qmul (qinv' (x.seq n)) (qmul (x.seq m) (qinv' (x.seq m))))) := by
        unfold qsub; exact qadd_respects e1 (qneg_respects e2)
      refine qEq_trans e3 ?_
      unfold qsub; rat_ring
    -- the product of the two inverses is between 0 and 2^k·2^k
    have hP : qclose (qmul (qinv' (x.seq m)) (qinv' (x.seq n))) qzero (qmul (qofInt (pow2 k)) (qofInt (pow2 k))) := by
      have hz1 : qEq (qsub (qinv' (x.seq m)) qzero) (qinv' (x.seq m)) := by unfold qsub; rat_ring
      have hz2 : qEq (qsub (qinv' (x.seq n)) qzero) (qinv' (x.seq n)) := by unfold qsub; rat_ring
      have hp := qofInt_le (pow2_nonneg k)
      exact qmul_abs_bound ⟨by rat_linarith, by rat_linarith⟩ ⟨by rat_linarith, by rat_linarith⟩
    have hD : qclose (qsub (x.seq n) (x.seq m)) qzero (qeps (k' + (k + k))) := by
      have hz : qEq (qsub (qsub (x.seq n) (x.seq m)) qzero) (qsub (x.seq n) (x.seq m)) := by
        unfold qsub; rat_ring
      have hs : qEq (qsub (x.seq n) (x.seq m)) (qneg (qsub (x.seq m) (x.seq n))) := by unfold qsub; rat_ring
      exact ⟨by rat_linarith, by rat_linarith⟩
    have hprod := qmul_abs_bound hD hP
    -- ε_{k'+2k} · 2^k · 2^k ≈ ε_{k'}
    have hm1 : qEq (qmul (qofInt (pow2 k)) (qeps ((k' + k) + k))) (qeps (k' + k)) := qpow2_mul_eps k (k' + k)
    have hm2 : qEq (qmul (qofInt (pow2 k)) (qeps (k' + k))) (qeps k') := qpow2_mul_eps k k'
    have hidx : k' + (k + k) = (k' + k) + k := (Nat.add_assoc k' k k).symm
    rw [hidx] at hprod
    have hE : qEq (qmul (qeps ((k' + k) + k)) (qmul (qofInt (pow2 k)) (qofInt (pow2 k)))) (qeps k') := by
      calc qmul (qeps ((k' + k) + k)) (qmul (qofInt (pow2 k)) (qofInt (pow2 k)))
          ≈q qmul (qofInt (pow2 k)) (qmul (qofInt (pow2 k)) (qeps ((k' + k) + k))) := by rat_ring
        _ ≈q qmul (qofInt (pow2 k)) (qeps (k' + k)) := qmul_respects (qEq_refl _) hm1
        _ ≈q qeps k' := hm2
    obtain ⟨p1, p2⟩ := hprod
    have hz : qEq (qsub (qmul (qsub (x.seq n) (x.seq m)) (qmul (qinv' (x.seq m)) (qinv' (x.seq n)))) qzero)
        (qmul (qsub (x.seq n) (x.seq m)) (qmul (qinv' (x.seq m)) (qinv' (x.seq n)))) := by
      unfold qsub; rat_ring
    constructor <;> rat_linarith⟩

/-- The reciprocal cancels: `x · (1/x) ≈ 1`. -/
theorem rinvPos_mul (x : RExpr) (k N : Nat) (hw : PosWitness x k N) :
    rEq (rmul x (rinvPos x k N hw)) rone := by
  intro k'
  refine ⟨N, fun n hn => ?_⟩
  have hc := qmul_inv'_cancel (ne_zero_of_eps_le (hw n hn))
  change qclose (qmul (x.seq n) (qinv' (x.seq n))) qone (qeps k')
  exact qclose_respects (qEq_symm hc) (qEq_refl _) (qEq_refl _) (qclose_refl _ _ (qeps_nonneg k'))

#print axioms rEq_trans
#print axioms radd_respects
#print axioms rbounded
#print axioms rmul_respects
#print axioms rmul_assoc
#print axioms rzero_ne_one
#print axioms RExpr.cr
#print axioms rle_antisymm
#print axioms rlt_respects
#print axioms rinvPos
#print axioms rinvPos_mul

end VR.Numbers
