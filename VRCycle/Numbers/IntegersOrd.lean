-- VRCycle/Numbers/IntegersOrd.lean
-- The order on VR numbers and on the witnessed integers, on the empty axiom list.
--
-- Integrity programme, step 1b (2026-09-12).  `vle a b := ∃ n, a + n = b` on VR numbers (a
-- witness, not a comparison oracle), decided by the structural `vleB`; on integer pairs the order
-- is the cross-sum criterion `a − b ≤ c − d ⟺ a + d ≤ b + c`, shown to respect `intEq`, to be
-- total and decidable, and to be compatible with `iadd` and with `imul` by a positive pair.
-- Every theorem on `[]`.
import VRCycle.Numbers.IntegersOp

namespace VR.Numbers

open VR

set_option genInjectivity false

-- ============================================================
-- §1. Order on VR numbers
-- ============================================================

/-- `a ≤ b` as a witnessed difference. -/
def vle (a b : VRObj) : Prop := ∃ n : VRObj, vadd a n = b
/-- `a < b` := `a + 1 ≤ b`. -/
def vlt (a b : VRObj) : Prop := vle (VRObj.succ a) b

theorem vle_refl (a : VRObj) : vle a a := ⟨VRObj.base, rfl⟩

theorem vle_trans {a b c : VRObj} : vle a b → vle b c → vle a c
  | ⟨n, hn⟩, ⟨m, hm⟩ => ⟨vadd n m, by rw [← T2_vadd_assoc, hn, hm]⟩

theorem vadd_left_cancel {a x y : VRObj} (h : vadd a x = vadd a y) : x = y :=
  vadd_right_cancel x y a ((T1_vadd_comm x a).trans (h.trans (T1_vadd_comm a y)))

theorem vadd_eq_base_left {a b : VRObj} (h : vadd a b = VRObj.base) : a = VRObj.base :=
  vadd_eq_base ((T1_vadd_comm b a).trans h)

theorem vle_antisymm {a b : VRObj} : vle a b → vle b a → a = b
  | ⟨n, hn⟩, ⟨m, hm⟩ => by
      have h1 : vadd a (vadd n m) = vadd a VRObj.base := by
        rw [← T2_vadd_assoc, hn, hm]; rfl
      have h2 : vadd n m = VRObj.base := vadd_left_cancel h1
      have hn0 : n = VRObj.base := vadd_eq_base_left h2
      rw [hn0] at hn
      exact hn

theorem vle_total : ∀ a b : VRObj, vle a b ∨ vle b a
  | VRObj.base, b => Or.inl ⟨b, vadd_zero_left b⟩
  | VRObj.succ a, b =>
    match vle_total a b with
    | Or.inl ⟨n, hn⟩ =>
      match n with
      | VRObj.base => Or.inr ⟨VRObj.succ VRObj.base, congrArg VRObj.succ hn.symm⟩
      | VRObj.succ k => Or.inl ⟨k, by rw [vadd_succ_left]; exact hn⟩
    | Or.inr ⟨n, hn⟩ => Or.inr ⟨VRObj.succ n, congrArg VRObj.succ hn⟩

/-- Decision of `vle` by structural recursion. -/
def vleB : VRObj → VRObj → Bool
  | VRObj.base, _ => true
  | VRObj.succ _, VRObj.base => false
  | VRObj.succ a, VRObj.succ b => vleB a b

theorem vle_succ_succ_iff {a b : VRObj} : vle (VRObj.succ a) (VRObj.succ b) ↔ vle a b :=
  ⟨fun ⟨n, hn⟩ => ⟨n, P4_succ_inj _ _ ((vadd_succ_left a n).symm.trans hn)⟩,
   fun ⟨n, hn⟩ => ⟨n, (vadd_succ_left a n).trans (congrArg VRObj.succ hn)⟩⟩

theorem vleB_iff : ∀ a b : VRObj, vleB a b = true ↔ vle a b
  | VRObj.base, b => ⟨fun _ => ⟨b, vadd_zero_left b⟩, fun _ => rfl⟩
  | VRObj.succ _, VRObj.base =>
    ⟨fun h => Bool.noConfusion h, fun ⟨n, hn⟩ => VRObj.noConfusion ((vadd_succ_left _ n).symm.trans hn)⟩
  | VRObj.succ a, VRObj.succ b =>
    ⟨fun h => vle_succ_succ_iff.mpr ((vleB_iff a b).mp h),
     fun h => (vleB_iff a b).mpr (vle_succ_succ_iff.mp h)⟩

instance vle.decidable (a b : VRObj) : Decidable (vle a b) :=
  match h : vleB a b with
  | true => isTrue ((vleB_iff a b).mp h)
  | false => isFalse (fun hle => Bool.noConfusion (h.symm.trans ((vleB_iff a b).mpr hle)))

theorem vle_add_right {a b : VRObj} (c : VRObj) : vle a b → vle (vadd a c) (vadd b c)
  | ⟨n, hn⟩ => ⟨n, by rw [← hn]; vr_ring⟩

theorem vle_of_add_le_add_right {a b c : VRObj} : vle (vadd a c) (vadd b c) → vle a b
  | ⟨n, hn⟩ => ⟨n, vadd_right_cancel _ _ c (by rw [← hn]; vr_ring)⟩

theorem vle_mul_right {a b : VRObj} (c : VRObj) : vle a b → vle (vmul a c) (vmul b c)
  | ⟨n, hn⟩ => ⟨vmul n c, by rw [← hn]; vr_ring⟩

theorem vle_zero_left (a : VRObj) : vle VRObj.base a := ⟨a, vadd_zero_left a⟩

theorem succ_vadd_ne : ∀ (a n : VRObj), VRObj.succ (vadd a n) ≠ a
  | VRObj.base, _, h => VRObj.noConfusion h
  | VRObj.succ a, n, h => succ_vadd_ne a n ((vadd_succ_left a n).symm.trans (P4_succ_inj _ _ h))

theorem vlt_irrefl (a : VRObj) : ¬ vlt a a
  | ⟨n, hn⟩ => succ_vadd_ne a n ((vadd_succ_left a n).symm.trans hn)

theorem vle_of_vlt {a b : VRObj} : vlt a b → vle a b
  | ⟨n, hn⟩ => ⟨VRObj.succ n, by rw [← hn]; exact (vadd_succ_left a n).symm⟩

theorem vlt_of_vle_of_ne {a b : VRObj} (h : vle a b) (hne : a ≠ b) : vlt a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | base => exact absurd hn hne
  | succ k => exact ⟨k, by rw [vadd_succ_left]; exact hn⟩

/-- Strict monotonicity of `vmul` by a positive factor. -/
theorem vlt_mul_right {a b c : VRObj} (hc : vlt VRObj.base c) : vlt a b → vlt (vmul a c) (vmul b c)
  | ⟨n, hn⟩ => by
      obtain ⟨k, hk⟩ := hc
      -- c = succ k (from base + 1 + k = c), b = a + 1 + n
      have hc' : c = VRObj.succ k := by rw [← hk, vadd_succ_left, vadd_zero_left]
      subst hc'
      refine ⟨vadd (vmul n (VRObj.succ k)) k, ?_⟩
      rw [← hn]
      vr_ring

theorem vle_mul_cancel_right {a b c : VRObj} (hc : vlt VRObj.base c) (h : vle (vmul a c) (vmul b c)) :
    vle a b := by
  rcases vle_total a b with hab | hba
  · exact hab
  · by_cases heq : b = a
    · subst heq; exact vle_refl _
    · have hlt := vlt_mul_right hc (vlt_of_vle_of_ne hba heq)
      exact absurd (vle_antisymm h (vle_of_vlt hlt)) (fun e => vlt_irrefl _ (e ▸ hlt))

-- ============================================================
-- §2. Order on integer pairs
-- ============================================================

/-- `a − b ≤ c − d ⟺ a + d ≤ b + c`. -/
def intLe : IntExpr → IntExpr → Prop
  | .mk a b, .mk c d => vle (vadd a d) (vadd b c)
def intLt (e f : IntExpr) : Prop := intLe (iadd e oneI) f
/-- Positive pairs. -/
def intPos (e : IntExpr) : Prop := intLt zeroI e

scoped infix:50 " ≤ᵢ " => intLe
scoped infix:50 " <ᵢ " => intLt

instance intLe.decidable : ∀ e f : IntExpr, Decidable (intLe e f)
  | .mk a b, .mk c d => (inferInstance : Decidable (vle (vadd a d) (vadd b c)))
instance intLt.decidable (e f : IntExpr) : Decidable (intLt e f) := intLe.decidable _ _
instance intPos.decidable (e : IntExpr) : Decidable (intPos e) := intLt.decidable _ _

theorem vle_congr {x x' y y' : VRObj} (hx : x = x') (hy : y = y') : vle x y → vle x' y' := by
  subst hx; subst hy; exact id

theorem intLe_refl : ∀ e : IntExpr, e ≤ᵢ e
  | .mk a b => vle_congr rfl (T1_vadd_comm a b) (vle_refl (vadd a b))

theorem intLe_trans : ∀ {e f g : IntExpr}, e ≤ᵢ f → f ≤ᵢ g → e ≤ᵢ g
  | .mk a b, .mk c d, .mk e f, h1, h2 => by
      change vle (vadd a d) (vadd b c) at h1
      change vle (vadd c f) (vadd d e) at h2
      change vle (vadd a f) (vadd b e)
      have h3 : vle (vadd (vadd a f) (vadd c d)) (vadd (vadd b c) (vadd c f)) :=
        vle_congr (by vr_ring) (by vr_ring) (vle_add_right (vadd c f) h1)
      have h4 : vle (vadd (vadd b c) (vadd c f)) (vadd (vadd b e) (vadd c d)) :=
        vle_congr (by vr_ring) (by vr_ring) (vle_add_right (vadd b c) h2)
      exact vle_of_add_le_add_right (vle_trans h3 h4)

theorem intLe_antisymm : ∀ {e f : IntExpr}, e ≤ᵢ f → f ≤ᵢ e → e ≈ᵢ f
  | .mk a b, .mk c d, h1, h2 => by
      change vle (vadd a d) (vadd b c) at h1
      change vle (vadd c b) (vadd d a) at h2
      change vadd a d = vadd b c
      exact vle_antisymm h1 (vle_congr (T1_vadd_comm c b) (T1_vadd_comm d a) h2)

theorem intLe_total : ∀ e f : IntExpr, e ≤ᵢ f ∨ f ≤ᵢ e
  | .mk a b, .mk c d =>
    match vle_total (vadd a d) (vadd b c) with
    | Or.inl h => Or.inl h
    | Or.inr h => Or.inr (vle_congr (T1_vadd_comm b c) (T1_vadd_comm a d) h)

theorem intLe_of_intEq : ∀ {e f : IntExpr}, e ≈ᵢ f → e ≤ᵢ f
  | .mk a b, .mk c d, h => by
      change vadd a d = vadd b c at h
      change vle (vadd a d) (vadd b c)
      rw [h]; exact vle_refl _

theorem intLe_respects {e e' f f' : IntExpr} (he : e ≈ᵢ e') (hf : f ≈ᵢ f') (h : e ≤ᵢ f) :
    e' ≤ᵢ f' :=
  intLe_trans (intLe_of_intEq (intEq_symm _ _ he)) (intLe_trans h (intLe_of_intEq hf))

theorem intLe_add_right : ∀ {e f : IntExpr} (g : IntExpr), e ≤ᵢ f → iadd e g ≤ᵢ iadd f g
  | .mk a b, .mk c d, .mk x y, h => by
      change vle (vadd a d) (vadd b c) at h
      change vle (vadd (vadd a x) (vadd d y)) (vadd (vadd b y) (vadd c x))
      exact vle_congr (by vr_ring) (by vr_ring) (vle_add_right (vadd x y) h)

theorem intLe_of_add_le_add_right : ∀ {e f g : IntExpr}, iadd e g ≤ᵢ iadd f g → e ≤ᵢ f
  | .mk a b, .mk c d, .mk x y, h => by
      change vle (vadd (vadd a x) (vadd d y)) (vadd (vadd b y) (vadd c x)) at h
      change vle (vadd a d) (vadd b c)
      exact vle_of_add_le_add_right (c := vadd x y)
        (vle_congr (by vr_ring) (by vr_ring) h)

/-- Positive pairs are exactly those `≈ (succ n, 0)`. -/
theorem intPos_iff : ∀ e : IntExpr, intPos e ↔ ∃ n : VRObj, e ≈ᵢ .mk (VRObj.succ n) VRObj.base
  | .mk a b => by
      constructor
      · intro h
        change vle (vadd (vadd VRObj.base (VRObj.succ VRObj.base)) b)
          (vadd (vadd VRObj.base VRObj.base) a) at h
        obtain ⟨n, hn⟩ := h
        refine ⟨n, ?_⟩
        change vadd a VRObj.base = vadd b (VRObj.succ n)
        have ha : a = vadd (vadd (vadd VRObj.base (VRObj.succ VRObj.base)) b) n := by
          rw [hn, vadd_zero_left, vadd_zero_left]
        rw [ha]; vr_ring
      · rintro ⟨n, hn⟩
        change vadd a VRObj.base = vadd b (VRObj.succ n) at hn
        change vle (vadd (vadd VRObj.base (VRObj.succ VRObj.base)) b)
          (vadd (vadd VRObj.base VRObj.base) a)
        refine ⟨n, ?_⟩
        have : a = vadd b (VRObj.succ n) := hn
        rw [this]; vr_ring

theorem intPos_respects {e e' : IntExpr} (h : e ≈ᵢ e') (hp : intPos e) : intPos e' :=
  intLe_respects (e := iadd zeroI oneI) (intEq_refl _) h hp

theorem intPos_one : intPos oneI := (intPos_iff oneI).mpr ⟨VRObj.base, intEq_refl _⟩

theorem intPos_mul {e f : IntExpr} (he : intPos e) (hf : intPos f) : intPos (imul e f) := by
  obtain ⟨n, hn⟩ := (intPos_iff e).mp he
  obtain ⟨m, hm⟩ := (intPos_iff f).mp hf
  apply (intPos_iff _).mpr
  refine ⟨vadd (vmul (VRObj.succ n) m) n, ?_⟩
  exact intEq_trans _ _ _ (imul_respects _ _ _ _ hn hm) (imul_pos_pos _ _)

theorem intPos_add {e f : IntExpr} (he : intPos e) (hf : intPos f) : intPos (iadd e f) := by
  obtain ⟨n, hn⟩ := (intPos_iff e).mp he
  obtain ⟨m, hm⟩ := (intPos_iff f).mp hf
  apply (intPos_iff _).mpr
  refine ⟨vadd n (VRObj.succ m), ?_⟩
  exact intEq_trans _ _ _ (iadd_respects _ _ _ _ hn hm) (by int_ring_pairs)

theorem ne_zero_of_intPos {e : IntExpr} (h : intPos e) : ¬ e ≈ᵢ zeroI := by
  obtain ⟨n, hn⟩ := (intPos_iff e).mp h
  intro h0
  have := (intEq_congr_left hn).mp h0
  exact VRObj.noConfusion ((intEq_zero_iff _ _).mp this)

/-- Monotonicity of `imul` by a positive pair. -/
theorem intLe_mul_right {e f g : IntExpr} (hg : intPos g) (h : e ≤ᵢ f) : imul e g ≤ᵢ imul f g := by
  obtain ⟨k, hk⟩ := (intPos_iff g).mp hg
  refine intLe_respects (imul_respects _ _ _ _ (intEq_refl e) (intEq_symm _ _ hk))
    (imul_respects _ _ _ _ (intEq_refl f) (intEq_symm _ _ hk)) ?_
  obtain ⟨a, b⟩ := e; obtain ⟨c, d⟩ := f
  change vle (vadd a d) (vadd b c) at h
  change vle (vadd (vadd (vmul a (VRObj.succ k)) (vmul b VRObj.base))
                   (vadd (vmul c VRObj.base) (vmul d (VRObj.succ k))))
             (vadd (vadd (vmul a VRObj.base) (vmul b (VRObj.succ k)))
                   (vadd (vmul c (VRObj.succ k)) (vmul d VRObj.base)))
  exact vle_congr (by vr_ring) (by vr_ring) (vle_mul_right (VRObj.succ k) h)

/-- Cancellation of a positive factor in `≤ᵢ`. -/
theorem intLe_of_mul_le_mul_right {e f g : IntExpr} (hg : intPos g) (h : imul e g ≤ᵢ imul f g) :
    e ≤ᵢ f := by
  obtain ⟨k, hk⟩ := (intPos_iff g).mp hg
  have h' := intLe_respects (imul_respects _ _ _ _ (intEq_refl e) hk)
    (imul_respects _ _ _ _ (intEq_refl f) hk) h
  obtain ⟨a, b⟩ := e; obtain ⟨c, d⟩ := f
  change vle (vadd (vadd (vmul a (VRObj.succ k)) (vmul b VRObj.base))
                   (vadd (vmul c VRObj.base) (vmul d (VRObj.succ k))))
             (vadd (vadd (vmul a VRObj.base) (vmul b (VRObj.succ k)))
                   (vadd (vmul c (VRObj.succ k)) (vmul d VRObj.base))) at h'
  change vle (vadd a d) (vadd b c)
  exact vle_mul_cancel_right (c := VRObj.succ k) ⟨k, by rw [vadd_succ_left, vadd_zero_left]⟩
    (vle_congr (by vr_ring) (by vr_ring) h')

theorem intLt_iff_le_not_le {e f : IntExpr} : e <ᵢ f ↔ (e ≤ᵢ f ∧ ¬ f ≤ᵢ e) := by
  obtain ⟨a, b⟩ := e; obtain ⟨c, d⟩ := f
  change vle (vadd (vadd a (VRObj.succ VRObj.base)) d) (vadd (vadd b VRObj.base) c)
      ↔ (vle (vadd a d) (vadd b c) ∧ ¬ vle (vadd c b) (vadd d a))
  constructor
  · intro h
    have h1 : vlt (vadd a d) (vadd b c) :=
      vle_congr (by vr_ring) (by vr_ring) h
    refine ⟨vle_of_vlt h1, fun h2 => ?_⟩
    have h3 : vle (vadd b c) (vadd a d) := vle_congr (T1_vadd_comm c b) (T1_vadd_comm d a) h2
    exact vlt_irrefl _ (vle_antisymm (vle_of_vlt h1) h3 ▸ h1)
  · rintro ⟨h1, h2⟩
    have hne : vadd a d ≠ vadd b c := fun e =>
      h2 (vle_congr (T1_vadd_comm b c) (T1_vadd_comm a d) (e ▸ vle_refl _))
    have h3 : vlt (vadd a d) (vadd b c) := vlt_of_vle_of_ne h1 hne
    exact vle_congr (by vr_ring) (by vr_ring) h3

theorem intLt_trichotomy (e f : IntExpr) : e <ᵢ f ∨ e ≈ᵢ f ∨ f <ᵢ e := by
  by_cases h1 : e ≤ᵢ f
  · by_cases h2 : f ≤ᵢ e
    · exact Or.inr (Or.inl (intLe_antisymm h1 h2))
    · exact Or.inl (intLt_iff_le_not_le.mpr ⟨h1, h2⟩)
  · rcases intLe_total e f with h | h
    · exact absurd h h1
    · exact Or.inr (Or.inr (intLt_iff_le_not_le.mpr ⟨h, h1⟩))

#print axioms vle_total
#print axioms vle.decidable
#print axioms intLe_trans
#print axioms intLe_respects
#print axioms intLe_mul_right
#print axioms intLe_of_mul_le_mul_right
#print axioms intPos_mul
#print axioms intLt_trichotomy

end VR.Numbers
