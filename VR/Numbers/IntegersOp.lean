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
import VR.Numbers.Integers
import VR.Meta.CSRNorm

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
-- §3. A normaliser on `[]`, zero, cancellation, products of non-zeros — what the rational layer needs
-- ============================================================

theorem vadd_zero_right (a : VRObj) : vadd a VRObj.base = a := rfl
theorem vmul_zero_right (a : VRObj) : vmul a VRObj.base = VRObj.base := rfl
theorem vmul_one_right (a : VRObj) : vmul a (VRObj.succ VRObj.base) = a := vadd_zero_left a
theorem vmul_one_left (a : VRObj) : vmul (VRObj.succ VRObj.base) a = a := by
  rw [vmul_comm]; exact vmul_one_right a
theorem vadd_left_comm (a b c : VRObj) : vadd a (vadd b c) = vadd b (vadd a c) := by
  rw [← T2_vadd_assoc, T1_vadd_comm a b, T2_vadd_assoc]
theorem vmul_left_comm (a b c : VRObj) : vmul a (vmul b c) = vmul b (vmul a c) := by
  rw [← vmul_assoc, vmul_comm a b, vmul_assoc]

/-- VR numbers as a commutative semiring up to `Eq` (negation = identity), for `csr_ring`. -/
def VRObj.csr : VR.CSR.CSR VRObj where
  r := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans
  add := vadd
  mul := vmul
  neg := id
  zero := VRObj.base
  one := VRObj.succ VRObj.base
  add_congr := fun h1 h2 => by rw [h1, h2]
  mul_congr := fun h1 h2 => by rw [h1, h2]
  neg_congr := fun h => h
  add_comm := T1_vadd_comm
  add_assoc := T2_vadd_assoc
  zero_add := vadd_zero_left
  mul_comm := vmul_comm
  mul_assoc := vmul_assoc
  one_mul := vmul_one_left
  zero_mul := vmul_zero_left
  mul_add := T3_vmul_distrib
  neg_add := fun _ _ => rfl
  neg_mul := fun _ _ => rfl
  neg_neg := fun _ => rfl
  neg_zero := rfl

/-- `vr_ring`: ring identities on VR numbers, by reflection (`Meta/CSRNorm.lean`), on `[]`. -/
syntax "vr_ring" : tactic
macro_rules
  | `(tactic| vr_ring) => `(tactic| csr_ring VR.Numbers.VRObj.csr)

/-- `int_ring_pairs`: an `intEq` between pairs in constructor form, unfolded to VR numbers and
decided by `vr_ring`. -/
syntax "int_ring_pairs" : tactic
macro_rules
  | `(tactic| int_ring_pairs) => `(tactic| (dsimp only [intEq, imul, iadd, ineg, zeroI, oneI]; vr_ring))

theorem vadd_right_cancel : ∀ (a b c : VRObj), vadd a c = vadd b c → a = b
  | _, _, VRObj.base, h => h
  | a, b, VRObj.succ c, h => vadd_right_cancel a b c (P4_succ_inj _ _ h)

theorem intEq_zero_iff (a b : VRObj) : intEq (.mk a b) zeroI ↔ a = b :=
  ⟨fun h => vadd_right_cancel a b VRObj.base h, fun h => congrArg (fun x => vadd x VRObj.base) h⟩

theorem vadd_eq_base : ∀ {a b : VRObj}, vadd a b = VRObj.base → b = VRObj.base
  | _, VRObj.base, _ => rfl
  | _, VRObj.succ _, h => VRObj.noConfusion h

theorem vmul_eq_base : ∀ {a b : VRObj}, vmul a b = VRObj.base → a = VRObj.base ∨ b = VRObj.base
  | _, VRObj.base, _ => Or.inr rfl
  | _, VRObj.succ _, h => Or.inl (vadd_eq_base h)

/-- Infix for the witnessed identity of integer pairs. -/
scoped infix:50 " ≈ᵢ " => intEq

instance : Trans intEq intEq intEq := ⟨fun h1 h2 => intEq_trans _ _ _ h1 h2⟩

/-- Cancellation on VR numbers, through the isomorphism with Nat (`O_mul`, `O_left_inv`,
`O_right_inv` and `Nat.eq_of_mul_eq_mul_right` are all on `[]`). -/
theorem vmul_right_cancel {a b c : VRObj} (hc : c ≠ VRObj.base) (h : vmul a c = vmul b c) :
    a = b := by
  have e1 : vmul a c = O (O_inv a * O_inv c) := by rw [O_mul, O_right_inv, O_right_inv]
  have e2 : vmul b c = O (O_inv b * O_inv c) := by rw [O_mul, O_right_inv, O_right_inv]
  have hn : O_inv a * O_inv c = O_inv b * O_inv c := by
    have h' := congrArg O_inv h
    rw [e1, e2, O_left_inv, O_left_inv] at h'
    exact h'
  have hcpos : 0 < O_inv c := Nat.pos_of_ne_zero (fun e => hc (by
    have h' := congrArg O e
    rw [O_right_inv] at h'
    exact h'))
  have hab := Nat.eq_of_mul_eq_mul_right hcpos hn
  rw [← O_right_inv a, ← O_right_inv b, hab]

-- Products of canonical forms (`canonical_form`, Integers.lean: every pair is `intEq` to
-- `(n, 0)` or `(0, n)`), and what `intEq` says between canonical forms.
theorem imul_pos_pos (n m : VRObj) :
    intEq (imul (.mk n VRObj.base) (.mk m VRObj.base)) (.mk (vmul n m) VRObj.base) := by int_ring_pairs
theorem imul_pos_neg (n m : VRObj) :
    intEq (imul (.mk n VRObj.base) (.mk VRObj.base m)) (.mk VRObj.base (vmul n m)) := by int_ring_pairs
theorem imul_neg_pos (n m : VRObj) :
    intEq (imul (.mk VRObj.base n) (.mk m VRObj.base)) (.mk VRObj.base (vmul n m)) := by int_ring_pairs
theorem imul_neg_neg (n m : VRObj) :
    intEq (imul (.mk VRObj.base n) (.mk VRObj.base m)) (.mk (vmul n m) VRObj.base) := by int_ring_pairs

theorem intEq_pos_pos (n m : VRObj) : intEq (.mk n VRObj.base) (.mk m VRObj.base) ↔ n = m := by
  change vadd n VRObj.base = vadd VRObj.base m ↔ n = m
  rw [vadd_zero_left]
  exact ⟨fun h => h, fun h => h⟩
theorem intEq_neg_neg (n m : VRObj) : intEq (.mk VRObj.base n) (.mk VRObj.base m) ↔ m = n := by
  change vadd VRObj.base m = vadd n VRObj.base ↔ m = n
  rw [vadd_zero_left]
  exact ⟨fun h => vadd_right_cancel m n VRObj.base h, fun h => congrArg (fun x => vadd x VRObj.base) h⟩
theorem intEq_pos_neg (n m : VRObj) :
    intEq (.mk n VRObj.base) (.mk VRObj.base m) ↔ n = VRObj.base ∧ m = VRObj.base := by
  change vadd n m = vadd VRObj.base VRObj.base ↔ _
  constructor
  · intro h
    have hm : m = VRObj.base := vadd_eq_base h
    subst hm
    exact ⟨h, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem intEq_congr_left {e e' f : IntExpr} (h : intEq e e') : intEq e f ↔ intEq e' f :=
  ⟨intEq_trans _ _ _ (intEq_symm _ _ h), intEq_trans _ _ _ h⟩
theorem intEq_congr_right {e f f' : IntExpr} (h : intEq f f') : intEq e f ↔ intEq e f' :=
  ⟨fun h' => intEq_trans _ _ _ h' h, fun h' => intEq_trans _ _ _ h' (intEq_symm _ _ h)⟩

private theorem ne_base_of_canon_pos {g : IntExpr} {k : VRObj} (hg : ¬ intEq g zeroI)
    (hk : intEq g (.mk k VRObj.base)) : k ≠ VRObj.base :=
  fun e => hg ((intEq_congr_left hk).mpr (by subst e; exact rfl))
private theorem ne_base_of_canon_neg {g : IntExpr} {k : VRObj} (hg : ¬ intEq g zeroI)
    (hk : intEq g (.mk VRObj.base k)) : k ≠ VRObj.base :=
  fun e => hg ((intEq_congr_left hk).mpr (by subst e; exact rfl))

/-- Non-zero times non-zero is non-zero, up to `intEq`. -/
theorem imul_ne_zero {e f : IntExpr} (he : ¬ intEq e zeroI) (hf : ¬ intEq f zeroI) :
    ¬ intEq (imul e f) zeroI := by
  intro h0
  rcases canonical_form e with ⟨n, hn⟩ | ⟨n, hn⟩ <;>
  rcases canonical_form f with ⟨m, hm⟩ | ⟨m, hm⟩
  all_goals have h1 := (intEq_congr_left (imul_respects _ _ _ _ hn hm)).mp h0
  · have h2 := (intEq_congr_left (imul_pos_pos n m)).mp h1
    rcases vmul_eq_base ((intEq_zero_iff _ _).mp h2) with rfl | rfl
    · exact ne_base_of_canon_pos he hn rfl
    · exact ne_base_of_canon_pos hf hm rfl
  · have h2 := (intEq_congr_left (imul_pos_neg n m)).mp h1
    rcases vmul_eq_base ((intEq_zero_iff _ _).mp h2).symm with rfl | rfl
    · exact ne_base_of_canon_pos he hn rfl
    · exact ne_base_of_canon_neg hf hm rfl
  · have h2 := (intEq_congr_left (imul_neg_pos n m)).mp h1
    rcases vmul_eq_base ((intEq_zero_iff _ _).mp h2).symm with rfl | rfl
    · exact ne_base_of_canon_neg he hn rfl
    · exact ne_base_of_canon_pos hf hm rfl
  · have h2 := (intEq_congr_left (imul_neg_neg n m)).mp h1
    rcases vmul_eq_base ((intEq_zero_iff _ _).mp h2) with rfl | rfl
    · exact ne_base_of_canon_neg he hn rfl
    · exact ne_base_of_canon_neg hf hm rfl

private theorem canon_pp {n m k : VRObj} (hk : k ≠ VRObj.base)
    (h : intEq (.mk (vmul n k) VRObj.base) (.mk (vmul m k) VRObj.base)) : n = m :=
  vmul_right_cancel hk ((intEq_pos_pos _ _).mp h)
private theorem canon_nn {n m k : VRObj} (hk : k ≠ VRObj.base)
    (h : intEq (.mk VRObj.base (vmul n k)) (.mk VRObj.base (vmul m k))) : n = m :=
  (vmul_right_cancel hk ((intEq_neg_neg _ _).mp h)).symm
private theorem canon_pn {n m k : VRObj} (hk : k ≠ VRObj.base)
    (h : intEq (.mk (vmul n k) VRObj.base) (.mk VRObj.base (vmul m k))) :
    n = VRObj.base ∧ m = VRObj.base :=
  match (intEq_pos_neg _ _).mp h with
  | ⟨h1, h2⟩ => ⟨(vmul_eq_base h1).resolve_right hk, (vmul_eq_base h2).resolve_right hk⟩

/-- **Cancellation up to `intEq`**: `e·g ≈ f·g` and `g ≉ 0` give `e ≈ f`. -/
theorem imul_cancel_right {e f g : IntExpr} (hg : ¬ intEq g zeroI)
    (h : intEq (imul e g) (imul f g)) : intEq e f := by
  rcases canonical_form e with ⟨n, hn⟩ | ⟨n, hn⟩ <;>
  rcases canonical_form f with ⟨m, hm⟩ | ⟨m, hm⟩ <;>
  rcases canonical_form g with ⟨k, hk⟩ | ⟨k, hk⟩
  all_goals (have h1 := ((intEq_congr_right (imul_respects _ _ _ _ hm hk)).mp
    ((intEq_congr_left (imul_respects _ _ _ _ hn hk)).mp h)))
  all_goals (first
    | (have hk0 := ne_base_of_canon_pos hg hk)
    | (have hk0 := ne_base_of_canon_neg hg hk))
  · have h2 := (intEq_congr_right (imul_pos_pos m k)).mp ((intEq_congr_left (imul_pos_pos n k)).mp h1)
    have := canon_pp hk0 h2; subst this; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_pos_neg m k)).mp ((intEq_congr_left (imul_pos_neg n k)).mp h1)
    have := canon_nn hk0 h2; subst this; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_neg_pos m k)).mp ((intEq_congr_left (imul_pos_pos n k)).mp h1)
    obtain ⟨rfl, rfl⟩ := canon_pn hk0 h2; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_neg_neg m k)).mp ((intEq_congr_left (imul_pos_neg n k)).mp h1)
    obtain ⟨rfl, rfl⟩ := canon_pn hk0 (intEq_symm _ _ h2); exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_pos_pos m k)).mp ((intEq_congr_left (imul_neg_pos n k)).mp h1)
    obtain ⟨rfl, rfl⟩ := canon_pn hk0 (intEq_symm _ _ h2); exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_pos_neg m k)).mp ((intEq_congr_left (imul_neg_neg n k)).mp h1)
    obtain ⟨rfl, rfl⟩ := canon_pn hk0 h2; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_neg_pos m k)).mp ((intEq_congr_left (imul_neg_pos n k)).mp h1)
    have := canon_nn hk0 h2; subst this; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)
  · have h2 := (intEq_congr_right (imul_neg_neg m k)).mp ((intEq_congr_left (imul_neg_neg n k)).mp h1)
    have := canon_pp hk0 h2; subst this; exact intEq_trans _ _ _ hn (intEq_symm _ _ hm)

/-- Decidable equality of VR numbers, by structural recursion (VR.lean derives none). -/
def VRObj.decEq : ∀ a b : VRObj, Decidable (a = b)
  | .base, .base => isTrue rfl
  | .base, .succ _ => isFalse (fun h => VRObj.noConfusion h)
  | .succ _, .base => isFalse (fun h => VRObj.noConfusion h)
  | .succ a, .succ b =>
    match VRObj.decEq a b with
    | isTrue h => isTrue (congrArg VRObj.succ h)
    | isFalse h => isFalse (fun e => h (P4_succ_inj _ _ e))
instance : DecidableEq VRObj := VRObj.decEq

instance intEq.decidable : ∀ (e f : IntExpr), Decidable (intEq e f)
  | .mk a b, .mk c d => (inferInstance : Decidable (vadd a d = vadd b c))

theorem imul_eq_zero {e f : IntExpr} (h : intEq (imul e f) zeroI) :
    intEq e zeroI ∨ intEq f zeroI := by
  by_cases he : intEq e zeroI
  · exact Or.inl he
  · by_cases hf : intEq f zeroI
    · exact Or.inr hf
    · exact absurd h (imul_ne_zero he hf)

theorem one_ne_zero_I : ¬ intEq oneI zeroI :=
  fun h => VRObj.noConfusion ((intEq_zero_iff _ _).mp h)

/-- Integer pairs as a commutative ring up to `intEq`, for `csr_ring`: identities are decided at
the level of pairs as atoms — no unfolding into VR numbers. -/
def IntExpr.csr : VR.CSR.CSR IntExpr where
  r := intEq
  refl := intEq_refl
  symm := fun h => intEq_symm _ _ h
  trans := fun h1 h2 => intEq_trans _ _ _ h1 h2
  add := iadd
  mul := imul
  neg := ineg
  zero := zeroI
  one := oneI
  add_congr := fun h1 h2 => iadd_respects _ _ _ _ h1 h2
  mul_congr := fun h1 h2 => imul_respects _ _ _ _ h1 h2
  neg_congr := fun h => ineg_respects _ _ h
  add_comm := iadd_comm
  add_assoc := iadd_assoc
  zero_add := zero_iadd
  mul_comm := imul_comm
  mul_assoc := imul_assoc
  one_mul := one_imul
  zero_mul := zero_imul
  mul_add := imul_iadd
  neg_add := fun e f => by
    obtain ⟨a, a'⟩ := e; obtain ⟨c, c'⟩ := f; int_ring_pairs
  neg_mul := fun e f => by
    obtain ⟨a, a'⟩ := e; obtain ⟨c, c'⟩ := f; int_ring_pairs
  neg_neg := fun e => by obtain ⟨a, a'⟩ := e; exact intEq_refl _
  neg_zero := intEq_refl _

/-- With cancellation `e + (−e) ≈ 0`: a ring. -/
def IntExpr.cr : VR.CSR.CR IntExpr := { IntExpr.csr with add_neg := iadd_ineg }

/-- `int_ring`: ring identities between integer pairs up to `intEq`, pairs as atoms, with
cancellation (`cr_ring`, `Meta/CSRNorm.lean`). -/
syntax "int_ring" : tactic
macro_rules
  | `(tactic| int_ring) => `(tactic| cr_ring VR.Numbers.IntExpr.cr)

-- ============================================================
-- §4. The audit: every act of this file is on the empty list
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
#print axioms imul_ne_zero
#print axioms imul_cancel_right
#print axioms vmul_right_cancel
#print axioms imul_eq_zero
#print axioms instDecidableEqVRObj
#print axioms IntExpr.csr
#print axioms VRObj.csr

end VR.Numbers
