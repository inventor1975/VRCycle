-- VRClassical/Numbers/IntegersBridge.lean
-- The QUOTIENT BRIDGE of ℤ_VR to Mathlib's `Int` (split out of `Numbers/Integers.lean` on
-- 2026-09-12, integrity programme: the witnessed layer `IntExpr`/`intEq` stays in the VR core on
-- `[]`; the quotient `ℤ_VR := Quotient intEqSetoid`, its lifted operations and the isomorphism
-- Theorem II.6 with `Int` live here, in the classical library, on `[Quot.sound]`/`[propext, …]`).

import VR.Numbers.Integers
import Mathlib.Tactic

namespace VR.Numbers

-- ============================================================
-- §II.2 + §II.6. Setoid and Quotient — ℤ_VR
-- ============================================================

-- Quot.sound — standard Lean 4 kernel axiom:
--   ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
--     r a b → Quot.mk r a = Quot.mk r b
-- If two elements are related, their equivalence classes are equal as terms
-- of the quotient type.
--
-- This is the only new axiom dependency that appears in VR-Numbers (beyond
-- Part I, where all theorems are axiom-free). Quotient type construction is
-- impossible without Quot.sound: without it, equivalence classes would be
-- distinguishable as terms, destroying the mathematical content of ℤ_VR.
--
-- Quot.sound is neither Classical.choice nor propext. It is specific to
-- quotient construction and compatible with a constructive interpretation:
-- it does not postulate tertium non datur and does not break computability.

-- §II.2. Setoid: packages intEq as a Lean equivalence relation.
instance intEqSetoid : Setoid IntExpr where
  r     := intEq
  iseqv := ⟨intEq_refl,
             fun {a b} h   => intEq_symm  a b h,
             fun {a b c} h1 h2 => intEq_trans a b c h1 h2⟩

-- §II.6. ℤ_VR — the type of equivalence classes of expressions a ⊖ b.
-- Corresponds to «set ℤ_VR of equivalence classes of expressions a ⊖ b»
-- from the preprint §II.6.
def IntVR : Type := Quotient intEqSetoid

-- Notation ℤ_VR to match the preprint when stating theorems.
notation "ℤ_VR" => IntVR

-- ============================================================
-- §II.4. Operations lifted to ℤ_VR
-- ============================================================

-- §II.4. Additive inverse on ℤ_VR.
-- Defined via Quotient.lift; Quot.sound first appears here.
def inegQ : ℤ_VR → ℤ_VR :=
  Quotient.lift (fun e => Quotient.mk intEqSetoid (ineg e))
    (fun a b h => Quotient.sound (ineg_respects a b h))

-- §II.4. Addition on ℤ_VR.
-- Quotient.lift₂ arg order: a₁ b₁ a₂ b₂ (interleaved, not grouped).
-- h1 : a₁ ≈ a₂ (first quotient), h2 : b₁ ≈ b₂ (second quotient).
-- iadd_respects called as (a₁, a₂, b₁, b₂, h1, h2).
def iaddQ : ℤ_VR → ℤ_VR → ℤ_VR :=
  Quotient.lift₂ (fun e₁ e₂ => Quotient.mk intEqSetoid (iadd e₁ e₂))
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (iadd_respects a₁ a₂ b₁ b₂ h1 h2))

-- §II.4. Multiplication on ℤ_VR.
def imulQ : ℤ_VR → ℤ_VR → ℤ_VR :=
  Quotient.lift₂ (fun e₁ e₂ => Quotient.mk intEqSetoid (imul e₁ e₂))
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (imul_respects a₁ a₂ b₁ b₂ h1 h2))

-- §II.4. Subtraction on ℤ_VR.
def isubQ : ℤ_VR → ℤ_VR → ℤ_VR :=
  Quotient.lift₂ (fun e₁ e₂ => Quotient.mk intEqSetoid (isub e₁ e₂))
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (isub_respects a₁ a₂ b₁ b₂ h1 h2))

-- ============================================================
-- §II.5. Embedding ℕ into ℤ_VR
-- ============================================================

-- §II.5. Embedding ℕ into ℤ_VR.
-- Natural number n maps to the class (n ⊖ ∅): non-negative integer n.
-- Operational interpretation: n stays n when viewed as the difference n − 0.
def embedN : VRObj → ℤ_VR :=
  fun n => Quotient.mk intEqSetoid (.mk n VRObj.base)

-- ============================================================
-- §II.6. Theorem II.6: ℤ_VR ≅ ℤ (Isomorphism with Lean Int)
-- ============================================================

-- §II.6. Bridge lemma: O_inv distributes over vadd.
-- O_inv (vadd a b) = O_inv a + O_inv b.
-- Proof: rewrite a = O (O_inv a), b = O (O_inv b) via O_right_inv,
-- then O_add : O (m + n) = vadd (O m) (O n) gives vadd = O of sum,
-- then O_left_inv collapses.
-- Methodological note: this is a right-inverse of O_add; it surfaces here
-- because the isomorphism proof needs to commute O_inv with operations.
private theorem O_inv_vadd (a b : VRObj) : O_inv (vadd a b) = O_inv a + O_inv b := by
  conv_lhs => rw [← O_right_inv a, ← O_right_inv b, ← O_add, O_left_inv]

-- §II.6. Bridge lemma: O_inv distributes over vmul.
-- O_inv (vmul a b) = O_inv a * O_inv b.
-- Proof: same strategy as O_inv_vadd, using O_mul in place of O_add.
private theorem O_inv_vmul (a b : VRObj) : O_inv (vmul a b) = O_inv a * O_inv b := by
  conv_lhs => rw [← O_right_inv a, ← O_right_inv b, ← O_mul, O_left_inv]

-- §II.6. The forward map on representatives.
-- forwardExpr (a ⊖ b) := (O_inv a : ℤ) - O_inv b.
-- Lean's Int subtraction; O_inv maps VRObj → ℕ, the cast ↑ goes ℕ → ℤ.
def forwardExpr : IntExpr → Int
  | .mk a b => (O_inv a : Int) - O_inv b

-- §II.6. forwardExpr respects intEq.
-- h : vadd a d = vadd b c  (VRObj equality)
-- goal : (O_inv a : ℤ) - O_inv b = (O_inv c : ℤ) - O_inv d
-- Key: apply O_inv to h, use O_inv_vadd to split, then omega on ℤ.
theorem forwardExpr_respects :
    ∀ e f : IntExpr, intEq e f → forwardExpr e = forwardExpr f := by
  intro e f h
  cases e with | mk a b =>
  cases f with | mk c d =>
  have h : vadd a d = vadd b c := h
  have key : O_inv a + O_inv d = O_inv b + O_inv c := by
    have := congrArg O_inv h
    rwa [O_inv_vadd, O_inv_vadd] at this
  simp only [forwardExpr]
  omega

-- §II.6. Forward map ℤ_VR → ℤ, lifted from forwardExpr via Quotient.lift.
-- Well-definedness: forwardExpr_respects.
def forward : ℤ_VR → Int :=
  Quotient.lift forwardExpr forwardExpr_respects

-- §II.6. Backward map ℤ → ℤ_VR.
-- Positive integers n ≥ 0: (n ⊖ ∅) in ℤ_VR.
-- Negative integers −(n+1): (∅ ⊖ (n+1)) in ℤ_VR.
-- Int.ofNat / Int.negSucc are Lean's core constructors for Int.
def backward : Int → ℤ_VR
  | Int.ofNat n   => Quotient.mk intEqSetoid (.mk (O n) VRObj.base)
  | Int.negSucc n => Quotient.mk intEqSetoid (.mk VRObj.base (O (n + 1)))

-- §II.6. Right inverse: forward ∘ backward = id on ℤ.
-- Case ofNat n: forward (backward n) = O_inv (O n) - O_inv base = n - 0 = n.
-- Case negSucc n: forward (backward (−(n+1))) = O_inv base - O_inv (O (n+1)) = 0 − (n+1).
-- Both branches close by O_left_inv + omega (for the cast arithmetic).
-- O_inv VRObj.base = 0 by definition (first equation of O_inv).
-- Not a consequence of O_left_inv (which rewrites O_inv (O n)); needed separately.
private theorem O_inv_void : O_inv VRObj.base = 0 := rfl

theorem right_inv_int : ∀ i : Int, forward (backward i) = i := by
  intro i
  cases i with
  | ofNat n =>
    simp only [backward, forward, Quotient.lift_mk, forwardExpr, O_left_inv, O_inv_void]
    simp
  | negSucc n =>
    simp only [backward, forward, Quotient.lift_mk, forwardExpr, O_left_inv, O_inv_void]
    omega

-- §II.6. Helper: (a ⊖ b) ~ (O n ⊖ ∅) when O_inv b + n = O_inv a.
-- Used in left_inv for the nonneg branch.
-- Strategy: O_inv is injective (O ∘ O_inv = id via O_right_inv),
-- so vadd b (O n) = a follows from O_inv_vadd + O_left_inv + hn.
private theorem intEq_nonneg (a b : VRObj) (n : Nat) (hn : O_inv b + n = O_inv a) :
    intEq (.mk a b) (.mk (O n) VRObj.base) := by
  have key : O_inv (vadd b (O n)) = O_inv a := by
    rw [O_inv_vadd, O_left_inv]; exact hn
  have heq : vadd b (O n) = a := by
    have h := congrArg O key; rwa [O_right_inv, O_right_inv] at h
  -- goal: vadd a VRObj.base = vadd b (O n)
  change vadd a VRObj.base = vadd b (O n)
  rw [T1_vadd_comm a VRObj.base, vadd_zero_left a]
  exact heq.symm

-- §II.6. Helper: (a ⊖ b) ~ (∅ ⊖ O n) when O_inv a + n = O_inv b.
-- Mirror of intEq_nonneg: the deficit goes to the right component.
private theorem intEq_neg (a b : VRObj) (n : Nat) (hn : O_inv a + n = O_inv b) :
    intEq (.mk a b) (.mk VRObj.base (O n)) := by
  have key : O_inv (vadd a (O n)) = O_inv b := by
    rw [O_inv_vadd, O_left_inv]; exact hn
  have heq : vadd a (O n) = b := by
    have h := congrArg O key; rwa [O_right_inv, O_right_inv] at h
  -- intEq (.mk a b) (.mk VRObj.base (O n)) unfolds to vadd a (O n) = vadd b VRObj.base
  -- (intEq .mk a b .mk c d  =  vadd a d = vadd b c; here c = base, d = O n)
  change vadd a (O n) = vadd b VRObj.base
  rw [T1_vadd_comm b VRObj.base, vadd_zero_left b]
  exact heq

-- §II.6. Left inverse: backward ∘ forward = id on ℤ_VR.
-- Quotient.ind reduces to a representative (.mk a b);
-- Nat.le_or_lt splits on O_inv a ≥ O_inv b vs <;
-- omega computes the Int value; Quotient.sound + helpers close the goal.
theorem left_inv_int : ∀ z : ℤ_VR, backward (forward z) = z := by
  intro z
  refine Quotient.inductionOn z (fun e => ?_)
  cases e with | mk a b =>
  simp only [forward, Quotient.lift_mk, forwardExpr]
  by_cases h : O_inv b ≤ O_inv a
  · -- nonneg: O_inv b ≤ O_inv a, integer value is ↑(O_inv a - O_inv b)
    have hn    : O_inv b + (O_inv a - O_inv b) = O_inv a := Nat.add_sub_cancel' h
    have hcast : (↑(O_inv a) : Int) - ↑(O_inv b) = ↑(O_inv a - O_inv b) := by omega
    rw [hcast]; simp only [backward]
    exact Quotient.sound (intEq_symm _ _ (intEq_nonneg a b _ hn))
  · -- neg: O_inv a < O_inv b, integer value is Int.negSucc (O_inv b - O_inv a - 1)
    have hlt   : O_inv a < O_inv b := Nat.lt_of_not_le h
    have hn    : O_inv a + (O_inv b - O_inv a) = O_inv b :=
      Nat.add_sub_cancel' (Nat.le_of_lt hlt)
    have hcast : (↑(O_inv a) : Int) - ↑(O_inv b) = Int.negSucc (O_inv b - O_inv a - 1) := by
      omega
    rw [hcast]; simp only [backward]
    -- backward unfolds to (.mk VRObj.base (O (... - 1 + 1))); fold the ±1 back
    have hstep : O_inv b - O_inv a - 1 + 1 = O_inv b - O_inv a := by omega
    rw [hstep]
    exact Quotient.sound (intEq_symm _ _ (intEq_neg a b _ hn))

-- §II.6. forward preserves negation: forward (inegQ z) = -(forward z).
-- After Quotient.ind, goal is a pure ℤ equation; ring closes.
theorem preserve_neg_int : ∀ z : ℤ_VR, forward (inegQ z) = -(forward z) := by
  intro z
  refine Quotient.inductionOn z (fun e => ?_)
  cases e with | mk a b =>
  simp only [inegQ, ineg, forward, Quotient.lift_mk, forwardExpr, Quotient.lift]
  ring

-- §II.6. forward preserves addition: forward (iaddQ z w) = forward z + forward w.
-- After Quotient.ind on both args, goal is a ℤ equation;
-- O_inv_vadd rewrites the additions; push_cast lifts Nat casts; ring closes.
theorem preserve_add_int : ∀ z w : ℤ_VR, forward (iaddQ z w) = forward z + forward w := by
  intro z w
  refine Quotient.inductionOn z (fun e => ?_)
  refine Quotient.inductionOn w (fun f => ?_)
  cases e with | mk a b =>
  cases f with | mk c d =>
  simp only [iaddQ, iadd, forward, Quotient.lift_mk, forwardExpr, O_inv_vadd]
  push_cast
  ring

-- §II.6. forward preserves multiplication: forward (imulQ z w) = forward z * forward w.
-- Same pattern; O_inv_vadd + O_inv_vmul rewrite all operations; ring closes.
theorem preserve_mul_int : ∀ z w : ℤ_VR, forward (imulQ z w) = forward z * forward w := by
  intro z w
  refine Quotient.inductionOn z (fun e => ?_)
  refine Quotient.inductionOn w (fun f => ?_)
  cases e with | mk a b =>
  cases f with | mk c d =>
  simp only [imulQ, imul, forward, Quotient.lift_mk, forwardExpr, O_inv_vadd, O_inv_vmul]
  push_cast
  ring

-- ============================================================
-- §II.6. Theorem II.6 — ℤ_VR ≅ ℤ
-- ============================================================

-- §II.6. Record witnessing the ring isomorphism ℤ_VR ≅ ℤ.
-- Fields: bijection (forward/backward + two inverses) + three operation laws.
-- Note: preserve_sub is omitted; it is derivable from preserve_add + preserve_neg.
structure IntVRIntIso where
  forward : ℤ_VR → Int
  backward : Int → ℤ_VR
  right_inv : ∀ i : Int, forward (backward i) = i
  left_inv : ∀ z : ℤ_VR, backward (forward z) = z
  preserve_add : ∀ z w : ℤ_VR, forward (iaddQ z w) = forward z + forward w
  preserve_mul : ∀ z w : ℤ_VR, forward (imulQ z w) = forward z * forward w
  preserve_neg : ∀ z : ℤ_VR, forward (inegQ z) = -(forward z)

-- §II.6. Theorem II.6: ℤ_VR is isomorphic to ℤ.
-- Explicit construction of the IntVRIntIso record from the above lemmas.
--
-- Axiom audit: `#print axioms Theorem_II_6_IntVR_Int` returns [propext, Quot.sound].
--   • Quot.sound is unavoidable: quotient types cannot be constructed without it
--     (see §II.2 comment above). It is not Classical.choice and does not
--     compromise constructivity of the computation rules.
--   • propext surfaces because Lean's Setoid API uses it internally.
--   All pre-isomorphism theorems (7.1–7.8) remain axiom-free.
--
-- Mathlib usage in this section:
--   • `ring`     — closes pure ℤ-algebra identities after O_inv_vadd/O_inv_vmul
--                  rewrite; not equivalent to the isomorphism claim.
--   • `push_cast` — lifts Nat casts to Int before ring; purely syntactic.
--   • `by_cases`  — classical excluded middle on a decidable Nat inequality;
--                   used only in left_inv (7.9.5) to split the sign of the integer.
--   No mathlib lemma is equivalent to the bijection or operation-preservation claims.
--
-- def (not theorem): IntVRIntIso is a Type (structure), not a Prop.
def Theorem_II_6_IntVR_Int : IntVRIntIso :=
  { forward := forward
    backward := backward
    right_inv := right_inv_int
    left_inv := left_inv_int
    preserve_add := preserve_add_int
    preserve_mul := preserve_mul_int
    preserve_neg := preserve_neg_int }

-- ============================================================
-- §II.6 / §III. Ring properties of ℤ_VR — used in Rationals §III.2.
-- ============================================================

-- Injectivity of forward: z1 = backward (forward z1) = backward (forward z2) = z2.
theorem forward_injective {z1 z2 : ℤ_VR} (h : forward z1 = forward z2) : z1 = z2 :=
  (left_inv_int z1).symm.trans ((congrArg backward h).trans (left_inv_int z2))

-- Commutativity and associativity of iaddQ and imulQ on ℤ_VR.
-- All four follow from forward_injective + the corresponding Int identity via ring.
theorem iaddQ_comm (a b : ℤ_VR) : iaddQ a b = iaddQ b a :=
  forward_injective (by simp only [preserve_add_int]; ring)

theorem imulQ_comm (a b : ℤ_VR) : imulQ a b = imulQ b a :=
  forward_injective (by simp only [preserve_mul_int]; ring)

theorem iaddQ_assoc (a b c : ℤ_VR) : iaddQ (iaddQ a b) c = iaddQ a (iaddQ b c) :=
  forward_injective (by simp only [preserve_add_int]; ring)

theorem imulQ_assoc (a b c : ℤ_VR) : imulQ (imulQ a b) c = imulQ a (imulQ b c) :=
  forward_injective (by simp only [preserve_mul_int]; ring)

-- §II.5 / §III. Multiplicative identity of ℤ_VR.
-- 1_ℤ = class of (succ base ⊖ base) = embedN (succ base).
def one_Z : ℤ_VR := embedN (VRObj.succ VRObj.base)

-- §II.6. forward maps one_Z to integer 1.
-- Proof: forwardExpr (.mk (succ base) base) = O_inv (succ base) - O_inv base = 1 - 0 = 1.
theorem forward_one_Z : forward one_Z = 1 := by
  simp only [one_Z, embedN, forward, Quotient.lift_mk, forwardExpr, O_inv]
  omega

end VR.Numbers
