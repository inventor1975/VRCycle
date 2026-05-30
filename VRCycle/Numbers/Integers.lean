-- VR-Numbers: Integers ℤ_VR (DOI 10.5281/zenodo.20272743)
-- Part II. Integers ℤ as an Operational Superstructure.

import VRCycle.VR
-- Mathlib imported for §II.6 only: ring and push_cast tactics for the
-- isomorphism theorem. All prior definitions (IntExpr, intEq, operations,
-- canonical form) are independent of mathlib. Per PLAN.md principle 1.
import Mathlib.Tactic

namespace VR.Numbers

open VR

-- ============================================================
-- §II.1. The Formal Language of Subtraction
-- ============================================================

-- §II.1. The Formal Language of Subtraction.
-- An expression a ⊖ b is a syntactic record of the operation
-- "subtract b from a", where a, b ∈ ℕ (= VRObj in VR).
--
-- §VI.5, item 1: pairs appear nowhere as independent ontological objects.
-- This is syntactic juxtaposition with binary operator ⊖, not a pair with
-- named projections. Access is exclusively through pattern matching:
-- match e with | .mk a b => ...
inductive IntExpr : Type where
  | mk : VRObj → VRObj → IntExpr

-- ============================================================
-- §II.2. Equivalence Relation
-- ============================================================

-- §II.2. Equivalence Relation.
-- «a ⊖ b ≈ c ⊖ d  ⟺  a + d = b + c»
--
-- Two expressions are equivalent when they would yield the same result
-- using the addition operation already defined on ℕ (= vadd on VRObj).
-- The = here is Lean's Eq on VRObj (not vrEq):
-- this is arithmetic equality of two VRObj-values, not a Leibnizian claim.
def intEq : IntExpr → IntExpr → Prop
  | .mk a b, .mk c d => vadd a d = vadd b c

-- ============================================================
-- §II.2. intEq is an equivalence relation
-- ============================================================

-- Auxiliary: right cancellation law for vadd.
-- vadd a c = vadd b c → a = b.
-- Not in the preprint (absorbed into "direct verification");
-- Lean requires it as an explicit lemma for intEq_trans.
-- Proof by induction on c, using P4_succ_inj (injectivity of succ).
-- Methodological note: the cancellation law surfaces here because
-- intEq_trans reduces to it; the preprint's "direct verification" conceals
-- this dependency. Candidate observation for VR-Numbers §VIII.
private theorem vadd_cancel : ∀ a b c : VRObj, vadd a c = vadd b c → a = b := by
  intro a b c h
  induction c with
  | mark      => exact h
  | succ d ih => exact ih (P4_succ_inj _ _ h)

-- §II.2. Reflexivity: intEq e e.
-- intEq (mk a b) (mk a b) = (vadd a b = vadd b a) = T1_vadd_comm a b.
-- First theorem of VR-Numbers that uses T1 substantively.
theorem intEq_refl : ∀ e : IntExpr, intEq e e
  | .mk a b => T1_vadd_comm a b

-- §II.2. Symmetry: intEq e f → intEq f e.
-- h : vadd a d = vadd b c
-- goal : vadd c b = vadd d a
-- Chain: vadd c b = vadd b c [T1] = vadd a d [h.symm] = vadd d a [T1].
theorem intEq_symm : ∀ e f : IntExpr, intEq e f → intEq f e
  | .mk a b, .mk c d, h =>
    (T1_vadd_comm c b).trans (h.symm.trans (T1_vadd_comm a d))

-- §II.2. Transitivity: intEq e f → intEq f g → intEq e g.
-- h1 : vadd a d = vadd b c
-- h2 : vadd c f' = vadd d e'
-- goal : vadd a f' = vadd b e'
-- Strategy: show vadd (vadd a f') d = vadd (vadd b e') d, then cancel d.
-- Uses vadd_cancel (see above); T1 and T2 rearrange the calc chain.
theorem intEq_trans : ∀ e f g : IntExpr, intEq e f → intEq f g → intEq e g := by
  intro e f g h1 h2
  cases e with | mk a b =>
  cases f with | mk c d =>
  cases g with | mk e' f' =>
  -- h1 : vadd a d = vadd b c  (intEq reduces definitionally)
  -- h2 : vadd c f' = vadd d e'
  -- goal : vadd a f' = vadd b e'
  have h1 : vadd a d = vadd b c := h1
  have h2 : vadd c f' = vadd d e' := h2
  apply vadd_cancel _ _ d
  calc vadd (vadd a f') d
      = vadd a (vadd f' d)  := T2_vadd_assoc a f' d
    _ = vadd a (vadd d f')  := congrArg (vadd a) (T1_vadd_comm f' d)
    _ = vadd (vadd a d) f'  := (T2_vadd_assoc a d f').symm
    _ = vadd (vadd b c) f'  := congrArg (fun x => vadd x f') h1
    _ = vadd b (vadd c f')  := T2_vadd_assoc b c f'
    _ = vadd b (vadd d e')  := congrArg (vadd b) h2
    _ = vadd b (vadd e' d)  := congrArg (vadd b) (T1_vadd_comm d e')
    _ = vadd (vadd b e') d  := (T2_vadd_assoc b e' d).symm

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
-- §II.3. Operations on IntExpr
-- ============================================================

-- §II.3. Addition.
-- (a ⊖ b) ⊕ (c ⊖ d) := (a + c) ⊖ (b + d)
def iadd : IntExpr → IntExpr → IntExpr
  | .mk a b, .mk c d => .mk (vadd a c) (vadd b d)

-- §II.3. Multiplication.
-- (a ⊖ b) ⊗ (c ⊖ d) := (a×c + b×d) ⊖ (a×d + b×c)
def imul : IntExpr → IntExpr → IntExpr
  | .mk a b, .mk c d => .mk (vadd (vmul a c) (vmul b d))
                             (vadd (vmul a d) (vmul b c))

-- §II.3. Additive inverse.
-- ⊖(a ⊖ b) := b ⊖ a
def ineg : IntExpr → IntExpr
  | .mk a b => .mk b a

-- §II.3. Subtraction.
-- (a ⊖ b) ⊟ (c ⊖ d) := (a + d) ⊖ (b + c)
-- Listed explicitly per preprint Remark §II.3; see isub_via_iadd_ineg below.
def isub : IntExpr → IntExpr → IntExpr
  | .mk a b, .mk c d => .mk (vadd a d) (vadd b c)

-- §II.3, Remark. Subtraction is definable through addition and additive inverse:
-- (a ⊖ b) ⊟ (c ⊖ d) = (a ⊖ b) ⊕ ⊖(c ⊖ d).
-- In Lean: isub e f = iadd e (ineg f).
-- Both sides reduce to .mk (vadd a d) (vadd b c) — rfl.
theorem isub_via_iadd_ineg : ∀ e f : IntExpr, isub e f = iadd e (ineg f)
  | .mk _ _, .mk _ _ => rfl

-- ============================================================
-- §II.4. Well-definedness of operations on ℤ_VR
-- ============================================================

-- Private helper: shuffle law for vadd.
-- (a + b) + (c + d) = (a + c) + (b + d).
-- Used in well-definedness proofs and vmul_distrib_right.
private theorem vadd_swap (a b c d : VRObj) :
    vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d) :=
  calc vadd (vadd a b) (vadd c d)
      = vadd a (vadd b (vadd c d))   := T2_vadd_assoc a b (vadd c d)
    _ = vadd a (vadd (vadd b c) d)   := congrArg (vadd a) (T2_vadd_assoc b c d).symm
    _ = vadd a (vadd (vadd c b) d)   :=
          congrArg (vadd a) (congrArg (fun x => vadd x d) (T1_vadd_comm b c))
    _ = vadd a (vadd c (vadd b d))   := congrArg (vadd a) (T2_vadd_assoc c b d)
    _ = vadd (vadd a c) (vadd b d)   := (T2_vadd_assoc a c (vadd b d)).symm

-- §II.3 (implicit). Left (right-argument) distributivity of vmul.
-- (a + b) × c = a×c + b×c.
-- T3_vmul_distrib gives RIGHT distributivity: a × (b + c) = a×b + a×c.
-- Left distributivity requires induction; surfaces here as an explicit lemma.
-- Methodological note: absence from T1–T4 parallels vadd_cancel in §II.2;
-- candidate for VR-Numbers §VIII.
theorem vmul_distrib_right : ∀ a b c : VRObj,
    vmul (vadd a b) c = vadd (vmul a c) (vmul b c) := by
  intro a b c
  induction c with
  | mark      => rfl
  | succ d ih =>
    change vadd (vmul (vadd a b) d) (vadd a b) =
           vadd (vadd (vmul a d) a) (vadd (vmul b d) b)
    rw [ih]
    exact vadd_swap (vmul a d) (vmul b d) a b

-- §II.4. Well-definedness — additive inverse.
-- ineg respects intEq: if e ~ f then ineg e ~ ineg f.
-- Proof: swap the two components; h.symm closes the goal.
theorem ineg_respects : ∀ e f : IntExpr, intEq e f → intEq (ineg e) (ineg f)
  | .mk _ _, .mk _ _, h =>
    -- h    : vadd a b' = vadd b a'
    -- goal : vadd b a' = vadd a b'
    h.symm

-- §II.4. Well-definedness — addition.
-- iadd respects intEq: if e₁ ~ f₁ and e₂ ~ f₂ then iadd e₁ e₂ ~ iadd f₁ f₂.
-- h1 : vadd a b' = vadd b a'
-- h2 : vadd c d' = vadd d c'
-- goal : vadd (vadd a c) (vadd b' d') = vadd (vadd b d) (vadd a' c')
-- Proof: vadd_swap reshuffles both sides; congrArg₂ substitutes h1, h2 in the middle.
theorem iadd_respects : ∀ (e₁ f₁ e₂ f₂ : IntExpr),
    intEq e₁ f₁ → intEq e₂ f₂ → intEq (iadd e₁ e₂) (iadd f₁ f₂)
  | .mk a b, .mk a' b', .mk c d, .mk c' d', h1, h2 =>
    calc vadd (vadd a c) (vadd b' d')
        = vadd (vadd a b') (vadd c d')   := vadd_swap a c b' d'
      _ = vadd (vadd b a') (vadd c d')   := congrArg (fun x => vadd x _) h1
      _ = vadd (vadd b a') (vadd d c')   := congrArg (vadd _) h2
      _ = vadd (vadd b d) (vadd a' c')   := vadd_swap b a' d c'

-- §II.4. Well-definedness — multiplication, left factor.
-- Fix second arg (.mk c d); vary first from (.mk a b) to (.mk a' b').
-- h1 : vadd a b' = vadd b a'
-- Key: multiply h1 on the right by c and d using vmul_distrib_right.
private theorem imul_left_respects :
    ∀ (a b a' b' c d : VRObj), vadd a b' = vadd b a' →
    intEq (imul (.mk a b) (.mk c d)) (imul (.mk a' b') (.mk c d)) := by
  intro a b a' b' c d h1
  -- derive: (a×c + b'×c = b×c + a'×c) and (a×d + b'×d = b×d + a'×d)
  have hc : vadd (vmul a c) (vmul b' c) = vadd (vmul b c) (vmul a' c) :=
    (vmul_distrib_right a b' c).symm.trans
      ((congrArg (fun x => vmul x c) h1).trans (vmul_distrib_right b a' c))
  have hd : vadd (vmul a d) (vmul b' d) = vadd (vmul b d) (vmul a' d) :=
    (vmul_distrib_right a b' d).symm.trans
      ((congrArg (fun x => vmul x d) h1).trans (vmul_distrib_right b a' d))
  -- goal : vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul a' d) (vmul b' c))
  --      = vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul a' c) (vmul b' d))
  calc vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul a' d) (vmul b' c))
      = vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul b' c) (vmul a' d)) :=
            congrArg (vadd _) (T1_vadd_comm _ _)
    _ = vadd (vadd (vmul a c) (vmul b' c)) (vadd (vmul b d) (vmul a' d)) :=
            vadd_swap _ _ _ _
    _ = vadd (vadd (vmul b c) (vmul a' c)) (vadd (vmul b d) (vmul a' d)) :=
            congrArg (fun x => vadd x _) hc
    _ = vadd (vadd (vmul b c) (vmul a' c)) (vadd (vmul a d) (vmul b' d)) :=
            congrArg (vadd _) hd.symm
    _ = vadd (vadd (vmul b c) (vmul a d)) (vadd (vmul a' c) (vmul b' d)) :=
            vadd_swap _ _ _ _
    _ = vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul a' c) (vmul b' d)) :=
            congrArg (fun x => vadd x _) (T1_vadd_comm _ _)

-- §II.4. Well-definedness — multiplication, right factor.
-- Fix first arg (.mk a b); vary second from (.mk c d) to (.mk c' d').
-- h2 : vadd c d' = vadd d c'
-- Key: multiply h2 on the left by a and b using T3_vmul_distrib.
private theorem imul_right_respects :
    ∀ (a b c d c' d' : VRObj), vadd c d' = vadd d c' →
    intEq (imul (.mk a b) (.mk c d)) (imul (.mk a b) (.mk c' d')) := by
  intro a b c d c' d' h2
  -- derive: (a×c + a×d' = a×d + a×c') and (b×c + b×d' = b×d + b×c')
  have ha : vadd (vmul a c) (vmul a d') = vadd (vmul a d) (vmul a c') :=
    (T3_vmul_distrib a c d').symm.trans
      ((congrArg (vmul a) h2).trans (T3_vmul_distrib a d c'))
  have hb : vadd (vmul b c) (vmul b d') = vadd (vmul b d) (vmul b c') :=
    (T3_vmul_distrib b c d').symm.trans
      ((congrArg (vmul b) h2).trans (T3_vmul_distrib b d c'))
  -- goal : vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul a d') (vmul b c'))
  --      = vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul a c') (vmul b d'))
  calc vadd (vadd (vmul a c) (vmul b d)) (vadd (vmul a d') (vmul b c'))
      = vadd (vadd (vmul a c) (vmul a d')) (vadd (vmul b d) (vmul b c')) :=
            vadd_swap _ _ _ _
    _ = vadd (vadd (vmul a d) (vmul a c')) (vadd (vmul b d) (vmul b c')) :=
            congrArg (fun x => vadd x _) ha
    _ = vadd (vadd (vmul a d) (vmul a c')) (vadd (vmul b c) (vmul b d')) :=
            congrArg (vadd _) hb.symm
    _ = vadd (vadd (vmul a d) (vmul b c)) (vadd (vmul a c') (vmul b d')) :=
            vadd_swap _ _ _ _

-- §II.4. Well-definedness — multiplication.
-- Chain imul_left_respects and imul_right_respects via intEq_trans.
theorem imul_respects : ∀ (e₁ f₁ e₂ f₂ : IntExpr),
    intEq e₁ f₁ → intEq e₂ f₂ → intEq (imul e₁ e₂) (imul f₁ f₂) := by
  intro e₁ f₁ e₂ f₂ h1 h2
  cases e₁ with | mk a b =>
  cases f₁ with | mk a' b' =>
  cases e₂ with | mk c d =>
  cases f₂ with | mk c' d' =>
  have h1 : vadd a b' = vadd b a' := h1
  have h2 : vadd c d' = vadd d c' := h2
  exact intEq_trans _ _ _
    (imul_left_respects a b a' b' c d h1)
    (imul_right_respects a' b' c d c' d' h2)

-- §II.4. Well-definedness — subtraction.
-- Reduces to iadd_respects + ineg_respects via isub_via_iadd_ineg.
theorem isub_respects : ∀ (e₁ f₁ e₂ f₂ : IntExpr),
    intEq e₁ f₁ → intEq e₂ f₂ → intEq (isub e₁ e₂) (isub f₁ f₂) := by
  intro e₁ f₁ e₂ f₂ h1 h2
  rw [isub_via_iadd_ineg, isub_via_iadd_ineg]
  exact iadd_respects e₁ f₁ (ineg e₂) (ineg f₂) h1 (ineg_respects e₂ f₂ h2)

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
  fun n => Quotient.mk intEqSetoid (.mk n VRObj.mark)

-- ============================================================
-- §II.4. Canonical form
-- ============================================================

-- §II.4. Auxiliary: for any two VRObj, one is a vadd-extension of the other.
-- Constructive totality of the natural order: either b ≤ a or a ≤ b.
-- Proof: induction on a. The hard case (succ a', right IH, n = succ m)
-- requires vadd_succ_left to build the right witness.
private theorem vadd_comparable : ∀ a b : VRObj,
    (∃ n : VRObj, vadd b n = a) ∨ (∃ n : VRObj, vadd a n = b) := by
  intro a
  induction a with
  | mark =>
    intro b
    -- right branch: vadd mark b = b (vadd_zero_left)
    exact Or.inr ⟨b, vadd_zero_left b⟩
  | succ a' iha =>
    intro b
    cases iha b with
    | inl h =>
      obtain ⟨n, hn⟩ := h
      -- hn : vadd b n = a'; take n' := succ n for succ a'
      exact Or.inl ⟨VRObj.succ n, congrArg VRObj.succ hn⟩
    | inr h =>
      obtain ⟨n, hn⟩ := h
      -- hn : vadd a' n = b; split on n
      cases n with
      | mark =>
        -- vadd a' mark = a' = b; left: vadd b (succ mark) = succ b = succ a'
        exact Or.inl ⟨VRObj.succ VRObj.mark, congrArg VRObj.succ hn.symm⟩
      | succ m =>
        -- hn : vadd a' (succ m) = b; right: vadd (succ a') m = succ (vadd a' m) = b
        exact Or.inr ⟨m, (vadd_succ_left a' m).trans hn⟩

-- §II.4. Canonical form theorem.
-- Every element of ℤ_VR has a representative of the form (n ⊖ ∅) or (∅ ⊖ n).
-- Both branches cover zero (n = mark in either gives .mk mark mark).
-- Proof: vadd_comparable gives the witness; intEq closes definitionally.
theorem canonical_form : ∀ e : IntExpr,
    (∃ n : VRObj, intEq e (.mk n VRObj.mark)) ∨
    (∃ n : VRObj, intEq e (.mk VRObj.mark n))
  | .mk a b =>
    (vadd_comparable a b).imp
      (fun ⟨n, hn⟩ => ⟨n, hn.symm⟩)
      (fun ⟨n, hn⟩ => ⟨n, hn⟩)

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
  | Int.ofNat n   => Quotient.mk intEqSetoid (.mk (O n) VRObj.mark)
  | Int.negSucc n => Quotient.mk intEqSetoid (.mk VRObj.mark (O (n + 1)))

-- §II.6. Right inverse: forward ∘ backward = id on ℤ.
-- Case ofNat n: forward (backward n) = O_inv (O n) - O_inv mark = n - 0 = n.
-- Case negSucc n: forward (backward (−(n+1))) = O_inv mark - O_inv (O (n+1)) = 0 − (n+1).
-- Both branches close by O_left_inv + omega (for the cast arithmetic).
-- O_inv VRObj.mark = 0 by definition (first equation of O_inv).
-- Not a consequence of O_left_inv (which rewrites O_inv (O n)); needed separately.
private theorem O_inv_void : O_inv VRObj.mark = 0 := rfl

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
    intEq (.mk a b) (.mk (O n) VRObj.mark) := by
  have key : O_inv (vadd b (O n)) = O_inv a := by
    rw [O_inv_vadd, O_left_inv]; exact hn
  have heq : vadd b (O n) = a := by
    have h := congrArg O key; rwa [O_right_inv, O_right_inv] at h
  -- goal: vadd a VRObj.mark = vadd b (O n)
  change vadd a VRObj.mark = vadd b (O n)
  rw [T1_vadd_comm a VRObj.mark, vadd_zero_left a]
  exact heq.symm

-- §II.6. Helper: (a ⊖ b) ~ (∅ ⊖ O n) when O_inv a + n = O_inv b.
-- Mirror of intEq_nonneg: the deficit goes to the right component.
private theorem intEq_neg (a b : VRObj) (n : Nat) (hn : O_inv a + n = O_inv b) :
    intEq (.mk a b) (.mk VRObj.mark (O n)) := by
  have key : O_inv (vadd a (O n)) = O_inv b := by
    rw [O_inv_vadd, O_left_inv]; exact hn
  have heq : vadd a (O n) = b := by
    have h := congrArg O key; rwa [O_right_inv, O_right_inv] at h
  -- intEq (.mk a b) (.mk VRObj.mark (O n)) unfolds to vadd a (O n) = vadd b VRObj.mark
  -- (intEq .mk a b .mk c d  =  vadd a d = vadd b c; here c = mark, d = O n)
  change vadd a (O n) = vadd b VRObj.mark
  rw [T1_vadd_comm b VRObj.mark, vadd_zero_left b]
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
    -- backward unfolds to (.mk VRObj.mark (O (... - 1 + 1))); fold the ±1 back
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
-- 1_ℤ = class of (succ mark ⊖ mark) = embedN (succ mark).
def one_Z : ℤ_VR := embedN (VRObj.succ VRObj.mark)

-- §II.6. forward maps one_Z to integer 1.
-- Proof: forwardExpr (.mk (succ mark) mark) = O_inv (succ mark) - O_inv mark = 1 - 0 = 1.
theorem forward_one_Z : forward one_Z = 1 := by
  simp only [one_Z, embedN, forward, Quotient.lift_mk, forwardExpr, O_inv]
  omega

end VR.Numbers
