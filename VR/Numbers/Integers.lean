-- VR-Numbers: Integers ℤ_VR (DOI 10.5281/zenodo.20272743)
-- Part II. Integers ℤ as an Operational Superstructure.

import VR.Arithmetic
-- Mathlib imported for §II.6 only: ring and push_cast tactics for the
-- isomorphism theorem. All prior definitions (IntExpr, intEq, operations,
-- canonical form) are independent of mathlib. Per PLAN.md principle 1.

namespace VR.Numbers

open VR

-- ============================================================
-- §II.1. The Formal Language of Subtraction
-- ============================================================

-- §II.1. The Formal Language of Subtraction.
-- An expression a ⊖ b is a syntactic record of the operation
-- "subtract b from a", where a, b ∈ Nat (= VRObj in VR).
--
-- §VI.5, item 1: pairs appear nowhere as independent primitive objects.
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
-- using the addition operation already defined on Nat (= vadd on VRObj).
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
  | base      => exact h
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
  | base      => rfl
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
  | base =>
    intro b
    -- right branch: vadd base b = b (vadd_zero_left)
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
      | base =>
        -- vadd a' base = a' = b; left: vadd b (succ base) = succ b = succ a'
        exact Or.inl ⟨VRObj.succ VRObj.base, congrArg VRObj.succ hn.symm⟩
      | succ m =>
        -- hn : vadd a' (succ m) = b; right: vadd (succ a') m = succ (vadd a' m) = b
        exact Or.inr ⟨m, (vadd_succ_left a' m).trans hn⟩

-- §II.4. Canonical form theorem.
-- Every element of ℤ_VR has a representative of the form (n ⊖ ∅) or (∅ ⊖ n).
-- Both branches cover zero (n = base in either gives .mk base base).
-- Proof: vadd_comparable gives the witness; intEq closes definitionally.
theorem canonical_form : ∀ e : IntExpr,
    (∃ n : VRObj, intEq e (.mk n VRObj.base)) ∨
    (∃ n : VRObj, intEq e (.mk VRObj.base n))
  | .mk a b =>
    (vadd_comparable a b).imp
      (fun ⟨n, hn⟩ => ⟨n, hn.symm⟩)
      (fun ⟨n, hn⟩ => ⟨n, hn⟩)

end VR.Numbers
