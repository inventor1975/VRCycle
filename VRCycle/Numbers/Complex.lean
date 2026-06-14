-- VR-Numbers: Complex ℂ_VR (DOI 10.5281/zenodo.20272743)
-- Part V. Complex Numbers ℂ.

import VRCycle.Numbers.Reals
import Mathlib.Data.Complex.Basic

namespace VR.Numbers
open VR

-- ============================================================
-- §V.4. Type ComplexVR
-- ============================================================

-- A complex number ℂ_VR is a formal expression a ⊕ b·i (a, b ∈ ℝ_VR) — a
-- two-component structure over ℝ_VR (a real and an imaginary part), built without
-- posited ordered pairs.
--
-- TWO-DIMENSIONALITY. ℂ_VR carries two real components: a real part (along which
-- ℕ → ℤ → ℚ → ℝ_VR unfolds) and an imaginary part, where expressions b·i live (i is
-- a syntactic marker of which component a value belongs to, not a number and not an
-- object). The two-dimensionality is simply the construction's two components; it is
-- not derived from anything more primitive.
--
-- (Versions through v1.1.0 ascribed the two components to a "duality of A1" — the
-- propositional implications F→F / F→⊤ of the VR formal system. VR v1.1.1 removed the
-- propositional layer entirely, so that grounding is withdrawn: it was an over-claim,
-- and even then i²=⊖1 was a separate postulate, so A1 gave a coincidence of count, not
-- a derivation. ℂ is the standard two-component construction.)
--
-- ALGEBRA. The two components are coupled by the joining postulate
--   i ⊗ i := ⊖1
-- encoded in cmul via the term ⊖(b⊗d) in the fst-component of the product. Without it
-- ℂ_VR is two independent copies of ℝ_VR; with it — an algebraic field.
structure ComplexVR where
  fst : ℝ_VR  -- real component
  snd : ℝ_VR  -- imaginary component

notation "ℂ_VR" => ComplexVR

-- ============================================================
-- §V.4 / auxiliary: zero constant of ℝ_VR
-- ============================================================

-- Zero of ℝ_VR: image of zero of ℚ_VR under the embedding.
-- Used in czero, cone, embedR, cconj.
def zero_R : ℝ_VR := embedQ zero_Q

-- ============================================================
-- §V.4. Constants and embedding
-- ============================================================

-- §V.4. Additive zero of ℂ_VR: 0 ⊕ 0·i.
def czero : ℂ_VR := ⟨zero_R, zero_R⟩

-- §V.4. Multiplicative unit of ℂ_VR: 1 ⊕ 0·i.
def cone : ℂ_VR := ⟨embedQ (embedZ one_Z), zero_R⟩

-- §V.7. Embedding ℝ_VR → ℂ_VR: a ↦ a ⊕ 0·i.
-- Every real a ∈ ℝ_VR embeds with zero imaginary part.
def embedR (a : ℝ_VR) : ℂ_VR := ⟨a, zero_R⟩

-- ============================================================
-- §V.6. Operations on ℂ_VR
-- ============================================================

-- §V.6. Addition: (a⊕b·i) ⊕_ℂ (c⊕d·i) := (a⊕c) ⊕ (b⊕d)·i.
def cadd (p q : ℂ_VR) : ℂ_VR :=
  ⟨realAdd p.fst q.fst, realAdd p.snd q.snd⟩

-- §V.6. Multiplication (joining rule i⊗i = ⊖1):
-- (a⊕b·i) ⊗_ℂ (c⊕d·i) := (a⊗c ⊖ b⊗d) ⊕ (a⊗d ⊕ b⊗c)·i.
-- The term ⊖(b⊗d) in fst is a direct consequence of i⊗i=⊖1 (§V.3).
def cmul (p q : ℂ_VR) : ℂ_VR :=
  ⟨realSub (realMul p.fst q.fst) (realMul p.snd q.snd),
   realAdd (realMul p.fst q.snd) (realMul p.snd q.fst)⟩

-- §V.6. Conjugation: conj(a⊕b·i) := a ⊕ (⊖b)·i.
def cconj (p : ℂ_VR) : ℂ_VR :=
  ⟨p.fst, realSub zero_R p.snd⟩

-- Subtraction (derived operation): (a⊕b·i) ⊖_ℂ (c⊕d·i) := (a⊖c) ⊕ (b⊖d)·i.
def csub (p q : ℂ_VR) : ℂ_VR :=
  ⟨realSub p.fst q.fst, realSub p.snd q.snd⟩

-- ============================================================
-- §V.8 / auxiliary: bijection ℂ_VR ↔ ℂ
-- ============================================================

-- §V.8. Forward map ℂ_VR → ℂ: applies forwardR componentwise.
-- ℂ_VR is not a quotient type (§V.5 — trivial equivalence),
-- so forwardC is a direct structure constructor, without Quotient.lift.
def forwardC (p : ℂ_VR) : ℂ := ⟨forwardR p.fst, forwardR p.snd⟩

-- §V.8. Backward map ℂ → ℂ_VR: applies backwardR componentwise.
def backwardC (z : ℂ) : ℂ_VR := ⟨backwardR z.re, backwardR z.im⟩

-- §V.8. forwardC is a right inverse of backwardC:
-- forwardC (backwardC z) = z.
theorem forwardC_right_inv (z : ℂ) : forwardC (backwardC z) = z :=
  Complex.ext (forwardR_right_inv z.re) (forwardR_right_inv z.im)

-- §V.8. backwardC is a right inverse of forwardC:
-- backwardC (forwardC p) = p.
theorem forwardC_left_inv (p : ℂ_VR) : backwardC (forwardC p) = p := by
  cases p with
  | mk a b => simp only [forwardC, backwardC, forwardR_left_inv]

-- ============================================================
-- §V.8 / auxiliary: bridge theorems (fR_*) for syntactic rw-compatibility
-- ============================================================

-- The theorems below expose forwardR syntactically, using fields of
-- Theorem_IV_7_RealVR_Real. This is needed because a structure field
-- (e.g. Theorem_IV_7_RealVR_Real.preserveAdd) is definitionally equal
-- to the forwardR lemma, but rw requires syntactic matching.

private theorem fR_add (p q : ℝ_VR) :
    forwardR (realAdd p q) = forwardR p + forwardR q :=
  Theorem_IV_7_RealVR_Real.preserveAdd p q

private theorem fR_sub (p q : ℝ_VR) :
    forwardR (realSub p q) = forwardR p - forwardR q :=
  Theorem_IV_7_RealVR_Real.preserveSub p q

private theorem fR_mul (p q : ℝ_VR) :
    forwardR (realMul p q) = forwardR p * forwardR q :=
  Theorem_IV_7_RealVR_Real.preserveMul p q

private theorem fR_zero : forwardR zero_R = 0 :=
  Theorem_IV_7_RealVR_Real.preserveZero

private theorem fR_one : forwardR (embedQ (embedZ one_Z)) = 1 :=
  Theorem_IV_7_RealVR_Real.preserveOne

-- ============================================================
-- §V.8. Isomorphism structure ℂ_VR ≅ ℂ
-- ============================================================

-- §V.8. Isomorphism record ℂ_VR ≅ ℂ: bijection + 5 operation-preservation fields.
-- Mirrors the structure of RealVRRealIso (§IV.7), lifted to the level of ℂ.
structure ComplexVRComplexIso where
  forward : ℂ_VR → ℂ
  backward : ℂ → ℂ_VR
  right_inv : ∀ z, forward (backward z) = z
  left_inv : ∀ w, backward (forward w) = w
  preserveZero : forward czero = 0
  preserveOne : forward cone = 1
  preserveAdd : ∀ p q, forward (cadd p q) = forward p + forward q
  preserveMul : ∀ p q, forward (cmul p q) = forward p * forward q
  preserveConj : ∀ p, forward (cconj p) = star (forward p)

-- ============================================================
-- §V.8. Theorem V.8: ℂ_VR ≅ ℂ
-- ============================================================

-- §V.8. Main theorem: ℂ_VR is isomorphic to ℂ as an algebraic field
-- with conjugation involution. Proof is componentwise via forwardC.
def Theorem_V_8_ComplexVR_Complex : ComplexVRComplexIso where
  forward  := forwardC
  backward := backwardC
  right_inv := forwardC_right_inv
  left_inv  := forwardC_left_inv
  preserveZero := Complex.ext fR_zero fR_zero
  preserveOne  := Complex.ext fR_one fR_zero
  preserveAdd  := fun p q => Complex.ext
    (fR_add p.fst q.fst) (fR_add p.snd q.snd)
  preserveMul  := fun p q => by
    apply Complex.ext
    · simp only [forwardC, cmul, Complex.mul_re]
      rw [fR_sub, fR_mul, fR_mul]
    · simp only [forwardC, cmul, Complex.mul_im]
      rw [fR_add, fR_mul, fR_mul]
  preserveConj := fun p => by
    apply Complex.ext
    · simp only [forwardC, cconj, Complex.star_def, Complex.conj_re]
    · simp only [forwardC, cconj, Complex.star_def, Complex.conj_im]
      rw [fR_sub, fR_zero, zero_sub]

-- ============================================================
-- §V.9. Derived operations: cabs, cdiv
-- ============================================================

-- §V.9. Modulus ℂ_VR → ℝ_VR: via forwardC and Real.sqrt (Complex.normSq).
-- Parallel to realDiv (§IV): defined through the isomorphism.
noncomputable def cabs (p : ℂ_VR) : ℝ_VR :=
  backwardR (Real.sqrt (Complex.normSq (forwardC p)))

-- §V.9. Division on ℂ_VR: via forwardC and division in ℂ.
noncomputable def cdiv (p q : ℂ_VR) : ℂ_VR :=
  backwardC (forwardC p / forwardC q)

-- §V.9. Preservation of modulus: forwardR (cabs p) = √(normSq (forwardC p)).
theorem preserveAbs (p : ℂ_VR) :
    forwardR (cabs p) = Real.sqrt (Complex.normSq (forwardC p)) :=
  forwardR_right_inv _

-- §V.9. Preservation of division: forwardC (cdiv p q) = forwardC p / forwardC q.
theorem preserveDiv (p q : ℂ_VR) :
    forwardC (cdiv p q) = forwardC p / forwardC q :=
  forwardC_right_inv _

end VR.Numbers
