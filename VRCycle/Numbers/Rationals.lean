-- VR-Numbers: Rationals ℚ_VR (DOI 10.5281/zenodo.20272743)
-- Part III. Rationals ℚ as an Operational Superstructure.

import VRCycle.Numbers.Integers
-- Mathlib.Tactic is transitively available via Numbers.Integers.

namespace VR.Numbers
open VR

-- ============================================================
-- §III.0. Infrastructure: zero element and DecidableEq for ℤ_VR
-- ============================================================

-- §II.5 / §III.1. Zero element of ℤ_VR.
-- 0_ℤ = class of (0 ⊖ 0) = embedN base
-- (§II.5: natural n embeds as class of n ⊖ 0; for n = 0 this is 0 ⊖ 0).
def zero_Z : ℤ_VR := embedN VRObj.base

-- §III.1. forward maps zero_Z to integer 0.
-- Proof: forwardExpr (.mk base base) = (O_inv base : Int) - O_inv base = 0 - 0.
-- Used in eq_zero_Z_iff and instDecidableEqIntVR.
theorem forward_zero_Z : forward zero_Z = 0 := by
  simp only [zero_Z, embedN, forward, Quotient.lift_mk, forwardExpr]
  omega

-- Private bridge: backward 0 = zero_Z.
-- backward (Int.ofNat 0) = ⟦.mk (O 0) base⟧ = ⟦.mk base base⟧ = zero_Z.
-- (O 0 = base definitionally; zero_Z = embedN base = ⟦.mk base base⟧.)
private theorem backward_zero : backward 0 = zero_Z := by
  simp [backward, zero_Z, embedN]
  -- ⊢ ⟦.mk (O 0) base⟧ = ⟦.mk base base⟧; close by O 0 = base (definitional)
  rfl

-- §III.1. Equality with zero_Z ↔ forward value is 0.
-- Preprint §III.1: «effectively decidable via canonical form in ℤ_VR».
-- The preprint suggests an internal route through canonical_form (7.7).
-- We use the isomorphism (7.9) as an equivalent and shorter route:
-- z = zero_Z iff forward z = 0, using injectivity from left_inv_int.
-- Both routes yield the same result; the isomorphism is operationally shorter.
theorem eq_zero_Z_iff (z : ℤ_VR) : z = zero_Z ↔ forward z = 0 :=
  ⟨fun h => h ▸ forward_zero_Z,
   fun h => (left_inv_int z).symm.trans ((congrArg backward h).trans backward_zero)⟩

-- §III.0 / §III.1. one_Z ≠ zero_Z: multiplicative identity is not zero.
-- Used as the default denominator for zero_Q and future ring axioms.
-- Proof: forward one_Z = 1 ≠ 0 = forward zero_Z; injectivity (eq_zero_Z_iff) closes.
theorem one_ne_zero_Z : one_Z ≠ zero_Z := by
  intro h
  have : forward one_Z = forward zero_Z := congrArg forward h
  simp only [forward_one_Z, forward_zero_Z] at this
  exact absurd this (by omega)

-- §III.1. DecidableEq on ℤ_VR via the bijection with Int.
-- z₁ = z₂  ↔  forward z₁ = forward z₂  (injectivity: left_inv_int).
-- Decidability of (forward z₁ = forward z₂) comes from DecidableEq Int (Lean core).
instance instDecidableEqIntVR : DecidableEq ℤ_VR :=
  fun z1 z2 =>
    if h : forward z1 = forward z2 then
      isTrue (by have h1 := congrArg backward h; rwa [left_inv_int, left_inv_int] at h1)
    else
      isFalse (fun heq => h (congrArg forward heq))

-- ============================================================
-- §III.1. The Formal Language of Division
-- ============================================================

-- §III.1. RatExpr — syntactic record of a ⊘ b, where a, b ∈ ℤ_VR.
-- Not an ordered pair (§VI.5, item 1); access exclusively via pattern matching:
--   match e with | .mk a b => ...
-- The constraint b ≠ 0_ℤ is not embedded in the type; see NonZeroRatExpr below.
-- Operational note (§VI.4): RatExpr is a finite syntactic operation over ℤ_VR,
-- which is itself a finite syntactic operation over ℕ (= VRObj). Depth 2 over ∅.
inductive RatExpr : Type where
  | mk : ℤ_VR → ℤ_VR → RatExpr

-- §III.1. Positional accessors — neutral names at the level of §III.1,
-- where a ⊘ b is purely syntactic («numerator/denominator» terminology
-- is premature here; it is justified only after canonical form §III.4).
-- fst = a,  snd = b  in the expression a ⊘ b.
def RatExpr.fst : RatExpr → ℤ_VR | .mk a _ => a
def RatExpr.snd : RatExpr → ℤ_VR | .mk _ b => b

-- §III.1. Subtype of RatExpr with nonzero second component.
-- The constraint b ≠ 0_ℤ is «syntactic and effectively decidable» (§III.1):
-- decidability comes from instDecidableEqIntVR above.
-- This subtype is the domain of ratEq and the Setoid (§III.2 and §III.4).
abbrev NonZeroRatExpr := {e : RatExpr // e.snd ≠ zero_Z}

-- ============================================================
-- §III.2. Rational equivalence ratEq
-- ============================================================

-- Private bridge: z ≠ zero_Z implies forward z ≠ 0.
-- Via eq_zero_Z_iff: forward z = 0 ↔ z = zero_Z.
private theorem forward_ne_zero {z : ℤ_VR} (h : z ≠ zero_Z) : forward z ≠ 0 :=
  fun hf => h ((eq_zero_Z_iff z).mpr hf)

-- ============================================================
-- §III.3 Infrastructure: zero absorption and integral domain for ℤ_VR.
-- Needed for well-typed denominators in rational operations.
-- ============================================================

-- imulQ b zero_Z = zero_Z.
-- Via forward_injective: forward (imulQ b zero_Z) = forward b * 0 = 0.
-- Uses ring (not mul_zero: the mul_zero lemma pulls Classical.choice via mathlib's Ring instance).
theorem imulQ_zero_right (b : ℤ_VR) : imulQ b zero_Z = zero_Z :=
  forward_injective (by simp only [preserve_mul_int, forward_zero_Z]; ring)

-- imulQ zero_Z b = zero_Z.
theorem imulQ_zero_left (b : ℤ_VR) : imulQ zero_Z b = zero_Z :=
  (imulQ_comm zero_Z b).trans (imulQ_zero_right b)

-- Private helper: Int has no zero divisors (Classical-free via Int.mul_eq_zero).
private theorem Int_mul_ne_zero {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  fun h => (Int.mul_eq_zero.mp h).elim ha hb

-- §III.3. ℤ_VR has no zero divisors: a ≠ zero_Z → b ≠ zero_Z → imulQ a b ≠ zero_Z.
-- Proof: forward (imulQ a b) = forward a * forward b ≠ 0 (Int_mul_ne_zero), hence ≠ zero_Z.
theorem imulQ_ne_zero {a b : ℤ_VR} (ha : a ≠ zero_Z) (hb : b ≠ zero_Z) :
    imulQ a b ≠ zero_Z := by
  intro h
  have key : forward a * forward b = 0 := by
    have := congrArg forward h
    simp only [preserve_mul_int, forward_zero_Z] at this
    exact this
  exact Int_mul_ne_zero (forward_ne_zero ha) (forward_ne_zero hb) key

-- §III.2. ratEq — the equivalence relation on NonZeroRatExpr.
-- a ⊘ b ~ c ⊘ d  iff  a ⊗ d = b ⊗ c  (cross-multiplication, §III.2).
-- Defined on the subtype NonZeroRatExpr; the nonzero condition is used in ratEq_trans.
def ratEq (e f : NonZeroRatExpr) : Prop :=
  match e.1, f.1 with
  | .mk a b, .mk c d => imulQ a d = imulQ b c

-- §III.2. ratEq is reflexive: a ⊗ b = b ⊗ a by imulQ_comm.
theorem ratEq_refl (e : NonZeroRatExpr) : ratEq e e := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  simp only [ratEq, imulQ_comm]

-- §III.2. ratEq is symmetric: a ⊗ d = b ⊗ c → c ⊗ b = d ⊗ a.
theorem ratEq_symm {e f : NonZeroRatExpr} (h : ratEq e f) : ratEq f e := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨c, d⟩, _⟩ := f
  simp only [ratEq] at h ⊢
  -- goal: imulQ c b = imulQ d a; h: imulQ a d = imulQ b c
  rw [imulQ_comm c b, ← imulQ_comm a d]
  exact h.symm

-- §III.2. Auxiliary: integer right-cancellation without Classical.choice.
-- Avoids mul_right_cancel₀ (pulls in Classical via mathlib's IntegralDomain instance).
-- Route: (a-b)*c = 0 → natAbs(a-b)*natAbs(c) = 0 → natAbs(a-b) = 0 → a = b.
-- All steps use only: Int.natAbs_mul (core), Int.natAbs_eq_zero (core),
-- Nat.mul_eq_zero (core), sub_eq_zero (propext only).
-- Axioms: [propext, Quot.sound]  (no Classical.choice).
private theorem Int_mul_right_cancel {a b c : Int} (hc : c ≠ 0)
    (h : a * c = b * c) : a = b := by
  have hdiff : (a - b) * c = 0 :=
    (show (a - b) * c = a * c - b * c from by ring).trans (sub_eq_zero.mpr h)
  have hna : Int.natAbs (a - b) * Int.natAbs c = 0 := by
    have key := Int.natAbs_mul (a - b) c
    rw [hdiff] at key; exact key.symm
  have hc0 : Int.natAbs c ≠ 0 := fun h0 => hc (Int.natAbs_eq_zero.mp h0)
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp ((Nat.mul_eq_zero.mp hna).resolve_right hc0))

-- §III.2. ratEq is transitive.
-- Strategy: lift to Int via forward, cancel common factor (forward d ≠ 0) via
-- Int_mul_right_cancel (Classical-free), close the Int identity by manual factoring.
theorem ratEq_trans {e f g : NonZeroRatExpr}
    (h1 : ratEq e f) (h2 : ratEq f g) : ratEq e g := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨c, d⟩, hd⟩ := f
  obtain ⟨⟨p, q⟩, _⟩ := g
  -- Reduce hd from (RatExpr.mk c d).snd ≠ zero_Z to d ≠ zero_Z.
  simp only [RatExpr.snd] at hd
  simp only [ratEq] at h1 h2 ⊢
  apply forward_injective
  apply Int_mul_right_cancel (forward_ne_zero hd)
  simp only [preserve_mul_int]
  have H1 : forward a * forward d = forward b * forward c := by
    have := congrArg forward h1; simp only [preserve_mul_int] at this; exact this
  have H2 : forward c * forward q = forward d * forward p := by
    have := congrArg forward h2; simp only [preserve_mul_int] at this; exact this
  -- Close via manual factoring instead of linear_combination (which pulls Classical.choice).
  -- Goal: forward a * forward q * forward d = forward b * forward p * forward d.
  have step : forward a * forward q * forward d - forward b * forward p * forward d = 0 := by
    have e1 := sub_eq_zero.mpr H1
    have e2 := sub_eq_zero.mpr H2
    have factored : forward a * forward q * forward d - forward b * forward p * forward d =
        forward q * (forward a * forward d - forward b * forward c) +
        forward b * (forward c * forward q - forward d * forward p) := by ring
    rw [factored, e1, e2]; ring
  exact sub_eq_zero.mp step

-- §III.3. Nonzero numerator is invariant under ratEq.
-- If e ~ f then e.fst ≠ zero_Z ↔ f.fst ≠ zero_Z.
-- Needed for well-definedness of iratDiv (8.6).
-- Proof: use imulQ_ne_zero + zero-absorption to derive contradiction in each direction.
theorem ratEq_preserves_nonzero_num {e f : NonZeroRatExpr} (h : ratEq e f) :
    e.1.fst ≠ zero_Z ↔ f.1.fst ≠ zero_Z := by
  obtain ⟨⟨a, b⟩, hb⟩ := e
  obtain ⟨⟨c, d⟩, hd⟩ := f
  simp only [RatExpr.snd] at hb hd
  simp only [RatExpr.fst]
  simp only [ratEq] at h
  -- h : imulQ a d = imulQ b c
  constructor
  · intro ha hc
    -- c = zero_Z → imulQ b c = zero_Z → imulQ a d = zero_Z, contradicts imulQ_ne_zero ha hd
    rw [hc, imulQ_zero_right] at h
    exact imulQ_ne_zero ha hd h
  · intro hc ha
    -- a = zero_Z → imulQ a d = zero_Z → imulQ b c = zero_Z, contradicts imulQ_ne_zero hb hc
    rw [ha, imulQ_zero_left] at h
    exact imulQ_ne_zero hb hc h.symm

-- ============================================================
-- §III.4. Setoid and the type ℚ_VR
-- ============================================================

-- §III.4. Setoid instance for NonZeroRatExpr via ratEq.
instance ratEqSetoid : Setoid NonZeroRatExpr :=
  { r := ratEq
    iseqv := ⟨ratEq_refl, ratEq_symm, ratEq_trans⟩ }

-- §III.4. ℚ_VR — the rational numbers as the quotient type NonZeroRatExpr / ratEq.
def RatVR : Type := Quotient ratEqSetoid

notation "ℚ_VR" => RatVR

-- ============================================================
-- §III.3. Operations on NonZeroRatExpr (raw, pre-quotient).
-- Well-definedness under ratEq is proved in §III.3 (step 8.6).
-- ============================================================

-- §III.3. Addition: (a ⊘ b) ⊞ (c ⊘ d) := (a ⊗ d ⊕ b ⊗ c) ⊘ (b ⊗ d).
-- Denominator b ⊗ d is nonzero by imulQ_ne_zero from the subtype conditions.
def iratAdd (e f : NonZeroRatExpr) : NonZeroRatExpr :=
  let ⟨.mk a b, hb⟩ := e
  let ⟨.mk c d, hd⟩ := f
  ⟨.mk (iaddQ (imulQ a d) (imulQ b c)) (imulQ b d),
   imulQ_ne_zero hb hd⟩

-- §III.3. Multiplication: (a ⊘ b) ⊠ (c ⊘ d) := (a ⊗ c) ⊘ (b ⊗ d).
def iratMul (e f : NonZeroRatExpr) : NonZeroRatExpr :=
  let ⟨.mk a b, hb⟩ := e
  let ⟨.mk c d, hd⟩ := f
  ⟨.mk (imulQ a c) (imulQ b d),
   imulQ_ne_zero hb hd⟩

-- §III.3. Subtraction: (a ⊘ b) ⊟⊘ (c ⊘ d) := (a ⊗ d ⊖ b ⊗ c) ⊘ (b ⊗ d).
-- isubQ is defined in Integers.lean as iaddQ x (inegQ y).
def iratSub (e f : NonZeroRatExpr) : NonZeroRatExpr :=
  let ⟨.mk a b, hb⟩ := e
  let ⟨.mk c d, hd⟩ := f
  ⟨.mk (isubQ (imulQ a d) (imulQ b c)) (imulQ b d),
   imulQ_ne_zero hb hd⟩

-- §III.3. Division: (a ⊘ b) ⊘⊘ (c ⊘ d) := (a ⊗ d) ⊘ (b ⊗ c), provided c ≠ 0_ℤ.
-- The condition hf_num : f.1.fst ≠ zero_Z captures the preprint's «provided c ≠ 0_ℤ».
-- Denominator b ⊗ c is nonzero by imulQ_ne_zero from e.2 (b ≠ 0) and hf_num (c ≠ 0).
def iratDiv (e f : NonZeroRatExpr) (hf_num : f.1.fst ≠ zero_Z) : NonZeroRatExpr :=
  let ⟨.mk a b, hb⟩ := e
  let ⟨.mk c d, _⟩ := f
  ⟨.mk (imulQ a d) (imulQ b c),
   imulQ_ne_zero hb hf_num⟩

-- ============================================================
-- §III.3. Well-definedness of operations under ratEq (Step 8.6)
-- ============================================================

-- Private helper: forward preserves subtraction.
-- forward (isubQ a b) = forward a - forward b.
-- Mirrors preserve_add_int; preserve_sub is intentionally omitted from
-- Integers.lean (comment there: «derivable from preserve_add + preserve_neg»).
private theorem preserve_sub_int (a b : ℤ_VR) : forward (isubQ a b) = forward a - forward b := by
  -- isubQ a b = iaddQ a (inegQ b) by definitional reduction (isub = iadd ∘ ineg by rfl).
  have key : isubQ a b = iaddQ a (inegQ b) :=
    Quotient.inductionOn₂ a b fun _ _ => rfl
  rw [key, preserve_add_int, preserve_neg_int]; ring

-- §III.3. iratAdd is well-defined under ratEq.
-- Factored identity:
--   (a*d + b*c)*(b'*d') - (b*d)*(a'*d' + b'*c')
--     = d*d'*(a*b' - b*a') + b*b'*(c*d' - d*c')
-- Both terms vanish by H1 (a*b' = b*a') and H2 (c*d' = d*c').
theorem iratAdd_respects {e e' f f' : NonZeroRatExpr}
    (h1 : ratEq e e') (h2 : ratEq f f') : ratEq (iratAdd e f) (iratAdd e' f') := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨a', b'⟩, _⟩ := e'
  obtain ⟨⟨c, d⟩, _⟩ := f
  obtain ⟨⟨c', d'⟩, _⟩ := f'
  simp only [ratEq] at h1 h2
  simp only [iratAdd, ratEq]
  apply forward_injective
  simp only [preserve_add_int, preserve_mul_int]
  have H1 : forward a * forward b' = forward b * forward a' := by
    have := congrArg forward h1; simp only [preserve_mul_int] at this; exact this
  have H2 : forward c * forward d' = forward d * forward c' := by
    have := congrArg forward h2; simp only [preserve_mul_int] at this; exact this
  have step : (forward a * forward d + forward b * forward c) * (forward b' * forward d') -
      forward b * forward d * (forward a' * forward d' + forward b' * forward c') = 0 := by
    have e1 := sub_eq_zero.mpr H1
    have e2 := sub_eq_zero.mpr H2
    have factored : (forward a * forward d + forward b * forward c) * (forward b' * forward d') -
        forward b * forward d * (forward a' * forward d' + forward b' * forward c') =
        forward d * forward d' * (forward a * forward b' - forward b * forward a') +
        forward b * forward b' * (forward c * forward d' - forward d * forward c') := by ring
    rw [factored, e1, e2]; ring
  exact sub_eq_zero.mp step

-- §III.3. iratMul is well-defined under ratEq.
-- Factored identity:
--   (a*c)*(b'*d') - (b*d)*(a'*c')
--     = c*d'*(a*b' - b*a') + b*a'*(c*d' - d*c')
theorem iratMul_respects {e e' f f' : NonZeroRatExpr}
    (h1 : ratEq e e') (h2 : ratEq f f') : ratEq (iratMul e f) (iratMul e' f') := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨a', b'⟩, _⟩ := e'
  obtain ⟨⟨c, d⟩, _⟩ := f
  obtain ⟨⟨c', d'⟩, _⟩ := f'
  simp only [ratEq] at h1 h2
  simp only [iratMul, ratEq]
  apply forward_injective
  simp only [preserve_mul_int]
  have H1 : forward a * forward b' = forward b * forward a' := by
    have := congrArg forward h1; simp only [preserve_mul_int] at this; exact this
  have H2 : forward c * forward d' = forward d * forward c' := by
    have := congrArg forward h2; simp only [preserve_mul_int] at this; exact this
  have step : forward a * forward c * (forward b' * forward d') -
      forward b * forward d * (forward a' * forward c') = 0 := by
    have e1 := sub_eq_zero.mpr H1
    have e2 := sub_eq_zero.mpr H2
    have factored : forward a * forward c * (forward b' * forward d') -
        forward b * forward d * (forward a' * forward c') =
        forward c * forward d' * (forward a * forward b' - forward b * forward a') +
        forward b * forward a' * (forward c * forward d' - forward d * forward c') := by ring
    rw [factored, e1, e2]; ring
  exact sub_eq_zero.mp step

-- §III.3. iratSub is well-defined under ratEq.
-- Factored identity:
--   (a*d - b*c)*(b'*d') - (b*d)*(a'*d' - b'*c')
--     = d*d'*(a*b' - b*a') - b*b'*(c*d' - d*c')
theorem iratSub_respects {e e' f f' : NonZeroRatExpr}
    (h1 : ratEq e e') (h2 : ratEq f f') : ratEq (iratSub e f) (iratSub e' f') := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨a', b'⟩, _⟩ := e'
  obtain ⟨⟨c, d⟩, _⟩ := f
  obtain ⟨⟨c', d'⟩, _⟩ := f'
  simp only [ratEq] at h1 h2
  simp only [iratSub, ratEq]
  apply forward_injective
  simp only [preserve_sub_int, preserve_mul_int]
  have H1 : forward a * forward b' = forward b * forward a' := by
    have := congrArg forward h1; simp only [preserve_mul_int] at this; exact this
  have H2 : forward c * forward d' = forward d * forward c' := by
    have := congrArg forward h2; simp only [preserve_mul_int] at this; exact this
  have step : (forward a * forward d - forward b * forward c) * (forward b' * forward d') -
      forward b * forward d * (forward a' * forward d' - forward b' * forward c') = 0 := by
    have e1 := sub_eq_zero.mpr H1
    have e2 := sub_eq_zero.mpr H2
    have factored : (forward a * forward d - forward b * forward c) * (forward b' * forward d') -
        forward b * forward d * (forward a' * forward d' - forward b' * forward c') =
        forward d * forward d' * (forward a * forward b' - forward b * forward a') -
        forward b * forward b' * (forward c * forward d' - forward d * forward c') := by ring
    rw [factored, e1, e2]; ring
  exact sub_eq_zero.mp step

-- §III.3. iratDiv is well-defined under ratEq.
-- Explicit nonzero-numerator preconditions are required on both the original and
-- the representative (well-definedness uses ratEq_preserves_nonzero_num at the
-- quotient level; see nonZeroQ and ratDiv in step 8.8).
-- Factored identity:
--   (a*d)*(b'*c') - (b*c)*(a'*d')
--     = d*c'*(a*b' - b*a') - b*a'*(c*d' - d*c')
theorem iratDiv_respects {e e' f f' : NonZeroRatExpr}
    (h1 : ratEq e e') (h2 : ratEq f f')
    (hf_num : f.1.fst ≠ zero_Z) (hf'_num : f'.1.fst ≠ zero_Z) :
    ratEq (iratDiv e f hf_num) (iratDiv e' f' hf'_num) := by
  obtain ⟨⟨a, b⟩, _⟩ := e
  obtain ⟨⟨a', b'⟩, _⟩ := e'
  obtain ⟨⟨c, d⟩, _⟩ := f
  obtain ⟨⟨c', d'⟩, _⟩ := f'
  simp only [RatExpr.fst] at hf_num hf'_num
  simp only [ratEq] at h1 h2
  simp only [iratDiv, ratEq]
  apply forward_injective
  simp only [preserve_mul_int]
  have H1 : forward a * forward b' = forward b * forward a' := by
    have := congrArg forward h1; simp only [preserve_mul_int] at this; exact this
  have H2 : forward c * forward d' = forward d * forward c' := by
    have := congrArg forward h2; simp only [preserve_mul_int] at this; exact this
  have step : forward a * forward d * (forward b' * forward c') -
      forward b * forward c * (forward a' * forward d') = 0 := by
    have e1 := sub_eq_zero.mpr H1
    have e2 := sub_eq_zero.mpr H2
    have factored : forward a * forward d * (forward b' * forward c') -
        forward b * forward c * (forward a' * forward d') =
        forward d * forward c' * (forward a * forward b' - forward b * forward a') -
        forward b * forward a' * (forward c * forward d' - forward d * forward c') := by ring
    rw [factored, e1, e2]; ring
  exact sub_eq_zero.mp step

-- ============================================================
-- §III.4. Lifted operations on ℚ_VR
-- ============================================================

-- §III.4. Addition on ℚ_VR. Well-defined by iratAdd_respects.
def ratAdd : ℚ_VR → ℚ_VR → ℚ_VR :=
  Quotient.lift₂ (fun e f => Quotient.mk ratEqSetoid (iratAdd e f))
    (fun _ _ _ _ h1 h2 => Quotient.sound (iratAdd_respects h1 h2))

-- §III.4. Multiplication on ℚ_VR. Well-defined by iratMul_respects.
def ratMul : ℚ_VR → ℚ_VR → ℚ_VR :=
  Quotient.lift₂ (fun e f => Quotient.mk ratEqSetoid (iratMul e f))
    (fun _ _ _ _ h1 h2 => Quotient.sound (iratMul_respects h1 h2))

-- §III.4. Subtraction on ℚ_VR. Well-defined by iratSub_respects.
def ratSub : ℚ_VR → ℚ_VR → ℚ_VR :=
  Quotient.lift₂ (fun e f => Quotient.mk ratEqSetoid (iratSub e f))
    (fun _ _ _ _ h1 h2 => Quotient.sound (iratSub_respects h1 h2))

-- §III.4. Nonzero predicate on ℚ_VR.
-- q is nonzero iff the numerator of any representative is ≠ zero_Z.
-- Well-defined by ratEq_preserves_nonzero_num (iff promoted to equality via propext).
def nonZeroQ : ℚ_VR → Prop :=
  Quotient.lift (fun e => e.1.fst ≠ zero_Z)
    (fun _ _ h => propext (ratEq_preserves_nonzero_num h))

-- §III.4. Zero element of ℚ_VR: class of 0_ℤ ⊘ 1_ℤ.
-- Any representative with numerator zero_Z gives the same class
-- (ratEq: zero_Z * b' = b * zero_Z by imulQ_zero_left/right for any b, b' ≠ 0).
def zero_Q : ℚ_VR :=
  Quotient.mk ratEqSetoid ⟨.mk zero_Z one_Z, one_ne_zero_Z⟩

-- §III.4. nonZeroQ is decidable.
-- Quotient.recOnSubsingleton handles the Type-valued motive (Decidable is in Type, not Prop).
-- The goal reduces definitionally to Decidable (e.1.fst ≠ zero_Z) without explicit simp.
-- Lean sees through Quotient.lift via iota reduction — no simp [nonZeroQ] needed.
instance instDecidableNonZeroQ (q : ℚ_VR) : Decidable (nonZeroQ q) :=
  Quotient.recOnSubsingleton q fun e =>
    @instDecidableNot _ (instDecidableEqIntVR e.1.fst zero_Z)

-- §III.3. Division on ℚ_VR — total function with junk value p / 0_ℚ := 0_ℚ.
-- The split_ifs respects proof uses iratDiv_respects for the nonzero branch,
-- and ratEq_preserves_nonzero_num to discharge the mixed-zero cases as impossible.
def ratDiv (p q : ℚ_VR) : ℚ_VR :=
  Quotient.lift₂
    (fun e f =>
      if hf : f.1.fst ≠ zero_Z then Quotient.mk ratEqSetoid (iratDiv e f hf)
      else zero_Q)
    -- Quotient.lift₂ respects argument: (num₁, denom₁, num₂, denom₂, he, hf)
    -- he : ratEq num₁ num₂ (first quotient), hf : ratEq denom₁ denom₂ (second quotient).
    -- The if-condition checks denom₁ (LHS) and denom₂ (RHS), not num₁/num₂.
    (fun _ d₁ _ d₂ he hf => by
      dsimp only  -- beta-reduce the lambda so dif_pos/dif_neg can match
      have key := ratEq_preserves_nonzero_num hf
      -- Classical-free case split on denom₁'s numerator via DecidableEq
      -- Lean 4: Decidable has isFalse first, isTrue second, so cases are (¬P, P).
      rcases instDecidableEqIntVR d₁.1.fst zero_Z with h_ne | h_eq
      · -- h_ne : d₁.fst ≠ zero_Z: both sides reduce to iratDiv
        have h_ne' : d₂.1.fst ≠ zero_Z := key.mp h_ne
        simp only [dif_pos h_ne, dif_pos h_ne']
        exact Quotient.sound (iratDiv_respects he hf h_ne h_ne')
      · -- h_eq : d₁.fst = zero_Z: both sides reduce to zero_Q
        have hfz : ¬(d₁.1.fst ≠ zero_Z) := fun h => h h_eq
        have hf'z : ¬(d₂.1.fst ≠ zero_Z) := fun h => hfz (key.mpr h)
        simp only [dif_neg hfz, dif_neg hf'z])
    p q

-- ============================================================
-- Axiom boundary: Classical.choice enters here.
--
-- Lean 4 Core's Rat is a structure with field `reduced : num.natAbs.Coprime den`.
-- Every Rat.add / Rat.mul normalises its result, which requires a coprimality
-- proof via Nat.gcd. That proof chain depends on Classical.choice.
-- Confirmed: `#print axioms Rat.add` returns [propext, Classical.choice, Quot.sound]
-- on bare Lean 4 core (no mathlib import needed).
--
-- This dependency is structural and unavoidable: any theorem mentioning + or * on ℚ,
-- or constructing ℚ values via Rat.divInt, inherits Classical.choice from the target
-- type itself. It cannot be removed by replacing individual lemmas or tactics.
--
-- Classical-free boundary in VR-Numbers formalisation:
--   §7 – §8.8 (ℤ_VR): [propext, Quot.sound]          -- Int arithmetic is axiom-free
--   §8.9+   (ℚ_VR+): [propext, Classical.choice, Quot.sound] -- Rat arithmetic is not
--
-- This corresponds to the transition from operations performed syntactically
-- (a + b, a * b on ℤ) to operations requiring a canonical representative
-- (gcd-reduction of a/b on ℚ). See §VI.4 "Depths of Operationality".
-- ============================================================

-- ============================================================
-- §III.5. Embedding ℤ_VR → ℚ_VR
-- ============================================================

-- §III.5. The integer a ∈ ℤ_VR embeds into ℚ_VR as the class of a ∅ 1_ℤ,
-- where 1_ℤ = 1 ⊖ 0 is the multiplicative identity in ℤ_VR.
def embedZ (a : ℤ_VR) : ℚ_VR :=
  Quotient.mk ratEqSetoid ⟨.mk a one_Z, one_ne_zero_Z⟩

-- ============================================================
-- §III.6. Isomorphism ℚ_VR ≅ ℚ
-- ============================================================

-- Auxiliary: n ≠ 0 implies backward n ≠ zero_Z.
-- If backward n = zero_Z, then forward (backward n) = forward zero_Z, i.e., n = 0 by right_inv_int
-- and forward_zero_Z. Contradiction with h.
private theorem backward_ne_zero_of_ne_zero {n : ℤ} (h : n ≠ 0) : backward n ≠ zero_Z := by
  intro heq
  have := congrArg forward heq
  rw [right_inv_int, forward_zero_Z] at this
  exact h this

-- §III.6. Well-definedness of forwardQ: ratEq e f implies equal Rat.divInt values.
-- Proof: ratEq gives fa*fd = fb*fc via preserve_mul_int; divInt_eq_divInt_iff + ring closes.
private theorem forwardQ_wd {e f : NonZeroRatExpr} (h : ratEq e f) :
    Rat.divInt (forward e.1.fst) (forward e.1.snd) =
    Rat.divInt (forward f.1.fst) (forward f.1.snd) := by
  obtain ⟨⟨a, b⟩, hb⟩ := e; obtain ⟨⟨c, d⟩, hd⟩ := f
  simp only [RatExpr.fst, RatExpr.snd] at hb hd ⊢
  simp only [ratEq] at h
  rw [Rat.divInt_eq_divInt_iff (forward_ne_zero hb) (forward_ne_zero hd)]
  have key : forward a * forward d = forward b * forward c := by
    have := congrArg forward h; simp only [preserve_mul_int] at this; exact this
  exact key.trans (by ring)

-- §III.6. The isomorphism map: forwardQ [a ∅ b] = forward(a) /. forward(b).
-- Well-defined by forwardQ_wd.
def forwardQ : ℚ_VR → ℚ :=
  Quotient.lift (fun (e : NonZeroRatExpr) => Rat.divInt (forward e.1.fst) (forward e.1.snd))
    (fun _ _ h => forwardQ_wd h)

-- §III.6. The inverse map: backwardQ r = [backward(r.num) ∅ backward(r.den)].
-- r.den : ℕ is always nonzero (Rat.den_ne_zero), giving backward(↑r.den) ≠ zero_Z.
def backwardQ (r : ℚ) : ℚ_VR :=
  Quotient.mk ratEqSetoid ⟨.mk (backward r.num) (backward ↑r.den),
    backward_ne_zero_of_ne_zero (Int.natCast_ne_zero.mpr (Rat.den_ne_zero r))⟩

-- §III.6. Right inverse: forwardQ ∘ backwardQ = id on ℚ.
-- forward(backward r.num) /. forward(backward r.den) = r.num /. r.den = r (num_divInt_den).
theorem forwardQ_right_inv (r : ℚ) : forwardQ (backwardQ r) = r := by
  simp only [forwardQ, backwardQ, Quotient.lift_mk, RatExpr.fst, RatExpr.snd, right_inv_int,
             Rat.num_divInt_den]

-- §III.6. Left inverse: backwardQ ∘ forwardQ = id on ℚ_VR.
-- For ⟨.mk a b, hb⟩: set r := Rat.divInt (forward a) (forward b).
-- Need ratEq ⟨backward r.num, backward ↑r.den⟩ ⟨a, b⟩, i.e., r.num * fb = ↑r.den * fa.
-- From num_divInt_den + divInt_eq_divInt_iff: r.num * fb = fa * ↑r.den; ring for commutativity.
theorem forwardQ_left_inv (q : ℚ_VR) : backwardQ (forwardQ q) = q :=
  Quotient.inductionOn q fun e => by
    obtain ⟨⟨a, b⟩, hb⟩ := e
    simp only [forwardQ, Quotient.lift_mk, RatExpr.fst, RatExpr.snd]
    set r := Rat.divInt (forward a) (forward b)
    have hb' : forward b ≠ 0 := forward_ne_zero hb
    have hden_ne : (↑r.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Rat.den_ne_zero r)
    have key : r.num * forward b = ↑r.den * forward a :=
      ((Rat.divInt_eq_divInt_iff hden_ne hb').mp (Rat.num_divInt_den r)).trans (by ring)
    simp only [backwardQ]
    apply Quotient.sound
    change ratEq ⟨.mk (backward r.num) (backward ↑r.den), backward_ne_zero_of_ne_zero hden_ne⟩
                 ⟨.mk a b, hb⟩
    simp only [ratEq]
    apply forward_injective
    simp only [preserve_mul_int, right_inv_int]
    exact key

-- §III.6. forwardQ maps zero_Q to 0.
-- forward(zero_Z) /. forward(one_Z) = 0 /. 1 = ↑0 = 0.
theorem forwardQ_zero_Q : forwardQ zero_Q = 0 := by
  simp only [forwardQ, zero_Q, Quotient.lift_mk, RatExpr.fst, RatExpr.snd,
             forward_zero_Z, forward_one_Z, Rat.divInt_one, Int.cast_zero]

-- §III.6. forwardQ maps embedZ one_Z to 1.
-- forward(one_Z) /. forward(one_Z) = 1 /. 1 = 1.
theorem forwardQ_one_Q : forwardQ (embedZ one_Z) = 1 := by
  simp only [forwardQ, embedZ, Quotient.lift_mk, RatExpr.fst, RatExpr.snd, forward_one_Z]
  exact Rat.divInt_one_one

-- §III.6. forwardQ preserves addition.
-- iratAdd ⟨a,b⟩ ⟨c,d⟩ = ⟨a*d + b*c, b*d⟩.
-- (a*d + b*c) /. (b*d) = a/b + c/d (by divInt_add_divInt + ring for commutativity).
theorem forwardQ_add (p q : ℚ_VR) : forwardQ (ratAdd p q) = forwardQ p + forwardQ q :=
  Quotient.inductionOn₂ p q fun e f => by
    obtain ⟨⟨a, b⟩, hb⟩ := e; obtain ⟨⟨c, d⟩, hd⟩ := f
    simp only [ratAdd, forwardQ, Quotient.lift_mk, iratAdd, RatExpr.fst, RatExpr.snd,
               preserve_add_int, preserve_mul_int]
    have hb' : forward b ≠ 0 := forward_ne_zero hb
    have hd' : forward d ≠ 0 := forward_ne_zero hd
    rw [Rat.divInt_add_divInt _ _ hb' hd']
    apply (Rat.divInt_eq_divInt_iff (Int_mul_ne_zero hb' hd') (Int_mul_ne_zero hb' hd')).mpr
    ring

-- §III.6. forwardQ preserves multiplication.
-- iratMul ⟨a,b⟩ ⟨c,d⟩ = ⟨a*c, b*d⟩.
-- (a*c) /. (b*d) = (a/b) * (c/d) (by divInt_mul_divInt, symmetric).
theorem forwardQ_mul (p q : ℚ_VR) : forwardQ (ratMul p q) = forwardQ p * forwardQ q :=
  Quotient.inductionOn₂ p q fun e f => by
    obtain ⟨⟨a, b⟩, hb⟩ := e; obtain ⟨⟨c, d⟩, hd⟩ := f
    simp only [ratMul, forwardQ, Quotient.lift_mk, iratMul, RatExpr.fst, RatExpr.snd,
               preserve_mul_int]
    exact (Rat.divInt_mul_divInt _ _).symm

-- §III.6. forwardQ preserves subtraction.
-- iratSub ⟨a,b⟩ ⟨c,d⟩ = ⟨a*d - b*c, b*d⟩.
-- (a*d - b*c) /. (b*d) = a/b - c/d (by divInt_sub_divInt + ring for commutativity).
theorem forwardQ_sub (p q : ℚ_VR) : forwardQ (ratSub p q) = forwardQ p - forwardQ q :=
  Quotient.inductionOn₂ p q fun e f => by
    obtain ⟨⟨a, b⟩, hb⟩ := e; obtain ⟨⟨c, d⟩, hd⟩ := f
    simp only [ratSub, forwardQ, Quotient.lift_mk, iratSub, RatExpr.fst, RatExpr.snd,
               preserve_sub_int, preserve_mul_int]
    have hb' : forward b ≠ 0 := forward_ne_zero hb
    have hd' : forward d ≠ 0 := forward_ne_zero hd
    rw [Rat.divInt_sub_divInt _ _ hb' hd']
    apply (Rat.divInt_eq_divInt_iff (Int_mul_ne_zero hb' hd') (Int_mul_ne_zero hb' hd')).mpr
    ring

-- §III.6. forwardQ preserves division.
-- Nonzero case (c ≠ zero_Z): iratDiv ⟨a,b⟩ ⟨c,d⟩ = ⟨a*d, b*c⟩;
--   (a*d) /. (b*c) = (a/b) / (c/d) (by divInt_div_divInt).
-- Zero case (c = zero_Z): ratDiv returns zero_Q; forwardQ = 0; and (a/b) / 0 = 0 (div_zero).
theorem forwardQ_div (p q : ℚ_VR) : forwardQ (ratDiv p q) = forwardQ p / forwardQ q :=
  Quotient.inductionOn₂ p q fun e f => by
    obtain ⟨⟨a, b⟩, hb⟩ := e; obtain ⟨⟨c, d⟩, hd⟩ := f
    rcases instDecidableEqIntVR c zero_Z with hc | hceq
    · -- hc : c ≠ zero_Z: genuine division
      simp only [ratDiv, Quotient.lift_mk, RatExpr.fst, dif_pos hc,
                 forwardQ, iratDiv, RatExpr.snd, preserve_mul_int]
      exact (Rat.divInt_div_divInt _ _ _ _).symm
    · -- hceq : c = zero_Z: junk value; both sides are 0
      have hfz : ¬(c ≠ zero_Z) := fun h => h hceq
      simp only [ratDiv, Quotient.lift_mk, RatExpr.fst, dif_neg hfz]
      rw [forwardQ_zero_Q]
      simp only [forwardQ, Quotient.lift_mk, RatExpr.fst, RatExpr.snd]
      rw [hceq, forward_zero_Z, Rat.zero_divInt, div_zero]

-- ============================================================
-- §III.6. Isomorphism record RatVRRatIso and main theorem
-- ============================================================

-- §III.6. Isomorphism record: bijection + preservation of all operations and constants.
-- Parallel to IntVRIntIso in Integers.lean (§II.6).
-- No preserve_neg field: ratNeg is not defined as a separate operation for ℚ_VR
-- (subtraction is independent, not routed through negation + addition).
structure RatVRRatIso where
  forward : ℚ_VR → ℚ
  backward : ℚ → ℚ_VR
  right_inv : ∀ r : ℚ,    forward (backward r) = r
  left_inv  : ∀ q : ℚ_VR, backward (forward q) = q
  preserve_zero : forward zero_Q = 0
  preserve_one  : forward (embedZ one_Z) = 1
  preserve_add  : ∀ p q : ℚ_VR, forward (ratAdd p q) = forward p + forward q
  preserve_mul  : ∀ p q : ℚ_VR, forward (ratMul p q) = forward p * forward q
  preserve_sub  : ∀ p q : ℚ_VR, forward (ratSub p q) = forward p - forward q
  preserve_div  : ∀ p q : ℚ_VR, forward (ratDiv p q) = forward p / forward q

-- §III.6. Theorem. ℚ_VR with operations ⊞, ⊠, ⊟⊘, ⊘⊘ is a field, isomorphic to ℚ
-- (VR-Numbers §III.6).
-- #print axioms Theorem_III_6_RatVR_Rat
def Theorem_III_6_RatVR_Rat : RatVRRatIso :=
  { forward      := forwardQ
    backward     := backwardQ
    right_inv    := forwardQ_right_inv
    left_inv     := forwardQ_left_inv
    preserve_zero := forwardQ_zero_Q
    preserve_one  := forwardQ_one_Q
    preserve_add  := forwardQ_add
    preserve_mul  := forwardQ_mul
    preserve_sub  := forwardQ_sub
    preserve_div  := forwardQ_div }

-- ============================================================
-- §III.4. Canonical Form (corollary of §III.6 isomorphism)
-- ============================================================

-- §III.4. Canonical form.
-- Preprint: «Every fraction a ⊘ b can be brought to canonical form by making
-- the denominator positive and reducing to lowest terms.»
-- Three components: (1) existence, (2) denominator > 0, (3) gcd = 1.
--
-- Lean formulation: q = backwardQ (forwardQ q).
-- Canonicity is hidden in the Lean 4 Rat structure:
--   forwardQ q = r : Rat, where r.num/r.den is already in canonical form
--   (r.den > 0, Rat.reduced : r.num.natAbs.Coprime r.den).
-- backwardQ transfers these invariants back: backward r.num ∅ backward ↑r.den.
--
-- Properties (1)–(3) from the preprint are witnessed by this equality:
-- (1) existence: the equality itself provides the witness
-- (2) denominator > 0: r.den : ℕ with r.den ≠ 0; use Rat.den_pos on (forwardQ q)
-- (3) coprimality: r.reduced : r.num.natAbs.Coprime r.den; use Rat.reduced on (forwardQ q)
theorem Theorem_III_4_CanonicalForm : ∀ q : ℚ_VR, q = backwardQ (forwardQ q) :=
  fun q => (forwardQ_left_inv q).symm

end VR.Numbers

-- #print axioms VR.Numbers.Theorem_III_6_RatVR_Rat
-- 'VR.Numbers.Theorem_III_6_RatVR_Rat' depends on axioms: [propext, Classical.choice, Quot.sound]
-- #print axioms VR.Numbers.Theorem_III_4_CanonicalForm
-- 'VR.Numbers.Theorem_III_4_CanonicalForm' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
