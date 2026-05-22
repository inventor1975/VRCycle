-- VR-Numbers: Reals ℝ_VR (DOI 10.5281/zenodo.20272743)
-- Part IV. Real Numbers ℝ via Cauchy Sequences.

import VRCycle.Numbers.Rationals

namespace VR.Numbers
open VR

-- ============================================================
-- Axiom note: Classical.choice is present throughout this file,
-- inherited from Rationals.lean (Rat.add pulls Classical.choice
-- via coprimality normalisation in Lean 4 Core). See comment in
-- Rationals.lean at the §III.5 boundary.
-- ============================================================

-- ============================================================
-- §IV.1. Functions as Operational Rules
-- ============================================================

-- §IV.1. A function a : ℕ → ℚ_VR is an "operational rule": a finite
-- description (algorithm) producing, for each n ∈ ℕ, a rational a(n) ∈ ℚ_VR.
-- In Lean 4, this is simply the type ℕ → ℚ_VR (total functions).
--
-- Note: Lean 4 does not distinguish computable from non-computable functions
-- at the type level. The operational ontology of VR-Numbers (§IV.1) restricts
-- functions to those with finite algorithmic descriptions; this restriction is
-- a metatheoretic claim not expressible as a Lean type predicate. See §IV.7
-- and the methodological note in Theorem_IV_7_RealVR_Real.

-- ============================================================
-- §IV.2 / auxiliary: order and absolute value on ℚ_VR
-- ============================================================

-- §IV.2 requires ε > 0 and |a(m) ⊟ a(n)| on ℚ_VR.
-- Technical definition via the isomorphism forwardQ : ℚ_VR ≃ ℚ.
--
-- Alternatives exist (direct definition on canonical representatives),
-- but the isomorphism route is much simpler and correct: the ℚ_VR structure
-- induced by forwardQ carries the same order and absolute value as ℚ.
-- The formulation of isFundamentalVR uses only ltRatVR and absRatVR,
-- not forwardQ directly — preserving the §IV.2 syntactic level of ℚ_VR.
-- The equivalence with the ℚ-level Cauchy condition is a separate theorem.

-- Order on ℚ_VR: p < q ↔ forwardQ p < forwardQ q in ℚ.
def ltRatVR (p q : ℚ_VR) : Prop := forwardQ p < forwardQ q

instance instLTRatVR : LT ℚ_VR := ⟨ltRatVR⟩

-- Decidability of equality and order on ℚ_VR (needed for ε/2 arithmetic).
instance instDecidableLTRatVR (p q : ℚ_VR) : Decidable (p < q) :=
  inferInstanceAs (Decidable (forwardQ p < forwardQ q))

-- Absolute value on ℚ_VR: |p| = backwardQ |forwardQ p|.
-- This is well-defined: backwardQ is the right-inverse of forwardQ,
-- and |·| on ℚ satisfies |r| ≥ 0 with |r| = 0 ↔ r = 0.
def absRatVR (p : ℚ_VR) : ℚ_VR := backwardQ |forwardQ p|

-- ============================================================
-- §IV.2 / auxiliary: key lemmas linking ltRatVR/absRatVR to ℚ
-- ============================================================

-- forwardQ is injective (left inverse: backwardQ ∘ forwardQ = id)
private theorem forwardQ_injective : Function.Injective forwardQ :=
  Function.LeftInverse.injective forwardQ_left_inv

-- zero_Q < ε ↔ 0 < forwardQ ε (needed to unpack ε-conditions)
theorem zero_Q_lt_iff (ε : ℚ_VR) : zero_Q < ε ↔ 0 < forwardQ ε := by
  simp only [LT.lt, ltRatVR, forwardQ_zero_Q]

-- forwardQ preserves and reflects <
theorem forwardQ_lt_iff (p q : ℚ_VR) : p < q ↔ forwardQ p < forwardQ q :=
  Iff.rfl

-- forwardQ (absRatVR p) = |forwardQ p|
theorem forwardQ_absRatVR (p : ℚ_VR) : forwardQ (absRatVR p) = |forwardQ p| := by
  simp only [absRatVR, forwardQ_right_inv]

-- absRatVR (ratSub p q) corresponds to |forwardQ p - forwardQ q|
theorem forwardQ_absRatVR_sub (p q : ℚ_VR) :
    forwardQ (absRatVR (ratSub p q)) = |forwardQ p - forwardQ q| := by
  rw [forwardQ_absRatVR, forwardQ_sub]

-- absRatVR p ≥ 0: ¬(absRatVR p < zero_Q)
theorem absRatVR_nonneg (p : ℚ_VR) : ¬(absRatVR p < zero_Q) := by
  -- LT on ℚ_VR unfolds definitionally to forwardQ · < forwardQ ·
  change ¬(forwardQ (absRatVR p) < forwardQ zero_Q)
  rw [forwardQ_absRatVR, forwardQ_zero_Q]
  exact not_lt.mpr (by positivity)

-- absRatVR zero_Q = zero_Q
theorem absRatVR_zero : absRatVR zero_Q = zero_Q := by
  apply forwardQ_injective
  simp only [forwardQ_absRatVR, forwardQ_zero_Q, abs_zero]

-- absRatVR (ratSub p q) < ε ↔ |forwardQ p - forwardQ q| < forwardQ ε
theorem absRatVR_sub_lt_iff (p q ε : ℚ_VR) :
    absRatVR (ratSub p q) < ε ↔ |forwardQ p - forwardQ q| < forwardQ ε := by
  change (forwardQ (absRatVR (ratSub p q)) < forwardQ ε) ↔ _
  rw [forwardQ_absRatVR_sub]

-- ============================================================
-- §IV.2. Fundamental (Cauchy) Sequences
-- ============================================================

-- §IV.2. A function a: ℕ → ℚ_VR is fundamental (a Cauchy sequence) if:
-- ∀ε ∈ ℚ_VR, ε > 0, ∃N ∈ ℕ such that ∀m, n ≥ N: |a(m) ⊟ a(n)| < ε.
def isFundamentalVR (a : ℕ → ℚ_VR) : Prop :=
  ∀ ε : ℚ_VR, zero_Q < ε →
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      absRatVR (ratSub (a m) (a n)) < ε

-- ============================================================
-- §IV.3. Equivalence of Sequences
-- ============================================================

-- §IV.3. a ≈_C b ⟺ ∀ε > 0, ∃N: ∀n ≥ N: |a(n) ⊟ b(n)| < ε.
def cauchyEqVR (a b : ℕ → ℚ_VR) : Prop :=
  ∀ ε : ℚ_VR, zero_Q < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      absRatVR (ratSub (a n) (b n)) < ε

-- ============================================================
-- §IV.3 / auxiliary: properties of cauchyEqVR
-- ============================================================

-- ratSub p p = zero_Q
theorem ratSub_self (p : ℚ_VR) : ratSub p p = zero_Q := by
  apply forwardQ_injective
  simp only [forwardQ_sub, forwardQ_zero_Q, sub_self]

-- |p - q| = |q - p| on ℚ_VR
theorem absRatVR_sub_comm (p q : ℚ_VR) : absRatVR (ratSub p q) = absRatVR (ratSub q p) := by
  apply forwardQ_injective
  simp only [forwardQ_absRatVR_sub, abs_sub_comm]

-- a - c = (a - b) + (b - c) on ℚ_VR
theorem ratSub_add_ratSub (a b c : ℚ_VR) :
    ratSub a c = ratAdd (ratSub a b) (ratSub b c) := by
  apply forwardQ_injective
  simp only [forwardQ_add, forwardQ_sub]
  ring

-- ε/2 exists: ∃ δ > 0 with δ + δ = ε
theorem half_exists (ε : ℚ_VR) (hε : zero_Q < ε) :
    ∃ δ : ℚ_VR, zero_Q < δ ∧ ratAdd δ δ = ε := by
  refine ⟨backwardQ (forwardQ ε / 2), ?_, ?_⟩
  · rw [zero_Q_lt_iff, forwardQ_right_inv]
    exact div_pos ((zero_Q_lt_iff ε).mp hε) (by norm_num)
  · apply forwardQ_injective
    simp only [forwardQ_add, forwardQ_right_inv]
    ring

-- ============================================================
-- §IV.3. cauchyEqVR is an equivalence relation
-- ============================================================

theorem cauchyEqVR_refl (a : ℕ → ℚ_VR) : cauchyEqVR a a := fun ε hε =>
  ⟨0, fun n _ => by rw [ratSub_self, absRatVR_zero]; exact hε⟩

theorem cauchyEqVR_symm (a b : ℕ → ℚ_VR) (h : cauchyEqVR a b) : cauchyEqVR b a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [absRatVR_sub_comm (b n) (a n)]
  exact hN n hn

theorem cauchyEqVR_trans (a b c : ℕ → ℚ_VR)
    (hab : cauchyEqVR a b) (hbc : cauchyEqVR b c) : cauchyEqVR a c := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := half_exists ε hε
  obtain ⟨N₁, h₁⟩ := hab δ hδ_pos
  obtain ⟨N₂, h₂⟩ := hbc δ hδ_pos
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have h₁' := (absRatVR_sub_lt_iff (a n) (b n) δ).mp (h₁ n hn₁)
  have h₂' := (absRatVR_sub_lt_iff (b n) (c n) δ).mp (h₂ n hn₂)
  rw [absRatVR_sub_lt_iff]
  have hδε : forwardQ δ + forwardQ δ = forwardQ ε := by
    have := congr_arg forwardQ hδ_sum
    rwa [forwardQ_add] at this
  calc |forwardQ (a n) - forwardQ (c n)|
      = |(forwardQ (a n) - forwardQ (b n)) + (forwardQ (b n) - forwardQ (c n))| := by
            congr 1; ring
    _ ≤ |forwardQ (a n) - forwardQ (b n)| + |forwardQ (b n) - forwardQ (c n)| := abs_add_le _ _
    _ < forwardQ δ + forwardQ δ := add_lt_add h₁' h₂'
    _ = forwardQ ε := hδε

-- ============================================================
-- §IV.3. Subtype of fundamental sequences and setoid
-- ============================================================

-- §IV.3. FundSeqVR: the type of Cauchy sequences ℕ → ℚ_VR.
def FundSeqVR : Type := {a : ℕ → ℚ_VR // isFundamentalVR a}

-- §IV.3. Setoid on FundSeqVR given by cauchyEqVR.
instance fundSeqSetoid : Setoid FundSeqVR where
  r a b := cauchyEqVR a.val b.val
  iseqv := {
    refl  := fun a => cauchyEqVR_refl a.val
    symm  := fun h => cauchyEqVR_symm _ _ h
    trans := fun h₁ h₂ => cauchyEqVR_trans _ _ _ h₁ h₂
  }

-- ============================================================
-- §IV.4. Real Numbers ℝ_VR
-- ============================================================

-- §IV.4. ℝ_VR := FundSeqVR / cauchyEqVR (equivalence classes of Cauchy sequences).
def RealVR : Type := Quotient fundSeqSetoid

notation "ℝ_VR" => RealVR

-- ============================================================
-- §IV.4 / auxiliary: algebraic identities for operations
-- ============================================================

-- (a + b) - (a' + b') = (a - a') + (b - b')
theorem ratAdd_sub_distrib (a a' b b' : ℚ_VR) :
    ratSub (ratAdd a b) (ratAdd a' b') = ratAdd (ratSub a a') (ratSub b b') := by
  apply forwardQ_injective
  simp only [forwardQ_add, forwardQ_sub]
  ring

-- (a - b) - (a' - b') = (a - a') - (b - b')
theorem ratSub_sub_distrib (a a' b b' : ℚ_VR) :
    ratSub (ratSub a b) (ratSub a' b') = ratSub (ratSub a a') (ratSub b b') := by
  apply forwardQ_injective
  simp only [forwardQ_sub]
  ring

-- a*b - a'*b' = a*(b - b') + b'*(a - a')
theorem ratMul_sub_expand (a a' b b' : ℚ_VR) :
    ratSub (ratMul a b) (ratMul a' b') =
    ratAdd (ratMul a (ratSub b b')) (ratMul b' (ratSub a a')) := by
  apply forwardQ_injective
  simp only [forwardQ_add, forwardQ_mul, forwardQ_sub]
  ring

-- ============================================================
-- §IV.4 / auxiliary: boundedness of Cauchy sequences
-- ============================================================

-- Maximum of |f 0|, ..., |f (n-1)|
private def seqMaxAbs (f : ℕ → ℚ) : ℕ → ℚ
  | 0     => 0
  | k + 1 => max (seqMaxAbs f k) |f k|

-- seqMaxAbs f n bounds |f k| for k < n
private theorem seqMaxAbs_le (f : ℕ → ℚ) : ∀ k n : ℕ, k < n → |f k| ≤ seqMaxAbs f n := by
  intro k n
  induction n with
  | zero => exact fun h => absurd h (Nat.not_lt_zero k)
  | succ n ih =>
    intro h
    simp only [seqMaxAbs]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · exact le_trans (ih hlt) (le_max_left _ _)
    · exact le_max_right _ _

-- Every isFundamentalVR sequence is bounded (via forwardQ)
private theorem isFundamentalVR_bounded (a : ℕ → ℚ_VR) (ha : isFundamentalVR a) :
    ∃ M : ℚ, 0 < M ∧ ∀ n : ℕ, |forwardQ (a n)| ≤ M := by
  let ε₁ : ℚ_VR := backwardQ 1
  have hε₁ : zero_Q < ε₁ := by rw [zero_Q_lt_iff, forwardQ_right_inv]; norm_num
  obtain ⟨N₀, hN₀⟩ := ha ε₁ hε₁
  let f := fun n => forwardQ (a n)
  have tail : ∀ k, N₀ ≤ k → |f k| ≤ |f N₀| + 1 := fun k hk => by
    have hc : |f k - f N₀| < 1 := by
      have h := (absRatVR_sub_lt_iff (a k) (a N₀) ε₁).mp (hN₀ k N₀ hk (le_refl N₀))
      simpa [forwardQ_right_inv] using h
    have tri := abs_add_le (f k - f N₀) (f N₀)
    simp only [sub_add_cancel] at tri
    linarith
  let M_head := seqMaxAbs f (N₀ + 1)
  let M_tail := |f N₀| + 1
  let M := max M_head M_tail + 1
  refine ⟨M, by linarith [le_max_right M_head M_tail, abs_nonneg (f N₀)], fun k => ?_⟩
  rcases Nat.lt_or_ge k (N₀ + 1) with hk | hk
  · exact le_trans (seqMaxAbs_le f k (N₀ + 1) hk)
      (by linarith [le_max_left M_head M_tail])
  · exact le_trans (tail k (Nat.le_of_succ_le hk))
      (by linarith [le_max_right M_head M_tail])

-- M * (ε / (2*M + 2)) < ε/2  for M ≥ 0, ε > 0
private theorem mul_div_lt_half (M ε : ℚ) (hM : 0 ≤ M) (hε : 0 < ε) :
    M * (ε / (2 * M + 2)) < ε / 2 := by
  have h : (0 : ℚ) < 2 * M + 2 := by linarith
  have key : M / (2 * M + 2) < 1 / 2 := by
    rw [div_lt_div_iff₀ h (by norm_num : (0 : ℚ) < 2)]
    nlinarith
  calc M * (ε / (2 * M + 2))
      = ε * (M / (2 * M + 2)) := by ring
    _ < ε * (1 / 2) := mul_lt_mul_of_pos_left key hε
    _ = ε / 2 := by ring

-- ============================================================
-- §IV.4 / auxiliary: Cauchy preservation for irealAdd/Sub/Mul
-- ============================================================

private theorem irealAdd_isFundamentalVR (a b : ℕ → ℚ_VR)
    (ha : isFundamentalVR a) (hb : isFundamentalVR b) :
    isFundamentalVR (fun n => ratAdd (a n) (b n)) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := half_exists ε hε
  obtain ⟨N_a, hN_a⟩ := ha δ hδ_pos
  obtain ⟨N_b, hN_b⟩ := hb δ hδ_pos
  refine ⟨max N_a N_b, fun m n hm hn => ?_⟩
  have hma := le_trans (le_max_left N_a N_b) hm
  have hna := le_trans (le_max_left N_a N_b) hn
  have hmb := le_trans (le_max_right N_a N_b) hm
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_mn := (absRatVR_sub_lt_iff (a m) (a n) δ).mp (hN_a m n hma hna)
  have hb_mn := (absRatVR_sub_lt_iff (b m) (b n) δ).mp (hN_b m n hmb hnb)
  have hδε : forwardQ δ + forwardQ δ = forwardQ ε := by
    have := congr_arg forwardQ hδ_sum; rwa [forwardQ_add] at this
  rw [absRatVR_sub_lt_iff, forwardQ_add, forwardQ_add]
  rw [show forwardQ (a m) + forwardQ (b m) - (forwardQ (a n) + forwardQ (b n)) =
    (forwardQ (a m) - forwardQ (a n)) + (forwardQ (b m) - forwardQ (b n)) from by ring]
  calc |(forwardQ (a m) - forwardQ (a n)) + (forwardQ (b m) - forwardQ (b n))|
      ≤ |forwardQ (a m) - forwardQ (a n)| + |forwardQ (b m) - forwardQ (b n)| :=
          abs_add_le _ _
    _ < forwardQ δ + forwardQ δ := add_lt_add ha_mn hb_mn
    _ = forwardQ ε := hδε

private theorem irealSub_isFundamentalVR (a b : ℕ → ℚ_VR)
    (ha : isFundamentalVR a) (hb : isFundamentalVR b) :
    isFundamentalVR (fun n => ratSub (a n) (b n)) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := half_exists ε hε
  obtain ⟨N_a, hN_a⟩ := ha δ hδ_pos
  obtain ⟨N_b, hN_b⟩ := hb δ hδ_pos
  refine ⟨max N_a N_b, fun m n hm hn => ?_⟩
  have hma := le_trans (le_max_left N_a N_b) hm
  have hna := le_trans (le_max_left N_a N_b) hn
  have hmb := le_trans (le_max_right N_a N_b) hm
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_mn := (absRatVR_sub_lt_iff (a m) (a n) δ).mp (hN_a m n hma hna)
  have hb_mn := (absRatVR_sub_lt_iff (b m) (b n) δ).mp (hN_b m n hmb hnb)
  have hδε : forwardQ δ + forwardQ δ = forwardQ ε := by
    have := congr_arg forwardQ hδ_sum; rwa [forwardQ_add] at this
  rw [absRatVR_sub_lt_iff, forwardQ_sub, forwardQ_sub]
  rw [show forwardQ (a m) - forwardQ (b m) - (forwardQ (a n) - forwardQ (b n)) =
    (forwardQ (a m) - forwardQ (a n)) - (forwardQ (b m) - forwardQ (b n)) from by ring]
  calc |(forwardQ (a m) - forwardQ (a n)) - (forwardQ (b m) - forwardQ (b n))|
      = |(forwardQ (a m) - forwardQ (a n)) + (-(forwardQ (b m) - forwardQ (b n)))| := by
          congr 1; ring
    _ ≤ |forwardQ (a m) - forwardQ (a n)| + |-(forwardQ (b m) - forwardQ (b n))| :=
          abs_add_le _ _
    _ = |forwardQ (a m) - forwardQ (a n)| + |forwardQ (b m) - forwardQ (b n)| := by
          rw [abs_neg]
    _ < forwardQ δ + forwardQ δ := add_lt_add ha_mn hb_mn
    _ = forwardQ ε := hδε

private theorem irealMul_isFundamentalVR (a b : ℕ → ℚ_VR)
    (ha : isFundamentalVR a) (hb : isFundamentalVR b) :
    isFundamentalVR (fun n => ratMul (a n) (b n)) := by
  obtain ⟨M_a, hMa_pos, hMa⟩ := isFundamentalVR_bounded a ha
  obtain ⟨M_b, hMb_pos, hMb⟩ := isFundamentalVR_bounded b hb
  intro ε hε
  have hfε_pos : 0 < forwardQ ε := (zero_Q_lt_iff ε).mp hε
  have hδa_pos : zero_Q < backwardQ (forwardQ ε / (2 * M_b + 2)) := by
    rw [zero_Q_lt_iff, forwardQ_right_inv]
    exact div_pos hfε_pos (by linarith)
  have hδb_pos : zero_Q < backwardQ (forwardQ ε / (2 * M_a + 2)) := by
    rw [zero_Q_lt_iff, forwardQ_right_inv]
    exact div_pos hfε_pos (by linarith)
  obtain ⟨N_a, hN_a⟩ := ha (backwardQ (forwardQ ε / (2 * M_b + 2))) hδa_pos
  obtain ⟨N_b, hN_b⟩ := hb (backwardQ (forwardQ ε / (2 * M_a + 2))) hδb_pos
  refine ⟨max N_a N_b, fun m n hm hn => ?_⟩
  have hma := le_trans (le_max_left N_a N_b) hm
  have hna := le_trans (le_max_left N_a N_b) hn
  have hmb := le_trans (le_max_right N_a N_b) hm
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_mn := (absRatVR_sub_lt_iff (a m) (a n)
    (backwardQ (forwardQ ε / (2 * M_b + 2)))).mp (hN_a m n hma hna)
  rw [forwardQ_right_inv] at ha_mn
  have hb_mn := (absRatVR_sub_lt_iff (b m) (b n)
    (backwardQ (forwardQ ε / (2 * M_a + 2)))).mp (hN_b m n hmb hnb)
  rw [forwardQ_right_inv] at hb_mn
  rw [absRatVR_sub_lt_iff, forwardQ_mul, forwardQ_mul]
  rw [show forwardQ (a m) * forwardQ (b m) - forwardQ (a n) * forwardQ (b n) =
    forwardQ (a m) * (forwardQ (b m) - forwardQ (b n)) +
    forwardQ (b n) * (forwardQ (a m) - forwardQ (a n)) from by ring]
  calc |forwardQ (a m) * (forwardQ (b m) - forwardQ (b n)) +
          forwardQ (b n) * (forwardQ (a m) - forwardQ (a n))|
      ≤ |forwardQ (a m) * (forwardQ (b m) - forwardQ (b n))| +
          |forwardQ (b n) * (forwardQ (a m) - forwardQ (a n))| := abs_add_le _ _
    _ = |forwardQ (a m)| * |forwardQ (b m) - forwardQ (b n)| +
          |forwardQ (b n)| * |forwardQ (a m) - forwardQ (a n)| := by
            simp only [abs_mul]
    _ ≤ M_a * |forwardQ (b m) - forwardQ (b n)| +
          M_b * |forwardQ (a m) - forwardQ (a n)| :=
            add_le_add (mul_le_mul_of_nonneg_right (hMa m) (abs_nonneg _))
                       (mul_le_mul_of_nonneg_right (hMb n) (abs_nonneg _))
    _ ≤ M_a * (forwardQ ε / (2 * M_a + 2)) +
          M_b * (forwardQ ε / (2 * M_b + 2)) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (le_of_lt hb_mn) (le_of_lt hMa_pos))
              (mul_le_mul_of_nonneg_left (le_of_lt ha_mn) (le_of_lt hMb_pos))
    _ < forwardQ ε / 2 + forwardQ ε / 2 :=
            add_lt_add
              (mul_div_lt_half M_a (forwardQ ε) (le_of_lt hMa_pos) hfε_pos)
              (mul_div_lt_half M_b (forwardQ ε) (le_of_lt hMb_pos) hfε_pos)
    _ = forwardQ ε := by ring

-- ============================================================
-- §IV.4 / auxiliary: well-definedness (respects cauchyEqVR)
-- ============================================================

private theorem irealAdd_respects (a a' b b' : FundSeqVR)
    (ha : cauchyEqVR a.1 a'.1) (hb : cauchyEqVR b.1 b'.1) :
    cauchyEqVR (fun n => ratAdd (a.1 n) (b.1 n)) (fun n => ratAdd (a'.1 n) (b'.1 n)) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := half_exists ε hε
  obtain ⟨N_a, hN_a⟩ := ha δ hδ_pos
  obtain ⟨N_b, hN_b⟩ := hb δ hδ_pos
  refine ⟨max N_a N_b, fun n hn => ?_⟩
  have hna := le_trans (le_max_left N_a N_b) hn
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_n := (absRatVR_sub_lt_iff (a.1 n) (a'.1 n) δ).mp (hN_a n hna)
  have hb_n := (absRatVR_sub_lt_iff (b.1 n) (b'.1 n) δ).mp (hN_b n hnb)
  have hδε : forwardQ δ + forwardQ δ = forwardQ ε := by
    have := congr_arg forwardQ hδ_sum; rwa [forwardQ_add] at this
  rw [absRatVR_sub_lt_iff, forwardQ_add, forwardQ_add]
  rw [show forwardQ (a.1 n) + forwardQ (b.1 n) - (forwardQ (a'.1 n) + forwardQ (b'.1 n)) =
    (forwardQ (a.1 n) - forwardQ (a'.1 n)) + (forwardQ (b.1 n) - forwardQ (b'.1 n)) from by ring]
  calc |(forwardQ (a.1 n) - forwardQ (a'.1 n)) + (forwardQ (b.1 n) - forwardQ (b'.1 n))|
      ≤ |forwardQ (a.1 n) - forwardQ (a'.1 n)| +
          |forwardQ (b.1 n) - forwardQ (b'.1 n)| := abs_add_le _ _
    _ < forwardQ δ + forwardQ δ := add_lt_add ha_n hb_n
    _ = forwardQ ε := hδε

private theorem irealSub_respects (a a' b b' : FundSeqVR)
    (ha : cauchyEqVR a.1 a'.1) (hb : cauchyEqVR b.1 b'.1) :
    cauchyEqVR (fun n => ratSub (a.1 n) (b.1 n)) (fun n => ratSub (a'.1 n) (b'.1 n)) := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_sum⟩ := half_exists ε hε
  obtain ⟨N_a, hN_a⟩ := ha δ hδ_pos
  obtain ⟨N_b, hN_b⟩ := hb δ hδ_pos
  refine ⟨max N_a N_b, fun n hn => ?_⟩
  have hna := le_trans (le_max_left N_a N_b) hn
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_n := (absRatVR_sub_lt_iff (a.1 n) (a'.1 n) δ).mp (hN_a n hna)
  have hb_n := (absRatVR_sub_lt_iff (b.1 n) (b'.1 n) δ).mp (hN_b n hnb)
  have hδε : forwardQ δ + forwardQ δ = forwardQ ε := by
    have := congr_arg forwardQ hδ_sum; rwa [forwardQ_add] at this
  rw [absRatVR_sub_lt_iff, forwardQ_sub, forwardQ_sub]
  rw [show forwardQ (a.1 n) - forwardQ (b.1 n) - (forwardQ (a'.1 n) - forwardQ (b'.1 n)) =
    (forwardQ (a.1 n) - forwardQ (a'.1 n)) - (forwardQ (b.1 n) - forwardQ (b'.1 n)) from by ring]
  calc |(forwardQ (a.1 n) - forwardQ (a'.1 n)) - (forwardQ (b.1 n) - forwardQ (b'.1 n))|
      = |(forwardQ (a.1 n) - forwardQ (a'.1 n)) +
          (-(forwardQ (b.1 n) - forwardQ (b'.1 n)))| := by congr 1; ring
    _ ≤ |forwardQ (a.1 n) - forwardQ (a'.1 n)| +
          |-(forwardQ (b.1 n) - forwardQ (b'.1 n))| := abs_add_le _ _
    _ = |forwardQ (a.1 n) - forwardQ (a'.1 n)| +
          |forwardQ (b.1 n) - forwardQ (b'.1 n)| := by rw [abs_neg]
    _ < forwardQ δ + forwardQ δ := add_lt_add ha_n hb_n
    _ = forwardQ ε := hδε

private theorem irealMul_respects (a a' b b' : FundSeqVR)
    (ha : cauchyEqVR a.1 a'.1) (hb : cauchyEqVR b.1 b'.1) :
    cauchyEqVR (fun n => ratMul (a.1 n) (b.1 n)) (fun n => ratMul (a'.1 n) (b'.1 n)) := by
  obtain ⟨M_a, hMa_pos, hMa⟩ := isFundamentalVR_bounded a.1 a.2
  obtain ⟨M_b', hMb'_pos, hMb'⟩ := isFundamentalVR_bounded b'.1 b'.2
  intro ε hε
  have hfε_pos : 0 < forwardQ ε := (zero_Q_lt_iff ε).mp hε
  have hδa_pos : zero_Q < backwardQ (forwardQ ε / (2 * M_b' + 2)) := by
    rw [zero_Q_lt_iff, forwardQ_right_inv]
    exact div_pos hfε_pos (by linarith)
  have hδb_pos : zero_Q < backwardQ (forwardQ ε / (2 * M_a + 2)) := by
    rw [zero_Q_lt_iff, forwardQ_right_inv]
    exact div_pos hfε_pos (by linarith)
  obtain ⟨N_a, hN_a⟩ := ha (backwardQ (forwardQ ε / (2 * M_b' + 2))) hδa_pos
  obtain ⟨N_b, hN_b⟩ := hb (backwardQ (forwardQ ε / (2 * M_a + 2))) hδb_pos
  refine ⟨max N_a N_b, fun n hn => ?_⟩
  have hna := le_trans (le_max_left N_a N_b) hn
  have hnb := le_trans (le_max_right N_a N_b) hn
  have ha_n := (absRatVR_sub_lt_iff (a.1 n) (a'.1 n)
    (backwardQ (forwardQ ε / (2 * M_b' + 2)))).mp (hN_a n hna)
  rw [forwardQ_right_inv] at ha_n
  have hb_n := (absRatVR_sub_lt_iff (b.1 n) (b'.1 n)
    (backwardQ (forwardQ ε / (2 * M_a + 2)))).mp (hN_b n hnb)
  rw [forwardQ_right_inv] at hb_n
  rw [absRatVR_sub_lt_iff, forwardQ_mul, forwardQ_mul]
  rw [show forwardQ (a.1 n) * forwardQ (b.1 n) - forwardQ (a'.1 n) * forwardQ (b'.1 n) =
    forwardQ (a.1 n) * (forwardQ (b.1 n) - forwardQ (b'.1 n)) +
    forwardQ (b'.1 n) * (forwardQ (a.1 n) - forwardQ (a'.1 n)) from by ring]
  calc |forwardQ (a.1 n) * (forwardQ (b.1 n) - forwardQ (b'.1 n)) +
          forwardQ (b'.1 n) * (forwardQ (a.1 n) - forwardQ (a'.1 n))|
      ≤ |forwardQ (a.1 n) * (forwardQ (b.1 n) - forwardQ (b'.1 n))| +
          |forwardQ (b'.1 n) * (forwardQ (a.1 n) - forwardQ (a'.1 n))| := abs_add_le _ _
    _ = |forwardQ (a.1 n)| * |forwardQ (b.1 n) - forwardQ (b'.1 n)| +
          |forwardQ (b'.1 n)| * |forwardQ (a.1 n) - forwardQ (a'.1 n)| := by
            simp only [abs_mul]
    _ ≤ M_a * |forwardQ (b.1 n) - forwardQ (b'.1 n)| +
          M_b' * |forwardQ (a.1 n) - forwardQ (a'.1 n)| :=
            add_le_add (mul_le_mul_of_nonneg_right (hMa n) (abs_nonneg _))
                       (mul_le_mul_of_nonneg_right (hMb' n) (abs_nonneg _))
    _ ≤ M_a * (forwardQ ε / (2 * M_a + 2)) +
          M_b' * (forwardQ ε / (2 * M_b' + 2)) :=
            add_le_add
              (mul_le_mul_of_nonneg_left (le_of_lt hb_n) (le_of_lt hMa_pos))
              (mul_le_mul_of_nonneg_left (le_of_lt ha_n) (le_of_lt hMb'_pos))
    _ < forwardQ ε / 2 + forwardQ ε / 2 :=
            add_lt_add
              (mul_div_lt_half M_a (forwardQ ε) (le_of_lt hMa_pos) hfε_pos)
              (mul_div_lt_half M_b' (forwardQ ε) (le_of_lt hMb'_pos) hfε_pos)
    _ = forwardQ ε := by ring

-- ============================================================
-- §IV.4. Operations on FundSeqVR and lifting to ℝ_VR
-- ============================================================

private def irealAdd (a b : FundSeqVR) : FundSeqVR :=
  ⟨fun n => ratAdd (a.1 n) (b.1 n), irealAdd_isFundamentalVR a.1 b.1 a.2 b.2⟩

private def irealSub (a b : FundSeqVR) : FundSeqVR :=
  ⟨fun n => ratSub (a.1 n) (b.1 n), irealSub_isFundamentalVR a.1 b.1 a.2 b.2⟩

private def irealMul (a b : FundSeqVR) : FundSeqVR :=
  ⟨fun n => ratMul (a.1 n) (b.1 n), irealMul_isFundamentalVR a.1 b.1 a.2 b.2⟩

-- §IV.4. Addition on ℝ_VR.
def realAdd : ℝ_VR → ℝ_VR → ℝ_VR :=
  Quotient.lift₂ (fun a b => ⟦irealAdd a b⟧)
    (fun a b a' b' ha hb => Quotient.sound (irealAdd_respects a a' b b' ha hb))

-- §IV.4. Subtraction on ℝ_VR.
def realSub : ℝ_VR → ℝ_VR → ℝ_VR :=
  Quotient.lift₂ (fun a b => ⟦irealSub a b⟧)
    (fun a b a' b' ha hb => Quotient.sound (irealSub_respects a a' b b' ha hb))

-- §IV.4. Multiplication on ℝ_VR.
def realMul : ℝ_VR → ℝ_VR → ℝ_VR :=
  Quotient.lift₂ (fun a b => ⟦irealMul a b⟧)
    (fun a b a' b' ha hb => Quotient.sound (irealMul_respects a a' b b' ha hb))

-- ============================================================
-- §IV.6. Embedding ℚ_VR ↪ ℝ_VR
-- ============================================================

-- §IV.6. Every rational q ∈ ℚ_VR embeds into ℝ_VR
-- as the class of the constant sequence a(n) = q for all n.

-- A constant sequence is fundamental:
-- for any ε > 0 take N = 0; |q ⊟ q| = |0| = 0 < ε.
private theorem constSeq_isFundamentalVR (q : ℚ_VR) :
    isFundamentalVR (fun _ => q) := fun ε hε =>
  ⟨0, fun m n _ _ => by rw [ratSub_self, absRatVR_zero]; exact hε⟩

-- §IV.6. Embedding ℚ_VR ↪ ℝ_VR: embedQ q = [fun _ => q].
def embedQ (q : ℚ_VR) : ℝ_VR :=
  ⟦⟨fun _ => q, constSeq_isFundamentalVR q⟩⟧

-- ============================================================
-- §IV.7 / auxiliary: bridge between isFundamentalVR and IsCauSeq
-- ============================================================

-- isFundamentalVR (two-sided ∀ m n ≥ N) → IsCauSeq abs (one-sided ∀ m ≥ N):
-- use n := N in the two-sided condition.
private theorem forwardQ_seq_isCauSeq (a : FundSeqVR) :
    IsCauSeq abs (fun n => forwardQ (a.1 n)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := a.2 (backwardQ ε) (by rw [zero_Q_lt_iff, forwardQ_right_inv]; exact hε)
  exact ⟨N, fun m hm => by
    have := (absRatVR_sub_lt_iff (a.1 m) (a.1 N) (backwardQ ε)).mp (hN m N hm (le_refl N))
    simpa [forwardQ_right_inv] using this⟩

-- IsCauSeq abs → isFundamentalVR (two-sided):
-- CauSeq.cauchy₂ gives the two-sided bound directly.
private theorem backwardQ_seq_isFundamentalVR (s : CauSeq ℚ abs) :
    isFundamentalVR (fun n => backwardQ (s.val n)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := CauSeq.cauchy₂ s ((zero_Q_lt_iff ε).mp hε)
  exact ⟨N, fun m n hm hn => by
    rw [absRatVR_sub_lt_iff, forwardQ_right_inv, forwardQ_right_inv]
    exact hN m hm n hn⟩

-- s ≈ t (CauSeq.equiv) → cauchyEqVR (backwardQ ∘ s.val) (backwardQ ∘ t.val).
-- Well-definedness witness for backwardR.
private theorem backwardQ_cauchy_equiv (s t : CauSeq ℚ abs) (h : s ≈ t) :
    cauchyEqVR (fun n => backwardQ (s.val n)) (fun n => backwardQ (t.val n)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (forwardQ ε) ((zero_Q_lt_iff ε).mp hε)
  exact ⟨N, fun n hn => by
    rw [absRatVR_sub_lt_iff, forwardQ_right_inv, forwardQ_right_inv]
    exact hN n hn⟩

-- cauchyEqVR a.1 a'.1 → Real.mk (forwardQ ∘ a.1) = Real.mk (forwardQ ∘ a'.1).
-- Well-definedness witness for forwardR.
private theorem forwardR_respects (a a' : FundSeqVR) (h : a ≈ a') :
    Real.mk ⟨fun n => forwardQ (a.1 n), forwardQ_seq_isCauSeq a⟩ =
    Real.mk ⟨fun n => forwardQ (a'.1 n), forwardQ_seq_isCauSeq a'⟩ := by
  rw [Real.mk_eq]
  intro ε hε
  obtain ⟨N, hN⟩ := h (backwardQ ε) (by rw [zero_Q_lt_iff, forwardQ_right_inv]; exact hε)
  exact ⟨N, fun n hn => by
    have := (absRatVR_sub_lt_iff (a.1 n) (a'.1 n) (backwardQ ε)).mp (hN n hn)
    simpa [forwardQ_right_inv] using this⟩

-- ============================================================
-- §IV.7 / auxiliary: forwardR and backwardR (bijection components)
-- ============================================================

-- §IV.7. forwardR: ℝ_VR → ℝ.
-- Maps the class of a Cauchy sequence a to Real.mk (forwardQ ∘ a).
def forwardR : ℝ_VR → ℝ :=
  Quotient.lift
    (fun a => Real.mk ⟨fun n => forwardQ (a.1 n), forwardQ_seq_isCauSeq a⟩)
    (fun a a' h => forwardR_respects a a' h)

-- §IV.7. backwardR: ℝ → ℝ_VR.
-- Maps r to the class of (backwardQ ∘ representative of r.cauchy).
-- Uses Quotient.liftOn (not Quotient.out) for an explicit well-definedness proof.
def backwardR (r : ℝ) : ℝ_VR :=
  Quotient.liftOn r.cauchy
    (fun s => ⟦⟨fun n => backwardQ (s.val n), backwardQ_seq_isFundamentalVR s⟩⟧)
    (fun s t hst => Quotient.sound (backwardQ_cauchy_equiv s t hst))

-- §IV.7. backwardR is right inverse of forwardR: forwardR (backwardR r) = r.
-- Key steps: (Real.mk s).cauchy = ⟦s⟧ (rfl); forwardQ ∘ backwardQ = id (forwardQ_right_inv).
theorem forwardR_right_inv (r : ℝ) : forwardR (backwardR r) = r :=
  Real.ind_mk r (fun s => by
    -- backwardR (Real.mk s) = ⟦⟨backwardQ ∘ s.val, ...⟩⟧ definitionally
    -- (since (Real.mk s).cauchy = ⟦s⟧ by rfl and Quotient.liftOn ⟦s⟧ f hf = f s)
    have h1 : backwardR (Real.mk s) =
        ⟦⟨fun n => backwardQ (s.val n), backwardQ_seq_isFundamentalVR s⟩⟧ := rfl
    rw [h1]
    simp only [forwardR, Quotient.lift_mk]
    rw [Real.mk_eq]
    intro ε hε
    exact ⟨0, fun n _ => by
      change |forwardQ (backwardQ (s.val n)) - s.val n| < ε
      rw [forwardQ_right_inv, sub_self, abs_zero]; exact hε⟩)

-- §IV.7. backwardR is left inverse of forwardR: backwardR (forwardR x) = x.
-- Key steps: forwardR reduces by Quotient.lift_mk; backwardR reduces by rfl;
-- then backwardQ ∘ forwardQ = id (forwardQ_left_inv).
theorem forwardR_left_inv (x : ℝ_VR) : backwardR (forwardR x) = x := by
  induction x using Quotient.inductionOn with
  | h a =>
    -- forwardR ⟦a⟧ reduces via Quotient.lift_mk after unfolding forwardR
    simp only [forwardR, Quotient.lift_mk]
    -- backwardR (Real.mk ...) reduces via rfl ((Real.mk s).cauchy = ⟦s⟧)
    have h2 : backwardR (Real.mk ⟨fun n => forwardQ (a.1 n), forwardQ_seq_isCauSeq a⟩) =
        ⟦⟨fun n => backwardQ (forwardQ (a.1 n)),
          backwardQ_seq_isFundamentalVR
            ⟨fun n => forwardQ (a.1 n), forwardQ_seq_isCauSeq a⟩⟩⟧ := rfl
    rw [h2]
    apply Quotient.sound
    -- rw would fail: the subtype proof depends on the rewritten function.
    -- change + simp_rw avoids the dependent-rewrite issue.
    change cauchyEqVR (fun n => backwardQ (forwardQ (a.1 n))) a.1
    simp_rw [forwardQ_left_inv]
    exact cauchyEqVR_refl a.1

-- ============================================================
-- §IV.5 / §IV.8. Division on ℝ_VR via the isomorphism
-- ============================================================

-- §IV.5. Division on ℝ_VR: transfer division from ℝ through the bijection.
-- When q = 0 inherits ℝ's junk value: forwardR 0 = 0, and ℝ gives p / 0 = 0.
noncomputable def realDiv (p q : ℝ_VR) : ℝ_VR := backwardR (forwardR p / forwardR q)

-- ============================================================
-- §IV.7. Isomorphism ℝ_VR ≅ ℝ
-- ============================================================

-- §IV.7. Isomorphism structure ℝ_VR ≅ ℝ:
-- bijection forwardR/backwardR + preservation of 0, 1, ⊕, ⊗, ⊟, ⊘.
structure RealVRRealIso where
  forward : ℝ_VR → ℝ
  backward : ℝ → ℝ_VR
  right_inv : ∀ r, forward (backward r) = r
  left_inv : ∀ x, backward (forward x) = x
  preserveZero : forward (embedQ zero_Q) = 0
  preserveOne : forward (embedQ (embedZ one_Z)) = 1
  preserveAdd : ∀ p q, forward (realAdd p q) = forward p + forward q
  preserveMul : ∀ p q, forward (realMul p q) = forward p * forward q
  preserveSub : ∀ p q, forward (realSub p q) = forward p - forward q
  preserveDiv : ∀ p q, forward (realDiv p q) = forward p / forward q

-- Pointwise equality of sequences implies equality of Real.mk.
-- Uses CauSeq.sub_apply to unfold |(f-g) n| in the definition of ≈.
private theorem mk_eq_of_pointwise {f g : CauSeq ℚ abs}
    (h : ∀ n, f n = g n) : Real.mk f = Real.mk g := by
  rw [Real.mk_eq]
  intro ε hε
  exact ⟨0, fun n _ => by
    rw [CauSeq.sub_apply, h n, sub_self, abs_zero]
    exact hε⟩

-- §IV.7. Theorem IV.7: ℝ_VR ≅ ℝ.
-- Methodological note: the restriction of §IV.1 (computable functions only)
-- is metatheoretic and cannot be expressed as a Lean 4 type.
-- The formalisation proves the structural isomorphism without this restriction.
def Theorem_IV_7_RealVR_Real : RealVRRealIso where
  forward   := forwardR
  backward  := backwardR
  right_inv := forwardR_right_inv
  left_inv  := forwardR_left_inv
  preserveZero := by
    simp only [embedQ, forwardR, Quotient.lift_mk]
    rw [← Real.mk_zero]
    apply mk_eq_of_pointwise
    intro n
    simp only [CauSeq.zero_apply]
    exact forwardQ_zero_Q
  preserveOne := by
    simp only [embedQ, forwardR, Quotient.lift_mk]
    rw [← Real.mk_one]
    apply mk_eq_of_pointwise
    intro n
    simp only [CauSeq.one_apply]
    exact forwardQ_one_Q
  preserveAdd := by
    intro p q
    induction p using Quotient.inductionOn with | h a => ?_
    induction q using Quotient.inductionOn with | h b => ?_
    simp only [realAdd, irealAdd, forwardR, Quotient.lift_mk]
    rw [← Real.mk_add]
    apply mk_eq_of_pointwise
    intro n
    simp only [CauSeq.add_apply]
    exact forwardQ_add (a.1 n) (b.1 n)
  preserveMul := by
    intro p q
    induction p using Quotient.inductionOn with | h a => ?_
    induction q using Quotient.inductionOn with | h b => ?_
    simp only [realMul, irealMul, forwardR, Quotient.lift_mk]
    rw [← Real.mk_mul]
    apply mk_eq_of_pointwise
    intro n
    simp only [CauSeq.mul_apply]
    exact forwardQ_mul (a.1 n) (b.1 n)
  preserveSub := by
    intro p q
    induction p using Quotient.inductionOn with | h a => ?_
    induction q using Quotient.inductionOn with | h b => ?_
    simp only [realSub, irealSub, forwardR, Quotient.lift_mk]
    rw [sub_eq_add_neg, ← Real.mk_neg, ← Real.mk_add]
    apply mk_eq_of_pointwise
    intro n
    simp only [CauSeq.add_apply, CauSeq.neg_apply]
    rw [forwardQ_sub]
    ring
  preserveDiv := fun p q => by
    simp only [realDiv]
    exact forwardR_right_inv _

end VR.Numbers
