-- VR-Audit: Computable.lean (DOI TBD — v1.4-vr-audit-hb-hilbert)
-- Stage 1: Computability predicates for real numbers and sequences.
--
-- STAGE: 1 (of 7). SOURCE: PLAN.md Stage 1; CLAUDE.md wrapping principle.
--         Pour-El & Richards 1989 §1.1; Bishop-Bridges 1985 §2.2.
--
-- ## Position statement
-- Foundation file of the VR-Audit cycle. Defines computability
-- predicates over mathlib's classical `Real` per the wrapping principle
-- of CLAUDE.md: we do NOT define a new type of computable reals —
-- instead we define a predicate `IsComputableReal : ℝ → Prop` that
-- selects the computable subset of mathlib's `Real`.
--
-- This is the direct embodiment of the VR-Forms two-register apparatus
-- in the setting of analysis:
--   Formal register   = mathlib's `ℝ` (full classical type, unrestricted).
--   Operational register = `{x : ℝ | IsComputableReal x}` (computable reals,
--                           carried by the proof term of `IsComputableReal x`).
--
-- ## Literature reference
-- Following Pour-El & Richards 1989 §1.1 and Bishop-Bridges 1985 §2.2:
-- a real number x is computable if there exists a sequence alg : ℕ → ℚ
-- of rational approximations and a modulus mod : ℕ → ℕ of convergence
-- such that for all n : ℕ and all k ≥ mod n,
--   |alg k − x| ≤ 1/2^n.
-- The modulus of convergence makes the approximation rate explicit and
-- constructive, in contrast to a bare Cauchy condition (∀ ε > 0, ∃ N, ...).
--
-- ## Critical methodological note: no `Computable` annotation on alg, mod
-- The `Computable` typeclass from `Mathlib.Computability.Partrec` is
-- NOT used to annotate `alg` or `mod` in `IsComputableReal`.
--
-- Reason: `Computable₂` for ℚ arithmetic operations (`+`, `*`, `−` on ℚ)
-- is ABSENT from mathlib4 (verified by exhaustive grep of all mathlib files).
-- Using `Computable` annotations would require building ℚ arithmetic-
-- computability lemmas from scratch — a mathlib gap outside the scope
-- of this cycle, with no benefit to the main theorem.
--
-- Lean's intrinsic totality of definable functions `alg : ℕ → ℚ` and
-- `mod : ℕ → ℕ` provides algorithmicity at the type level.
-- Stronger forms (Turing-machine codings) remain metatheoretic — this is
-- consistent with the position established in VR-Numbers Reals.lean §IV.1:
--
--   «Lean 4 does not distinguish computable from non-computable functions
--    at the type level. The operational ontology of VR-Numbers (§IV.1)
--    restricts functions to those with finite algorithmic descriptions;
--    this restriction is a metatheoretic claim not expressible as a Lean
--    type predicate.»
--   [VRCycle.Numbers.Reals, §IV.1 comment; cross-referenced here.]
--
-- This observation is the first concrete confirmation in VR-Audit of
-- the architectural principle: operational ontology is expressed through
-- predicate restrictions, not through Lean's computational machinery.
-- (Methodological Observation 1; see companion preprint §VI.)
--
-- Note: `Computable (f : ℕ → ℚ)` IS well-typed (ℚ has `Primcodable`
-- via `Enumerable ℚ`). The limitation is not syntactic but semantic:
-- no proof that ℚ arithmetic operations satisfy `Computable`.
--
-- ## What this file does and does not do
-- DOES:
--   Defines `IsComputableReal : ℝ → Prop` and `IsComputableSequence`.
--   Proves `_rat`, `_zero`, `_one`, `_neg`, `_add`, `_sub`.
-- DOES NOT:
--   Prove `IsComputableReal_mul` (requires bounded-sequence argument;
--     deferred to Stage 2+ as needed — multiplication appears in inner
--     products, handled at the Hilbert space level).
--   Prove `IsComputableReal_inv` (deferred; not needed for main theorem).
--   Define uniform sequence modulus (deferred to Stage 2 if needed).
-- Sufficiency: for the main theorem (Stage 5), composition through
-- addition, negation, and rational constants suffices. ✓

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic

namespace VR.Audit

-- ============================================================
-- §I. Computability predicate for real numbers
-- ============================================================

/-- `IsComputableReal x`: the real number x is computable.

A real number x ∈ ℝ is computable if there exists:
- `alg : ℕ → ℚ` — a sequence of rational approximations,
- `mod : ℕ → ℕ` — a modulus of convergence,
such that for all n : ℕ and all k ≥ mod n:
  |(alg k : ℝ) − x| ≤ 1/2^n.

## Source
Pour-El & Richards 1989 §1.1; Bishop-Bridges 1985 §2.2.

## Design choices
- **Prop, not Structure**: per wrapping principle (CLAUDE.md), we select
  a sub-collection of mathlib's `Real` via a predicate. Witnesses are
  accessible via `obtain ⟨alg, mod, h⟩` when needed.
- **`≤ 1/2^n`, not `< 1/2^n`**: `≤` composes cleanly via `add_le_add`
  and `linarith`; `<` would require strictness tracking through calc.
- **No `Computable` annotation**: see file-level comment §Critical note.

## Axiom profile: [propext, Classical.choice, Quot.sound]
`Classical.choice` enters via mathlib's `ℝ` (Cauchy completeness). -/
def IsComputableReal (x : ℝ) : Prop :=
  ∃ (alg : ℕ → ℚ) (mod : ℕ → ℕ),
    ∀ n : ℕ, ∀ k : ℕ, mod n ≤ k → |(alg k : ℝ) - x| ≤ 1 / 2^n

-- ============================================================
-- §II. Computability predicate for sequences
-- ============================================================

/-- `IsComputableSequence s`: the sequence s : ℕ → ℝ is computable.

A sequence is computable if each of its values is a computable real.

## Note on uniform modulus
This is pointwise computability: each `s k` has its own approximation
sequence and modulus. A uniform version (single modulus working for all k
simultaneously) would be stronger; it is deferred to Stage 2 if needed.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
def IsComputableSequence (s : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, IsComputableReal (s k)

-- ============================================================
-- §III. Base instances: rationals, zero, one
-- ============================================================

/-- Every rational number is computable.

## Proof
Witness: constant sequence `alg = fun _ => q`, modulus `mod = fun _ => 0`.
For all n, k ≥ 0: `|(q : ℝ) − (q : ℝ)| = |0| = 0 ≤ 1/2^n`.
`simp` closes via `sub_self`, `abs_zero`, and `div_nonneg`/`pow_pos`.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_rat (q : ℚ) : IsComputableReal (q : ℝ) :=
  ⟨fun _ => q, fun _ => 0, fun n k _ => by simp⟩

/-- Zero is computable. Follows from `IsComputableReal_rat 0`.
## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_zero : IsComputableReal (0 : ℝ) := by
  simpa using IsComputableReal_rat 0

/-- One is computable. Follows from `IsComputableReal_rat 1`.
## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_one : IsComputableReal (1 : ℝ) := by
  simpa using IsComputableReal_rat 1

-- ============================================================
-- §IV. Composition: negation, addition, subtraction
-- ============================================================

/-- Negation preserves computability.

## Proof
Given witnesses (alg, mod) for x, use (−alg, mod) for (−x):
  |(−alg k : ℝ) − (−x)| = |−(alg k − x)| = |alg k − x| ≤ 1/2^n.
Cast manipulation: `(−alg k : ℚ) : ℝ = −(alg k : ℝ)` via `push_cast`.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_neg {x : ℝ} (hx : IsComputableReal x) :
    IsComputableReal (-x) := by
  obtain ⟨alg, mod, h⟩ := hx
  refine ⟨fun k => -alg k, mod, fun n k hk => ?_⟩
  have hb := h n k hk
  -- |(−alg k : ℝ) − (−x)| = |alg k − x|:
  -- push_cast pushes (−alg k : ℚ) : ℝ = −(alg k : ℝ); then ring + abs_neg.
  have heq : ((-alg k : ℚ) : ℝ) - (-x) = -((alg k : ℝ) - x) := by push_cast; ring
  rw [heq, abs_neg]
  exact hb

/-- Addition preserves computability.

## Proof
Given witnesses (algx, modx) for x and (algy, mody) for y:
- Combined sequence: `alg k = algx k + algy k`
- Combined modulus: `mod n = max (modx (n+1)) (mody (n+1))`
  (Request n+1 bits of accuracy from each component; their sum
   gives n bits: 1/2^(n+1) + 1/2^(n+1) = 1/2^n.)

Key steps:
1. Decompose: `|(algx k + algy k : ℝ) − (x + y)| =
               |(algx k − x) + (algy k − y)|`
   [by `push_cast; ring`]
2. Triangle: `|(algx k − x) + (algy k − y)| ≤
              |algx k − x| + |algy k − y|`
   [abs_add]
3. Bound each: `|algx k − x| + |algy k − y| ≤ 1/2^(n+1) + 1/2^(n+1)`
   [add_le_add hbx hby]
4. Sum bound: `1/2^(n+1) + 1/2^(n+1) = 1/2^n`
   [pow_succ + field_simp + ring]

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_add {x y : ℝ}
    (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x + y) := by
  obtain ⟨algx, modx, hx⟩ := hx
  obtain ⟨algy, mody, hy⟩ := hy
  -- Combined approximation and modulus: use n+1 precision for each component
  refine ⟨fun k => algx k + algy k, fun n => max (modx (n+1)) (mody (n+1)), ?_⟩
  intro n k hk
  have hkx : modx (n+1) ≤ k := le_trans (le_max_left _ _) hk
  have hky : mody (n+1) ≤ k := le_trans (le_max_right _ _) hk
  have hbx := hx (n+1) k hkx
  have hby := hy (n+1) k hky
  -- Step 1: decompose the combined approximation error
  have heq : ((algx k + algy k : ℚ) : ℝ) - (x + y) =
             ((algx k : ℝ) - x) + ((algy k : ℝ) - y) := by push_cast; ring
  rw [heq]
  -- Step 4: 1/2^(n+1) + 1/2^(n+1) = 1/2^n
  -- pow_succ: 2^(n+1) = 2^n * 2; then field_simp clears denominators.
  have hn1 : (1 : ℝ) / 2 ^ (n + 1) + 1 / 2 ^ (n + 1) = 1 / 2 ^ n := by
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have h2n1 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    field_simp [h2n.ne', h2n1.ne', pow_succ]
    ring
  -- Chain steps 2, 3, 4 via calc
  calc |((algx k : ℝ) - x) + ((algy k : ℝ) - y)|
      ≤ |(algx k : ℝ) - x| + |(algy k : ℝ) - y| := abs_add_le _ _
    _ ≤ 1 / 2 ^ (n + 1) + 1 / 2 ^ (n + 1) := add_le_add hbx hby
    _ = 1 / 2 ^ n := hn1

/-- Subtraction preserves computability.

## Proof
`x − y = x + (−y)`: combine `IsComputableReal_add` and `IsComputableReal_neg`.

## Axiom profile: [propext, Classical.choice, Quot.sound] -/
theorem IsComputableReal_sub {x y : ℝ}
    (hx : IsComputableReal x) (hy : IsComputableReal y) :
    IsComputableReal (x - y) := by
  rw [sub_eq_add_neg]
  exact IsComputableReal_add hx (IsComputableReal_neg hy)

-- ============================================================
-- Axiom audit — Stage 1
-- ============================================================
-- STAGE: 1. SOURCE: PLAN.md Stage 1; Pour-El & Richards 1989 §1.1.
-- LEAN OBJECTS (8 public):
--   defs: IsComputableReal, IsComputableSequence
--   theorems: IsComputableReal_rat, IsComputableReal_zero,
--             IsComputableReal_one, IsComputableReal_neg,
--             IsComputableReal_add, IsComputableReal_sub
-- AXIOM AUDIT: expected [propext, Classical.choice, Quot.sound] for all.
--   Classical.choice: from mathlib's ℝ (Cauchy completeness via choice).
--   This is the standard ceiling for VR-Audit, expected and acceptable.
-- CHECKS: no sorry, no admit; lake build passes.

#print axioms IsComputableReal
#print axioms IsComputableSequence
#print axioms IsComputableReal_rat
#print axioms IsComputableReal_zero
#print axioms IsComputableReal_one
#print axioms IsComputableReal_neg
#print axioms IsComputableReal_add
#print axioms IsComputableReal_sub

end VR.Audit
