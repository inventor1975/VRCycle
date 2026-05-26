-- VRCycle: Algebra/ModeA.lean
-- Operational Algebra v0.1.0 — Stage 3: Mode A theorems + PredicateOperationality instance.
-- Operational Algebra v0.2.0 — Stage 5: Ring Mode A theorems + PredicateOperationality for OperationalRing.
--
-- STAGE: 3 (v0.1.0); 5 (v0.2.0). SOURCE: PLAN.md Stage 3 (v0.1.0); Stage 5 (v0.2.0).
--
-- ## Position statement
-- This file is the **critical connection** between the VR-Apparatus framework
-- and the operational algebra module.
--
-- It accomplishes two things:
--
-- (A) **PredicateOperationality instance**: registers `OperationalAddGroup G`
--     as an instance of the existing apparatus class `PredicateOperationality`
--     (VRCycle.Apparatus.Wrapping). This is the formal statement that
--     OperationalAddGroup is NOT a parallel apparatus — it IS an instance
--     of the universal predicate-wrapping apparatus.
--
-- (B) **Mode A theorems**: proves that all additive group operations (+, -, -, nsmul)
--     preserve the operational predicate — they are Mode A operations in the
--     predicate-wrapping apparatus sense (VRCycle.Apparatus.ModeA).
--
-- ## Critical checkpoint: apparatus reuse status
--
-- **Result: apparatus applies cleanly without modification.**
--
-- The `PredicateOperationality` class (zero-field marker, Prop-valued) requires
-- no adaptation for the algebraic setting. The instance is `⟨⟩` — a bare
-- declaration with no proof obligations. This is exactly the design intent:
-- the apparatus is generic over (T, P) pairs, and (G, IsOperational) is one
-- such pair.
--
-- The `IsModeAOp` and `IsModeAOp₂` definitions (VRCycle.Apparatus.ModeA)
-- require no modification. They are ∀-over-P statements, and our
-- `OperationalAddGroup.IsOperational` plugs in as P directly.
--
-- **Finding A3 (apparatus reuse confirmed)**: The predicate-wrapping apparatus
-- from VR-Apparatus v1.0.0 applies to additive groups without modification.
-- No parallel apparatus structures required. OperationalAddGroup instances
-- are registered as PredicateOperationality instances by the zero-cost marker
-- mechanism. This confirms the apparatus framework's generality beyond analysis.
--
-- ## Axiom profile observations (Finding A4)
--
-- Unexpected asymmetry within Stage 3 objects:
--   instPredOpAddGroup   []   -- zero-field marker, no proof obligations
--   add_isModeAOp        []   -- +  (HAdd, from AddSemigroup infrastructure)
--   sub_isModeAOp        []   -- -  (Sub + simp, sub_eq_add_neg)
--   nsmul_isOperational  []   -- •  (induction, AddMonoid)
--   neg_isModeAOp  [propext]  -- - (Neg, from SubNegMonoid/Neg infrastructure)
--
-- Negation alone pulls propext; addition and subtraction do not.
-- Root cause: elaborating `(-x : G)` in the generic `G : Type*` context with
-- `[OperationalAddGroup G]` touches the `Neg G` infrastructure (from SubNegMonoid)
-- at a point where propext enters. Addition and scalar multiplication avoid this.
--
-- This sub-ceiling asymmetry within a single typeclass is a new observation.
-- Subtraction is `[]` (via sub_eq_add_neg + add_isOperational + neg_isOperational)
-- even though it logically "uses" negation — the simp-path avoids the propext
-- that the direct neg elaboration triggers.
--
-- This mirrors Finding S5-B from VR-Apparatus (axiom asymmetry between apparatus
-- tracks) but at a finer granularity: asymmetry within operations of the SAME
-- algebraic structure.
--
-- ## Mode A recap (from VRCycle.Apparatus.ModeA)
--
-- IsModeAOp P f   :=  ∀ x : T, P x → P (f x)         (unary)
-- IsModeAOp₂ P f  :=  ∀ x y : T, P x → P y → P (f x y) (binary)
--
-- "f is Mode A" means f stays in the operational register. Equivalently,
-- f lifts to a function on the operational subtype { x : T // P x }.
-- Lifting is Subtype.mk — definitionally trivial (Finding A from VR-Apparatus).

import VRCycle.Apparatus.ModeA
import VRCycle.Algebra.AddGroup
import VRCycle.Algebra.Instances
import VRCycle.Algebra.Ring

namespace VR.Algebra

open VR.Apparatus

-- ============================================================
-- §1. PredicateOperationality instance — apparatus registration
-- ============================================================

/-- `OperationalAddGroup G` registers as a predicate-wrapping apparatus.

**Formal apparatus anatomy**:
  T = G  (any additive group with OperationalAddGroup instance)
  P = IsOperational  (the operational predicate from the typeclass)
  Identity mode = AsPoint  (objects identified by position in G)

**Zero-cost registration**: `PredicateOperationality G IsOperational` is a
zero-field marker class (Prop-valued, no obligations). The instance is ⟨⟩.
The mathematical content — closure under operations — lives in the Mode A
theorems below (§2), not in this declaration.

**Design note**: this mirrors the existing VR-Audit instance
`instance : PredicateOperationality ℝ IsComputableReal := ⟨⟩` (Wrapping.lean).
The algebra cycle adds a NEW family of (G, IsOperational) pairs to the apparatus
framework using the same zero-cost mechanism.

## Axiom profile: [] -/
instance instPredOpAddGroup {G : Type*} [OperationalAddGroup G] :
    PredicateOperationality G OperationalAddGroup.IsOperational := ⟨⟩

-- ============================================================
-- §2. Mode A theorems — group operations preserve operationality
-- ============================================================

/-- Addition is a Mode A binary operation for `OperationalAddGroup G`.

**Statement**: `(· + ·)` preserves the operational predicate — if x and y are
operational, so is x + y.

**Proof**: immediate from `add_isOperational`, the closure axiom of `OperationalAddGroup`.
The Mode A certificate IS the typeclass field.

**Apparatus reading**: addition lifts to a binary operation on the operational
subtype `{ x : G // IsOperational x }` at zero cost (via `modeA_liftFn₂`).

This is the algebraic analogue of `isComputableReal_add_isModeA` from
VRCycle.Apparatus.ModeA (which wraps `IsComputableReal_add`), but proved
trivially — all work is in the typeclass closure axiom.

## Axiom profile: [] -/
theorem add_isModeAOp {G : Type*} [OperationalAddGroup G] :
    PredicateOperationality.IsModeAOp₂ (P := OperationalAddGroup.IsOperational (G := G)) (· + ·) :=
  fun _ _ ha hb => OperationalAddGroup.add_isOperational ha hb

/-- Negation is a Mode A unary operation for `OperationalAddGroup G`.

**Statement**: `(fun a => -a)` preserves the operational predicate.

**Proof**: immediate from `neg_isOperational`, the closure axiom for negation.

**Note on axiom profile**: this theorem depends on `[propext]` (vs `[]` for
`add_isModeAOp`). See Finding A4 in the module doc-comment: elaborating `(-x : G)`
in a generic context touches SubNegMonoid/Neg infrastructure where propext enters.

## Axiom profile: [propext] -/
theorem neg_isModeAOp {G : Type*} [OperationalAddGroup G] :
    PredicateOperationality.IsModeAOp
      (P := OperationalAddGroup.IsOperational (G := G)) (fun a => -a) :=
  fun _ ha => OperationalAddGroup.neg_isOperational ha

/-- Subtraction is a Mode A binary operation for `OperationalAddGroup G`.

**Statement**: `(· - ·)` preserves the operational predicate.

**Proof**: rewrite `a - b = a + (-b)` via `sub_eq_add_neg` (propositional equality
in general AddGroup — not definitional), then apply `add_isOperational` and
`neg_isOperational`.

**Why simp?** The goal has the form `IsOperational ((fun x1 x2 => x1 - x2) a b)`.
The outer lambda is not beta-reduced before `rw`, but `simp only [sub_eq_add_neg]`
handles beta reduction and the rewrite simultaneously. Direct `rw [sub_eq_add_neg]`
fails (pattern `?a - ?b` not found in unreduced form).

**Surprising axiom profile**: `[]` despite using negation structurally. The
simp-path bypasses the propext trigger in negation elaboration. This contributes
to Finding A4 (intra-operation axiom asymmetry).

## Axiom profile: [] -/
theorem sub_isModeAOp {G : Type*} [OperationalAddGroup G] :
    PredicateOperationality.IsModeAOp₂ (P := OperationalAddGroup.IsOperational (G := G)) (· - ·) :=
  fun _ _ ha hb => by
    simp only [sub_eq_add_neg]
    exact OperationalAddGroup.add_isOperational ha (OperationalAddGroup.neg_isOperational hb)

/-- Natural number scalar multiplication preserves operationality.

**Statement**: if `a : G` is operational and `n : ℕ`, then `n • a` is operational.

**Proof**: by induction on `n`.
- Base case `n = 0`: `0 • a = 0` (by `zero_nsmul`); `0` is operational by
  `zero_isOperational`.
- Inductive step `n → n+1`: `(n+1) • a = n • a + a` (by `succ_nsmul`);
  `n • a` is operational by IH; `a` is operational by hypothesis;
  sum is operational by `add_isOperational`.

**Note**: this is not captured by `IsModeAOp` or `IsModeAOp₂` (those are for
fixed arity). The statement is: for each `n : ℕ`, the map `a ↦ n • a` is Mode A.
Equivalently: `∀ n, IsModeAOp (P := IsOperational) (n • ·)`. We state it in the
more readable ∀-quantified form.

## Axiom profile: [] -/
theorem nsmul_isOperational {G : Type*} [OperationalAddGroup G] {a : G}
    (ha : OperationalAddGroup.IsOperational a) :
    ∀ n : ℕ, OperationalAddGroup.IsOperational (n • a)
  | 0     => by
      rw [zero_nsmul]
      exact OperationalAddGroup.zero_isOperational
  | n + 1 => by
      rw [succ_nsmul]
      exact OperationalAddGroup.add_isOperational (nsmul_isOperational ha n) ha

-- ============================================================
-- §3. Concrete demonstrations applied to ℤ
-- ============================================================
-- The ℤ instance (instOperationalAddGroupInt) is imported from
-- VRCycle.Algebra.Instances. All demonstrations use the trivial
-- predicate (IsOperational = fun _ => True), so witnesses are trivial.

/-- `add_isModeAOp` specialised to ℤ: addition is Mode A for the ℤ apparatus. -/
example : PredicateOperationality.IsModeAOp₂
    (P := OperationalAddGroup.IsOperational (G := ℤ)) (· + ·) :=
  add_isModeAOp

/-- Negation of any integer is operational (via Mode A certificate). -/
example (n : ℤ) (hn : OperationalAddGroup.IsOperational n) :
    OperationalAddGroup.IsOperational (-n) :=
  neg_isModeAOp n hn

/-- Concrete: `-7 : ℤ` is operational. -/
example : OperationalAddGroup.IsOperational (-(7 : ℤ)) :=
  neg_isModeAOp 7 trivial

/-- Concrete: `3 - 5 : ℤ` is operational. -/
example : OperationalAddGroup.IsOperational ((3 : ℤ) - 5) :=
  sub_isModeAOp 3 5 trivial trivial

/-- Concrete: `4 • 3 : ℤ` is operational. -/
example : OperationalAddGroup.IsOperational ((4 : ℕ) • (3 : ℤ)) :=
  nsmul_isOperational (ha := trivial) 4

-- ============================================================
-- §4. PredicateOperationality instance for OperationalRing (Stage 5)
-- ============================================================

/-- `OperationalRing R` registers as a predicate-wrapping apparatus.

**Formal apparatus anatomy** (ring extension):
  T = R  (any ring with OperationalRing instance)
  P = OperationalRing.IsOperational  (the operational predicate from the typeclass)
  Identity mode = AsPoint  (objects identified by position in R)

**Finding A3 extension to rings**: `PredicateOperationality` applies to rings without
modification — the same zero-field marker mechanism used for additive groups (v0.1.0)
works identically for rings. This confirms that the apparatus framework is genuinely
generic over (T, P) pairs, not specialised to any algebraic structure.

**Predicate note**: when `[OperationalRing R]` is in context, the bridge instance
`OperationalRing.toOperationalAddGroup` also provides `[OperationalAddGroup R]`,
which in turn gives `instPredOpAddGroup` (from §1). Both `instPredOpAddGroup` and
`instPredOpRing` declare `PredicateOperationality R IsOperational` with the same P
(definitionally equal). Lean resolves ambiguity trivially since both instances are `⟨⟩`.

**`one_isOperational_bridge` recognition**: PLAN.md Stage 5 listed `one_isOperational_bridge`
as a separate theorem. Applying recognition discipline: in v0.1.0, no `zero_isOperational_bridge`
theorem exists — the field is accessed directly via `OperationalAddGroup.zero_isOperational`.
`OperationalRing.one_isOperational` IS the bridge. A separate wrapper theorem would be a
trivial alias with no new content. Omitted per recognition discipline.

**`mul_chain_isOperational` recognition**: listed as "Natural extension of binary closure."
Derivable from `mul_isModeAOp` via `IsModeAOp.compose` applied iteratively. No new
mathematical content; no separate theorem needed. Omitted per recognition discipline.

## Axiom profile: [] -/
instance instPredOpRing {R : Type*} [OperationalRing R] :
    PredicateOperationality R OperationalRing.IsOperational := ⟨⟩

-- ============================================================
-- §5. Ring Mode A theorems (Stage 5)
-- ============================================================

/-- Multiplication is a Mode A binary operation for `OperationalRing R`.

**Statement**: `(· * ·)` preserves the operational predicate — if a and b are
operational, so is a * b.

**Proof**: immediate from `mul_isOperational`, the closure axiom of `OperationalRing`.
The Mode A certificate IS the typeclass field.

**Apparatus reading**: multiplication lifts to a binary operation on the operational
subtype `{ r : R // IsOperational r }` at zero cost (via `modeA_liftFn₂`).

This is the ring analogue of `add_isModeAOp` from v0.1.0 ModeA.lean — same pattern,
same axiom profile, different operation.

**Apparatus reuse confirmed**: `IsModeAOp₂` from VRCycle.Apparatus.ModeA requires
no modification for the multiplicative context. Finding A3 extends to ring multiplication.

## Axiom profile: [] -/
theorem mul_isModeAOp {R : Type*} [OperationalRing R] :
    PredicateOperationality.IsModeAOp₂ (P := OperationalRing.IsOperational (R := R)) (· * ·) :=
  fun _ _ ha hb => OperationalRing.mul_isOperational ha hb

/-- Natural number powers preserve operationality.

**Statement**: if `a : R` is operational and `n : ℕ`, then `a ^ n` is operational.

**Proof**: by induction on `n`.
- Base case `n = 0`: `a^0 = 1` (by `pow_zero`); `1` is operational by `one_isOperational`.
- Inductive step `n → n+1`: `a^(n+1) = a^n * a` (by `pow_succ`); `a^n` is operational
  by IH; `a` is operational by hypothesis; product operational by `mul_isOperational`.

**Note**: `pow_succ` gives `a^(n+1) = a^n * a` — the IH applies to `a^n` (left factor),
then `mul_isOperational IH ha` concludes. This matches the algebraic order of multiplication
in `Monoid.npow`.

**Parallel to `nsmul_isOperational`** (v0.1.0): same inductive structure, `+` replaced by `*`,
`0` replaced by `1`, `zero_nsmul/succ_nsmul` replaced by `pow_zero/pow_succ`.

**Not captured by `IsModeAOp`**: the statement is ∀ n, the map `a ↦ a^n` is Mode A.
Equivalently: `∀ n, IsModeAOp (P := IsOperational) (a ^ n • ·)`. Stated in readable
∀-quantified form, as in v0.1.0's `nsmul_isOperational`.

## Axiom profile: [] -/
theorem npow_isOperational {R : Type*} [OperationalRing R] {a : R}
    (ha : OperationalRing.IsOperational a) :
    ∀ n : ℕ, OperationalRing.IsOperational (a ^ n)
  | 0     => by rw [pow_zero]; exact OperationalRing.one_isOperational
  | n + 1 => by
      rw [pow_succ]
      exact OperationalRing.mul_isOperational (npow_isOperational ha n) ha

-- ============================================================
-- §6. Concrete demonstrations — ring Mode A applied to ℤ
-- ============================================================

/-- `mul_isModeAOp` specialised to ℤ: multiplication is Mode A for the ℤ apparatus. -/
example : PredicateOperationality.IsModeAOp₂
    (P := OperationalRing.IsOperational (R := ℤ)) (· * ·) :=
  mul_isModeAOp

/-- Concrete: `2 * 3 : ℤ` is operational via Mode A theorem. -/
example : OperationalRing.IsOperational ((2 : ℤ) * 3) :=
  mul_isModeAOp 2 3 trivial trivial

/-- Concrete: `2 ^ 5 : ℤ` is operational via `npow_isOperational`. -/
example : OperationalRing.IsOperational ((2 : ℤ) ^ 5) :=
  npow_isOperational (ha := trivial) 5

-- ============================================================
-- §7. Concrete demonstrations — ring Mode A applied to ZMod 5
-- ============================================================

/-- Concrete: `3 * 4 : ZMod 5` is operational via Mode A theorem. -/
example : OperationalRing.IsOperational ((3 : ZMod 5) * 4) :=
  mul_isModeAOp 3 4 trivial trivial

/-- Concrete: `2 ^ 3 : ZMod 5` is operational via `npow_isOperational`. -/
example : OperationalRing.IsOperational ((2 : ZMod 5) ^ 3) :=
  npow_isOperational (ha := trivial) 3

-- ============================================================
-- Axiom audit — Stages 3 (v0.1.0) and 5 (v0.2.0), ModeA.lean
-- ============================================================
-- STAGE: 3 (v0.1.0); 5 (v0.2.0). SOURCE: PLAN.md Stage 3 (v0.1.0); Stage 5 (v0.2.0).
-- LEAN OBJECTS:
--   v0.1.0 Stage 3 (5 objects):
--     instPredOpAddGroup    (instance, PredicateOperationality G IsOperational)
--     add_isModeAOp         (theorem, IsModeAOp₂ (+))
--     neg_isModeAOp         (theorem, IsModeAOp (fun a => -a))
--     sub_isModeAOp         (theorem, IsModeAOp₂ (-))
--     nsmul_isOperational   (theorem, ∀ n : ℕ, IsOperational (n • a))
--   v0.2.0 Stage 5 (3 objects):
--     instPredOpRing        (instance, PredicateOperationality R IsOperational)
--     mul_isModeAOp         (theorem, IsModeAOp₂ (*))
--     npow_isOperational    (theorem, ∀ n : ℕ, IsOperational (a ^ n))
-- RECOGNITION DISCIPLINE (Stage 5):
--   one_isOperational_bridge: OMITTED — OperationalRing.one_isOperational IS the bridge.
--     No separate theorem needed; cf. v0.1.0 has no zero_isOperational_bridge.
--   mul_chain_isOperational: OMITTED — derivable from mul_isModeAOp via compose.
--     No new content.
-- AXIOM AUDIT:
--   v0.1.0 objects:
--     instPredOpAddGroup  []         — zero-field marker
--     add_isModeAOp       []         — pure algebraic
--     sub_isModeAOp       []         — simp-path avoids propext
--     nsmul_isOperational []         — induction on ℕ
--     neg_isModeAOp       [propext]  — Neg elaboration (Finding A4)
--   v0.2.0 objects:
--     instPredOpRing      []         — zero-field marker (apparatus reuse confirmed)
--     mul_isModeAOp       []         — pure algebraic (no propext, cf. add_isModeAOp)
--     npow_isOperational  []         — induction on ℕ (cf. nsmul_isOperational)
-- Finding A3 confirmed for rings: apparatus reuse without modification.
-- Finding A4 ring analogue: multiplication is [] like addition; no propext.
-- CHECKS: no sorry, no admit.

#print axioms instPredOpAddGroup
#print axioms add_isModeAOp
#print axioms neg_isModeAOp
#print axioms sub_isModeAOp
#print axioms nsmul_isOperational
#print axioms instPredOpRing
#print axioms mul_isModeAOp
#print axioms npow_isOperational

end VR.Algebra
