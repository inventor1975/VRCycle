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
import VRCycle.Algebra.MulGroup
import VRCycle.Algebra.Field

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
-- §8. OperationalGroup Mode A theorems (v0.3.0 Stage 4)
-- ============================================================
--
-- Namespace: VR.Algebra.MulGroup
-- Reason: v0.2.0 has `VR.Algebra.mul_isModeAOp` for OperationalRing.
-- MulGroup theorems use a nested namespace to avoid the name collision.
-- Full names: VR.Algebra.MulGroup.mul_isModeAOp, .inv_isModeAOp, etc.
--
-- Symmetry with additive side (v0.1.0 §1-2):
--   add_isModeAOp    ↔  MulGroup.mul_isModeAOp
--   neg_isModeAOp    ↔  MulGroup.inv_isModeAOp
--   sub_isModeAOp    ↔  MulGroup.div_isModeAOp
--   nsmul_isOp       ↔  MulGroup.npow_isOperational  (ℕ-power)
--   [absent v0.1.0]  ↔  MulGroup.zpow_isOperational  (ℤ-power — NEW, richer than additive)
--
-- Vitaly's Stage 4 question: does multiplicative side become richer due to
-- DivInvMonoid/Field infrastructure? Answer: YES — zpow (ℤ-exponentiation)
-- is available for any Group via DivInvMonoid.zpow, but v0.1.0 additive side
-- only proved nsmul (ℕ). The additive analogue would be zsmul : ℤ → G → G
-- from SubNegMonoid, but was deferred in v0.1.0.
--
-- Design decision: include zpow_isOperational in Stage 4 to fully exploit
-- Group structure. This makes MulGroup Mode A complete: all Group operations
-- (1, *, ⁻¹, /, npow, zpow) have Mode A certificates.
-- Additive zsmul_isOperational left as noted gap (consistent: v0.1.0 was silent on it).

namespace VR.Algebra.MulGroup

/-- `OperationalGroup G` registers as a predicate-wrapping apparatus.

**Finding A3 extension (third structure)**: `PredicateOperationality` applies to
multiplicative groups without modification. The same zero-field marker mechanism
used for additive groups (v0.1.0) and rings (v0.2.0) works identically here.
This confirms the apparatus framework is genuinely generic over (T, P) pairs,
independent of whether the algebraic structure is additive or multiplicative.

**Predicate note**: when `[OperationalGroup G]` is in context, this instance
provides `PredicateOperationality G OperationalGroup.IsOperational`. If also
`[OperationalField K]` (which gives `OperationalGroup Kˣ` in Stage 5), then
the predicate is `OperationalGroup.IsOperational` for the units group. No conflict.

## Axiom profile: [] -/
instance instPredOpMulGroup {G : Type*} [OperationalGroup G] :
    PredicateOperationality G OperationalGroup.IsOperational := ⟨⟩

/-- Multiplication is a Mode A binary operation for `OperationalGroup G`.

**Statement**: `(· * ·)` preserves the operational predicate — if a and b are
operational, so is a * b.

**Proof**: immediate from `mul_isOperational`, the closure axiom of `OperationalGroup`.

**Namespace**: `VR.Algebra.MulGroup` to avoid collision with `VR.Algebra.mul_isModeAOp`
(v0.2.0, for `OperationalRing`). Full name: `VR.Algebra.MulGroup.mul_isModeAOp`.

**Apparatus reading**: multiplication lifts to a binary operation on
`{ g : G // IsOperational g }` at zero cost (via `modeA_liftFn₂`).

**Finding A3 for multiplicative groups**: apparatus reuse without modification.
`IsModeAOp₂` from VRCycle.Apparatus.ModeA requires no changes for the
multiplicative context, just as it required none for rings.

## Axiom profile: [] -/
theorem mul_isModeAOp {G : Type*} [OperationalGroup G] :
    PredicateOperationality.IsModeAOp₂
      (P := OperationalGroup.IsOperational (G := G)) (· * ·) :=
  fun _ _ ha hb => OperationalGroup.mul_isOperational ha hb

/-- Inversion is a Mode A unary operation for `OperationalGroup G`.

**Statement**: `(·⁻¹)` preserves the operational predicate.

**Proof**: immediate from `inv_isOperational`, the closure axiom for inversion.

**Multiplicative analogue of `neg_isModeAOp`** (v0.1.0): same structure, `⁻¹` in
place of `-`. The axiom profile is expected to mirror Finding A4 (neg_isModeAOp
pulled [propext] due to Neg elaboration); verify in audit.

## Axiom profile: [propext] (predicted — Inv elaboration, cf. Finding A4) -/
theorem inv_isModeAOp {G : Type*} [OperationalGroup G] :
    PredicateOperationality.IsModeAOp
      (P := OperationalGroup.IsOperational (G := G)) (·⁻¹) :=
  fun _ ha => OperationalGroup.inv_isOperational ha

/-- Division is a Mode A binary operation for `OperationalGroup G`.

**Statement**: `(· / ·)` preserves the operational predicate.

**Derivation**: `a / b = a * b⁻¹` in any `Group G` (from `div_eq_mul_inv`,
available via `DivInvMonoid`). Closure follows from `mul_isOperational` and
`inv_isOperational`.

**Multiplicative analogue of `sub_isModeAOp`** (v0.1.0): same simp-path pattern.
`sub_isModeAOp` used `sub_eq_add_neg`; this uses `div_eq_mul_inv`.
Expected axiom profile `[]` (simp-path bypasses propext, cf. sub_isModeAOp).

## Axiom profile: [] (predicted — simp-path like sub_isModeAOp) -/
theorem div_isModeAOp {G : Type*} [OperationalGroup G] :
    PredicateOperationality.IsModeAOp₂
      (P := OperationalGroup.IsOperational (G := G)) (· / ·) :=
  fun a b ha hb => by
    simp only [div_eq_mul_inv]
    exact OperationalGroup.mul_isOperational ha (OperationalGroup.inv_isOperational hb)

/-- Natural number powers preserve operationality for `OperationalGroup G`.

**Statement**: if `a : G` is operational and `n : ℕ`, then `a ^ n` is operational.

**Proof**: by induction on `n`.
- Base case `n = 0`: `a^0 = 1` (by `pow_zero`); `1` is operational by `one_isOperational`.
- Inductive step `n → n+1`: `a^(n+1) = a^n * a` (by `pow_succ`); IH + `ha` + `mul_isOperational`.

**Parallel structure**:
  nsmul_isOperational (v0.1.0):  `n • a` by ℕ induction, `zero_nsmul`/`succ_nsmul`.
  npow_isOperational (v0.2.0):   `a ^ n` by ℕ induction, `pow_zero`/`pow_succ` (for Ring).
  This theorem (v0.3.0):         `a ^ n` by ℕ induction, `pow_zero`/`pow_succ` (for Group).

The proof is identical to v0.2.0's `npow_isOperational` but over `OperationalGroup`
(which has `one_isOperational` and `mul_isOperational` but NOT `zero_isOperational`).
Both are in scope without conflict: v0.2.0's theorem takes `[OperationalRing R]`;
this theorem takes `[OperationalGroup G]`. Lean resolves by typeclass parameter.

## Axiom profile: [] -/
theorem npow_isOperational {G : Type*} [OperationalGroup G] {a : G}
    (ha : OperationalGroup.IsOperational a) :
    ∀ n : ℕ, OperationalGroup.IsOperational (a ^ n)
  | 0     => by rw [pow_zero]; exact OperationalGroup.one_isOperational
  | n + 1 => by
      rw [pow_succ]
      exact OperationalGroup.mul_isOperational (npow_isOperational ha n) ha

/-- Integer powers preserve operationality for `OperationalGroup G`.

**Statement**: if `a : G` is operational and `n : ℤ`, then `a ^ n` is operational.

**Proof**: by case analysis on `n : ℤ`.
- `Int.ofNat n`: `a ^ (↑n : ℤ) = a ^ n` (by `zpow_natCast`); operational by `npow_isOperational`.
- `Int.negSucc n`: `a ^ (Int.negSucc n) = (a ^ (n+1))⁻¹` (by `zpow_negSucc`);
  `a ^ (n+1)` is operational by `npow_isOperational`; `⁻¹` preserves by `inv_isOperational`.

**Why zpow and not just npow?**
`Group G extends DivInvMonoid G` which provides `zpow : ℤ → G → G`. Integer exponentiation
is native to groups via their inverse structure — negative powers `a^(-n) = (a^n)⁻¹`.
This is genuinely NEW compared to v0.1.0 (additive side only proved `nsmul` for ℕ) and
v0.2.0 (ring `npow_isOperational` for ℕ). The v0.3.0 multiplicative group is richer:
the full integer exponent range is operational.

**Enrichment over additive side**: v0.1.0 has `nsmul_isOperational` (ℕ-scalar). The ℤ-scalar
analogue (`zsmul_isOperational`) was not proved in v0.1.0 (additive groups do have
`zsmul : ℤ → G → G` via SubNegMonoid). Stage 4 proves the multiplicative version here;
the additive gap is noted as a possible v0.4.0 addition.

## Axiom profile: [] (predicted — natCast case from npow, negSucc case from inv + npow)

**Proof note**: `rw [zpow_natCast]` fails — after pattern matching on `Int.ofNat n`,
the goal contains `a ^ (Int.ofNat n : ℤ)` while `zpow_natCast` rewrites `a ^ (↑n : ℤ)`
(syntactically different via Nat.cast vs Int.ofNat, though definitionally equal).
Using `exact` directly works: Lean's unification handles definitional equality.
`zpow` defaults to `zpowRec` for generic Group, which reduces `Int.ofNat n → a ^ n`
and `Int.negSucc n → (a ^ (n+1))⁻¹` definitionally. -/
theorem zpow_isOperational {G : Type*} [OperationalGroup G] {a : G}
    (ha : OperationalGroup.IsOperational a) :
    ∀ n : ℤ, OperationalGroup.IsOperational (a ^ n)
  | Int.ofNat n   => by
      change OperationalGroup.IsOperational (a ^ (n : ℤ))
      rw [zpow_natCast]; exact npow_isOperational ha n
  | Int.negSucc n => by
      rw [zpow_negSucc]
      exact OperationalGroup.inv_isOperational (npow_isOperational ha (n + 1))

end VR.Algebra.MulGroup

-- ============================================================
-- §9. OperationalField Mode A (v0.3.0 Stage 4)
-- ============================================================
--
-- OperationalField → OperationalRing → OperationalAddGroup (via bridges).
-- Therefore ALL ring Mode A theorems (§5) apply automatically to OperationalField
-- via the bridge: mul_isModeAOp, npow_isOperational, add_isModeAOp, etc.
--
-- The ONLY genuinely new Mode A theorem for OperationalField is:
--   inv_isModeAOp_field : IsModeAOp (P := OperationalField.IsOperational) (·⁻¹)
-- This mirrors MulGroup.inv_isModeAOp but is stated for OperationalField (different P).
--
-- PredicateOperationality instance: OperationalField → OperationalRing gives
-- instPredOpRing, but that uses OperationalRing.IsOperational. Since the bridge
-- sets OperationalRing.IsOperational := OperationalField.IsOperational definitionally,
-- instPredOpRing fires. For directness and safety, we add instPredOpField explicitly.

/-- `OperationalField K` registers as a predicate-wrapping apparatus.

**Finding A3 extension (fourth structure)**: apparatus reuse confirmed for fields.
Same zero-cost `⟨⟩` pattern as AddGroup, Ring, and MulGroup. No modification.

**Relationship to instPredOpRing**: when `[OperationalField K]` is in scope,
the bridge `toOperationalRing` fires, and `instPredOpRing` provides
`PredicateOperationality K OperationalRing.IsOperational`. This instance provides
`PredicateOperationality K OperationalField.IsOperational` — same predicate
definitionally, declared directly for syntactic safety.

## Axiom profile: [propext, Quot.sound] (inherited from OperationalField, via Field) -/
instance instPredOpField {K : Type*} [OperationalField K] :
    PredicateOperationality K OperationalField.IsOperational := ⟨⟩

/-- Multiplicative inversion is a Mode A unary operation for `OperationalField K`.

**Statement**: `(·⁻¹)` preserves the operational predicate — if a is operational,
so is a⁻¹.

**Proof**: immediate from `inv_isOperational`, the closure axiom of `OperationalField`.

**Relationship to MulGroup.inv_isModeAOp**: both are Mode A theorems for inversion.
MulGroup.inv_isModeAOp works for any `[OperationalGroup G]`.
This theorem works for any `[OperationalField K]` — a different typeclass, different P.
After Stage 5 (Units bridge), `[OperationalField K] → OperationalGroup Kˣ`, and
`MulGroup.inv_isModeAOp` will apply to `Kˣ`. This theorem applies to `K` directly.

**Concrete use**: `OperationalField.IsOperational (a⁻¹)` when `IsOperational a`.
For ℚ: `inv_isOperational : IsOperational (1/2 : ℚ) → IsOperational (1/2)⁻¹`.

**Finding A15 — import-context ceiling escalation**:
The axiom profile of this theorem is `[propext, Classical.choice, Quot.sound]`,
which is the ANALYSIS ceiling, not the algebraic `[propext, Quot.sound]`.
This is NOT because the logic of `inv_isOperational` requires `Classical.choice`.

Root cause: `VRCycle.Apparatus.ModeA` (imported above) transitively imports
`VRCycle.Audit.Computable`, which imports `Mathlib.Data.Real.Basic`.
`Mathlib.Data.Real.Basic` introduces many Mathlib instances into the elaboration
context, including ones that change how Lean resolves `Inv K` for a generic
`[Field K]`. When `(·⁻¹)` is elaborated in the type of `IsModeAOp ... (·⁻¹)`,
Lean selects a resolution path (influenced by these imported instances) that
involves `Classical.choice`. This is an **import-context effect**, not a
logical property of the theorem.

Contrast with `instPredOpField` (same `OperationalField` ceiling, `⟨⟩` proof,
no `(·⁻¹)` in the type): `[propext, Quot.sound]` — no `Classical.choice`.
The `Classical.choice` enters only when `(·⁻¹)` is elaborated in the ModeA context.

## Axiom profile: [propext, Classical.choice, Quot.sound]
## (import-context effect — Finding A15; logical ceiling is [propext, Quot.sound]) -/
theorem inv_isModeAOp_field {K : Type*} [OperationalField K] :
    PredicateOperationality.IsModeAOp
      (P := OperationalField.IsOperational (K := K)) (·⁻¹) :=
  fun _ ha => OperationalField.inv_isOperational ha

-- ============================================================
-- §10. Concrete demonstrations — OperationalField Mode A applied to ℚ
-- ============================================================

/-- `inv_isModeAOp_field` specialised to ℚ: inversion is Mode A for the ℚ apparatus. -/
example : PredicateOperationality.IsModeAOp
    (P := OperationalField.IsOperational (K := ℚ)) (·⁻¹) :=
  inv_isModeAOp_field

/-- Concrete: `(1/2 : ℚ)⁻¹` is operational via Mode A certificate. -/
example : OperationalField.IsOperational ((1 / 2 : ℚ)⁻¹) :=
  inv_isModeAOp_field (1 / 2) trivial

/-- Finding A3 confirmed for OperationalField: apparatus applies at zero cost.
`instPredOpField` fires as `⟨⟩` with no additional obligations. -/
example : PredicateOperationality ℚ OperationalField.IsOperational :=
  inferInstance

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
--   v0.3.0 Stage 4 (9 objects):
--     MulGroup.instPredOpMulGroup  (instance, PredicateOperationality G IsOperational)
--     MulGroup.mul_isModeAOp       (theorem, IsModeAOp₂ (*))
--     MulGroup.inv_isModeAOp       (theorem, IsModeAOp (·⁻¹))
--     MulGroup.div_isModeAOp       (theorem, IsModeAOp₂ (/))
--     MulGroup.npow_isOperational  (theorem, ∀ n : ℕ, IsOperational (a ^ n))
--     MulGroup.zpow_isOperational  (theorem, ∀ n : ℤ, IsOperational (a ^ n))
--     instPredOpField              (instance, PredicateOperationality K IsOperational)
--     inv_isModeAOp_field          (theorem, IsModeAOp (·⁻¹) for OperationalField)
-- AXIOM AUDIT (v0.3.0 confirmed by build):
--     MulGroup.instPredOpMulGroup  []         — zero-field marker (confirmed)
--     MulGroup.mul_isModeAOp       []         — pure algebraic (confirmed)
--     MulGroup.inv_isModeAOp       [propext]  — Inv elaboration, Finding A4 (confirmed)
--     MulGroup.div_isModeAOp       []         — simp-path, cf. sub_isModeAOp (confirmed)
--     MulGroup.npow_isOperational  []         — ℕ induction (confirmed)
--     MulGroup.zpow_isOperational  []         — Int case split (confirmed)
--     instPredOpField              [propext, Quot.sound]  — Field ceiling (confirmed)
--     inv_isModeAOp_field          [propext, Classical.choice, Quot.sound]
--                                  — import-context effect, Finding A15 (confirmed)
--                                    Logical ceiling is [propext, Quot.sound];
--                                    Classical.choice enters via Mathlib.Data.Real.Basic
--                                    (through apparatus import chain) affecting Inv K
--                                    elaboration in the IsModeAOp type. Contrast:
--                                    instPredOpField [propext, Quot.sound] — no (·⁻¹)
--                                    in type, no import-context escalation.
-- Finding A3 extended: apparatus applies to MulGroup and Field (4th structure).
-- Finding A15: import-context ceiling escalation — elaborating (·⁻¹) in Field K context
--   when Mathlib.Data.Real.Basic is transitively imported escalates from [propext, Quot.sound]
--   to [propext, Classical.choice, Quot.sound]. This is an import effect, not logic.
-- CHECKS: no sorry, no admit.

#print axioms instPredOpAddGroup
#print axioms add_isModeAOp
#print axioms neg_isModeAOp
#print axioms sub_isModeAOp
#print axioms nsmul_isOperational
#print axioms instPredOpRing
#print axioms mul_isModeAOp
#print axioms npow_isOperational
#print axioms VR.Algebra.MulGroup.instPredOpMulGroup
#print axioms VR.Algebra.MulGroup.mul_isModeAOp
#print axioms VR.Algebra.MulGroup.inv_isModeAOp
#print axioms VR.Algebra.MulGroup.div_isModeAOp
#print axioms VR.Algebra.MulGroup.npow_isOperational
#print axioms VR.Algebra.MulGroup.zpow_isOperational
#print axioms instPredOpField
#print axioms inv_isModeAOp_field

end VR.Algebra
