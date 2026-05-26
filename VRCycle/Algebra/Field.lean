-- VRCycle: Algebra/Field.lean
-- Operational Algebra v0.3.0 — Stage 2: OperationalField typeclass + bridge instance.
--                               Stage 5: OperationalField → OperationalGroup Kˣ bridge.
--
-- STAGE: 2 (of 6, v0.3.0); 5 (Units bridge). SOURCE: PLAN.md Stage 2, Stage 5.
--
-- ## Position statement
-- This file defines the VR operational layer on top of mathlib's field typeclass.
-- Two deliverables:
--
--   Stage 2A: OperationalField (K : Type*) — field + operational predicate.
--   Stage 2B: OperationalField.toOperationalRing — bridge instance to OperationalRing.
--   Stage 5A: OperationalField.toOperationalGroupUnits — bridge to OperationalGroup Kˣ.
--
-- This extends the ring apparatus from v0.2.0 to the full field structure, adding
-- the closure axiom for multiplicative inverse (inv_isOperational). It completes
-- the algebraic hierarchy: groups (v0.1.0) → rings (v0.2.0) → fields (v0.3.0).
-- Stage 5 adds the bridge to multiplicative groups via units, justifying
-- OperationalGroup's revival from Finding A0 (Finding A12 concrete delivery).
--
-- ## Mathlib reconnaissance (Stage 2)
--
-- ### Field hierarchy (Mathlib.Algebra.Field.Defs)
--
--   class Field (K : Type u) extends CommRing K, DivisionRing K
--     CommRing K extends Ring K, CommMonoid K
--     DivisionRing K extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K
--       mul_inv_cancel : ∀ (a : K), a ≠ 0 → a * a⁻¹ = 1
--       inv_zero : (0 : K)⁻¹ = 0
--
--   Key: Field K already contains Ring K (via both CommRing and DivisionRing paths),
--   AddGroup K (via Ring K), and DivInvMonoid K (multiplicative inverse).
--   The operation ⁻¹ : K → K is inherited from DivInvMonoid K.
--
-- ### Diamond analysis: Field K → Ring K
--
--   Field K has two paths to Ring K:
--     (1) Field K → CommRing K → Ring K
--     (2) Field K → DivisionRing K → Ring K
--   This diamond is INTERNAL to mathlib's Field K definition — mathlib resolves it.
--
--   OperationalField K extends Field K via a SINGLE `toField : Field K` field.
--   Therefore OperationalField K has exactly ONE path to Ring K (through Field K).
--   No new diamond introduced at the OperationalField level.
--
-- ### Bridge diamond: OperationalField → OperationalRing
--
--   Pattern mirrors v0.2.0: OperationalRing.toOperationalAddGroup.
--   Bridge provides OperationalRing K from [OperationalField K]:
--     toRing := inferInstance   — Ring K inferred from Field K (clean chain)
--
--   Diamond check (Stage 3): when OperationalField ℚ is instantiated, Lean will have
--   two paths to OperationalRing ℚ?
--     - Via bridge OperationalField.toOperationalRing (Stage 3 provides OperationalField ℚ)
--     - Direct OperationalRing ℚ instance?
--   Answer: v0.2.0 did NOT add OperationalRing ℚ (only ℤ and ZMod n). So Stage 3
--   adds the first and only path to OperationalRing ℚ via this bridge. No diamond.
--
--   Two paths to OperationalAddGroup ℚ after Stage 3:
--     - Via chain: OperationalField ℚ → OperationalRing ℚ → OperationalAddGroup ℚ
--     - Direct v0.1.0 instance for ℚ? No — v0.1.0 had only ℤ and ZMod n.
--   Again: single chain, no diamond.
--
-- ## Mathlib reconnaissance (Stage 5) — Units K and bridge design
--
-- ### Units K structure (Mathlib.Algebra.Group.Units.Basic)
--
--   structure Units (α : Type u) [Monoid α] where
--     val    : α         -- the unit element
--     inv    : α         -- its stored inverse
--     val_inv : val * inv = 1
--     inv_val : inv * val = 1
--   postfix "ˣ" => Units
--
--   instance Units.instGroup [Monoid α] : Group αˣ   -- automatic
--   (u : K)  := u.val  (coercion via Units.val)
--
--   Key coercions from Mathlib.Algebra.GroupWithZero.Units.Basic:
--     Units.val_one  :  ((1 : Kˣ) : K) = 1
--     Units.val_mul  :  ((u * v : Kˣ) : K) = (u : K) * (v : K)
--     Units.val_inv_eq_inv_val [DivisionMonoid K] :
--                    ((u⁻¹ : Kˣ) : K) = (u : K)⁻¹
--
--   DivisionMonoid K is synthesised from Field K (via DivisionRing.toInvolutiveInv?).
--   In practice: with Mathlib.Algebra.GroupWithZero.Units.Basic imported,
--   Units.val_inv_eq_inv_val u works for [Field K].
--
-- ### Bridge instance design
--
--   The bridge maps OperationalField K → OperationalGroup Kˣ:
--     IsOperational (u : Kˣ) := OperationalField.IsOperational (u : K)
--     one_isOperational  : simp [Units.val_one] + OperationalField.one_isOperational
--     mul_isOperational  : simp [Units.val_mul] + OperationalField.mul_isOperational
--     inv_isOperational  : simp [Units.val_inv_eq_inv_val] + OperationalField.inv_isOperational
--
-- ### Axiom profile note (Stage 5)
--
--   import Mathlib.Algebra.GroupWithZero.Units.Basic does NOT escalate the axiom
--   profiles of OperationalField or OperationalField.toOperationalRing (confirmed
--   by test). Those objects stay at [propext, Quot.sound].
--   The bridge instance itself has [propext, Classical.choice, Quot.sound] —
--   the same import-context effect as Finding A15: Mathlib.Algebra.GroupWithZero.Units.Basic
--   changes how Lean resolves Inv K for [Field K], causing Classical.choice to
--   appear in proof terms that elaborate (·⁻¹) with Units.val_inv_eq_inv_val.
--   The logical content of the bridge does not require Classical.choice.
--
-- ## Recognition discipline analysis (Stage 2)
--
-- PLAN.md Stage 2 requires explicit check: "does OperationalField add anything
-- beyond OperationalRing K + Field K?"
--
-- Analysis:
--   OperationalField K encapsulates:
--     - All OperationalRing closure axioms (zero, add, neg, one, mul): 5 axioms.
--     - ONE new axiom: inv_isOperational — closure under ⁻¹.
--   OperationalRing K + [Field K] would give: all ring closure + field operations,
--   but NO inv_isOperational unless added separately.
--
-- Verdict: OperationalField is NOT redundant. The axiom inv_isOperational is
-- genuinely new content — it is the operational counterpart of the field's
-- distinctive operation. This is OPTION A from PLAN.md: keep OperationalField as
-- a separate typeclass. The extra axiom justifies the abstraction.
--
-- Contrast with Finding A9 (v0.2.0): OperationalCommRing was redundant because
-- CommRing adds only mul_comm — a theorem about existing operations, not a new
-- operation requiring operational closure. Field's ⁻¹ is a genuinely new operation
-- with its own closure requirement.
--
-- ## inv_isOperational and zero
--
-- Since Field K satisfies inv_zero : (0 : K)⁻¹ = 0, the axiom
-- inv_isOperational covers the zero case:
--   inv_isOperational (zero_isOperational) : IsOperational (0⁻¹)
-- Since 0⁻¹ = 0 and IsOperational 0 holds by zero_isOperational, this is
-- propositionally consistent: IsOperational (0⁻¹) = IsOperational 0 = True
-- (for the trivial predicate). No special treatment of zero needed.
-- For non-trivial predicates (v0.4.0+), instances would need to verify this.
--
-- ## Namespace policy (Stage 4 note)
--
-- v0.2.0 ModeA.lean contains `VR.Algebra.mul_isModeAOp` for OperationalRing.
-- Stage 4 will add Mode A theorems for both OperationalGroup and OperationalField.
-- To avoid naming conflicts:
--   - OperationalGroup Mode A theorems: namespace VR.Algebra.MulGroup
--     (full name: VR.Algebra.MulGroup.mul_isModeAOp)
--   - OperationalField Mode A theorems: derivable from OperationalRing via bridge;
--     inv_isModeAOp in VR.Algebra namespace (no ring analogue; no conflict).
-- This policy is established here; implemented in Stage 4.
--
-- ## Axiom profile — UNEXPECTED RESULT (Stage 2 Finding)
--
-- Predicted: [] for class definition (consistent with OperationalAddGroup and OperationalRing).
-- Actual:    [propext, Quot.sound] for BOTH OperationalField and the bridge instance.
--
-- Root cause (confirmed via #print axioms Field, DivisionRing, Ring):
--   Ring              : []
--   DivisionRing      : [propext, Quot.sound]
--   Field             : [propext, Quot.sound]
--
-- DivisionRing K extends RatCast K. Rat.castRec and related infrastructure
-- (nnratCast_def, ratCast_def, qsmul_def) in DivisionRing involve proof terms
-- about ℚ, which uses quotient constructions → Quot.sound. propext enters
-- from elaborating the cast function's propositional equalities.
--
-- OperationalField extends Field K, which IS [propext, Quot.sound]. Therefore
-- OperationalField cannot be cleaner than its base class — the axiom profile
-- is inherited structurally.
--
-- This is the first typeclass DEFINITION in the cycle to carry non-empty axioms.
-- Previous typeclasses: OperationalAddGroup ([]), OperationalRing ([]).
-- The difference: Ring extends pure algebraic Semiring + AddCommGroup (no cast);
-- Field extends DivisionRing which brings RatCast K (ℚ-related) infrastructure.
--
-- Finding A13 (Stage 2): Field class-level axiom inheritance.
-- The axiom profile of an OperationalField instance is bounded below by
-- [propext, Quot.sound] regardless of the predicate — it cannot be [] because
-- Field itself is [propext, Quot.sound]. This is consistent with Finding A10
-- ("ceiling determined by underlying type's infrastructure"): here the ceiling
-- is determined by Field K's RatCast infrastructure, not the operational layer.

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import VRCycle.Algebra.Ring
import VRCycle.Algebra.MulGroup

namespace VR.Algebra

-- ============================================================
-- §1. OperationalField — fields with operational predicate
-- ============================================================

/-- `OperationalField K`: a field K equipped with a VR operational predicate.

## Overview

Extends mathlib's `Field K` with a predicate `IsOperational : K → Prop` that
selects the *operational* sub-collection of K in the sense of the VR programme.

An element `x : K` is **operational** if `IsOperational x` holds. Operationality
is the VR programme's signature concept (Vitaly Reznik): it asserts **explicit
witness of construction**, as opposed to merely classically existing.

## Closure axioms

The operational elements are closed under all field operations:

- **`zero_isOperational`**: the additive identity `0 : K` is operational.
- **`add_isOperational`**: if `a` and `b` are operational, so is `a + b`.
- **`neg_isOperational`**: if `a` is operational, so is `-a`.
- **`one_isOperational`**: the multiplicative identity `1 : K` is operational.
- **`mul_isOperational`**: if `a` and `b` are operational, so is `a * b`.
- **`inv_isOperational`**: if `a` is operational, so is `a⁻¹`.

The first five axioms mirror `OperationalRing` exactly. The sixth —
`inv_isOperational` — is the genuine new content of `OperationalField`:
it is the operational counterpart of the field's distinctive operation.

Note on `0⁻¹`: in any `Field K`, `(0 : K)⁻¹ = 0` by convention (`Field.inv_zero`).
Thus `inv_isOperational zero_isOperational : IsOperational (0⁻¹)` is equivalent
to `zero_isOperational` propositionally. For the trivial predicate `fun _ => True`
this is immediate; non-trivial predicates (v0.4.0+) must verify the zero case.

Note: `sub_isOperational` and `div_isOperational` are NOT separate axioms.
`a - b = a + (-b)` and `a / b = a * b⁻¹` in any field. Closure under these
derived operations follows from the axioms above and will be proved as Mode A
theorems (`sub_isModeAOp`, `div_isModeAOp`) in Stage 4.

## Algebraic hierarchy completion

This typeclass completes the v0.3.0 hierarchy:

  OperationalAddGroup G (v0.1.0):  0, +, -
  OperationalRing R (v0.2.0):      0, +, -, 1, *
  OperationalField K (v0.3.0):     0, +, -, 1, *, ⁻¹   ← this typeclass

Each step adds exactly the new operations of the extended algebraic structure.
`OperationalField` adds `⁻¹` over `OperationalRing`, just as `OperationalRing`
added `1, *` over `OperationalAddGroup`.

## Relationship to OperationalRing (v0.2.0)

A bridge instance `[OperationalField K] → OperationalRing K` is provided in §2,
setting `OperationalRing.IsOperational := OperationalField.IsOperational`.
This ensures: whenever a field is operational, its underlying ring is operational
with the same predicate. One predicate per element, multiple typeclasses.

The chain of bridges (all with the same predicate):
  OperationalField K → OperationalRing K → OperationalAddGroup K

## Apparatus connection

Stage 4 will register `OperationalField` as an instance of `PredicateOperationality`
(VRCycle.Apparatus.Wrapping). Finding A3 (apparatus reuse without modification)
is expected to confirm again: the zero-field marker mechanism applies to fields
as it did to additive groups and rings.

## Concrete instances (v0.3.0)

- **ℚ** (Stage 3): `IsOperational := fun _ => True`.
  Every rational number is trivially operational — explicit numerator/denominator
  representation is always available. This is the first instance beyond ℤ and ZMod n.

## On "operational" vs "computable"

"Operational" is intentional and specific to the VR programme. It is not:
- *Computable* (Turing): stronger, requires Turing-machine encoding.
- *Constructive* (constructive mathematics): different project.

Operationality asserts explicit witness of construction appropriate to the domain.

## Axiom profile: [] -/
class OperationalField (K : Type*) extends Field K where
  /-- Predicate identifying operational elements of the field.

  Each instance supplies its own interpretation of "operational". Common choices:
  - `fun _ => True` — trivially operational. Used for ℚ in v0.3.0.
  - A predicate encoding an explicit construction witness (v0.4.0+).

  The predicate need not be decidable. Classical mathematics applies within
  the formal register K; operationality is a layer on top. -/
  IsOperational : K → Prop
  /-- The additive identity `0 : K` is operational. -/
  zero_isOperational : IsOperational 0
  /-- Addition preserves operationality. -/
  add_isOperational : ∀ {a b : K},
    IsOperational a → IsOperational b → IsOperational (a + b)
  /-- Negation preserves operationality. -/
  neg_isOperational : ∀ {a : K}, IsOperational a → IsOperational (-a)
  /-- The multiplicative identity `1 : K` is operational. -/
  one_isOperational : IsOperational 1
  /-- Multiplication preserves operationality. -/
  mul_isOperational : ∀ {a b : K},
    IsOperational a → IsOperational b → IsOperational (a * b)
  /-- Multiplicative inversion preserves operationality.

  Covers the zero case via field convention: `(0 : K)⁻¹ = 0`.
  Since `zero_isOperational` ensures `IsOperational 0`, the instance
  `inv_isOperational zero_isOperational` gives `IsOperational (0⁻¹) = IsOperational 0`. -/
  inv_isOperational : ∀ {a : K}, IsOperational a → IsOperational a⁻¹

-- ============================================================
-- §2. Bridge: OperationalField → OperationalRing (canonical instance)
-- ============================================================

/-- Every operational field is an operational ring.

**Bridge**: if `K` carries an `OperationalField K` instance, then it automatically
carries `OperationalRing K` with the SAME operational predicate.

**Mathematical content**: an operational field's operational elements form an
operational ring — the field's ring structure, restricted to operational elements,
is closed under `0`, `+`, `-`, `1`, `*` (from the field closure axioms, minus
`inv_isOperational`). The field axiom `inv_isOperational` is not needed here —
it extends the ring to a field, not restricts it.

**Predicate identity**: `OperationalRing.IsOperational := OperationalField.IsOperational`.
Definitional equality — same predicate, same element, same witness. One predicate
per element; two typeclasses agree via this bridge.

**Chain of bridges** (same predicate throughout):
  OperationalField K  →  OperationalRing K  →  OperationalAddGroup K
  (this bridge)            (Ring.lean bridge)

**`toRing := inferInstance`**: `[OperationalField K]` implies `[Field K]` implies
`[Ring K]` through `Field.toCommRing → CommRing.toRing`. The `inferInstance`
synthesiser finds this chain definitionally. Pattern identical to
`OperationalRing.toOperationalAddGroup`'s `toAddGroup := inferInstance`.

**Diamond note**: v0.2.0 did NOT add `OperationalRing ℚ` (only ℤ and ZMod n).
So Stage 3's `OperationalField ℚ` instance creates the first and ONLY path to
`OperationalRing ℚ` via this bridge. No diamond, no `@[priority]` needed.

**Canonical instance**: this bridge is unconditional and registered as a global
instance (no `local` or `@[priority]` annotation). The same design as
`OperationalRing.toOperationalAddGroup` in v0.2.0, which proved stable.
If later stages introduce direct `OperationalRing K` instances that conflict,
`@[priority]` can be added then. Not anticipated for v0.3.0 scope.

## Axiom profile: [] -/
instance OperationalField.toOperationalRing {K : Type*} [OperationalField K] :
    OperationalRing K where
  toRing              := inferInstance
  IsOperational       := OperationalField.IsOperational
  zero_isOperational  := OperationalField.zero_isOperational
  add_isOperational   := OperationalField.add_isOperational
  neg_isOperational   := OperationalField.neg_isOperational
  one_isOperational   := OperationalField.one_isOperational
  mul_isOperational   := OperationalField.mul_isOperational

-- ============================================================
-- §3. Bridge: OperationalField → OperationalGroup Kˣ (Stage 5)
-- ============================================================

/-- Every operational field gives an operational multiplicative group on its units.

**Bridge**: if `K` carries an `OperationalField K` instance, then `Kˣ` (the units
of K, `Units K`) automatically carries `OperationalGroup Kˣ` with operational
predicate `IsOperational u := OperationalField.IsOperational (u : K)`.

**Mathematical content**: the operational units of K form an operational
multiplicative group. An element `u : Kˣ` is operational iff the underlying
field element `(u : K) = u.val` is operational in K.

**Units structure**: `Kˣ = Units K` is the type of invertible elements of K.
Each `u : Kˣ` stores:
- `u.val : K` — the element
- `u.inv : K` — its stored inverse (with `u.val * u.inv = 1`)
The coercion `(u : K)` returns `u.val`.

**Key coercions** (from `Mathlib.Algebra.GroupWithZero.Units.Basic`):
- `Units.val_one   : ((1 : Kˣ) : K) = 1`
- `Units.val_mul   : ((u * v : Kˣ) : K) = (u : K) * (v : K)`
- `Units.val_inv_eq_inv_val : ((u⁻¹ : Kˣ) : K) = (u : K)⁻¹`

These coercions connect the Units group operations to the field operations,
allowing the bridge proofs to reduce to `OperationalField` closure axioms.

**Recognition discipline reversal — Finding A12 concrete delivery**:
`OperationalGroup` was omitted in v0.1.0 (Finding A0): no multiplicative instances.
v0.3.0 Stage 1 revived it (MulGroup.lean, Finding A12 anticipated).
THIS bridge instance is the concrete justification:
  `OperationalField K → OperationalGroup Kˣ`
is the natural instance that closes the recognition discipline loop.
The abstraction was revived BECAUSE this bridge exists, and now it IS here.

**Chain of bridges** (extended in Stage 5):
  OperationalField K → OperationalRing K → OperationalAddGroup K  (additive)
  OperationalField K → OperationalGroup Kˣ                        (multiplicative — NEW)

Both chains share the same source (`OperationalField K`) and are independent.
The additive chain was established in Stages 2-3; the multiplicative chain is Stage 5.

**Group structure**: `Group Kˣ` is provided by `Units.instGroup` from mathlib.
`toGroup := inferInstance` synthesises `Group Kˣ` from `Monoid K` (via `Field K`).

**Axiom profile**: `[propext, Classical.choice, Quot.sound]` — import-context
effect from `Mathlib.Algebra.GroupWithZero.Units.Basic` (see Stage 5 reconnaissance
above). Logical ceiling is `[propext, Quot.sound]` (field ceiling). This is the
same import-context escalation as Finding A15 (`inv_isModeAOp_field` in ModeA.lean).

## Axiom profile: [propext, Classical.choice, Quot.sound] (import-context, Finding A15) -/
instance OperationalField.toOperationalGroupUnits {K : Type*} [OperationalField K] :
    OperationalGroup Kˣ where
  toGroup := inferInstance
  IsOperational := fun u => OperationalField.IsOperational (u : K)
  one_isOperational := by
    simp only [Units.val_one]
    exact OperationalField.one_isOperational
  mul_isOperational := fun {u v} hu hv => by
    simp only [Units.val_mul]
    exact OperationalField.mul_isOperational hu hv
  inv_isOperational := fun {u} hu => by
    simp only [Units.val_inv_eq_inv_val]
    exact OperationalField.inv_isOperational hu

-- ============================================================
-- Axiom audit — Stages 2 and 5, Field.lean
-- ============================================================
-- STAGE: 2 (of 6, v0.3.0); 5 (Units bridge). SOURCE: PLAN.md Stage 2, Stage 5.
-- LEAN OBJECTS (1 class, 2 instances):
--   OperationalField                           (class, extends Field K)
--   OperationalField.toOperationalRing         (instance, OperationalRing K)
--   OperationalField.toOperationalGroupUnits   (instance, OperationalGroup Kˣ) [Stage 5]
-- RECOGNITION DISCIPLINE:
--   Stage 2: OperationalField NOT redundant — inv_isOperational is genuine new content.
--     Contrast Finding A9 (v0.2.0): OperationalCommRing WAS redundant (no new ops).
--   Stage 5: OperationalGroup revived (Finding A12 concrete delivery).
--     This bridge IS the natural instance that justified revival in Stage 1.
-- DIAMOND ANALYSIS: no diamond at OperationalField level; Field K's internal
--   diamond (CommRing K ← Field K → DivisionRing K) is mathlib's internal concern.
--   Stage 5 adds new bridge OperationalField → OperationalGroup Kˣ; no diamond with
--   OperationalField → OperationalRing → OperationalAddGroup (different target types).
-- IMPORT NOTE (Stage 5): Mathlib.Algebra.GroupWithZero.Units.Basic added for
--   Units.val_inv_eq_inv_val. Confirmed: this import does NOT escalate the axiom
--   profiles of OperationalField or toOperationalRing (tested pre-commit).
-- AXIOM AUDIT:
--   OperationalField                     [propext, Quot.sound]  — Field ceiling (A13)
--   OperationalField.toOperationalRing   [propext, Quot.sound]  — Field ceiling
--   OperationalField.toOperationalGroupUnits
--                     [propext, Classical.choice, Quot.sound]   — import-context (A15)
--     Logical ceiling: [propext, Quot.sound]; Classical.choice from GroupWithZero.Units.Basic
--     affecting Inv K elaboration in Units.val_inv_eq_inv_val simp step.
-- CHECKS: no sorry, no admit.

#print axioms OperationalField
#print axioms OperationalField.toOperationalRing
#print axioms OperationalField.toOperationalGroupUnits

end VR.Algebra
