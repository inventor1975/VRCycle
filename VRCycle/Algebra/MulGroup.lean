-- VRCycle: Algebra/MulGroup.lean
-- Operational Algebra v0.3.0 — Stage 1: OperationalGroup typeclass (multiplicative).
--
-- STAGE: 1 (of 6, v0.3.0). SOURCE: PLAN.md Stage 1; CLAUDE.md §What is being built in v0.3.0.
--
-- ## Position statement
-- This file introduces the VR operational layer on top of mathlib's multiplicative
-- group typeclass. One typeclass is defined:
--
--   OperationalGroup (G : Type*): multiplicative group + operational predicate.
--
-- This is the multiplicative mirror of `OperationalAddGroup` (v0.1.0 Stage 1,
-- AddGroup.lean). The design is symmetric: same predicate pattern, same closure
-- axioms, multiplicative notation in place of additive.
--
-- ## Recognition discipline reversal — Finding A12 (v0.3.0)
--
-- v0.1.0 Stage 1 design INCLUDED both `OperationalGroup` (multiplicative) and
-- `OperationalAddGroup` (additive). Post-build review applied recognition discipline
-- (Finding A0):
--
--   All v0.1.0 instances (ℤ, ZMod n) are additive groups.
--   OperationalGroup (multiplicative) has no instance in v0.1.0 scope.
--   → Preemptive abstraction without users. Removed.
--
-- v0.3.0 REVERSES this omission because a natural multiplicative instance arrives:
--
--   Fields K have unit groups Kˣ (Units K). Units form a multiplicative group.
--   OperationalGroup Kˣ is the NATURAL instance justified by OperationalField.
--   → Abstraction introduced when users arrive. Revived.
--
-- This is **bidirectional recognition discipline**: recognise BOTH when an
-- abstraction is unnecessary (remove it) AND when it becomes necessary (introduce it).
-- The reversal is the explicit methodological contribution documented here.
-- v0.1.0 (Finding A0): recognised preemptive abstraction → omitted.
-- v0.3.0 (Finding A12): recognised justified abstraction → introduced.
--
-- The Units instance will be provided in Stage 5 (Instances.lean or FieldInstances.lean).
-- Stage 1 only defines the typeclass; the instance justification follows.
--
-- ## Mathlib reconnaissance (Stage 1)
--
-- ### Multiplicative Group hierarchy (Mathlib.Algebra.Group.Defs)
--
--   Group G extends DivInvMonoid G where
--     protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
--
--   DivInvMonoid G extends Monoid G, Inv G, Div G
--     operations: 1, *, ⁻¹, / (with zpow for ℤ-exponentiation)
--     Division: a / b = a * b⁻¹ (default from DivInvMonoid)
--
--   CommGroup G extends Group G, CommMonoid G
--
--   Key observation: Group G provides 1, *, ⁻¹, / — closure axioms for
--   OperationalGroup need cover 1, *, ⁻¹. Division is derived (Stage 4):
--   div_isOperational follows from mul_isOperational + inv_isOperational
--   via a / b = a * b⁻¹, EXACTLY parallel to sub_isModeAOp in v0.1.0
--   (sub = add + neg). No explicit div axiom needed.
--
-- ### Units K (Mathlib.Algebra.Group.Units.Defs)
--
--   structure Units (α : Type u) [Monoid α] where
--     val    : α          -- the unit element
--     inv    : α          -- its inverse
--     val_inv : val * inv = 1
--     inv_val : inv * val = 1
--   postfix "ˣ" => Units  (so Units K = Kˣ)
--
--   instance instGroup : Group αˣ   -- units form a group automatically
--   instance instCommGroupUnits : CommGroup αˣ  (if α is CommMonoid)
--
--   The val coercion (u : Kˣ) → (u : K) is `Units.val`.
--   Stage 5 will use this coercion to define:
--     IsOperational (u : Kˣ) := OperationalField.IsOperational (u : K)
--   connecting the field's operational predicate to the units group.
--
-- ### Field K (Mathlib.Algebra.Field.Defs) — preparation for Stage 2
--
--   class Field (K : Type u) extends CommRing K, DivisionRing K
--   DivisionRing K extends Ring K, DivInvMonoid K, Nontrivial K, NNRatCast K, RatCast K
--
--   Key: Field K already includes DivInvMonoid K (multiplicative inverse).
--   OperationalField (Stage 2) will extend Field K, adding inv_isOperational.
--   Bridge OperationalField → OperationalGroup Kˣ (Stage 5) justified by instGroup.
--
-- ### ℚ as Field (Mathlib.Data.Rat.Defs) — preparation for Stage 3
--
--   Rat.instField : Field ℚ  — available in mathlib.
--   ℚˣ = Units ℚ is thus a multiplicative group.
--   Stage 3 will instantiate OperationalField ℚ; Stage 5 gives OperationalGroup ℚˣ.
--
-- ## Design decisions (Stage 1)
--
-- ### Decision A: extends Group G (not CommGroup)
-- OperationalGroup extends the non-commutative Group typeclass.
-- Rationale: Units Kˣ of a commutative field K forms CommGroup Kˣ.
-- But for generality — future matrix group instances, free groups —
-- non-commutative Group is the correct base. CommGroup Kˣ is available
-- from mathlib's instCommGroupUnits automatically when K is commutative.
-- No separate OperationalCommGroup needed (consistent with Finding A9:
-- OperationalCommRing omitted for same reason).
--
-- ### Decision B: div_isOperational is NOT an axiom
-- Division a / b = a * b⁻¹ in any Group (from DivInvMonoid.div_eq_mul_inv).
-- Closure under / follows from mul_isOperational + inv_isOperational.
-- This will be proved as div_isModeAOp in Stage 4, exactly parallel to
-- sub_isModeAOp in v0.1.0 ModeA.lean (where sub = add + neg).
-- No explicit div axiom in the typeclass — avoids redundancy.
--
-- ### Decision C: zpow_isOperational deferred
-- zpow (ℤ-exponentiation, a ^ (n : ℤ)) is provided by DivInvMonoid.
-- Closure: zpow n a is operational if a is operational, follows by
-- case analysis: positive powers via npow_isOperational, negative via inv.
-- This is an analogue of nsmul_isOperational (v0.1.0) / npow_isOperational (v0.2.0).
-- Deferred to Stage 4 (Mode A theorems), not a typeclass axiom.
--
-- ### Decision D: IsOperational predicate — same pattern as v0.1.0/v0.2.0
-- Generic predicate G → Prop, concrete interpretation per instance.
-- For Kˣ (Stage 5): IsOperational u := OperationalField.IsOperational (u : K).
-- Trivially-operational if OperationalField.IsOperational = fun _ => True.
--
-- ## Naming note for Stage 4
-- v0.2.0 ModeA.lean contains `mul_isModeAOp` for OperationalRing multiplication.
-- Stage 4 will prove the multiplicative group analogue. Name conflict will require
-- namespace separation: e.g., VR.Algebra.MulGroup.mul_isModeAOp vs the ring theorem.
-- This is documented here for awareness; NOT a concern for Stage 1 (typeclass only).
--
-- ## Axiom profile
-- OperationalGroup (class definition): []
-- Class definitions introduce no proof obligations.

import Mathlib.Algebra.Group.Defs

namespace VR.Algebra

-- ============================================================
-- §1. OperationalGroup — multiplicative groups with operational predicate
-- ============================================================

/-- `OperationalGroup G`: a multiplicative group G equipped with a VR operational predicate.

## Overview

Extends mathlib's `Group G` with a predicate `IsOperational : G → Prop` that
selects the *operational* sub-collection of G in the sense of the VR programme.

An element `g : G` is **operational** if `IsOperational g` holds. Operationality
is the VR programme's signature concept (Vitaly Reznik): it asserts **explicit
witness of construction**, as opposed to merely classically existing. The precise
character of the witness is determined by each concrete instance.

## Closure axioms

The operational elements are closed under all multiplicative group operations:

- **`one_isOperational`**: the unit element `1 : G` is operational.
- **`mul_isOperational`**: if `a` and `b` are operational, so is `a * b`.
- **`inv_isOperational`**: if `a` is operational, so is `a⁻¹`.

Together these say the operational elements of G form a substructure closed under
the multiplicative group operations — a *sub-apparatus* in the VR sense.

Note: division `a / b` closure is NOT a separate axiom. Since `a / b = a * b⁻¹`
in any `Group G` (from `DivInvMonoid.div_eq_mul_inv`), division closure follows
from `mul_isOperational` and `inv_isOperational`. This will be proved as
`div_isModeAOp` in Stage 4, exactly parallel to `sub_isModeAOp` in v0.1.0.

## Symmetry with OperationalAddGroup

This typeclass is the multiplicative mirror of `OperationalAddGroup` (v0.1.0):

  OperationalAddGroup G     ↔     OperationalGroup G
  extends AddGroup G              extends Group G
  zero_isOperational              one_isOperational
  add_isOperational               mul_isOperational
  neg_isOperational               inv_isOperational
  [sub_isModeAOp, Stage 3]        [div_isModeAOp, Stage 4]

The additive/multiplicative symmetry of mathlib is exactly mirrored here.

## Recognition discipline reversal (Finding A12)

`OperationalGroup` was omitted in v0.1.0 (Finding A0): no multiplicative instances
existed, so the abstraction had no users — recognition discipline removed it.

v0.3.0 **reverses** this decision: fields K provide natural multiplicative instances
through their unit groups `Kˣ` (`Units K`, which carries `Group Kˣ` automatically).
Stage 5 will provide:

  `instance [OperationalField K] : OperationalGroup Kˣ`

This is the instance that justifies the abstraction. Recognition discipline applies
**bidirectionally**: remove preemptive abstractions AND introduce justified ones.
The reversal from Finding A0 to this Stage 1 is Finding A12.

## Apparatus connection

This is an instance of the VR-Apparatus predicate-wrapping apparatus:

  Formal register      = G  (the full classical group, mathlib's `Group G`)
  Operational register = { g : G // IsOperational g }  (operational sub-collection)

Stage 4 will register `OperationalGroup` as an instance of `PredicateOperationality`
(VRCycle.Apparatus.Wrapping), confirming Finding A3 extends to multiplicative groups
(third structure after AddGroup and Ring).

## Concrete instances (v0.3.0)

- **ℚˣ** (Stage 5): `IsOperational := fun u => OperationalField.IsOperational (u : ℚ)`.
  Since ℚ's operational predicate is `fun _ => True`, every unit of ℚ is trivially
  operational. The bridge demonstrates the conceptual connection from fields to groups.

## On "operational" vs "computable"

"Operational" is intentional and specific to the VR programme. It is not:
- *Computable* (Turing): stronger, requires Turing-machine encoding.
- *Constructive* (constructive mathematics): different project — CML rewrites
  classical theory; VR wraps it.

Operationality in VR asserts an explicit witness of construction appropriate to
the domain. For Kˣ with trivial field predicate, every unit has an obvious witness.

## Axiom profile: [] -/
class OperationalGroup (G : Type*) extends Group G where
  /-- Predicate identifying operational elements of the multiplicative group.

  Each instance supplies its own interpretation of "operational". Common choices:
  - `fun _ => True` — trivially operational (every element has a witness).
  - `fun u => OperationalField.IsOperational (u : K)` — for Units Kˣ, inheriting
    the field's operational predicate via the coercion `Units.val`.

  The predicate need not be decidable. Classical mathematics applies within
  the formal register G; operationality is a layer on top. -/
  IsOperational : G → Prop
  /-- The unit element `1 : G` is operational. -/
  one_isOperational : IsOperational 1
  /-- Multiplication preserves operationality: if `a` and `b` are operational,
  then `a * b` is operational. -/
  mul_isOperational : ∀ {a b : G},
    IsOperational a → IsOperational b → IsOperational (a * b)
  /-- Inversion preserves operationality: if `a` is operational,
  then `a⁻¹` is operational. -/
  inv_isOperational : ∀ {a : G}, IsOperational a → IsOperational a⁻¹

-- ============================================================
-- Axiom audit — Stage 1, MulGroup.lean
-- ============================================================
-- STAGE: 1 (of 6, v0.3.0). SOURCE: PLAN.md Stage 1.
-- LEAN OBJECTS (1 class):
--   OperationalGroup (class, extends Group G)
-- RECOGNITION DISCIPLINE: OperationalGroup REVIVED from v0.1.0 Finding A0 omission.
--   Justification: OperationalGroup Kˣ (Stage 5) provides natural instance.
--   Finding A12: recognition discipline reversal documented above.
-- AXIOM AUDIT: expected [] for the class definition.
--   Class definition introduces no proof obligations.
-- CHECKS: no sorry, no admit.

#print axioms OperationalGroup

end VR.Algebra
