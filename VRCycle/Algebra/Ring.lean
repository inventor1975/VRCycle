-- VRCycle: Algebra/Ring.lean
-- Operational Algebra v0.2.0 — Stages 1-2: OperationalRing typeclass + bridge instance.
--
-- STAGE: 1-2 (of 7). SOURCE: PLAN.md Stages 1, 2; CLAUDE.md §What is being built in v0.2.0.
--
-- ## Position statement
-- This file defines the VR operational layer on top of mathlib's ring typeclass.
-- Two deliverables across Stages 1-2:
--
--   Stage 1: OperationalRing (R : Type*) — ring + operational predicate.
--   Stage 2: OperationalRing.toOperationalAddGroup — bridge instance.
--            OperationalCommRing — recognition discipline applied (see §2).
--
-- This extends the additive-group apparatus from v0.1.0 to the full ring structure,
-- adding closure axioms for the multiplicative identity (1) and multiplication (*).
-- It is the algebraic analogue of the v0.1.0 OperationalAddGroup, extended to rings.
--
-- ## Mathlib reconnaissance (Stage 1)
--
-- ### Ring hierarchy (Mathlib.Algebra.Ring.Defs)
--
--   Ring R extends Semiring R, AddCommGroup R, AddGroupWithOne R.
--     Semiring α extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α.
--     AddCommGroup R provides: 0, +, -(neg), - (sub), commutativity, group axioms.
--     MonoidWithZero α provides: 1, *, associativity, identity axioms, mul_zero/zero_mul.
--     AddGroupWithOne R: bridge from ℕ-cast and ℤ-cast to ring.
--     Distributivity: left_distrib, right_distrib (from Semiring → Distrib).
--
--   Consequence: Ring R has operations {0, 1, +, -, *} with all expected axioms.
--   In particular, Ring R already contains AddGroup R (via AddCommGroup R).
--
-- ### CommRing hierarchy
--
--   CommRing α extends Ring α, CommMonoid α.
--
--   CommRing is a direct extension of Ring, not a parallel structure. This means:
--     [CommRing R] → [Ring R] automatically via CommRing.toRing.
--   CommMonoid adds mul_comm on top of Monoid. No independent path.
--   CommRing is NOT independent of Ring — it is Ring + commutativity of multiplication.
--
-- ## Design decisions (Stage 1)
--
-- ### Decision A: OperationalRing extends Ring R directly
--
-- Pattern: same as OperationalAddGroup extends AddGroup G in v0.1.0.
-- Rationale: OperationalRing R implies Ring R — downstream code obtains all ring
-- operations for free. Pattern matches mathlib's enriched typeclasses.
--
-- Alternative considered: OperationalRing extends Ring R, OperationalAddGroup R.
-- REJECTED. Reason: this creates a diamond through AddGroup R (Ring R already
-- implies AddGroup R via AddCommGroup R; OperationalAddGroup R also implies AddGroup R).
-- Lean 4 can sometimes resolve such diamonds, but the elaboration risk is non-trivial.
-- The clean design is:
--   OperationalRing R extends Ring R (standalone, with all closure axioms)
--   Bridge instance [OperationalRing R] → OperationalAddGroup R provided separately
--   (Stage 2 or RingInstances.lean, once diamond handling is tested)
--
-- This gives the same mathematical content — same predicate, same closure — without
-- the elaboration risk. The bridge instance will make OperationalAddGroup available
-- automatically whenever OperationalRing is in context.
--
-- ### Decision B: Predicate shared with OperationalAddGroup
--
-- The operational predicate IsOperational is a property of elements, not of
-- the algebraic structure. An element that is operational for its ring structure
-- is equally operational for its additive group structure (same element, same witness).
--
-- Implementation: OperationalRing carries its own IsOperational field (fresh,
-- not inherited from OperationalAddGroup — that would require the diamond extension
-- rejected in Decision A). The bridge instance [OperationalRing R] → OperationalAddGroup R
-- (Stage 2) will set OperationalAddGroup.IsOperational := OperationalRing.IsOperational,
-- ensuring the predicates are definitionally equal.
--
-- This is the honest design: one predicate per element, two typeclasses that
-- agree on it via the bridge.
--
-- ### Decision C: zero_isOperational explicit
--
-- Include zero_isOperational as an explicit typeclass field rather than deriving
-- it from neg + add. Reasons:
--   (1) Readability: all closure axioms visible in one place.
--   (2) Avoids bootstrapping: deriving 0-closure requires an operational element
--       to start from (a + (-a) = 0), which requires existence of an operational
--       element in the first place. Explicit axiom avoids this.
--   (3) Consistency with v0.1.0: OperationalAddGroup has zero_isOperational as
--       an explicit field. Same pattern maintained.
--
-- Note: sub_isOperational is NOT a separate axiom. Subtraction a - b = a + (-b)
-- follows from add_isOperational and neg_isOperational (as in v0.1.0 ModeA.lean
-- theorem sub_isModeAOp). No explicit sub_isOperational field needed.
--
-- ## Axiom profile
-- OperationalRing (class definition): []
-- Class definitions introduce no proof obligations.

import Mathlib.Algebra.Ring.Defs
import VRCycle.Algebra.AddGroup

namespace VR.Algebra

-- ============================================================
-- §1. OperationalRing — rings with operational predicate
-- ============================================================

/-- `OperationalRing R`: a ring R equipped with a VR operational predicate.

## Overview

Extends mathlib's `Ring R` with a predicate `IsOperational : R → Prop` that
selects the *operational* sub-collection of R in the sense of the VR programme.

An element `r : R` is **operational** if `IsOperational r` holds. Operationality
is the VR programme's signature concept, introduced by Vitaly Reznik: it asserts
**explicit witness of construction**, as opposed to merely classically existing.
The precise character of the witness is determined by each concrete instance.

## Closure axioms

The operational elements are closed under all ring operations:

- **`zero_isOperational`**: the additive identity `0 : R` is operational.
- **`add_isOperational`**: if `a` and `b` are operational, so is `a + b`.
- **`neg_isOperational`**: if `a` is operational, so is `-a`.
- **`one_isOperational`**: the multiplicative identity `1 : R` is operational.
- **`mul_isOperational`**: if `a` and `b` are operational, so is `a * b`.

Note: subtraction closure (`a - b` operational when `a`, `b` operational) is
not a separate axiom — it follows from `add_isOperational` and `neg_isOperational`
via `a - b = a + (-b)`. This is proved as a Mode A theorem in `RingModeA.lean`
(Stage 5), consistent with the v0.1.0 pattern in `ModeA.lean`.

## Relationship to OperationalAddGroup (v0.1.0)

`OperationalAddGroup G` (v0.1.0) wraps the additive group structure of G.
`OperationalRing R` extends this to the full ring structure by adding
`one_isOperational` and `mul_isOperational`.

A bridge instance `[OperationalRing R] → OperationalAddGroup R` will be provided
(Stage 2), setting `OperationalAddGroup.IsOperational := OperationalRing.IsOperational`.
This ensures: whenever a ring is operational, its underlying additive group is
operational with the same predicate. One predicate per element, two typeclasses.

## Apparatus connection

This is an instance of the VR-Apparatus predicate-wrapping apparatus:

  Formal register      = R  (the full classical ring, mathlib's `Ring R`)
  Operational register = { r : R // IsOperational r }  (operational sub-collection)

`PredicateOperationality R OperationalRing.IsOperational` will be registered
in Stage 5 (RingModeA.lean), consistent with the v0.1.0 pattern in ModeA.lean.

## Concrete instances (planned for v0.2.0)

- **ℤ** (Stage 3): `IsOperational := fun _ => True`.
  Every integer is trivially operational. Demonstrates ring apparatus collapses
  gracefully for fully-operational types.

- **ZMod n** (Stage 4): `IsOperational := fun _ => True`.
  Every residue class trivially operational. `[NeZero n]` constraint as in v0.1.0.

## On "operational" vs "computable"

"Operational" is intentional and specific to the VR programme. It is not:
- *Computable* (Turing): stronger, requires Turing-machine encoding.
- *Constructive* (constructive mathematics): different project — CML rewrites
  classical theory; VR wraps it.

Operationality in VR asserts an explicit witness of construction appropriate to
the domain. For ℤ and ZMod n, every element has an obvious explicit representation,
so the trivial witness suffices.

## Axiom profile: [] -/
class OperationalRing (R : Type*) extends Ring R where
  /-- Predicate identifying operational elements of the ring.

  Each instance supplies its own interpretation of "operational". Common choices:
  - `fun _ => True` — trivially operational (every element has a witness).
    Used for ℤ and ZMod n in v0.2.0.
  - A predicate encoding an explicit construction witness.

  The predicate need not be decidable. Classical mathematics applies within
  the formal register R; operationality is a layer on top. -/
  IsOperational : R → Prop
  /-- The additive identity `0 : R` is operational. -/
  zero_isOperational : IsOperational 0
  /-- Addition preserves operationality: if `a` and `b` are operational,
  then `a + b` is operational. -/
  add_isOperational : ∀ {a b : R},
    IsOperational a → IsOperational b → IsOperational (a + b)
  /-- Negation preserves operationality: if `a` is operational,
  then `-a` is operational. -/
  neg_isOperational : ∀ {a : R}, IsOperational a → IsOperational (-a)
  /-- The multiplicative identity `1 : R` is operational. -/
  one_isOperational : IsOperational 1
  /-- Multiplication preserves operationality: if `a` and `b` are operational,
  then `a * b` is operational. -/
  mul_isOperational : ∀ {a b : R},
    IsOperational a → IsOperational b → IsOperational (a * b)

-- ============================================================
-- §2. OperationalCommRing — recognition discipline (Stage 2)
-- ============================================================
--
-- ## Recognition analysis
--
-- PLAN.md Stage 2 specified `OperationalCommRing` as a typeclass extending CommRing.
-- Stage 2 instructions require explicit recognition discipline check:
-- "if OperationalCommRing adds nothing beyond OperationalRing + CommRing instance bridge,
-- consider whether a separate typeclass is needed."
--
-- ## Finding A9 — OperationalCommRing is redundant
--
-- `OperationalCommRing` as a typeclass would require one of two forms:
--
-- Form A: `class OperationalCommRing (R : Type*) extends CommRing R, OperationalRing R`
--   FAILS: both CommRing and OperationalRing bring `toRing : Ring R` as their primary
--   auto-generated parent field. This is a same-name field conflict at the immediate
--   inheritance level — unlike the deeper Monoid diamond in `CommRing extends Ring,
--   CommMonoid` where shared ancestors are reached through distinct fields (toRing vs
--   toCommMonoid). Lean 4 cannot resolve this diamond automatically. Form A is not viable.
--
-- Form B: `class OperationalCommRing (R : Type*) extends CommRing R where [all axioms]`
--   COMPILES: but DUPLICATES all 6 fields from OperationalRing verbatim.
--   The only difference from OperationalRing: `extends CommRing R` vs `extends Ring R`.
--   Mathematical content added: mul_comm — but this is already available from mathlib's
--   `CommRing` whenever the concrete type (ℤ, ZMod n) is known.
--
-- ## Verdict: omit OperationalCommRing
--
-- Form B would introduce preemptive abstraction with duplicated fields and no genuine
-- new mathematical content. All v0.2.0 instances (ℤ, ZMod n) will be instantiated as
-- `OperationalRing`. Since `CommRing ℤ` and `CommRing (ZMod n)` are already in mathlib,
-- any downstream context needing commutativity uses `[OperationalRing R] [CommRing R]`
-- — both already present, no new typeclass needed.
--
-- This is the v0.2.0 analogue of Finding A0 (v0.1.0): just as `OperationalGroup`
-- (multiplicative) was omitted because no multiplicative instances existed,
-- `OperationalCommRing` is omitted because it duplicates `OperationalRing` without
-- genuine new content. Recognition discipline — do not abstract preemptively.
--
-- ## Implication for Stages 3-4
--
-- Stage 3 (ℤ): instantiate `OperationalRing ℤ`. Since `CommRing ℤ` is in mathlib,
--   both `OperationalRing ℤ` and `CommRing ℤ` are available; no `OperationalCommRing`
--   instantiation required.
-- Stage 4 (ZMod n): same pattern with `[NeZero n]` constraint.
-- Stage 5 (Mode A): generic theorems over `[OperationalRing R]`. Commutativity-specific
--   results use `[OperationalRing R] [CommRing R]` if needed — no separate typeclass.

-- ============================================================
-- §3. Bridge instance: OperationalRing → OperationalAddGroup (Stage 2)
-- ============================================================

/-- Every operational ring is an operational additive group.

**Bridge**: if `R` carries an `OperationalRing R` instance, then it automatically
carries `OperationalAddGroup R` with the SAME operational predicate.

**Mathematical content**: an operational ring's operational elements form an
operational additive group — the ring's additive structure, restricted to operational
elements, is closed under `0`, `+`, `-` (from the ring closure axioms). The new ring
axioms `one_isOperational` and `mul_isOperational` are not needed here — they extend
the additive group to a ring, not restrict it.

**Predicate identity**: `OperationalAddGroup.IsOperational := OperationalRing.IsOperational`.
This is definitional equality — the same predicate, same element, same witness. Decision B
from Stage 1 is fulfilled here: one predicate per element, two typeclasses agree via this
bridge.

**Diamond note**: `OperationalRing R extends Ring R`, and `Ring R extends AddCommGroup R
extends AddGroup R`. So `inferInstance : AddGroup R` is reachable from `[OperationalRing R]`
by projecting through `OperationalRing.toRing`, `Ring.toAddCommGroup`, `AddCommGroup.toAddGroup`.
The chain is definitional, no proof obligations introduced.

**Instance conflict note**: in Stage 3, when `OperationalRing ℤ` is instantiated, Lean
will have two paths to `OperationalAddGroup ℤ`: the v0.1.0 direct instance
`instOperationalAddGroupInt` (Instances.lean) and this bridge from `instOperationalRingInt`.
Both produce `IsOperational := fun _ => True`, so the conflict is at the instance
resolution level only, not at the mathematical level. Priority or `@[priority]` annotation
may be needed in Stage 3 if Lean reports ambiguity. Noted here as a stage-boundary concern.

## Axiom profile: [] (generic; concrete R may inherit axioms from Ring infra) -/
instance OperationalRing.toOperationalAddGroup {R : Type*} [OperationalRing R] :
    OperationalAddGroup R where
  toAddGroup    := inferInstance
  IsOperational := OperationalRing.IsOperational
  zero_isOperational              := OperationalRing.zero_isOperational
  add_isOperational  {_} {_} ha hb := OperationalRing.add_isOperational ha hb
  neg_isOperational  {_} ha        := OperationalRing.neg_isOperational ha

-- ============================================================
-- Axiom audit — Stages 1-2, Ring.lean
-- ============================================================
-- STAGE: 1-2 (of 7). SOURCE: PLAN.md Stages 1, 2.
-- LEAN OBJECTS (1 class, 1 instance):
--   OperationalRing                        (class, extends Ring R)
--   OperationalRing.toOperationalAddGroup  (instance, OperationalAddGroup R)
-- OperationalCommRing: OMITTED (Finding A9 — recognition discipline, see §2).
-- AXIOM AUDIT:
--   OperationalRing                       []  — class definition, no obligations
--   OperationalRing.toOperationalAddGroup []  — generic bridge, no proof obligations
-- CHECKS: no sorry, no admit.

#print axioms OperationalRing
#print axioms OperationalRing.toOperationalAddGroup

end VR.Algebra
