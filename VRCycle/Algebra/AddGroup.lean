-- VRCycle: Algebra/AddGroup.lean
-- Operational Algebra v0.1.0 — Stage 1: OperationalAddGroup typeclass.
--
-- STAGE: 1 (of 7). SOURCE: PLAN.md Stage 1; CLAUDE.md §What is being built.
--
-- ## Position statement
-- This file introduces the VR operational layer on top of mathlib's additive group
-- typeclass. One typeclass is defined:
--
--   OperationalAddGroup (G : Type*): additive group + operational predicate.
--
-- This is the algebraic analogue of the predicate-wrapping apparatus established
-- in VR-Audit (IsComputableReal on ℝ) and meta-formalised in VR-Apparatus
-- (PredicateOperationality). The apparatus framework is REUSED here — we do not
-- create a parallel apparatus for algebra. Stage 3 will register
-- OperationalAddGroup as an instance of PredicateOperationality.
--
-- ## Finding A0 — Recognition discipline applied
--
-- Initial Stage 1 design included both OperationalGroup (multiplicative) and
-- OperationalAddGroup (additive) typeclasses. Post-build review applied the
-- recognition discipline established in VR-Apparatus (Finding F11: generic
-- Register abstraction unnecessary):
--
--   All v0.1.0 instances (ℤ, ZMod n) are additive groups.
--   OperationalGroup (multiplicative) has no instance in v0.1.0 scope.
--   → Preemptive abstraction without users. Removed.
--
-- Multiplicative operational groups are deferred to v0.2.0 or a future cycle
-- when actual multiplicative content (e.g., matrix groups, free groups) arrives.
-- This removal follows the principle: recognise when a planned structure is
-- unnecessary, omit rather than duplicate or speculate.
--
-- Echoes Finding F11 from VR-Apparatus: "generic Register abstraction unnecessary."
--
-- ## Reconnaissance summary (Stage 1)
--
-- ### Mathlib algebraic hierarchy (Mathlib.Algebra.Group.Defs)
--
--   AddGroup A extends SubNegMonoid A:
--     operations: 0, +, -(neg), −;  axiom: -a + a = 0.
--
--   AddCommGroup A extends AddGroup A, AddCommMonoid A.
--
-- ### ℤ as AddCommGroup (Mathlib.Algebra.Group.Int.Defs)
--   instance instAddCommGroup : AddCommGroup ℤ  — fully defined, extends AddGroup ℤ.
--   ℤ is naturally an *additive* group (integers under addition).
--   Multiplicative ℤ is a CommMonoid but NOT a Group
--   (no multiplicative inverse for n ≠ ±1).
--
-- ### ZMod n (Mathlib.Data.ZMod.Defs)
--   def ZMod : ℕ → Type  |  0 => ℤ  |  n+1 => Fin (n+1).
--   instance commRing (n : ℕ) : CommRing (ZMod n)  — CommRing includes AddCommGroup.
--   ZMod n is an additive group for all n.
--
-- ### VR-Apparatus patterns (VRCycle.Apparatus.Wrapping, ModeA)
--   PredicateOperationality T P : Prop — zero-field marker class.
--   IsModeAOp P f : Prop — preservation of predicate P under f.
--   Pattern: apparatus wraps (T, P) pairs; closure is in instances, not the class.
--
-- ### VR-Audit pattern (VRCycle.Audit.Computable)
--   IsComputableReal (x : ℝ) : Prop := ∃ alg mod, approximation condition.
--   Predicate-wrapping: ℝ is the classical type; IsComputableReal selects operational.
--   Closure proven as theorems: IsComputableReal_add, _neg, _sub, etc.
--
-- ## Design decisions (Stage 1)
--
-- ### Decision A: Additive only for v0.1.0
-- Both planned instances (ℤ, ZMod n) are additive groups.
-- Single typeclass OperationalAddGroup suffices for all v0.1.0 content.
-- Multiplicative version deferred (Finding A0 above).
--
-- ### Decision B: What "operational" means in v0.1.0
-- An operational additive group element is one satisfying IsOperational : G → Prop,
-- provided by each typeclass INSTANCE. The typeclass itself is generic.
--
-- For the v0.1.0 instances (ℤ, ZMod n), IsOperational will be fun _ => True:
-- every element is trivially operational via standard representations.
--
-- This is intentional: it demonstrates the apparatus collapses gracefully when
-- all elements are operational. Non-trivial predicates are possible for other
-- types (e.g., a group of reals with explicit Cauchy witnesses) and deferred.
--
-- The term "operational" is the VR programme's signature concept (Vitaly Reznik).
-- It is NOT "computable" (Turing) or "constructive" (constructive mathematics).
-- Operationality asserts explicit witness of construction appropriate to the
-- domain. For trivially-operational types, the trivial proof is the witness.
--
-- ### Decision C: Typeclass shape — extends vs parameter
-- We use `extends AddGroup G`.
-- Rationale: OperationalAddGroup G implies AddGroup G — downstream code obtains
-- group operations for free. Pattern matches mathlib's enriched typeclasses
-- (OrderedAddCommGroup, TopologicalAddGroup, etc.).
--
-- ## Axiom profile
-- OperationalAddGroup (class definition): []
-- Class definitions introduce no proof obligations.

import Mathlib.Algebra.Group.Defs

namespace VR.Algebra

-- ============================================================
-- §1. OperationalAddGroup — additive groups with operational predicate
-- ============================================================

/-- `OperationalAddGroup G`: an additive group G equipped with a VR operational predicate.

## Overview

Extends mathlib's `AddGroup G` with a predicate `IsOperational : G → Prop` that
selects the *operational* sub-collection of G in the sense of the VR programme.

An element `g : G` is **operational** if `IsOperational g` holds. Operationality
is the VR programme's signature concept: it asserts **explicit witness of
construction**, as opposed to merely classically existing. The precise character
of the witness is determined by each instance.

## Closure axioms

The operational elements are closed under all additive group operations:

- **`zero_isOperational`**: the zero element `0 : G` is operational.
- **`add_isOperational`**: if `a` and `b` are operational, so is `a + b`.
- **`neg_isOperational`**: if `a` is operational, so is `-a`.

Together these say the operational elements of G form a substructure closed under
the additive group operations — a *sub-apparatus* in the VR sense.

## Apparatus connection

This is an instance of the VR-Apparatus predicate-wrapping apparatus:

  Formal register      = G  (the full classical additive group, mathlib's `AddGroup G`)
  Operational register = { g : G // IsOperational g }  (operational sub-collection)

Stage 3 will register OperationalAddGroup as an instance of `PredicateOperationality`
(VRCycle.Apparatus.Wrapping), formalising this connection explicitly.

## Concrete instances (v0.1.0)

- **ℤ** (Stage 2): `IsOperational := fun _ => True`.
  Every integer is trivially operational via standard binary representation.
  Demonstrates apparatus collapses gracefully for fully-operational types.

- **ZMod n** (Stage 4): `IsOperational := fun _ => True`.
  Every element trivially operational since ZMod n is finite.

## On "operational" vs "computable"

"Operational" is intentional and specific to the VR programme. It is not:
- *Computable* (Turing): stronger, requires Turing-machine encoding.
- *Constructive* (constructive mathematics): different project — CML rewrites
  classical theory; VR wraps it.

Operationality in VR asserts an explicit witness of construction appropriate to
the domain. For ℤ and ZMod n, every element has an obvious explicit representation,
so the trivial witness suffices.

## Note on multiplicative groups

`OperationalGroup` (multiplicative analogue) is deferred to v0.2.0.
See Finding A0 in this file's module doc-comment.

## Axiom profile: [] -/
class OperationalAddGroup (G : Type*) extends AddGroup G where
  /-- Predicate identifying operational elements of the additive group.

  Each instance supplies its own interpretation of "operational". Common choices:
  - `fun _ => True` — trivially operational (every element has a witness).
    Used for ℤ and ZMod n in v0.1.0.
  - A predicate encoding an explicit construction witness.

  The predicate need not be decidable. Classical mathematics applies within
  the formal register G; operationality is a layer on top. -/
  IsOperational : G → Prop
  /-- The zero element `0 : G` is operational. -/
  zero_isOperational : IsOperational 0
  /-- Addition preserves operationality: if `a` and `b` are operational,
  then `a + b` is operational. -/
  add_isOperational : ∀ {a b : G},
    IsOperational a → IsOperational b → IsOperational (a + b)
  /-- Negation preserves operationality: if `a` is operational,
  then `-a` is operational. -/
  neg_isOperational : ∀ {a : G}, IsOperational a → IsOperational (-a)

-- ============================================================
-- Axiom audit — Stage 1, AddGroup.lean
-- ============================================================
-- STAGE: 1 (revised). SOURCE: PLAN.md Stage 1 + Finding A0 (recognition discipline).
-- LEAN OBJECTS (1 class):
--   OperationalAddGroup (class, extends AddGroup G)
-- AXIOM AUDIT: expected [] for the class definition.
--   Class definition introduces no proof obligations.
-- CHECKS: no sorry, no admit.

#print axioms OperationalAddGroup

end VR.Algebra
