-- VRCycle: Algebra/Module.lean
-- Operational Algebra v0.4.0 — Stage 3: OperationalModule typeclass.
--
-- STAGE: 3 (of 6, v0.4.0). SOURCE: PLAN.md Stage 3.
--
-- ## Position statement
-- This file introduces the VR operational layer on top of mathlib's module typeclass.
-- One typeclass is defined:
--
--   OperationalModule (R M : Type*): module with operational scalar-action closure.
--
-- ## Design overview
--
-- `OperationalModule` is a **bridge-based** typeclass: it does not introduce a
-- new predicate on M. Instead, it:
--   (a) Requires existing typeclasses: `[OperationalRing R]` and `[OperationalAddGroup M]`.
--   (b) Adds exactly one new axiom: `smul_isOperational` — scalar action preserves
--       the operational predicate already present on M.
--
-- This contrasts with `OperationalRing` and `OperationalField`, which each defined
-- their own new predicate (`IsOperational : R → Prop` or `IsOperational : K → Prop`).
-- `OperationalModule` adds NO new predicate field. The predicate on M is fully
-- determined by the underlying `[OperationalAddGroup M]` instance.
--
-- **Predicate ownership**: when `[OperationalModule R M]` is in scope, the operational
-- predicate for elements of M is `OperationalAddGroup.IsOperational (M := M)`.
-- When checking operationality of scalars r : R, the predicate is
-- `OperationalRing.IsOperational (R := R)` (from the `[OperationalRing R]` instance).
-- Two typeclasses, one (predicate type for M), one (predicate type for R).
-- `OperationalModule` binds them together through scalar action closure.
--
-- ## Mathlib reconnaissance (Stage 3)
--
-- ### Module hierarchy (Mathlib.Algebra.Module.Defs)
--
--   class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
--     DistribMulAction R M
--     add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
--     zero_smul : ∀ (x : M), (0 : R) • x = 0
--
--   DistribMulAction M A [Monoid M] [AddMonoid A] extends MulAction M A
--     smul_zero : ∀ (r : M), r • (0 : A) = 0
--     smul_add : ∀ (r : M) (x y : A), r • (x + y) = r • x + r • y
--
--   MulAction α β [Monoid α] extends SemigroupAction α β
--     one_smul : ∀ (b : β), (1 : α) • b = b
--     mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • (y • b)
--
-- ### Key: Module weaker than Ring
--
--   `Module` requires `Semiring R` and `AddCommMonoid M` — NOT Ring and AddCommGroup.
--   Our `OperationalModule` uses `[Ring R] [AddCommGroup M]`, which is STRONGER.
--   Lean synthesises `[Semiring R]` from `[Ring R]` via `Ring.toSemiring`.
--   Lean synthesises `[AddCommMonoid M]` from `[AddCommGroup M]` via the chain
--   AddCommGroup → AddCommMonoid. Both syntheses are in the standard typeclass hierarchy.
--
-- ### SMul origin
--
--   `r • m` for `r : R`, `m : M` with `[Module R M]` uses `SMul R M` from
--   `Module R M → DistribMulAction R M → MulAction R M → SemigroupAction R M → SMul R M`.
--   This is the standard module scalar action. No ambiguity in our context.
--
-- ## Design decisions
--
-- ### Decision A: predicate from OperationalAddGroup M (no new predicate)
--
--   The operational predicate for M is supplied by `[OperationalAddGroup M]`.
--   `OperationalModule` does NOT introduce a new predicate field.
--
--   Rationale: in the VR hierarchy, each algebraic STRUCTURE level (group, ring,
--   field) owns its predicate. The module structure IS the additive group structure
--   of M with a scalar action from R. Adding a new predicate for "operationality in
--   the module sense" would duplicate the additive group's predicate without new content.
--   Decision A keeps the design minimal: one predicate per carrier type, owned by the
--   most basic operational structure that type participates in.
--
--   Contrast: `OperationalField` DID introduce a new predicate (vs `OperationalRing`),
--   because `Field K` adds the genuinely new operation `(·⁻¹)` requiring a new closure
--   axiom. `Module R M` adds scalar action, but M's carrier identity (AddGroup) already
--   owns the predicate for M-elements.
--
-- ### Decision B: closure axiom for scalar action
--
--   Single new axiom: `smul_isOperational`. States that the scalar action `(· • ·)`
--   maps (operational-in-R, operational-in-M) to operational-in-M.
--
--   This is the minimal new content of `OperationalModule`: all other operations
--   (addition, subtraction, negation, zero in M) are already covered by
--   `[OperationalAddGroup M]`.
--
-- ### Decision C: naming — explicit predicate qualification
--
--   The `smul_isOperational` field uses fully qualified predicates:
--     `OperationalRing.IsOperational r` — operationality of the scalar r in R
--     `OperationalAddGroup.IsOperational m` — operationality of m in M (hypothesis)
--     `OperationalAddGroup.IsOperational (r • m)` — operationality of result in M (goal)
--
--   This avoids any ambiguity between the two predicates in scope.
--
-- ## Recognition discipline check
--
-- **Question**: is `OperationalModule` genuinely needed, or could downstream use
-- `[OperationalRing R] [OperationalAddGroup M] + hypothesis smul_isOperational` directly?
--
-- **Arguments for KEEPING** (decision: KEEP):
--   (a) Mode A theorem (Stage 5): `smul_isModeAOp` needs a clean binding for the
--       scalar action closure. `[OperationalModule R M]` provides this binding as
--       a single typeclass constraint, matching the pattern of `mul_isModeAOp`
--       using `[OperationalRing R]` and `add_isModeAOp` using `[OperationalAddGroup G]`.
--   (b) Concrete instances (Stage 4): ℤ as ℤ-module and ℚ as ℚ-module are natural
--       `OperationalModule` instances. Without the typeclass, there is no natural
--       instance declaration mechanism.
--   (c) Structural completeness: the hierarchy
--       OperationalAddGroup → OperationalRing → OperationalField → [OperationalModule]
--       is the natural algebraic hierarchy with modules as the fourth structure.
--   (d) Consistent with programme pattern: each algebraic extension gets its own
--       operational typeclass.
--
-- **Arguments against** (considered and rejected):
--   (a) All v0.4.0 instances (ℤ-module, ℚ-module) have trivial predicate → smul
--       is trivially operational. So the typeclass adds zero mathematical difficulty.
--   Response: triviality of instances doesn't negate the design necessity.
--   The typeclass mechanism is needed for clean downstream use regardless of
--   how simple the instances are.
--
-- **Verdict**: KEEP. Finding A17 will document apparatus reuse for module structure.
--
-- ## Apparatus connection (Stage 5 / Finding A17)
--
-- When `[OperationalModule R M]` is in scope, the Mode A theorem `smul_isModeAOp`
-- (Stage 5) will state that scalar action is a Mode A operation for the apparatus
-- instance from `[OperationalAddGroup M]`. This will confirm Finding A3 for the
-- fourth algebraic structure (additive group → ring → field → module).
-- No new `PredicateOperationality` instance is needed: `instPredOpAddGroup` from
-- ModeA.lean already covers `OperationalAddGroup M`, and module inherits this.
--
-- ## Axiom profile prediction
-- `OperationalModule` class definition: [] (class definitions introduce no proof
-- obligations; type-level only).

import Mathlib.Algebra.Module.Defs
import VRCycle.Algebra.Ring

namespace VR.Algebra

-- ============================================================
-- §1. OperationalModule — modules with operational scalar action
-- ============================================================

/-- `OperationalModule R M`: a module over an operational ring, with scalar action
preserving the operational predicate of the underlying additive group.

## Overview

Requires:
- `[Ring R]` and `[AddCommGroup M]` — standard algebraic structure.
- `[Module R M]` — scalar action of R on M (standard mathlib module).
- `[OperationalRing R]` — operational predicate on R (v0.2.0).
- `[OperationalAddGroup M]` — operational predicate on M (v0.1.0).

Adds exactly ONE new axiom:
- **`smul_isOperational`**: if `r : R` is operational and `m : M` is operational,
  then `r • m : M` is operational.

## Bridge-based design (no new predicate)

`OperationalModule` does **not** introduce a new predicate field. The operational
predicate for elements of M is `OperationalAddGroup.IsOperational (M := M)` from
the underlying `[OperationalAddGroup M]` instance. `OperationalModule` adds only
the scalar-action closure axiom on top of the existing predicates.

This is the correct design: M's identity as an operational additive group already
owns the predicate for M-elements. The module structure adds scalar action from R,
and `smul_isOperational` is the single new mathematical content.

Contrast with `OperationalField K` (v0.3.0), which DID add a new predicate:
`Field K` introduces `(·⁻¹)` as a genuinely new operation, so a new closure axiom
requires a new typeclass with a new predicate field. For modules, the new operation
is scalar action `(· • ·)`, but M's carrier is already an operational additive
group — no new predicate needed on M.

## Closure axioms provided

All additive operations on M are covered by `[OperationalAddGroup M]`:
  - `0 : M` is operational (zero_isOperational)
  - `m₁ + m₂` is operational if m₁, m₂ are (add_isOperational)
  - `-m` is operational if m is (neg_isOperational)

`OperationalModule` adds:
  - `r • m` is operational if r (in R) and m (in M) are (smul_isOperational ← NEW)

## Concrete instances (v0.4.0 Stage 4)

- **ℤ as ℤ-module**: `smul_isOperational := fun _ _ => trivial`.
  ℤ acts on itself via ring multiplication. Both ℤ predicates are `True`.
- **ℚ as ℚ-module**: `smul_isOperational := fun _ _ => trivial`.
  ℚ acts on itself via ring multiplication. Both ℚ predicates are `True`.

Both trivial because `OperationalRing.IsOperational := fun _ => True` and
`OperationalAddGroup.IsOperational := fun _ => True` for these instances.

## Module structure

`Module R M` (from `Mathlib.Algebra.Module.Defs`) requires `[Semiring R] [AddCommMonoid M]`.
Our context provides `[Ring R] [AddCommGroup M]`, which are strictly stronger:
  Ring R → Semiring R (via Ring.toSemiring)
  AddCommGroup M → AddCommMonoid M (via AddCommGroup.toAddCommMonoid)
Lean synthesises the required instances automatically via these chains.

## Recognition discipline

Decision: KEEP `OperationalModule`. The typeclass provides the natural binding for:
  (a) Stage 5 `smul_isModeAOp` Mode A theorem.
  (b) Stage 4 concrete instances (ℤ-module, ℚ-module).
  (c) Structural completeness of the algebraic hierarchy.

## Axiom profile: [] -/
class OperationalModule (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    [OperationalRing R] [OperationalAddGroup M] where
  /-- Scalar action preserves operationality: if `r : R` is operational and `m : M` is
  operational, then `r • m : M` is operational.

  This is the single new closure axiom of `OperationalModule`, bridging the scalar
  action with the existing operational predicates on R (from `OperationalRing R`)
  and on M (from `OperationalAddGroup M`). -/
  smul_isOperational : ∀ {r : R} {m : M},
    OperationalRing.IsOperational r →
    OperationalAddGroup.IsOperational m →
    OperationalAddGroup.IsOperational (r • m)

-- ============================================================
-- Axiom audit — Stage 3, Module.lean
-- ============================================================
-- STAGE: 3 (of 6, v0.4.0). SOURCE: PLAN.md Stage 3.
-- LEAN OBJECTS (1 class):
--   OperationalModule (class, [Ring R] [AddCommGroup M] [Module R M]
--                      [OperationalRing R] [OperationalAddGroup M])
-- DESIGN DECISIONS:
--   A: predicate from OperationalAddGroup M (no new predicate field) — bridge-based.
--   B: single new axiom smul_isOperational.
--   C: explicit qualification OperationalRing.IsOperational / OperationalAddGroup.IsOperational.
-- RECOGNITION DISCIPLINE: OperationalModule KEPT (see §1 doc-comment).
-- APPARATUS CONNECTION: Stage 5 will confirm Finding A3 for module (4th structure).
--   instPredOpAddGroup (ModeA.lean) already covers OperationalAddGroup M.
--   No new PredicateOperationality instance needed.
-- AXIOM AUDIT: expected [] for class definition.
-- CHECKS: no sorry, no admit.

#print axioms OperationalModule

end VR.Algebra
