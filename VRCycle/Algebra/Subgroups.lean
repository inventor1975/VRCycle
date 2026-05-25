-- VRCycle: Algebra/Subgroups.lean
-- Operational Algebra v0.1.0 — Stage 5: Operational subgroups.
--
-- STAGE: 5 (of 7). SOURCE: PLAN.md Stage 5.
--
-- ## Position statement
-- This file introduces the VR operational layer on `AddSubgroup G`: an additive
-- subgroup of an `OperationalAddGroup G` is **operationally compatible** if every
-- element it contains is operational.
--
-- ## Finding A6 — Recognition discipline applied at Stage 5
--
-- Initial Stage 5 plan called for a new bundled structure:
--
--   `structure OperationalAddSubgroup (G : Type*) [OperationalAddGroup G] where`
--     `toAddSubgroup : AddSubgroup G`
--     `mem_isOperational : ∀ x ∈ toAddSubgroup, IsOperational x`
--
-- Reconnaissance showed this structure is **unnecessary**. The compatibility
-- condition `∀ x ∈ H, IsOperational x` is already a well-formed Prop over
-- mathlib's `AddSubgroup G`. It does not require a new type — it is a PREDICATE
-- on existing data:
--
--   `IsOperationalAddSubgroup H : Prop := ∀ x ∈ H, IsOperational x`
--
-- The bundled structure would wrap `AddSubgroup G` with a condition that:
-- (a) is trivially satisfied for all v0.1.0 instances (trivial predicate),
-- (b) adds syntactic overhead without mathematical content,
-- (c) requires new API for membership, coercion, etc., that replicates
--     what `AddSubgroup` already provides.
--
-- **Decision**: use the predicate approach. The bundled structure is deferred
-- pending actual use cases that require it (likely when non-trivial operational
-- predicates appear in future cycles).
--
-- This echoes Finding F11 from VR-Apparatus (generic Register abstraction
-- unnecessary) and Finding A0 from this cycle (OperationalGroup multiplicative
-- typeclass unnecessary). Recognition discipline applied for the third time.
--
-- ## AddSubgroup reconnaissance (Mathlib.Algebra.Group.Subgroup.Basic)
--
--   `AddSubgroup G : Type*`  — subgroup of an AddGroup G.
--   Fields: `carrier : Set G`, `add_mem'`, `zero_mem'`, `neg_mem'`.
--
--   Key API:
--     `AddSubgroup.mem_bot : x ∈ ⊥ ↔ x = 0`             [propext, Quot.sound]
--     `AddSubgroup.mem_top : x ∈ ⊤`                       [propext]
--     `AddSubgroup.mem_inf : x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K` [propext]
--     `AddSubgroup.zero_mem H : 0 ∈ H`                     [propext, Quot.sound]
--     `AddSubgroup.add_mem H : x ∈ H → y ∈ H → x + y ∈ H`
--     `AddSubgroup.neg_mem H : x ∈ H → -x ∈ H`
--
-- ## Apparatus connection
--
-- `IsOperationalAddSubgroup H` is a Prop. It does not introduce a new apparatus
-- instance — `H : AddSubgroup G` inherits the `PredicateOperationality` apparatus
-- from the parent `[OperationalAddGroup G]` via the `instPredOpAddGroup` instance
-- (VRCycle.Algebra.ModeA). The predicate `IsOperationalAddSubgroup` is a
-- **condition** on subgroups within the parent apparatus, not a new apparatus tier.
--
-- ## Axiom profile observations
--
--   IsOperationalAddSubgroup (def):         [propext]
--   bot_isOperationalAddSubgroup (theorem): [propext, Quot.sound]  ← mem_bot ceiling
--   top_isOperationalAddSubgroup (theorem): [propext]
--   inf_isOperationalAddSubgroup (theorem): [propext]
--
-- `bot_isOperationalAddSubgroup` pulls `Quot.sound` from `AddSubgroup.mem_bot`.
-- This is the same tier as ZMod instances (Stage 4). The other subgroup theorems
-- stay at `[propext]`.

import Mathlib.Algebra.Group.Subgroup.Basic
import VRCycle.Algebra.Instances

namespace VR.Algebra

-- ============================================================
-- §1. IsOperationalAddSubgroup — predicate on AddSubgroup G
-- ============================================================

/-- `IsOperationalAddSubgroup H`: every element of `H : AddSubgroup G` is operational.

## Overview

An additive subgroup `H` of an `OperationalAddGroup G` is **operationally
compatible** if every element it contains satisfies the operational predicate:

  `IsOperationalAddSubgroup H  :=  ∀ x ∈ H, IsOperational x`

This is the natural notion of "operational subgroup" in the VR apparatus setting:
the subgroup stays within the operational sub-collection of G.

## Design: predicate, not structure

The natural formulation is a Prop over existing `AddSubgroup G`, not a new
bundled type. See Finding A6 in the module doc-comment.

## Behaviour for v0.1.0 instances

For ℤ and ZMod n where `IsOperational = fun _ => True`:
- `IsOperationalAddSubgroup H` holds for EVERY `H : AddSubgroup G`.
- All subgroups are operationally compatible.
- This is the apparatus collapse expected for fully-operational types.

For future non-trivial `IsOperational` predicates, this condition is meaningful:
it selects the subgroups that "stay within" the operational sub-collection.

## Axiom profile: [propext] -/
def IsOperationalAddSubgroup {G : Type*} [OperationalAddGroup G]
    (H : AddSubgroup G) : Prop :=
  ∀ x ∈ H, OperationalAddGroup.IsOperational x

-- ============================================================
-- §2. Theorems on operational subgroups
-- ============================================================

/-- The trivial subgroup `⊥` (containing only `0`) is always operationally compatible.

**Proof**: `⊥ = {0}` (by `AddSubgroup.mem_bot`). Any `x ∈ ⊥` satisfies `x = 0`.
The zero element is operational by `zero_isOperational`.

**Significance**: this is a non-trivial theorem — it holds for ALL `OperationalAddGroup`
instances, including non-trivial ones. It uses `zero_isOperational` from the typeclass,
confirming that the identity element is always in the operational sub-collection.

## Axiom profile: [propext, Quot.sound]
(Quot.sound enters via `AddSubgroup.mem_bot`; same tier as ZMod instances.) -/
theorem bot_isOperationalAddSubgroup {G : Type*} [OperationalAddGroup G] :
    IsOperationalAddSubgroup (⊥ : AddSubgroup G) := by
  intro x hx
  rw [AddSubgroup.mem_bot] at hx
  subst hx
  exact OperationalAddGroup.zero_isOperational

/-- If all elements of G are operational, then `⊤` (the whole group) is operationally
compatible.

**Proof**: immediate — every element of `⊤` is in G, and all G-elements are operational.

**Conditional**: the hypothesis `∀ x : G, IsOperational x` is required. Without it,
`⊤` need not be operational (for non-trivial predicates, some elements of G may not
be operational). This is distinct from `bot_isOperationalAddSubgroup`, which holds
unconditionally.

**Corollary for v0.1.0**: for ℤ and ZMod n (trivial `IsOperational`), `⊤` is always
operational — proved by `top_int_isOperationalAddSubgroup` below.

## Axiom profile: [propext] -/
theorem top_isOperationalAddSubgroup {G : Type*} [OperationalAddGroup G]
    (hall : ∀ x : G, OperationalAddGroup.IsOperational x) :
    IsOperationalAddSubgroup (⊤ : AddSubgroup G) :=
  fun x _ => hall x

/-- Intersection is one-sided: if `H` is operationally compatible, then `H ⊓ K` is
operationally compatible for any `K`.

**Proof**: if `x ∈ H ⊓ K`, then `x ∈ H` (left component), so `IsOperational x` by `hH`.

**One-sided sufficiency**: the condition on `K` is not needed — membership in `H` alone
suffices because `H ⊓ K ⊆ H`. This is stronger than the standard formulation requiring
both H and K to be operational: a subgroup inherits operationality from a single
operational parent via the inclusion `H ⊓ K ↪ H`.

This captures the mathematical principle: the intersection of an operational subgroup
with ANY subgroup is operational (not just with another operational subgroup).

## Axiom profile: [propext] -/
theorem inf_isOperationalAddSubgroup {G : Type*} [OperationalAddGroup G]
    {H K : AddSubgroup G}
    (hH : IsOperationalAddSubgroup H) :
    IsOperationalAddSubgroup (H ⊓ K) :=
  fun x hx => hH x ((AddSubgroup.mem_inf.mp hx).1)

/-- If both `H` and `K` are operationally compatible, so is `H ⊓ K`.

**Corollary of `inf_isOperationalAddSubgroup`** (one-sided version).
Provided for symmetry — the standard bilateral statement expected by the plan.

## Axiom profile: [propext] -/
theorem inf_isOperationalAddSubgroup_bilateral {G : Type*} [OperationalAddGroup G]
    {H K : AddSubgroup G}
    (hH : IsOperationalAddSubgroup H) (_hK : IsOperationalAddSubgroup K) :
    IsOperationalAddSubgroup (H ⊓ K) :=
  inf_isOperationalAddSubgroup hH

-- ============================================================
-- §3. Concrete demonstrations via ℤ (Stage 5)
-- ============================================================

/-- `⊥ : AddSubgroup ℤ` is operationally compatible. -/
theorem int_bot_isOperationalAddSubgroup :
    IsOperationalAddSubgroup (⊥ : AddSubgroup ℤ) :=
  bot_isOperationalAddSubgroup

/-- `⊤ : AddSubgroup ℤ` is operationally compatible.

Since `IsOperational = fun _ => True` for ℤ, all elements are operational.
The `⊤` subgroup (= all of ℤ) is therefore operationally compatible.

## Axiom profile: [propext] -/
theorem int_top_isOperationalAddSubgroup :
    IsOperationalAddSubgroup (⊤ : AddSubgroup ℤ) :=
  top_isOperationalAddSubgroup (fun _ => trivial)

/-- The intersection of `⊤ : AddSubgroup ℤ` with any subgroup is operationally
compatible. Concrete demonstration of `inf_isOperationalAddSubgroup`.

## Axiom profile: [propext] -/
theorem int_inf_top_isOperationalAddSubgroup (K : AddSubgroup ℤ) :
    IsOperationalAddSubgroup ((⊤ : AddSubgroup ℤ) ⊓ K) :=
  inf_isOperationalAddSubgroup int_top_isOperationalAddSubgroup

-- ============================================================
-- Axiom audit — Stage 5, Subgroups.lean
-- ============================================================
-- STAGE: 5. SOURCE: PLAN.md Stage 5.
-- LEAN OBJECTS (1 def, 4 general theorems, 3 ℤ demonstrations):
--   IsOperationalAddSubgroup              (def, predicate on AddSubgroup G)
--   bot_isOperationalAddSubgroup          (theorem, ⊥ always operational)
--   top_isOperationalAddSubgroup          (theorem, ⊤ operational if all-operational)
--   inf_isOperationalAddSubgroup          (theorem, one-sided intersection)
--   inf_isOperationalAddSubgroup_bilateral (theorem, bilateral intersection corollary)
--   int_bot_isOperationalAddSubgroup      (theorem, ℤ ⊥ demo)
--   int_top_isOperationalAddSubgroup      (theorem, ℤ ⊤ demo)
--   int_inf_top_isOperationalAddSubgroup  (theorem, ℤ intersection demo)
-- AXIOM PROFILE:
--   IsOperationalAddSubgroup              [propext]
--   bot_isOperationalAddSubgroup          [propext, Quot.sound]  ← mem_bot
--   top_isOperationalAddSubgroup          [propext]
--   inf_isOperationalAddSubgroup          [propext]
--   inf_isOperationalAddSubgroup_bilateral [propext]
--   int_bot_isOperationalAddSubgroup      [propext, Quot.sound]
--   int_top_isOperationalAddSubgroup      [propext]
--   int_inf_top_isOperationalAddSubgroup  [propext]
-- CHECKS: no sorry, no admit.

#print axioms IsOperationalAddSubgroup
#print axioms bot_isOperationalAddSubgroup
#print axioms top_isOperationalAddSubgroup
#print axioms inf_isOperationalAddSubgroup
#print axioms inf_isOperationalAddSubgroup_bilateral
#print axioms int_bot_isOperationalAddSubgroup
#print axioms int_top_isOperationalAddSubgroup
#print axioms int_inf_top_isOperationalAddSubgroup

end VR.Algebra
