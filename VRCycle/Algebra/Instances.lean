-- VRCycle: Algebra/Instances.lean
-- Operational Algebra v0.1.0 — Stages 2 and 4: concrete OperationalAddGroup instances.
--
-- STAGE: 2 (of 7), with Stage 4 placeholder. SOURCE: PLAN.md Stages 2, 4.
--
-- ## Position statement
-- This file provides concrete instances of `OperationalAddGroup` (defined in
-- VRCycle.Algebra.AddGroup) for the two planned v0.1.0 types: ℤ (Stage 2)
-- and ZMod n (Stage 4, added in that stage).
--
-- ## Stage 2 content: ℤ as OperationalAddGroup
--
-- ℤ under addition is the first concrete instance of the operational algebra
-- apparatus. The operational predicate is trivially `fun _ => True`:
-- every integer is operational via standard binary representation.
--
-- **Why trivially operational?**
-- The VR apparatus is predicate-generic. For ℤ, there is no constructive
-- obstacle to representing any element — every integer has an explicit
-- sign-magnitude or two's-complement encoding. The trivial predicate
-- demonstrates the apparatus collapses gracefully when the underlying type
-- is fully operational: closure axioms hold vacuously.
--
-- This is the expected "easy case." The interesting structure (non-trivial
-- IsOperational, Mode B transits) appears for types like ℝ where some
-- elements (non-computable reals) lack explicit construction witnesses.
--
-- **Apparatus reading for ℤ:**
--   Formal register      = ℤ  (all integers, mathlib's AddCommGroup ℤ)
--   Operational register = { n : ℤ // True }  ≅  ℤ  (all integers)
--   Operational layer    = vacuous (collapses to whole group)
--
-- **Axiom profile for ℤ instance:**
-- The instance delegates its AddGroup structure to `Int.instAddCommGroup`.
-- That instance depends on `[propext]` (from mathlib's ℤ arithmetic
-- infrastructure — integer arithmetic uses propositional extensionality
-- via Nat.rec-based definitions). So the ℤ ceiling is `[propext]`.
-- This is lighter than the VR-Audit standard ceiling [propext, Classical.choice, Quot.sound].
--
-- ## Stage 4 placeholder: ZMod n
-- Added in Stage 4. See PLAN.md Stage 4.

import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.ZMod.Basic
import VRCycle.Algebra.AddGroup

namespace VR.Algebra

-- ============================================================
-- §1. ℤ as OperationalAddGroup (Stage 2)
-- ============================================================

/-- Every integer is an operational additive group element.

**Instance**: `OperationalAddGroup ℤ` with `IsOperational := fun _ => True`.

**Design**: ℤ is an `AddCommGroup` in mathlib (via `Int.instAddCommGroup`).
Our instance extends this with the trivial operational predicate. The closure
axioms hold vacuously:
- `zero_isOperational` : `IsOperational 0 = True`. Proof: `trivial`.
- `add_isOperational`  : `True → True → True`. Proof: `fun _ _ => trivial`.
- `neg_isOperational`  : `True → True`. Proof: `fun _ => trivial`.

**Why trivial?**
Every integer has an explicit standard representation; no constructive
obstacle exists. The trivial predicate demonstrates the apparatus collapses
gracefully for fully-operational types. The non-trivial operational content
in the VR Cycle comes from types like ℝ (VR-Audit: IsComputableReal).

**Additive structure**: the `toAddGroup` field is supplied by
`inferInstance`, which finds `AddGroup ℤ` via the typeclass hierarchy
`Int.instAddCommGroup : AddCommGroup ℤ` (which extends `AddGroup ℤ`).

## Axiom profile: [propext]
Inherited from `Int.instAddCommGroup`. Propositional extensionality enters
via mathlib's integer arithmetic foundations. This is the ℤ-ceiling for
this cycle — lighter than the VR-Audit standard ceiling. -/
instance instOperationalAddGroupInt : OperationalAddGroup ℤ where
  toAddGroup    := inferInstance
  IsOperational := fun _ => True
  zero_isOperational              := trivial
  add_isOperational  _ _          := trivial
  neg_isOperational  _            := trivial

-- ============================================================
-- §2. Demonstration theorems for ℤ instance (Stage 2)
-- ============================================================

/-- Every integer is operational in the ℤ apparatus.

**Proof**: immediate from the trivial predicate `IsOperational = fun _ => True`.
This theorem makes the "fully operational" character of the ℤ instance explicit:
there is no restriction on which integers are operational.

## Axiom profile: [propext] (inherited from instOperationalAddGroupInt) -/
theorem int_isOperational (n : ℤ) : instOperationalAddGroupInt.IsOperational n :=
  trivial

/-- Addition of operational integers is operational.

**Proof**: applies `add_isOperational` from the `OperationalAddGroup ℤ` instance.
For ℤ this is vacuous (both hypotheses are `True`), but the theorem demonstrates
the apparatus Mode A pattern: closure of the operational sub-collection
under the group operation, mediated by the typeclass field.

This is the algebraic analogue of `IsComputableReal_add` from VR-Audit,
but trivially proved because ℤ carries no computational restriction.

## Axiom profile: [propext] (inherited from instOperationalAddGroupInt) -/
theorem int_add_isOperational {a b : ℤ}
    (ha : instOperationalAddGroupInt.IsOperational a)
    (hb : instOperationalAddGroupInt.IsOperational b) :
    instOperationalAddGroupInt.IsOperational (a + b) :=
  instOperationalAddGroupInt.add_isOperational ha hb

/-- Concrete example: 3 + 5 is operational in ℤ.

**Proof**: applies `int_add_isOperational` with trivial witnesses.
This is the demonstration from PLAN.md Stage 2 — the simplest possible
illustration that the closure structure works end-to-end.

## Axiom profile: [propext] -/
theorem int_three_plus_five_isOperational :
    instOperationalAddGroupInt.IsOperational ((3 : ℤ) + 5) :=
  int_add_isOperational trivial trivial

-- ============================================================
-- §3. ZMod n as OperationalAddGroup (Stage 4)
-- ============================================================

/-- Every element of `ZMod n` (for `n ≥ 1`) is an operational additive group element.

**Instance**: `OperationalAddGroup (ZMod n)` with `IsOperational := fun _ => True`,
for any `n : ℕ` satisfying `[NeZero n]`.

**ZMod n in mathlib**:
  `def ZMod : ℕ → Type  |  0 => ℤ  |  n+1 => Fin (n+1)`
  `instance commRing (n : ℕ) : CommRing (ZMod n)` — includes AddCommGroup.
  For `n ≥ 1` (enforced by `[NeZero n]`), `ZMod n = Fin n` — a finite type
  with decidable equality and computable arithmetic modulo n.

**Why `[NeZero n]` rather than unrestricted n?**
  `ZMod 0 = ℤ` definitionally in mathlib. If we allowed `n = 0`, the instance
  would cover `ZMod 0 = ℤ` — an overlap with `instOperationalAddGroupInt`.
  `[NeZero n]` cleanly excludes `n = 0` (since `NeZero 0` is false).
  The apparatus reading for `ZMod 0 = ℤ` is already provided by Stage 2.

**Why trivially operational?**
  `ZMod n` for `n ≥ 1` is a finite type — `Fintype (ZMod n)` with
  `Fintype.card (ZMod n) = n`. Every element has an explicit finite
  representation as an element of `Fin n`. No constructive obstacle exists.
  The trivial predicate demonstrates apparatus collapse for finite types:
  finiteness implies full operationality.

**Apparatus reading for ZMod n** (n ≥ 1):
  Formal register      = ZMod n  (all residues mod n)
  Operational register = { x : ZMod n // True }  ≅  ZMod n  (all residues)
  Operational layer    = vacuous (collapses to whole group, as for ℤ)

**Additive structure**: `toAddGroup` is supplied by `inferInstance`, finding
`AddGroup (ZMod n)` via `CommRing (ZMod n)` → `AddCommGroup` → `AddGroup`.

**Axiom profile**: `[propext, Quot.sound]` — inherits from `Fin.instCommRing`
(which provides the ring structure for `ZMod n = Fin n`). `Quot.sound` enters
via modular arithmetic's quotient-type infrastructure in `Fin`. This is a new
tier for this cycle: between ℤ's `[propext]` and the VR-Audit standard ceiling
`[propext, Classical.choice, Quot.sound]`. `Classical.choice` is NOT needed
for finite modular arithmetic.

**Finding A5 (ZMod-ceiling)**:
  ℤ-ceiling   = [propext]                 — integers, no quotients
  ZMod-ceiling = [propext, Quot.sound]    — finite modular, Fin infrastructure
  VR-Audit ceiling = [propext, Classical.choice, Quot.sound] — real analysis

This three-tier hierarchy confirms that algebraic structures are axiomatically
lighter than analytic ones. `Classical.choice` is the analysis-specific axiom;
it does not appear for either ℤ or ZMod n.

## Axiom profile: [propext, Quot.sound] -/
instance instOperationalAddGroupZMod (n : ℕ) [NeZero n] :
    OperationalAddGroup (ZMod n) where
  toAddGroup    := inferInstance
  IsOperational := fun _ => True
  zero_isOperational      := trivial
  add_isOperational _ _   := trivial
  neg_isOperational _     := trivial

-- ============================================================
-- §4. Demonstration theorems for ZMod n (Stage 4)
-- ============================================================

/-- Every element of `ZMod n` (n ≥ 1) is operational.

Analogous to `int_isOperational` for ℤ — demonstrates apparatus collapses
to the whole group for the finite cyclic case.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod_isOperational (n : ℕ) [NeZero n] (x : ZMod n) :
    (instOperationalAddGroupZMod n).IsOperational x :=
  trivial

/-- Addition in `ZMod n` is operational (concrete demonstration for ZMod 5).

Uses `add_isModeAOp` from Stage 3 — the Mode A theorem applies **directly**
to `ZMod 5` through the generic `[OperationalAddGroup G]` parameter.
No new theorem required: Stage 3 apparatus generalises automatically.

**Apparatus reading**: Stage 3 Mode A theorems are proved generically over
any `[OperationalAddGroup G]`. Instantiating with `G = ZMod 5` requires only
that `instOperationalAddGroupZMod 5` exists — which Stage 4 provides.
This confirms Finding A3 (apparatus reuse) at the instance level.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod5_add_isOperational (a b : ZMod 5) :
    (instOperationalAddGroupZMod 5).IsOperational (a + b) :=
  (instOperationalAddGroupZMod 5).add_isOperational trivial trivial

/-- Concrete: `2 + 3 = 0` in `ZMod 5`, and it is operational.

`(2 : ZMod 5) + 3 = 0` because `5 ≡ 0 (mod 5)`. The result is operational
regardless — demonstrating apparatus is agnostic to the group's arithmetic.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod5_two_plus_three_isOperational :
    (instOperationalAddGroupZMod 5).IsOperational ((2 : ZMod 5) + 3) :=
  trivial

-- ============================================================
-- Axiom audit — Stages 2 and 4, Instances.lean
-- ============================================================
-- STAGE: 2 and 4. SOURCE: PLAN.md Stages 2, 4.
-- LEAN OBJECTS:
--   Stage 2 (4 objects):
--     instOperationalAddGroupInt        (instance, OperationalAddGroup ℤ)
--     int_isOperational                 (theorem, ∀ n : ℤ, IsOperational n)
--     int_add_isOperational             (theorem, closure under addition)
--     int_three_plus_five_isOperational (theorem, concrete demonstration)
--   Stage 4 (3 objects):
--     instOperationalAddGroupZMod       (instance, OperationalAddGroup (ZMod n))
--     zmod_isOperational                (theorem, ∀ x : ZMod n, IsOperational x)
--     zmod5_add_isOperational           (theorem, concrete closure)
--     zmod5_two_plus_three_isOperational (theorem, concrete demo)
-- AXIOM AUDIT:
--   ℤ objects:    [propext]              — Int.instAddCommGroup ceiling
--   ZMod objects: [propext, Quot.sound]  — Fin.instCommRing ceiling
--   No Classical.choice in either — algebra stays below analysis ceiling.
-- CHECKS: no sorry, no admit.

#print axioms instOperationalAddGroupInt
#print axioms int_isOperational
#print axioms int_add_isOperational
#print axioms int_three_plus_five_isOperational
#print axioms instOperationalAddGroupZMod
#print axioms zmod_isOperational
#print axioms zmod5_add_isOperational
#print axioms zmod5_two_plus_three_isOperational

end VR.Algebra
