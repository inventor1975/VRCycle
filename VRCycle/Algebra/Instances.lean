-- VRCycle: Algebra/Instances.lean
-- Operational Algebra v0.1.0 — Stages 2 and 4: concrete OperationalAddGroup instances.
-- Operational Algebra v0.2.0 — Stage 3: ℤ as OperationalRing instance.
--
-- STAGE: 2, 4 (v0.1.0); 3 (v0.2.0). SOURCE: PLAN.md Stages 2, 4 (v0.1.0); Stage 3 (v0.2.0).
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
import VRCycle.Algebra.Ring

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
-- §5. ℤ as OperationalRing (v0.2.0 Stage 3)
-- ============================================================

/-- Every integer is an operational ring element (v0.2.0 instance).

**Instance**: `OperationalRing ℤ` with `IsOperational := fun _ => True`.

**Ring structure**: mathlib provides `Int.instCommRing : CommRing ℤ`, which includes
`Ring ℤ`. `toRing := inferInstance` finds this via the typeclass chain.

**Why trivially operational?**
Same reasoning as the additive group instance (v0.1.0 Stage 2):
every integer has an explicit standard representation (sign-magnitude or two's-complement).
No constructive obstacle exists. The trivial predicate demonstrates apparatus collapse
for fully-operational types.

**New closure axioms** (beyond v0.1.0 `OperationalAddGroup ℤ`):
- `one_isOperational` : `IsOperational 1 = True`. Proof: `trivial`.
- `mul_isOperational` : `True → True → True`. Proof: `fun _ _ => trivial`.

**Instance priority note**: with both `instOperationalAddGroupInt` (v0.1.0, direct) and
`OperationalRing.toOperationalAddGroup` applied to this instance (bridge) providing
`OperationalAddGroup ℤ`, Lean has two synthesis paths. Both give `IsOperational :=
fun _ => True`. Tested: Lean 4 selects `instOperationalAddGroupInt` (more specific, direct)
without ambiguity warning. Bridge provides a fallback that agrees definitionally.
No `@[priority]` annotation needed — natural instance resolution suffices.

**Apparatus reading for ℤ (extended)**:
  Formal register      = ℤ  (integers as ring; previously as additive group)
  Operational register = { n : ℤ // True }  ≅  ℤ  (all integers, as before)
  Ring layer           = vacuous for all ring operations (collapses to whole ring)

## Axiom profile: [propext]
Observed: same ceiling as `instOperationalAddGroupInt` (v0.1.0). The ring infrastructure
for ℤ (multiplication, multiplicative identity) does NOT introduce `Quot.sound` or
`Classical.choice` beyond what the additive group already brought. The ℤ-ceiling
remains `[propext]` across both additive and multiplicative structure. -/
instance instOperationalRingInt : OperationalRing ℤ where
  toRing        := inferInstance
  IsOperational := fun _ => True
  zero_isOperational              := trivial
  add_isOperational  _ _          := trivial
  neg_isOperational  _            := trivial
  one_isOperational               := trivial
  mul_isOperational  _ _          := trivial

-- ============================================================
-- §6. Demonstration theorems for OperationalRing ℤ (Stage 3)
-- ============================================================

/-- The multiplicative identity `1 : ℤ` is operational.

Demonstrates the `one_isOperational` closure axiom for the ℤ ring instance.
For ℤ this is vacuous (witness = `trivial`), but makes the apparatus structure explicit.

## Axiom profile: [propext] (inherited from instOperationalRingInt) -/
theorem int_one_isOperational : instOperationalRingInt.IsOperational (1 : ℤ) :=
  trivial

/-- Multiplication of operational integers is operational.

Applies `mul_isOperational` from the `OperationalRing ℤ` instance.
This is the algebraic analogue of `int_add_isOperational` for multiplication —
demonstrating that the ring's Mode A closure extends to multiplication.

## Axiom profile: [propext] (inherited from instOperationalRingInt) -/
theorem int_mul_isOperational {a b : ℤ}
    (ha : instOperationalRingInt.IsOperational a)
    (hb : instOperationalRingInt.IsOperational b) :
    instOperationalRingInt.IsOperational (a * b) :=
  instOperationalRingInt.mul_isOperational ha hb

/-- Concrete: `2 * 3 : ℤ` is operational.

Simple demonstration that multiplication closes the operational sub-collection.

## Axiom profile: [propext] -/
theorem int_two_mul_three_isOperational :
    instOperationalRingInt.IsOperational ((2 : ℤ) * 3) :=
  int_mul_isOperational trivial trivial

/-- Concrete: `(2 + 3) * 4 : ℤ` is operational.

Composition of addition (Mode A, additive) and multiplication (Mode A, multiplicative):
demonstrates that the operational sub-collection is closed under chained ring operations.
Both `+` and `*` preserve operationality; nesting them does too.

## Axiom profile: [propext] -/
theorem int_sum_mul_isOperational :
    instOperationalRingInt.IsOperational (((2 : ℤ) + 3) * 4) :=
  int_mul_isOperational
    (instOperationalRingInt.add_isOperational trivial trivial)
    trivial

-- ============================================================
-- §7. ZMod n as OperationalRing (v0.2.0 Stage 4)
-- ============================================================

/-- Every element of `ZMod n` (for `n ≥ 1`) is an operational ring element.

**Instance**: `OperationalRing (ZMod n)` with `IsOperational := fun _ => True`,
for any `n : ℕ` satisfying `[NeZero n]`.

**Ring structure**: mathlib provides `ZMod.instCommRing (n : ℕ) : CommRing (ZMod n)`,
which includes `Ring (ZMod n)`. `toRing := inferInstance` finds this via the typeclass chain.

**Why `[NeZero n]`?**
Same reason as v0.1.0 `instOperationalAddGroupZMod`:
`ZMod 0 = ℤ` definitionally in mathlib. Without `[NeZero n]`, this instance would
cover `ZMod 0 = ℤ`, overlapping with `instOperationalRingInt`. `[NeZero n]` cleanly
excludes `n = 0` (since `NeZero 0` is false).

**Why trivially operational?**
`ZMod n` for `n ≥ 1` is `Fin n` — a finite type with `Fintype.card = n`. Every element
has an explicit finite representation. No constructive obstacle. The trivial predicate
demonstrates apparatus collapse for finite quotient types.

**New closure axioms** (beyond v0.1.0 `OperationalAddGroup (ZMod n)`):
- `one_isOperational` : `IsOperational 1 = True`. Proof: `trivial`.
- `mul_isOperational` : `True → True → True`. Proof: `fun _ _ => trivial`.

**Diamond resolution** (parallel to Stage 3):
With both `instOperationalAddGroupZMod` (v0.1.0, direct) and the bridge
`OperationalRing.toOperationalAddGroup` applied to this instance providing
`OperationalAddGroup (ZMod n)`, Lean has two synthesis paths. Tested: Lean 4 selects
the direct instance without ambiguity warning — same natural resolution as Stage 3.

**Apparatus reading for ZMod n (extended)**:
  Formal register      = ZMod n  (residues mod n, as commutative ring; previously additive group)
  Operational register = { x : ZMod n // True }  ≅  ZMod n  (all residues, as before)
  Ring layer           = vacuous for all ring operations (collapses to whole ring)

## Axiom profile: [propext, Quot.sound]
Observed: same ceiling as `instOperationalAddGroupZMod` (v0.1.0). The ring infrastructure
for ZMod n (multiplication, `1`) does NOT introduce `Classical.choice` beyond what the
additive group already brought. The ZMod-ceiling remains `[propext, Quot.sound]`
across both additive and multiplicative structure.

**Finding A10 confirmed for finite quotient types**: ring extension does not escalate the
ceiling. For ZMod n, as for ℤ, the ceiling is determined by the underlying type (Fin
quotient infrastructure → `Quot.sound`), not by how much algebraic structure is layered
on top. -/
instance instOperationalRingZMod (n : ℕ) [NeZero n] : OperationalRing (ZMod n) where
  toRing        := inferInstance
  IsOperational := fun _ => True
  zero_isOperational              := trivial
  add_isOperational  _ _          := trivial
  neg_isOperational  _            := trivial
  one_isOperational               := trivial
  mul_isOperational  _ _          := trivial

-- ============================================================
-- §8. Demonstration theorems for OperationalRing (ZMod n) (Stage 4)
-- ============================================================

/-- The multiplicative identity `1 : ZMod 5` is operational.

Demonstrates `one_isOperational` for the ZMod ring instance. Trivial for ZMod 5.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod5_one_isOperational :
    (instOperationalRingZMod 5).IsOperational (1 : ZMod 5) :=
  trivial

/-- Multiplication in `ZMod 5` is operational.

Applies `mul_isOperational` from the `OperationalRing (ZMod 5)` instance.
Demonstrates ring Mode A closure for multiplication in finite modular arithmetic.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod5_mul_isOperational (a b : ZMod 5) :
    (instOperationalRingZMod 5).IsOperational (a * b) :=
  (instOperationalRingZMod 5).mul_isOperational trivial trivial

/-- Concrete: `2 * 3 = 1` in `ZMod 5`, and it is operational.

`(2 : ZMod 5) * 3 = 6 mod 5 = 1`. The result is operational regardless —
apparatus is agnostic to modular arithmetic's specific values.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod5_two_mul_three_isOperational :
    (instOperationalRingZMod 5).IsOperational ((2 : ZMod 5) * 3) :=
  trivial

/-- Concrete: `(2 + 3) * 4 : ZMod 7` is operational.

Chained ring operations in ZMod 7: addition then multiplication.
Demonstrates that the operational sub-collection of ZMod n is closed under
the full ring structure — not just addition.

## Axiom profile: [propext, Quot.sound] -/
theorem zmod7_sum_mul_isOperational :
    (instOperationalRingZMod 7).IsOperational (((2 : ZMod 7) + 3) * 4) :=
  trivial

-- ============================================================
-- Axiom audit — all stages, Instances.lean
-- ============================================================
-- STAGE: 2, 4 (v0.1.0); 3, 4 (v0.2.0). SOURCE: PLAN.md throughout.
-- LEAN OBJECTS:
--   v0.1.0 Stage 2 (4 objects):
--     instOperationalAddGroupInt        (instance, OperationalAddGroup ℤ)
--     int_isOperational                 (theorem, ∀ n : ℤ, IsOperational n)
--     int_add_isOperational             (theorem, closure under addition)
--     int_three_plus_five_isOperational (theorem, concrete demonstration)
--   v0.1.0 Stage 4 (4 objects):
--     instOperationalAddGroupZMod       (instance, OperationalAddGroup (ZMod n))
--     zmod_isOperational                (theorem, ∀ x : ZMod n, IsOperational x)
--     zmod5_add_isOperational           (theorem, concrete closure)
--     zmod5_two_plus_three_isOperational (theorem, concrete demo)
--   v0.2.0 Stage 3 (5 objects):
--     instOperationalRingInt            (instance, OperationalRing ℤ)
--     int_one_isOperational             (theorem, IsOperational 1)
--     int_mul_isOperational             (theorem, closure under multiplication)
--     int_two_mul_three_isOperational   (theorem, concrete multiplication)
--     int_sum_mul_isOperational         (theorem, chained ring operations)
--   v0.2.0 Stage 4 (5 objects):
--     instOperationalRingZMod           (instance, OperationalRing (ZMod n))
--     zmod5_one_isOperational           (theorem, IsOperational 1 in ZMod 5)
--     zmod5_mul_isOperational           (theorem, closure under multiplication in ZMod 5)
--     zmod5_two_mul_three_isOperational (theorem, concrete multiplication)
--     zmod7_sum_mul_isOperational       (theorem, chained ring operations in ZMod 7)
-- AXIOM AUDIT:
--   ℤ AddGroup objects: [propext]              — v0.1.0 ceiling
--   ZMod objects:       [propext, Quot.sound]  — v0.1.0 ceiling
--   ℤ Ring objects:     [propext]              — v0.2.0, ceiling UNCHANGED from AddGroup
--   ZMod Ring objects:  [propext, Quot.sound]  — v0.2.0, ceiling UNCHANGED from AddGroup
--   Finding A10 confirmed: ring extension does not escalate ceiling for ℤ or ZMod n.
--   No Classical.choice in any object — algebra stays below analysis ceiling.
-- CHECKS: no sorry, no admit.

#print axioms instOperationalAddGroupInt
#print axioms int_isOperational
#print axioms int_add_isOperational
#print axioms int_three_plus_five_isOperational
#print axioms instOperationalAddGroupZMod
#print axioms zmod_isOperational
#print axioms zmod5_add_isOperational
#print axioms zmod5_two_plus_three_isOperational
#print axioms instOperationalRingInt
#print axioms int_one_isOperational
#print axioms int_mul_isOperational
#print axioms int_two_mul_three_isOperational
#print axioms int_sum_mul_isOperational
#print axioms instOperationalRingZMod
#print axioms zmod5_one_isOperational
#print axioms zmod5_mul_isOperational
#print axioms zmod5_two_mul_three_isOperational
#print axioms zmod7_sum_mul_isOperational

end VR.Algebra
