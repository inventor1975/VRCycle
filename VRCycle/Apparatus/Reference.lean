-- VR-Apparatus: Reference (DOI TBD — v0.1.0)
-- Stage 1: ReferenceOperationality — class for reference semantics apparatus.
--
-- STAGE: 1 (of 7). SOURCE: PLAN.md Stage 1; CLAUDE.md §Apparatus modes.
--
-- ## Position statement
-- Defines `ReferenceOperationality Q [Setoid Q]` — the apparatus class
-- for the reference semantics pattern used in VR-Sets and VR-Sets-ZFA.
--
-- ## Design: class with [Setoid Q] and substantive fields
-- `ReferenceOperationality (Q : Type*) [s : Setoid Q]` uses Lean's typeclass
-- mechanism to carry the equivalence relation. Two substantive fields:
--   membership — membership predicate on the quotient Quotient s
--   ext        — extensionality: same members implies equal objects
--
-- These two fields ARE uniform across all reference semantics cases in VR:
--   OSet (PSet.setoid): ZFSet.ext, ZFSet.mem
--   OSetZFA (CoPSet.instSetoid): OSetZFA.ext, OSetZFA.Mem
-- Both satisfy membership + ext. Contrast with PredicateOperationality
-- where operations (add, inner product) are type-specific.
--
-- ## [Setoid Q] vs (R : Q → Q → Prop) parametrization
-- Using [s : Setoid Q] instead of explicit (R, iseqv) avoids field-
-- dependency issues (iseqv as both a field and a component of later
-- field types). The setoid instances (CoPSet.instSetoid, PSet.setoid)
-- already exist in mathlib/VRCycle, so typeclass inference works directly.
--
-- ## Q1 test: [Setoid Q] class syntax
-- Before the OSetZFA instance, verify that the class syntax
-- `class ... (Q : Type*) [s : Setoid Q] where membership : Quotient s → ...`
-- compiles on a trivial case (Unit with trivial setoid).
-- RESULT: Q1 CONFIRMED. No workaround needed.
--
-- ## Q2 test: OSetZFA.ext wrapper
-- `ext := fun x y h => OSetZFA.ext h` — wrapper lambda is sufficient.
-- Lean sees through membership → OSetZFA.Mem and Quotient s → OSetZFA
-- definitionally. RESULT: Q2 CONFIRMED.
--
-- ## Axiom profile
-- ReferenceOperationality class itself: [].
-- identityNature def: [].
-- Instance for CoPSet (OSetZFA): [propext, Classical.choice, Quot.sound].
--   propext: from OSetZFA.ext (used in CoPSet.mem_congr via propext).
--   Quot.sound: from OSetZFA.Mem (liftOn₂) and OSetZFA.ext (Quotient.sound).
--   Classical.choice: from CoPSet = PFunctor.M (mathlib M-type uses choice).
--   Note: Classical.choice enters via transitive import of PFunctor.M,
--   not from OSetZFA operations directly. This is the standard ceiling
--   for VR-Sets-ZFA work. Within axiom ceiling [propext, Classical.choice, Quot.sound].
-- Cross-apparatus examples live in Apparatus.lean (requires both Wrapping + Reference).

import VRCycle.Apparatus.Identity
import VRCycle.SetsZFA.Membership

namespace VR.Apparatus

-- ============================================================
-- §1. Q1 test: verify [Setoid Q] class syntax on trivial case
-- ============================================================

-- Before the main class definition, verify that the Lean 4 class syntax
-- `[s : Setoid Q]` compiles correctly and that `Quotient s` in field types
-- refers correctly to the inferred setoid.

private instance trivialUnitSetoid : Setoid Unit where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

-- ============================================================
-- §2. ReferenceOperationality class
-- ============================================================

/-- ReferenceOperationality Q [s]: apparatus class for reference semantics.

**Q** is the pre-set type: CoPSet (for ZFA), PSet (for ZFC).
Elements of Q are *representatives* — pre-set trees before identification
by the equivalence relation s.

**[s : Setoid Q]** is the equivalence relation (inferred from instances):
  CoPSet → CoPSet.instSetoid (cobisimulation, extensional bisimulation)
  PSet   → PSet.setoid       (PSet.Equiv, mutual inductive bisimulation)

**Quotient s** is the operational type: OSetZFA, OSet (ZFSet), etc.
Objects in the quotient are identified by their equivalence class.
Identity = position in the membership graph. Identity mode: AsReference.

**Fields**:

  `membership : Quotient s → Quotient s → Prop`
    The membership predicate on the quotient type.
    For OSetZFA: OSetZFA.Mem (lifted from CoPSet.mem via liftOn₂).

  `ext : ∀ x y : Quotient s, (∀ z, membership z x ↔ membership z y) → x = y`
    Extensionality: two objects with the same members are equal.
    For OSetZFA: OSetZFA.ext (proved via bisimulation argument).

**Why these fields are uniform** (contrast with PredicateOperationality):
Membership and extensionality characterise all reference semantics cases:
  OSet:    ZFSet.mem + ZFSet.ext
  OSetZFA: OSetZFA.Mem + OSetZFA.ext
Both satisfy the same schema. Additional operations (union, pair, power set,
AFA) are instance-specific, not universal to the apparatus class.
PredicateOperationality has no fields because its operations (add, inner
product) are type-specific. This asymmetry is intentional.

## Axiom profile: [] (class definition, no proof obligations) -/
class ReferenceOperationality (Q : Type*) [s : Setoid Q] where
  membership : Quotient s → Quotient s → Prop
  ext : ∀ x y : Quotient s,
        (∀ z : Quotient s, membership z x ↔ membership z y) → x = y

-- Q1 test instance: verify trivial case compiles.
-- Proof via Subsingleton: all elements of Quotient trivialUnitSetoid
-- are equal (trivial setoid makes all Unit elements equivalent).
-- `fun _ _ _` avoids any unused-variable binding.
private instance trivialQuotientSubsingleton :
    Subsingleton (Quotient trivialUnitSetoid) :=
  ⟨fun x y => Quotient.inductionOn₂ x y (fun _ _ => Quotient.sound trivial)⟩

private instance : ReferenceOperationality Unit where
  membership := fun _ _ => True
  ext := fun _ _ _ => Subsingleton.elim _ _

-- Q1 RESULT: CONFIRMED. Class compiles with [s : Setoid Q].
-- Quotient s in field types refers to the inferred setoid correctly.
-- No syntax workaround needed.

-- ============================================================
-- §3. Identity nature
-- ============================================================

/-- The identity nature of every reference semantics apparatus is AsReference.

Objects in Quotient s are identified by their equivalence class.
Identity = position in the membership graph. This is AsReference by definition.

## Axiom profile: [] -/
def ReferenceOperationality.identityNature
    {Q : Type*} [Setoid Q] [ReferenceOperationality Q] :
    IdentityNature :=
  .AsReference

-- ============================================================
-- §4. Main instance: OSetZFA
-- ============================================================

-- Technical notes on Q2 (implicit/explicit matching for OSetZFA.ext):
--
-- OSetZFA.ext signature:
--   theorem OSetZFA.ext {x y : OSetZFA} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y
-- Class field expects:
--   ∀ x y : Quotient s, (∀ z, membership z x ↔ membership z y) → x = y
--
-- After membership := OSetZFA.Mem and s := CoPSet.instSetoid:
--   membership z x   = OSetZFA.Mem z x   = (z ∈ x)  [via instMembership]
--   Quotient s       = OSetZFA            [definitional]
--
-- Field becomes:
--   ∀ x y : OSetZFA, (∀ z : OSetZFA, z ∈ x ↔ z ∈ y) → x = y
-- which matches OSetZFA.ext (with explicit x y via wrapper lambda).
--
-- Q2 RESULT: `ext := fun x y h => OSetZFA.ext h` works directly.
-- No `show`/`change` needed. Lean sees through the definitional equalities.
--
-- Axiom note: instRefOpCoPSet carries [propext, Classical.choice, Quot.sound].
-- Classical.choice enters transitively through CoPSet = PFunctor.M CoPSetFunctor
-- (mathlib's M-type construction uses Classical.choice in termination proofs).
-- This is the standard ceiling for all VR-Sets-ZFA work. Acceptable.

/-- OSetZFA is a reference semantics apparatus over CoPSet.

Pre-set type:    CoPSet (coinductive trees, PFunctor.M CoPSetFunctor).
Setoid:          CoPSet.instSetoid (extensional cobisimulation, Cobisimulation.lean).
Quotient:        OSetZFA = Quotient CoPSet.instSetoid (ZFA set universe).
Membership:      OSetZFA.Mem (lifted from CoPSet.mem via liftOn₂, Membership.lean).
Extensionality:  OSetZFA.ext (bisimulation argument, Membership.lean).

This apparatus underlies VR-Sets-ZFA: AFA holds in OSetZFA as a theorem.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  propext:         from OSetZFA.ext → CoPSet.mem_congr → propext.
  Classical.choice: from CoPSet = PFunctor.M (mathlib M-type infrastructure).
  Quot.sound:      from OSetZFA.Mem (liftOn₂) and OSetZFA.ext (Quotient.sound).
  Within standard ceiling [propext, Classical.choice, Quot.sound]. ✓ -/
instance instRefOpCoPSet :
    @ReferenceOperationality
      VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid where
  membership := VR.SetsZFA.OSetZFA.Mem
  ext := fun x y h => @VR.SetsZFA.OSetZFA.ext x y h

-- ============================================================
-- §5. Verification (Reference.lean scope)
-- ============================================================

-- Local verification examples — cross-apparatus comparison lives in Apparatus.lean
-- (which imports both Wrapping.lean and Reference.lean).

/-- The identity nature of the OSetZFA apparatus is AsReference. -/
example : @ReferenceOperationality.identityNature
    VR.SetsZFA.CoPSet VR.SetsZFA.CoPSet.instSetoid instRefOpCoPSet =
    IdentityNature.AsReference := rfl

/-- The two IdentityNature constructors are distinct. -/
example : IdentityNature.AsReference ≠ IdentityNature.AsPoint := by decide

-- ============================================================
-- Axiom audit — Stage 1, Reference.lean
-- ============================================================
-- STAGE: 1. SOURCE: PLAN.md Stage 1.
-- LEAN OBJECTS (1 class, 1 def, 1 instance):
--   ReferenceOperationality (class, 2 fields: membership, ext)
--   ReferenceOperationality.identityNature (def)
--   instRefOpCoPSet : @ReferenceOperationality CoPSet CoPSet.instSetoid
-- AXIOM AUDIT:
--   ReferenceOperationality:      [].
--   identityNature:               [].
--   instRefOpCoPSet:              [propext, Classical.choice, Quot.sound].
--     Classical.choice: transitive via PFunctor.M (CoPSet infrastructure).
--     This is the standard ceiling for VR-Sets-ZFA. Acceptable.
-- CHECKS: no sorry, no admit.

#print axioms ReferenceOperationality
#print axioms ReferenceOperationality.identityNature
#print axioms instRefOpCoPSet

end VR.Apparatus
