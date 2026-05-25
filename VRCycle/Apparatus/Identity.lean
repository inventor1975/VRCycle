-- VR-Apparatus: Identity (DOI TBD — v0.1.0)
-- Stage 1: IdentityNature — usage mode indicator.
--
-- STAGE: 1 (of 7). SOURCE: PLAN.md Stage 1; CLAUDE.md Finding B.
--
-- ## Position statement
-- Defines `IdentityNature`, the categorical distinction between the two
-- apparatus modes identified in Finding B (PLAN.md, 25 May 2026):
--
--   AsPoint     — identity = position in a classical type.
--                 Apparatus: predicate-wrapping (VR-Audit pattern).
--
--   AsReference — identity = position in a membership graph.
--                 Apparatus: reference semantics (VR-Sets / VR-Sets-ZFA pattern).
--
-- ## IdentityNature as usage indicator (Hazard 3 mitigation)
-- IdentityNature is a *usage mode* indicator, not an intrinsic type property.
-- The same Lean type can appear in different modes in different contexts:
--
--   ℕ as von Neumann ordinal in VR (via O : ℕ → VRObj):
--     → effectively AsReference in that usage (indexed by structure).
--   ℕ as counter / array index:
--     → AsPoint in that usage (identity = the numeral value itself).
--
-- Numbers in the VR cycle are a hybrid (PLAN.md Open Question 4): they
-- arise as von Neumann ordinals (Layer 1, reference semantics) but are
-- used as computable points (Layer 2, predicate-wrapping). IdentityNature
-- does not resolve this hybrid nature — it documents it.
--
-- ## No imports
-- Pure inductive type. No mathlib imports. No Classical axioms.
-- Expected axiom profile for all objects in this file: [].

namespace VR.Apparatus

-- ============================================================
-- §1. IdentityNature
-- ============================================================

/-- IdentityNature: indicator of how objects are identified in a given usage context.

**AsPoint** — identity = position in a classical type.
Apparatus: predicate-wrapping. A classical type T provides the substrate;
a predicate P : T → Prop selects the operational sub-collection.
Objects are identified as elements of T (e.g., `x : ℝ`); operational
status is certified by P x (e.g., `IsComputableReal x`).
Witness data is extracted from the proof of P x.

**AsReference** — identity = position in a membership graph.
Apparatus: reference semantics. A pre-set type Q and equivalence relation
R : Q → Q → Prop define the structure; the quotient `Quotient ⟨R, _⟩`
is the operational type. Objects are identified by their equivalence class
(e.g., `a : OSetZFA` identified by its cobisimulation class). Identity
*is* the membership relation — two objects are equal iff they have the
same members (extensionality).

**Usage indicator, not type property**: IdentityNature is attached to a
*usage context*, not to a Lean type. The same type may appear as AsPoint
in one context (ℕ as index) and AsReference in another (ℕ as von Neumann
ordinal). Numbers in the VR cycle exemplify this hybrid nature (PLAN.md §4).

**Categorical distinction**: these two modes are qualitatively different,
not endpoints of a spectrum. Choosing the wrong apparatus for a given
object's identity nature leads to either:
- predicate-wrapping for a reference object: no stable witness (the object's
  "value" in the classical type is representation-dependent), or
- reference semantics for a point object: no meaningful graph structure
  (a computable real has no useful membership relation).

**Two-layer architecture** (consequence, PLAN.md §Finding B):
- Foundational layer: sets via references (AsReference).
- Applied layer: constructed objects via predicates on classical types (AsPoint).
- Hybrid: numbers (AsPoint in VR-Audit, AsReference in VR-Sets).

Source: PLAN.md Finding B (25 May 2026); Stage 0 Observation B. -/
inductive IdentityNature : Type where
  | AsPoint     : IdentityNature   -- predicate-wrapping mode
  | AsReference : IdentityNature   -- reference semantics mode
  deriving DecidableEq, Repr

-- ============================================================
-- §2. Basic properties
-- ============================================================

/-- The two identity natures are distinct.

Proved by `decide`: `DecidableEq IdentityNature` (derived) reduces
this to a finite case check.

## Axiom profile: [] -/
theorem IdentityNature.AsPoint_ne_AsReference :
    IdentityNature.AsPoint ≠ IdentityNature.AsReference := by decide

-- ============================================================
-- Axiom audit — Stage 1, Identity.lean
-- ============================================================
-- STAGE: 1. SOURCE: PLAN.md Stage 1; CLAUDE.md Finding B.
-- LEAN OBJECTS (1 type, 1 theorem):
--   IdentityNature (inductive, 2 constructors: AsPoint, AsReference)
--   IdentityNature.AsPoint_ne_AsReference (theorem)
-- AXIOM AUDIT: expected [] for all objects.
--   No imports from mathlib; no Classical; pure inductive type.
--   DecidableEq is auto-derived (no axioms for simple inductive types).
-- CHECKS: no sorry, no admit.

#print axioms IdentityNature
#print axioms IdentityNature.AsPoint_ne_AsReference

end VR.Apparatus
