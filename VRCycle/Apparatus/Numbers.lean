-- VR-Apparatus: Numbers (DOI TBD — v1.0.0)
-- Stage 5: Numbers as hybrid apparatus subjects.
--
-- STAGE: 5 (of 6). ORDER: 4 → 6 → 2 → 3 → 5 → 1. SOURCE: CLAUDE.md §v1.0.0 piece (5).
--
-- ## Position statement
-- Stage 5 is a documentation-first stage: its primary contribution is a methodological
-- observation about lens applicability, supported by minimal Lean illustration.
-- No new structural framework is introduced. No v0.1.0 files are modified.
--
-- ## Finding S5-A: Lens applicability depends on natural structure
--
-- The headline finding: the two apparatus lenses (predicate-wrapping, reference semantics)
-- are NOT uniformly applicable to all mathematical types. Applicability depends on what
-- natural structure the type carries.
--
-- Apparatus lens inventory for number types:
--
-- | Type | Predicate (AsPoint)               | Reference (AsReference)             |
-- |------|-----------------------------------|-------------------------------------|
-- | ℝ    | IsComputableReal ✓ (v0.1.0)       | Cauchy abs — carrier exists,        |
-- |      |                                   | but ARTIFICIAL (no natural ∈)       |
-- | ℕ    | trivial predicate (fun _ => True) | von Neumann ordinals ✓ (natural ∈) |
--
-- Details:
--
-- **ℝ + PredicateOperationality (IsComputableReal)**: natural and existing.
--   Point identity. Predicate selects computable reals within ℝ.
--
-- **ℝ + ReferenceOperationality via Cauchy**: ARTIFICIAL.
--   The reference carrier is `Cauchy abs = Quotient CauSeq.equiv` (definitionally).
--   Bridge: `Real.equivCauchy : ℝ ≃ Cauchy abs`.
--   BUT: Cauchy sequences are NOT sets. They carry no natural membership relation.
--   ReferenceOperationality requires `membership` and `ext` fields.
--   Forcing membership (e.g., `fun _ _ => False`) would be methodologically hollow.
--   Decision: document the carrier and bridge; do NOT construct artificial instance.
--
-- **ℕ + ReferenceOperationality via von Neumann**: natural.
--   PSet.ofNat : ℕ → PSet embeds each natural n as the n-th von Neumann ordinal
--   n = {0, 1, ..., n-1} — a set with natural membership structure.
--   This is an InterApparatusMorphism from (ℕ, =) to (PSet, PSet.Equiv).
--   The image lives in the ZFSet apparatus (instRefOpPSet, Instances.lean).
--   Reference lens for ℕ is methodologically honest: ordinals ARE sets with membership.
--
-- ## Lean content (4 public objects)
-- Group A — Real numbers: predicate carrier vs. reference carrier.
--   A1. cauchy_abs_isQuotient  — Cauchy abs definitionally equals Quotient CauSeq.equiv.
--   A2. real_cauchy_bridge     — ℝ ≃ Cauchy abs (bridge between the two carriers).
-- Group B — Natural numbers: reference lens via von Neumann ordinals.
--   B1. natEqSetoid             — discrete setoid on ℕ (equality as equivalence).
--   B2. nat_vonNeumann_isInterApparatus — PSet.ofNat is InterApparatusMorphism (ℕ,=) → (PSet,≈).
--
-- ## Axiom profile
-- Group A (ℝ / Cauchy): [propext, Classical.choice, Quot.sound] — standard ceiling.
--   Inherited from ℝ/Cauchy typeclass infrastructure (Field ℚ, IsAbsoluteValue).
--   Even rfl and structure packing inherit axioms through their types.
-- Group B (ℕ / PSet): [] — axiom-free.
--   PSet.Equiv.refl: pure structural recursion on inductive PSet.
--   eq_equivalence: Eq.refl / Eq.symm / Eq.trans — no classical machinery.
--
-- Asymmetry finding: the ℝ apparatus track (predicate lens via IsComputableReal)
-- inherits classical ceiling through the ℝ/Cauchy infrastructure. The ℕ apparatus
-- track (reference lens via von Neumann) is axiom-free. This mirrors the general
-- asymmetry between analysis-based apparatus (ceiling) and set-theoretic apparatus
-- (constructive).
--
-- ## Scope discipline
-- This file does NOT construct ReferenceOperationality for CauSeq ℚ abs.
-- Reason: no natural membership relation on Cauchy sequences.
-- Forcing synthetic membership would violate the apparatus framework's methodological honesty.

import VRCycle.Apparatus.Composition
import VRCycle.Apparatus.Instances

namespace VR.Apparatus

-- ============================================================
-- §1. Group A — Real numbers: predicate carrier vs. reference carrier
-- ============================================================

-- The reference-semantics apparatus for real numbers, if it existed, would use:
--   Q     = CauSeq ℚ abs        (pre-set type: Cauchy sequences of rationals)
--   s     = CauSeq.equiv        (setoid: two sequences equivalent iff their difference → 0)
--   Quotient s = Cauchy abs     (the Cauchy completion)
--
-- This quotient IS definitionally a standard Lean quotient (A1 below).
-- Bridge to ℝ: Real.equivCauchy : ℝ ≃ Cauchy abs (A2 below).
--
-- Why no ReferenceOperationality instance:
-- ReferenceOperationality requires `membership : Q/s → Q/s → Prop` and extensionality.
-- For Cauchy abs, there is no natural membership. Cauchy sequences represent real numbers,
-- not sets. The reference apparatus is set-theoretically motivated; forcing it onto Cauchy
-- sequences would require a synthetic, mathematically unmotivated membership relation.

/-- **A1**: The reference carrier for reals (`Cauchy abs`) is definitionally a quotient.

`CauSeq.Completion.Cauchy (abs : ℚ → ℚ)` is *defined as*
`@Quotient (CauSeq ℚ abs) CauSeq.equiv`, so this equality holds by `rfl`.

This documents the type-theoretic content of "the reals = equivalence classes of Cauchy
sequences of rationals" at the level of types (not just as a mathematical statement).

The predicate carrier is `ℝ` (a *structure* wrapping `cauchy : Cauchy abs`).
The reference carrier is `Cauchy abs` (a *quotient* of `CauSeq ℚ abs`).
These are distinct Lean types, related by `Real.equivCauchy` (see A2). -/
theorem cauchy_abs_isQuotient :
    CauSeq.Completion.Cauchy (abs : ℚ → ℚ) =
    @Quotient (CauSeq ℚ (abs : ℚ → ℚ)) CauSeq.equiv := rfl

/-- **A2**: Bridge between the predicate carrier (ℝ) and the reference carrier (Cauchy abs).

`Real.equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ)` is the canonical
equivalence between the two carriers. It witnesses that the predicate apparatus over ℝ
(using `IsComputableReal`) and the hypothetical reference apparatus over `CauSeq ℚ abs`
(using `Cauchy abs` as quotient) represent the **same mathematical real numbers**.

Note: `ℝ` is a *structure* (`Real where ofCauchy :: cauchy : Cauchy abs`), NOT
definitionally equal to `Cauchy abs`. The bridge `Real.equivCauchy` is non-trivial
(structurally, it wraps/unwraps the `Real.ofCauchy` constructor).

The reference apparatus for `CauSeq ℚ abs` is NOT constructed in this stage
(no natural membership on Cauchy sequences). This definition names the bridge
for documentation and for potential future cross-apparatus morphism statements. -/
def real_cauchy_bridge : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  Real.equivCauchy

-- ============================================================
-- §2. Group B — Natural numbers: reference lens via von Neumann ordinals
-- ============================================================

-- ℕ's reference lens is methodologically honest: each natural number n embeds into ZFSet
-- as the n-th von Neumann ordinal n = {0, 1, ..., n-1}. Von Neumann ordinals ARE sets with
-- natural membership structure. This is the canonical set-theoretic interpretation of ℕ.
--
-- The embedding PSet.ofNat : ℕ → PSet is defined in mathlib (Mathlib.SetTheory.ZFC.PSet):
--   PSet.ofNat 0     = ∅
--   PSet.ofNat (n+1) = insert (PSet.ofNat n) (PSet.ofNat n)
--
-- This maps ℕ into the pre-set universe, and equal naturals map to equivalent pre-sets.
-- The embedding is an InterApparatusMorphism from (ℕ, =) to (PSet, PSet.Equiv) (B2 below).
--
-- Cross-reference (not re-derived here):
-- In VR-Sets-ZFA (SetsZFA/Examples.lean), PSet.ofNat participates in the omega set:
--   PSet.omega = ⟨ULift ℕ, fun n => PSet.ofNat n.down⟩
-- This is the von Neumann ordinal ω = {0, 1, 2, ...} in the ZFSet apparatus.
--
-- ℕ predicate lens: the trivial predicate `fun _ => True` gives a PredicateOperationality
-- instance for ℕ (no operational sub-selection needed — all naturals are "operational").
-- This is not formalized here (trivially follows from the class definition) but noted
-- for completeness of the hybrid picture.

/-- **B1**: The discrete setoid on ℕ: two naturals are equivalent iff equal.

This is the minimal setoid structure for treating ℕ as an apparatus pre-set type.
Under this setoid, `Quotient natEqSetoid ≃ ℕ` (collapse is identity on a discrete type).

Methodological role: `natEqSetoid` is the *source* apparatus for the von Neumann embedding.
The *target* apparatus is `PSet.setoid` (PSet.Equiv, the set-theoretic bisimulation setoid).
The map `PSet.ofNat : ℕ → PSet` is an `InterApparatusMorphism` between them (B2 below). -/
def natEqSetoid : Setoid ℕ where
  r     := (· = ·)
  iseqv := eq_equivalence

/-- **B2**: `PSet.ofNat` is an `InterApparatusMorphism` from `(ℕ, =)` to `(PSet, PSet.Equiv)`.

`PSet.ofNat n` is the `n`-th von Neumann ordinal as a pre-set:
  `PSet.ofNat 0     = ∅`
  `PSet.ofNat (n+1) = insert (PSet.ofNat n) (PSet.ofNat n)` (= {0, ..., n})

Equal naturals `n = m` map to equivalent pre-sets `PSet.Equiv (PSet.ofNat n) (PSet.ofNat m)`.
This follows from `PSet.Equiv.refl`: if `n = m` then `PSet.ofNat n = PSet.ofNat m`, hence
`PSet.Equiv (PSet.ofNat n) (PSet.ofNat m)` by reflexivity.

**Finding S5-A illustration**: the von Neumann embedding makes ℕ's reference lens
methodologically natural. Von Neumann ordinals carry membership as their primary structure
(n ∈ m iff n < m as naturals), exactly what ReferenceOperationality requires.
This contrasts with `Cauchy abs` (no natural membership) and vindicates the
"lens applicability depends on natural structure" finding. -/
theorem nat_vonNeumann_isInterApparatus :
    @InterApparatusMorphism ℕ PSet natEqSetoid PSet.setoid PSet.ofNat :=
  fun _ _ h => h ▸ PSet.Equiv.refl _

-- ============================================================
-- Axiom audit (Stage 5 — 4 public objects)
-- ============================================================

section AxiomAudit

-- A1: rfl, but type mentions CauSeq.Completion.Cauchy — inherits ceiling via Field ℚ.
#print axioms cauchy_abs_isQuotient
-- Verified: [propext, Classical.choice, Quot.sound]

-- A2: Real.equivCauchy (structure packing), but type mentions ℝ and Cauchy — ceiling.
#print axioms real_cauchy_bridge
-- Verified: [propext, Classical.choice, Quot.sound]

-- B1: eq_equivalence (Eq.refl / Eq.symm / Eq.trans), no axioms.
#print axioms natEqSetoid
-- Verified: [] — does not depend on any axioms

-- B2: PSet.Equiv.refl (structural recursion on inductive PSet), no axioms.
#print axioms nat_vonNeumann_isInterApparatus
-- Verified: [] — does not depend on any axioms

end AxiomAudit

end VR.Apparatus
