-- VR-Apparatus: InterMorphism (v1.0.0, Stage 2)
-- Cross-apparatus morphisms — InterApparatusMorphism.
--
-- STAGE: v1.0.0 Stage 2 (third of six pieces). SOURCE: PLAN.md Stage 2.
--
-- ## Position statement
-- Generalises Mode A across different reference semantics apparatus instances.
-- Mode A (ModeA.lean) handles endomorphisms: f : Q → Quotient s where source
-- setoid and target quotient belong to the SAME apparatus.
-- InterApparatusMorphism handles heteromorphisms: f : Q1 → Q2 where source
-- and target belong to DIFFERENT apparatus instances.
--
-- Canonical example: embedPSet : PSet → CoPSet. This map satisfies
--   PSet.Equiv x y → CoPSet.Equiv (embedPSet x) (embedPSet y)
-- making it an inter-apparatus morphism from the ZFC apparatus (PSet, PSet.setoid)
-- to the ZFA apparatus (CoPSet, CoPSet.instSetoid). Its lift is precisely
-- embedOSet : ZFSet → OSetZFA.
--
-- ## Architecture
--
-- InterApparatusMorphism is defined at the REPRESENTATIVE level:
--   f : Q1 → Q2  maps between representative types.
--   Condition: a ≈₁ b → f a ≈₂ f b  (preserves equivalences across setoids).
--
-- The lift operates at the QUOTIENT level:
--   lift hf : Quotient s1 → Quotient s2  (well-defined quotient map).
--
-- ## Finding S2-A — Layered, not subset (critical architectural observation)
--
-- Mode A (ReferenceOperationality.IsModeAOp) and InterApparatusMorphism operate
-- at DIFFERENT architectural levels:
--
--   Mode A:   g : Q → Quotient s  (representatives to quotients, SAME apparatus)
--             Condition: a ≈ b → g a = g b  (equality of quotient elements).
--             Lifting: Quotient.lift g hg : Quotient s → Quotient s.
--
--   IAM:      f : Q1 → Q2  (representative to representative, DIFFERENT apparatus)
--             Condition: a ≈₁ b → f a ≈₂ f b  (equivalence preservation).
--             Lifting: Quotient.lift (fun q => ⟦f q⟧) hf : Quotient s1 → Quotient s2.
--
-- Relationship: LAYERED, not a subset hierarchy.
--   (a) Same-setoid IAM (Q1=Q2, s1=s2) → Mode A after post-composing with Quotient.mk
--       (IsModeAOp_of_interApparatus, §3). The IAM condition (f a ≈ f b) becomes
--       Mode A condition (⟦f a⟧ = ⟦f b⟧) via Quotient.sound.
--   (b) Mode A map g : Q → Quotient s is NOT directly an IAM: type mismatch.
--       IAM requires f : Q → Q (representative to representative), but g goes
--       to Quotient s (quotient, not representative). Mode A operates at quotient
--       level; IAM operates at representative level.
--
-- Consequence for Tier 3 architecture:
--   Mode A = endomorphism machinery AT QUOTIENT LEVEL (intra-apparatus).
--   IAM    = congruence condition AT REPRESENTATIVE LEVEL (inter-apparatus).
-- The architecture is two-tier within Tier 3 (morphisms): representative-level
-- IAM feeds quotient-level Mode A via post-composition with Quotient.mk.
-- Calling IAM a "generalisation" of Mode A is imprecise: they are complementary
-- mechanisms at different levels.
--
-- ## Composition (§4)
-- IAMs compose: f : Q1 → Q2, g : Q2 → Q3 both IAMs → g ∘ f IAM.
-- Lifts distribute: (g ∘ f).lift = g.lift ∘ f.lift.
-- Identity id is trivially IAM for any apparatus (reflexivity of ≈).
--
-- ## Methodological re-reading (§6)
-- embedOSet (VR-Sets-ZFA Stage 6) constructed via Quotient.lift with
-- embedPSet_congr as the well-definedness proof IS the IAM lift of embedPSet.
-- The v0.1.0 pattern (embedPSet_congr_modeA_pattern in Instances.lean Group D)
-- is re-read as the IAM certificate. Framework retroactively formalises existing work.
--
-- ## Import chain
-- InterMorphism.lean → Factorisation.lean → ModeB.lean → ModeA.lean
-- → SetsZFA.API → SetsZFA.Examples → SetsZFA.Embedding
-- (embedPSet, embedPSet_congr, embedOSet accessible transitively).
--
-- ## Axiom profile overview
--   InterApparatusMorphism                       []
--   InterApparatusMorphism.compose               []
--   (lift, lift_mk, IsModeAOp_of_interApparatus, lift_compose — in
--    VRClassical/Apparatus/QuotientBridge.lean, [Quot.sound]; embedPSet_isInterApparatus,
--    embedOSet_eq_interApparatus_lift — in VRClassical/Apparatus/InterMorphism.lean, Mathlib's profile)
--
-- Everything in this file: [].

import VR.Apparatus.Factorisation

-- Integrity programme (2026-09-12): the QUOTIENT BRIDGE of this file — `lift`, `lift_mk`,
-- `IsModeAOp_of_interApparatus`, `lift_compose` (all `[Quot.sound]`) — moved to
-- VRClassical/Apparatus/QuotientBridge.lean. What stays here is on `[]`.

namespace VR.Apparatus

-- ============================================================
-- §1. InterApparatusMorphism — definition
-- ============================================================

/-- A map `f : Q1 → Q2` is an **inter-apparatus morphism** from apparatus
`(Q1, s1)` to apparatus `(Q2, s2)` if it preserves equivalences:
equivalent representatives in Q1 map to equivalent representatives in Q2.

`InterApparatusMorphism f  :=  ∀ x y : Q1, x ≈ y → f x ≈ f y`

This is the well-definedness condition enabling `InterApparatusMorphism.lift`
to produce a well-defined quotient-level map `Quotient s1 → Quotient s2`.

**Level**: representative level. `f` maps pre-set types (not quotients).
Contrast with `ReferenceOperationality.IsModeAOp` which maps to quotients:
  - `IsModeAOp g` (g : Q → Quotient s): condition `a ≈ b → g a = g b`.
  - `InterApparatusMorphism f` (f : Q1 → Q2): condition `a ≈₁ b → f a ≈₂ f b`.
See Finding S2-A in the module header for the architectural distinction.

**Canonical example**: `embedPSet : PSet → CoPSet` (see §5).

## Axiom profile: [] -/
def InterApparatusMorphism {Q1 Q2 : Type _} [Setoid Q1] [Setoid Q2]
    (f : Q1 → Q2) : Prop :=
  ∀ x y : Q1, x ≈ y → f x ≈ f y

-- ============================================================
-- §4. Composition
-- ============================================================

/-- Inter-apparatus morphisms compose.

If `f : Q1 → Q2` and `g : Q2 → Q3` are IAMs, then `g ∘ f : Q1 → Q3` is IAM.

**Proof**: `a ≈₁ b → f a ≈₂ f b` (hf) `→ g (f a) ≈₃ g (f b)` (hg). One-liner:
`fun x y hxy => hg _ _ (hf x y hxy)`.

**Categorical structure**: IAMs form a category (composition closed;
`id` is trivially an IAM: `fun _ _ h => h`). Representative-level analogue
of `IsModeAOp.compose` in ModeA.lean (which operates at quotient level).

## Axiom profile: [] -/
theorem InterApparatusMorphism.compose {Q1 Q2 Q3 : Type _}
    [Setoid Q1] [Setoid Q2] [Setoid Q3]
    {f : Q1 → Q2} {g : Q2 → Q3}
    (hf : InterApparatusMorphism f) (hg : InterApparatusMorphism g) :
    InterApparatusMorphism (g ∘ f) :=
  fun x y hxy => hg _ _ (hf x y hxy)

-- ============================================================
-- Axiom audit — Stage 2, InterMorphism.lean
-- ============================================================
-- STAGE: v1.0.0 Stage 2. SOURCE: PLAN.md Stage 2.
-- LEAN OBJECTS (8 public objects):
--   InterApparatusMorphism              (def, Prop, representative-level)
--   InterApparatusMorphism.lift         (noncomputable def, quotient map)
--   InterApparatusMorphism.lift_mk      (theorem, @[simp], rfl)
--   IsModeAOp_of_interApparatus         (theorem, layered architecture bridge)
--   InterApparatusMorphism.compose      (theorem, composition)
--   InterApparatusMorphism.lift_compose (theorem, functor law)
--   (lift, lift_mk, IsModeAOp_of_interApparatus, lift_compose, embedPSet_isInterApparatus,
--    embedOSet_eq_interApparatus_lift — moved out, see the note after the imports)
-- AXIOM AUDIT: every object in this file [] (InterApparatusMorphism, compose).
-- CHECKS: no sorry, no admit.

#print axioms InterApparatusMorphism
#print axioms InterApparatusMorphism.compose

end VR.Apparatus
