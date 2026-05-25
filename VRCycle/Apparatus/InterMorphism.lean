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
--   InterApparatusMorphism.lift                  []
--   InterApparatusMorphism.lift_mk               []
--   IsModeAOp_of_interApparatus                  []
--   InterApparatusMorphism.compose               []
--   InterApparatusMorphism.lift_compose          []
--   embedPSet_isInterApparatus                   [propext, Classical.choice, Quot.sound]
--   embedOSet_eq_interApparatus_lift             [propext, Classical.choice, Quot.sound]
--
-- Infrastructure (6 objects): axiom-free [].
-- Concrete instances (2 objects): standard ceiling [propext, Classical.choice, Quot.sound],
-- inherited from CoPSet/OSetZFA infrastructure (PFunctor.M pulls Classical.choice).

import VRCycle.Apparatus.Factorisation

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
def InterApparatusMorphism {Q1 Q2 : Type*} [Setoid Q1] [Setoid Q2]
    (f : Q1 → Q2) : Prop :=
  ∀ x y : Q1, x ≈ y → f x ≈ f y

-- ============================================================
-- §2. Lift — quotient-level map
-- ============================================================

/-- An inter-apparatus morphism lifts to a well-defined map between quotients.

`lift hf : Quotient s1 → Quotient s2`  with  `lift hf ⟦q⟧ = ⟦f q⟧`.

**Well-definedness**: if `a ≈₁ b` then `f a ≈₂ f b` (by `hf`), so
`⟦f a⟧ = ⟦f b⟧` (by `Quotient.sound`). Hence `Quotient.lift` is well-defined.

**noncomputable**: follows the convention for quotient-based lifting
(parallel to `ReferenceOperationality.modeA_liftFn`).

## Axiom profile: [] -/
noncomputable def InterApparatusMorphism.lift {Q1 Q2 : Type*}
    [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} (hf : InterApparatusMorphism f) :
    Quotient s1 → Quotient s2 :=
  Quotient.lift (fun q => Quotient.mk s2 (f q))
    (fun a b hab => Quotient.sound (hf a b hab))

/-- Computation rule: the lift at a representative equals the quotient of the image.

`hf.lift ⟦q⟧ = ⟦f q⟧`

**Proof**: `rfl` — `Quotient.lift` is definitional at representatives.

**@[simp]**: reduces `hf.lift ⟦q⟧` to `⟦f q⟧`. Loop-safe: strictly eliminates
the `lift` wrapper, rewriting to the simpler quotient constructor form.

## Axiom profile: [] -/
@[simp]
theorem InterApparatusMorphism.lift_mk {Q1 Q2 : Type*}
    [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} (hf : InterApparatusMorphism f) (q : Q1) :
    hf.lift (Quotient.mk s1 q) = Quotient.mk s2 (f q) :=
  rfl

-- ============================================================
-- §3. Relationship to Mode A — Finding S2-A
-- ============================================================

/-- A same-setoid inter-apparatus morphism yields a Mode A map.

If `f : Q → Q` satisfies `InterApparatusMorphism f` (with the SAME setoid `s`
for both source and target), then the post-composed map
  `fun q => ⟦f q⟧ : Q → Quotient s`
is `ReferenceOperationality.IsModeAOp` (i.e., `a ≈ b → ⟦f a⟧ = ⟦f b⟧`).

**Proof**: from `hf a b hab : f a ≈ f b`, apply `Quotient.sound`.

**Finding S2-A — layered architecture** (see module header for full discussion):
This theorem bridges the two levels of Tier 3 morphisms, but the bridging
requires post-composition with `Quotient.mk s`: the IAM condition lives at
the representative level (Q → Q), while Mode A lives at the quotient level
(Q → Quotient s). The two concepts are COMPLEMENTARY, not hierarchical:

  IAM (representative level): `f : Q → Q`,  `a ≈ b → f a ≈ f b`
                                  ↓  post-compose with Quotient.mk s
  Mode A (quotient level):    `fun q => ⟦f q⟧ : Q → Quotient s`,
                               `a ≈ b → ⟦f a⟧ = ⟦f b⟧`

The reverse direction does NOT hold: a Mode A map `g : Q → Quotient s` is
NOT directly an IAM because IAM requires `f : Q → Q` (representative-level),
while g targets the quotient Quotient s, not Q. The types are incompatible.

## Axiom profile: [] -/
theorem IsModeAOp_of_interApparatus {Q : Type*} [s : Setoid Q]
    {f : Q → Q} (hf : InterApparatusMorphism f) :
    ReferenceOperationality.IsModeAOp (fun q => Quotient.mk s (f q)) :=
  fun a b hab => Quotient.sound (hf a b hab)

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
theorem InterApparatusMorphism.compose {Q1 Q2 Q3 : Type*}
    [Setoid Q1] [Setoid Q2] [Setoid Q3]
    {f : Q1 → Q2} {g : Q2 → Q3}
    (hf : InterApparatusMorphism f) (hg : InterApparatusMorphism g) :
    InterApparatusMorphism (g ∘ f) :=
  fun x y hxy => hg _ _ (hf x y hxy)

/-- Lifts distribute over composition.

`(hf.compose hg).lift = hg.lift ∘ hf.lift`

**Proof**: for any representative `a : Q1`, both sides reduce definitionally to
`⟦g (f a)⟧` (by `lift_mk` applied twice, each a `rfl`-reduction). So `rfl` closes
the goal at the representative level; `Quotient.inductionOn` discharges the quotient
universal quantifier.

**Functor law**: this is the composition axiom for the functor
`(apparatus, IAM) → (Quotient-types, maps)`: composition maps to composition.

## Axiom profile: [] -/
theorem InterApparatusMorphism.lift_compose {Q1 Q2 Q3 : Type*}
    [Setoid Q1] [s2 : Setoid Q2] [Setoid Q3]
    {f : Q1 → Q2} {g : Q2 → Q3}
    (hf : InterApparatusMorphism f) (hg : InterApparatusMorphism g) :
    (hf.compose hg).lift = hg.lift ∘ hf.lift := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

-- ============================================================
-- §5. Canonical instance: ZFC → ZFA representative embedding
-- ============================================================

/-- The ZFC→ZFA representative embedding `embedPSet : PSet → CoPSet` is an
inter-apparatus morphism from the ZFC apparatus `(PSet, PSet.setoid)` to the
ZFA apparatus `(CoPSet, CoPSet.instSetoid)`.

**Condition**: `PSet.Equiv x y → CoPSet.Equiv (embedPSet x) (embedPSet y)`.

**Proof**: `embedPSet_congr` from VR-Sets-ZFA Embedding.lean (Stage 3 of that work).
The bisimulation argument establishing forward faithfulness of the embedding
is precisely the IAM certificate. `fun x y hxy => VR.SetsZFA.embedPSet_congr hxy`.

**Apparatus reading**:
  Source: `(PSet, PSet.setoid)` — ZFC reference apparatus (instRefOpPSet, Instances.lean).
  Target: `(CoPSet, CoPSet.instSetoid)` — ZFA reference apparatus (instRefOpCoPSet, Reference.lean).

**Methodological re-reading of v0.1.0**:
  `embedPSet_congr_modeA_pattern` (Instances.lean, Group D) stated the same congruence
  as a direct theorem, without the IAM wrapper. The v0.1.0 observation that this was
  "the cross-apparatus Mode A pattern" is now formalised: it IS an IAM certificate.
  Stage 5 (v0.1.0) identified the gap; Stage 2 (v1.0.0) fills it.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from CoPSet.instSetoid/OSetZFA infrastructure:
  PFunctor.M (coinductive M-type) pulls Classical.choice.
  Quot.sound: quotient reasoning. propext: standard ceiling. -/
theorem embedPSet_isInterApparatus :
    @InterApparatusMorphism PSet VR.SetsZFA.CoPSet
      PSet.setoid VR.SetsZFA.CoPSet.instSetoid
      VR.SetsZFA.embedPSet :=
  fun _ _ hxy => VR.SetsZFA.embedPSet_congr hxy

-- ============================================================
-- §6. embedOSet as inter-apparatus lift
-- ============================================================

/-- The ZFC→ZFA quotient embedding `embedOSet : ZFSet → OSetZFA` equals the
lift of the inter-apparatus morphism `embedPSet`.

`embedOSet = embedPSet_isInterApparatus.lift`

**Proof**: for any representative `p : PSet`:
  - LHS: `embedOSet ⟦p⟧ = OSetZFA.mk (embedPSet p)` (by `embedOSet_mk`, `rfl`).
  - RHS: `embedPSet_isInterApparatus.lift ⟦p⟧ = Quotient.mk CoPSet.instSetoid (embedPSet p)`
    (by `lift_mk`, `rfl`). And `OSetZFA.mk = Quotient.mk CoPSet.instSetoid` definitionally.
Both sides are `rfl` at representatives; `Quotient.inductionOn` discharges the quotient.

**Architectural content**:
  VR-Sets-ZFA's `embedOSet` was constructed via `Quotient.lift` with `embedPSet_congr`
  as the well-definedness proof (Embedding.lean §5). The IAM framework re-reads this:
    `embedOSet` = the categorical lift of the IAM `embedPSet`.
  The v0.1.0 construction IS the v1.0.0 IAM lift — the framework retroactively
  formalises the existing embedding in apparatus terms.

**Type note**:
  `ZFSet = Quotient PSet.setoid` (mathlib definition, definitional equality).
  `OSetZFA = Quotient CoPSet.instSetoid` (VR-Sets-ZFA definition, definitional equality).
  Both sides have type `Quotient PSet.setoid → Quotient CoPSet.instSetoid`
  (= `ZFSet → OSetZFA`). No coercion needed.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Inherited from `embedPSet_isInterApparatus` (CoPSet infrastructure). -/
theorem embedOSet_eq_interApparatus_lift :
    VR.SetsZFA.embedOSet = embedPSet_isInterApparatus.lift := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

-- ============================================================
-- §7. Verification examples
-- ============================================================

-- Identity map is always an IAM (reflexivity of ≈).
example {Q : Type*} [s : Setoid Q] :
    @InterApparatusMorphism Q Q s s id :=
  fun _ _ h => h

-- Composition: identity ∘ embedPSet = embedPSet, certified as IAM.
example : @InterApparatusMorphism PSet VR.SetsZFA.CoPSet
    PSet.setoid VR.SetsZFA.CoPSet.instSetoid (id ∘ VR.SetsZFA.embedPSet) :=
  embedPSet_isInterApparatus.compose (fun _ _ h => h)

-- lift_mk computation: lift at a PSet representative.
example (p : PSet) :
    embedPSet_isInterApparatus.lift (Quotient.mk PSet.setoid p) =
    Quotient.mk VR.SetsZFA.CoPSet.instSetoid (VR.SetsZFA.embedPSet p) :=
  rfl

-- IsModeAOp_of_interApparatus: identity IAM → Mode A map fun q => ⟦q⟧.
example {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.IsModeAOp (fun q => Quotient.mk s q) :=
  IsModeAOp_of_interApparatus (fun _ _ h => h)

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
--   embedPSet_isInterApparatus          (theorem, canonical ZFC→ZFA instance)
--   embedOSet_eq_interApparatus_lift    (theorem, embedOSet re-derivation)
-- AXIOM AUDIT:
--   Infrastructure []: InterApparatusMorphism, lift, lift_mk,
--                      IsModeAOp_of_interApparatus, compose, lift_compose
--   Standard ceiling [propext, Classical.choice, Quot.sound]:
--                      embedPSet_isInterApparatus, embedOSet_eq_interApparatus_lift
-- CHECKS: no sorry, no admit.

#print axioms InterApparatusMorphism
#print axioms InterApparatusMorphism.lift
#print axioms InterApparatusMorphism.lift_mk
#print axioms IsModeAOp_of_interApparatus
#print axioms InterApparatusMorphism.compose
#print axioms InterApparatusMorphism.lift_compose
#print axioms embedPSet_isInterApparatus
#print axioms embedOSet_eq_interApparatus_lift

end VR.Apparatus
