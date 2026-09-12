-- VRClassical/Apparatus/QuotientBridge.lean — the QUOTIENT BRIDGE of the reference track.
--
-- Split out of VRCycle/Apparatus/InterMorphism.lean and Composition.lean on 2026-09-12 (integrity
-- programme). The VR core states the reference-track algebra in the witnessed register (maps
-- between pre-types with congruence certificates, laws pointwise up to `≈`, all on `[]`). This file
-- lifts it to Lean's `Quotient` for Mathlib-style consumers: the quotient-level map of an
-- inter-apparatus morphism, its computation rule and functor law, the Mode A reading of a
-- same-setoid IAM, the identity element `Quotient.mk s` and the cross-level functor law.
-- Every object here is on `[Quot.sound]` (Lean's quotient axiom) — kind 3 in VR-LOGIC §1.

import VRCycle.Apparatus.Composition

namespace VR.Apparatus

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
-- Identity elements and functor law at the quotient level (from Composition.lean)
-- ============================================================

/-- Reference Mode A identity: `Quotient.mk s` is a Mode A map for `(Q, s)`.

`IsModeAOp (Quotient.mk s) = ∀ a b : Q, a ≈ b → Quotient.mk s a = Quotient.mk s b`

**Proof**: `fun a b hab => Quotient.sound hab`. Equivalent representatives give
equal quotient elements — Quotient.sound exactly.

**Compositional role**: identity element of the Level 2 composition monoid.
Unlike Levels 1, 3, 4 where `id` is the identity, Level 2's identity element
is `Quotient.mk s` (type: Q → Quotient s, not Q → Q), because Level 2 maps
are Q → Quotient s, not endomorphisms on Q. The lifted identity is `id` on
Quotient s (see `modeA_liftFn_quotientMk_eq_id`).

## Axiom profile: [Quot.sound] -/
theorem ReferenceOperationality.IsModeAOp_quotientMk {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.IsModeAOp (Quotient.mk s) :=
  fun _ _ hab => Quotient.sound hab

/-- The Mode A lift of `Quotient.mk s` is the identity on `Quotient s`.

`modeA_liftFn IsModeAOp_quotientMk = id`

**Proof**: `modeA_liftFn IsModeAOp_quotientMk ⟦a⟧ = Quotient.mk s a = ⟦a⟧`.
`rfl` at representative level; `Quotient.inductionOn` discharges the quotient.

**Identity certificate**: completes the Level 2 identity element story.
`IsModeAOp_quotientMk`: "Quotient.mk s is Mode A."
`modeA_liftFn_quotientMk_eq_id`: "its lift is the identity function on Quotient s."

## Axiom profile: [Quot.sound] -/
theorem ReferenceOperationality.modeA_liftFn_quotientMk_eq_id
    {Q : Type*} [s : Setoid Q] :
    ReferenceOperationality.modeA_liftFn
      (@ReferenceOperationality.IsModeAOp_quotientMk Q s) = id := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

/-- Functor law: Mode A lift ∘ IAM lift = direct Quotient.lift of composition.

`modeA_liftFn hg ∘ hf.lift = Quotient.lift (g ∘ f) (interApparatus_comp_modeA_wd hf hg)`

**Proof**: for representative `a : Q1`:
  - LHS: `(modeA_liftFn hg ∘ hf.lift) ⟦a⟧ = modeA_liftFn hg ⟦f a⟧ = g(f a)`.
  - RHS: `Quotient.lift (g ∘ f) _ ⟦a⟧ = (g ∘ f) a = g(f a)`.
Both reduce to `g(f a)` definitionally. `rfl` closes; `Quotient.inductionOn` discharges.

**Two functor laws in the reference track**:
  Level 3 ∘ Level 3 at quotient: `lift_compose` (Stage 2).
  Level 3 + Level 2 at quotient: `modeA_liftFn_comp_interApparatus` (Stage 3 B2).
Together: quotient-level maps respect both within-level and cross-level composition.

**Parallel to**: `InterApparatusMorphism.lift_compose` from Stage 2 (which is the
IAM ∘ IAM version of this functor law).

## Axiom profile: [Quot.sound]
  Quotient.inductionOn uses Quot.sound. -/
theorem modeA_liftFn_comp_interApparatus
    {Q1 Q2 : Type*} [s1 : Setoid Q1] [s2 : Setoid Q2]
    {f : Q1 → Q2} {g : Q2 → Quotient s2}
    (hf : InterApparatusMorphism f)
    (hg : @ReferenceOperationality.IsModeAOp Q2 s2 g) :
    ReferenceOperationality.modeA_liftFn hg ∘ hf.lift =
    Quotient.lift (g ∘ f) (interApparatus_comp_modeA_wd hf hg) := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

-- ============================================================
-- Verification examples (from Composition.lean §5)
-- ============================================================

-- Level 2 identity: the lift of IsModeAOp_quotientMk is id on Quotient.
example {Q : Type*} [s : Setoid Q] (q : Quotient s) :
    ReferenceOperationality.modeA_liftFn
      (@ReferenceOperationality.IsModeAOp_quotientMk Q s) q = q := by
  simp [ReferenceOperationality.modeA_liftFn_quotientMk_eq_id]

-- Level 3 identity: lift of id_isInterApparatus is id on the quotient.
example {Q : Type*} [s : Setoid Q] :
    (@InterApparatusMorphism.id_isInterApparatus Q s).lift = id := by
  funext q
  exact Quotient.inductionOn q (fun _ => rfl)

#print axioms InterApparatusMorphism.lift
#print axioms InterApparatusMorphism.lift_mk
#print axioms IsModeAOp_of_interApparatus
#print axioms InterApparatusMorphism.lift_compose
#print axioms ReferenceOperationality.IsModeAOp_quotientMk
#print axioms ReferenceOperationality.modeA_liftFn_quotientMk_eq_id
#print axioms modeA_liftFn_comp_interApparatus

end VR.Apparatus
