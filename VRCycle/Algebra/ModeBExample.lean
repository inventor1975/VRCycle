-- VRCycle: Algebra/ModeBExample.lean
-- Operational Algebra v0.1.0 — Stage 6: Mode B skeleton example.
-- Operational Algebra v0.2.0 — Stage 6: Substantive Mode B audit (sorry eliminated).
--
-- STAGE: 6 (v0.1.0 skeleton); 6 (v0.2.0 completion). SOURCE: PLAN.md Stage 6.
--
-- ## v0.2.0 Stage 6 — Substantive Mode B Audit
--
-- The intentional sorry from v0.1.0 §2 has been REPLACED in v0.2.0 with a complete
-- algebraic derivation. See §2 for the completed proof and methodological commentary.
-- `image_isOperationalAddSubgroup_isModeBOp` is now fully proved: no sorry, no sorryAx.
--
-- This is the first substantive Mode B audit on algebraic content in the VR programme.
-- Comparison to VR-Audit-1 (Hahn-Banach) is documented in §2 and the stage report.
--
-- ## v0.1.0 — Mode B skeleton (historical)
-- This file began as a SKELETON demonstrating the Mode B apparatus structure in the
-- algebraic setting. The original sorry mirrored VRCycle.Examples.E04_ModeBSkeleton
-- from VR-Apparatus: the apparatus structure was in place; sorry stood for proof
-- obligations requiring domain-specific content beyond the framework machinery.
--
-- ## What this demonstrates
--
-- **Mode B in algebra**: the image-of-subgroup operation under a group
-- homomorphism produces an operationally compatible result when the source
-- subgroup is operational AND the homomorphism satisfies a term-level
-- witness condition (Mode A preservation of the operational predicate).
--
-- **Mode B apparatus schema** for the image-of-subgroup operation:
--   A  = AddSubgroup G          (source: subgroups of G)
--   B  = AddSubgroup H          (target: subgroups of H)
--   PA = IsOperationalAddSubgroup (in G) — source subgroup is compatible
--   PB = IsOperationalAddSubgroup (in H) — image subgroup is compatible
--   W  = "φ is Mode A on operands":
--        ∀ x : G, IsOperational x → IsOperational (φ x)
--   f  = fun S => S.map φ       (classical image-of-subgroup construction)
--
-- **Mode B claim**: PA(S) ∧ W(S) → PB(f(S)).
-- Unpacked: if S is operationally compatible in G AND φ maps operational
-- elements to operational elements, then φ(S) is operationally compatible in H.
--
-- ## Stage 6 findings
--
-- ### Finding A7 — Mode B-term in algebra vs Mode B-typeclass in analysis
--
-- In VR-Apparatus ModeB.lean §5 (Riesz instance), the Mode B witness is
-- at the TYPECLASS level: W = fun _ => True at term level, with the actual
-- separability witness inside [OperationalHilbertSpace E]. This is
-- "Mode B-typeclass."
--
-- Here (§2 skeleton), W is at the TERM level: a ∀-statement that φ
-- maps operational elements to operational elements. This is "Mode B-term."
-- The witness is an explicit hypothesis in the theorem, not a typeclass.
--
-- This confirms the apparatus generalises across both witness forms. The
-- distinction (Mode B-term vs Mode B-typeclass) is a structural finding
-- that extends the VR-Apparatus §3.2 framing to the algebraic setting.
--
-- ### Finding A8 — Mode A apparatus subsumes trivial-predicate Mode B
--
-- For v0.1.0 instances (trivial IsOperational = fun _ => True), the sorry
-- in §2 has a one-line completion: `exact hW x (hS x hxS)`. For these
-- instances, the Mode A apparatus from Stage 3 already handles image
-- subgroup operationality without requiring a separate Mode B witness:
-- W is trivially satisfied and the conclusion follows immediately.
--
-- This is the algebraic analogue of the VR-Forms S1-A finding: when the
-- operational predicate is trivial, all modes collapse to Mode A (or
-- vacuously). Mode B adds value for NON-TRIVIAL predicates where φ's
-- operational-preservation must be verified substantively.
--
-- The concrete ℤ demonstrations in §3 show this collapse explicitly:
-- no sorry needed, proof is `fun _ _ => trivial`.
--
-- ## Apparatus integration (Stages 1–5 connected by Stage 6)
--
-- This skeleton integrates all five algebra stages:
--   Stage 1 (AddGroup.lean)   — OperationalAddGroup typeclass
--   Stages 2,4 (Instances.lean) — ℤ and ZMod n instances
--   Stage 3 (ModeA.lean)      — Mode A closure theorems
--   Stage 5 (Subgroups.lean)  — IsOperationalAddSubgroup predicate
--
-- The Mode B certificate (§2) uses IsOperationalAddSubgroup as BOTH
-- PA and PB, confirming Stage 5's predicate is the natural apparatus notion
-- for subgroup operationality in Mode B chains.
--
-- ## Axiom profile summary (v0.2.0, from #print axioms)
--   §1 neg_isModeBOp             [propext]              — negation elaboration
--      neg_modeb_lift_val         [propext]              — type-level ref
--   §2 image_...isModeBOp        [propext]              — COMPLETED v0.2.0; sorryAx gone
--      operationalImage_lift_val  [propext]              — COMPLETED; sorryAx gone
--   §3 int_ker_...                [propext]              — ℤ, no Quot.sound
--      int_to_zmod_ker_...        [propext, Quot.sound]  — ZMod ceiling

import VRCycle.Apparatus.ModeB
import VRCycle.Algebra.Subgroups

namespace VR.Algebra

open VR.Apparatus

-- ============================================================
-- §1. Mode A as Mode B (fully proved — no sorry)
-- ============================================================

/-- Negation is Mode B for `OperationalAddGroup G` with trivial witness W = True.

**Mode B anatomy**:
  A = G, B = G  (same type — unary operation)
  PA = IsOperational  (operand is operational)
  PB = IsOperational  (result is operational)
  W  = fun _ => True  (no extra witness — Mode A is globally Mode B)
  f  = fun a => -a    (negation)

**Degenerate case**: Mode B with W = True collapses to Mode A. This is
`IsModeAOp.toModeBOp` applied to negation — the apparatus equivalence
`IsModeAOp P f ↔ IsModeBOp P P (fun _ => True) f` from
`VRCycle.Apparatus.ModeB` (IsModeAOp_iff_IsModeBOp).

**Why include it (not redundant with neg_isModeAOp)?**
Stage 3 (`ModeA.lean`) proved `neg_isModeAOp` using `PredicateOperationality.IsModeAOp`
— the Mode A apparatus interface. This theorem uses `IsModeBOp` — a different
apparatus interface (from `VRCycle.Apparatus.ModeB`). Together they demonstrate
the Mode A/Mode B relationship:
  - `neg_isModeAOp` : negation fits Mode A interface (specialized).
  - `neg_isModeBOp` : negation also fits Mode B with trivial W (general).
The equivalence `IsModeAOp P f ↔ IsModeBOp P P (fun _ => True) f` is
`IsModeAOp_iff_IsModeBOp` (VR-Apparatus ModeB.lean). Including both sides
demonstrates this equivalence concretely in the algebra setting.

## Axiom profile: [propext]
Negation elaboration in generic OperationalAddGroup context pulls propext
(Finding A4 from Stage 3 ModeA.lean). -/
theorem neg_isModeBOp {G : Type*} [OperationalAddGroup G] :
    IsModeBOp
      (A := G) (B := G)
      (PA := OperationalAddGroup.IsOperational (G := G))
      (PB := OperationalAddGroup.IsOperational (G := G))
      (W  := fun _ => True)
      (fun a => -a) :=
  fun _ ha _ => OperationalAddGroup.neg_isOperational ha

/-- Mode B lift for negation: maps operational elements to operational elements.

The domain subtype `{a : G // IsOperational a ∧ True}` has the vacuous
conjunct True, reflecting the trivial witness W. The lift packages the
negation closure proof into a Subtype-valued function.

**Computation rule**: `(neg_lift a).val = -a.val` (rfl — definitional).

## Axiom profile: [propext] (from neg_isModeBOp) -/
def neg_modeb_lift {G : Type*} [OperationalAddGroup G] :
    {a : G // OperationalAddGroup.IsOperational a ∧ True} →
    {b : G // OperationalAddGroup.IsOperational b} :=
  neg_isModeBOp.lift

/-- Computation rule for `neg_modeb_lift`: val is the negation.

**Proof**: rfl — definitional unfolding of `IsModeBOp.lift`.

**On axiom profile**: even though the proof is `rfl`, Lean reports `[propext]`
because the theorem STATEMENT references `neg_modeb_lift` (which depends on
`neg_isModeBOp`), and type-level references count in axiom traversal.

## Axiom profile: [propext] -/
@[simp]
theorem neg_modeb_lift_val {G : Type*} [OperationalAddGroup G]
    (a : {x : G // OperationalAddGroup.IsOperational x ∧ True}) :
    (neg_modeb_lift a).val = -a.val :=
  rfl

/-- Concrete: `-7 : ℤ` produced via Mode B lift. Computation rule: val = -(7 : ℤ). -/
example : (neg_modeb_lift ⟨(7 : ℤ), trivial, trivial⟩).val = -(7 : ℤ) := rfl

-- ============================================================
-- §2. Skeleton: operational image subgroup (contains sorry)
-- ============================================================

/-- The image of an operationally compatible subgroup under a Mode A group
homomorphism is operationally compatible.

## v0.2.0 Stage 6 — Substantive Mode B Audit (completed)

This theorem was a sorry-skeleton in v0.1.0. The sorry has been replaced in v0.2.0
with a complete algebraic derivation. This is the first substantive Mode B audit on
algebraic content in the VR programme.

## Setup

Given two `OperationalAddGroup` instances G and H and a group homomorphism
`φ : G →+ H`, the image-of-subgroup operation

  f : AddSubgroup G → AddSubgroup H,    f(S) = S.map φ

is Mode B with:

**PA(S)** = `IsOperationalAddSubgroup S`
  Every element of S satisfies `IsOperational` in G.

**PB(T)** = `IsOperationalAddSubgroup T`
  Every element of T satisfies `IsOperational` in H.

**W(S)** = `∀ x : G, IsOperational x → IsOperational (φ x)`
  The homomorphism φ maps operational elements of G to operational
  elements of H. This is the **Mode A condition for φ** encoded as a
  term-level predicate (Mode B-term — see Finding A7).
  W does not depend on S; it is a global condition on φ.

## Mode B claim: PA(S) ∧ W(S) → PB(S.map φ)

If S is operationally compatible in G (PA) AND φ is Mode A on G→H (W),
then φ(S) is operationally compatible in H (PB).

## Proof derivation (v0.2.0 completion)

Given S, hS : PA(S), hW : W(S), and y ∈ S.map φ:
  1. Rewrite `hy : y ∈ S.map φ` via `AddSubgroup.mem_map`:
     obtain `⟨x, hxS, rfl⟩` with `x ∈ S` and `φ x = y` (by rfl after `obtain`).
     The `rfl` pattern substitutes y := φ x in the goal immediately.
  2. Goal becomes: `IsOperational (G := H) (φ x)`.
  3. From `hS x hxS`: `IsOperational (G := G) x` (x is in operational subgroup S).
  4. Apply `hW x (hS x hxS)`: `IsOperational (G := H) (φ x)`. Done.

The full proof is a single application: `exact hW x (hS x hxS)`.

## Methodological observations (Finding A11)

**Simplicity of algebraic Mode B**: the proof is ONE LINE — `exact hW x (hS x hxS)`.
This contrasts sharply with VR-Audit-1 (Hahn-Banach via Riesz), where the Mode B
proof required substantial functional-analytic infrastructure (Riesz representation,
operator norm estimates, inner product continuity).

**Why so simple here?**
- `AddSubgroup.mem_map` provides a CONSTRUCTIVE existential witness `⟨x, hxS, rfl⟩`.
  No classical choice is required — membership in the image subgroup is by definition
  "∃ x ∈ S, φ x = y", and this exists by construction of the subgroup image.
- The Mode A condition `hW` applies point-wise: once x is extracted, one application
  of `hW x` suffices.
- No auxiliary lemmas, no continuity arguments, no approximations.

**Algebraic vs analytic Mode B**: algebraic structures provide explicit witnesses
through set-theoretic membership. Analytic structures (like Hilbert spaces) require
choice or limit arguments to extract witnesses. This is the key reason algebraic Mode B
is structurally simpler than analytic Mode B.

**Classical.choice absent**: `AddSubgroup.mem_map` pulls only `[propext]`, not
`Classical.choice`. Existential extraction from a defined set is constructive.

## Witness form (Finding A7 — confirmed)

W is at the term level: an explicit ∀-statement on φ. This contrasts with
the Riesz Mode B instance (VR-Apparatus ModeB.lean §5) where W = fun _ => True
and the separability witness is in [OperationalHilbertSpace E]. Mode B-term
(this theorem) vs Mode B-typeclass (Riesz instance) — both are valid
manifestations of the Mode B schema.

## Axiom profile: [propext]
  propext — from OperationalAddGroup infrastructure (same as neg_isModeBOp)
  sorryAx — ELIMINATED in v0.2.0 (was [propext, sorryAx] in v0.1.0)
  Note: AddSubgroup.mem_map does NOT pull Quot.sound in this mathlib version.
  This sub-ceiling observation (from v0.1.0) is confirmed: the image subgroup
  theorem is axiomatically lighter than bot_isOperationalAddSubgroup, which uses
  mem_bot and pulls Quot.sound. API-level axiom variation within the same module. -/
theorem image_isOperationalAddSubgroup_isModeBOp
    {G H : Type*} [OperationalAddGroup G] [OperationalAddGroup H]
    (φ : G →+ H) :
    IsModeBOp
      (A := AddSubgroup G)
      (B := AddSubgroup H)
      (PA := IsOperationalAddSubgroup)
      (PB := IsOperationalAddSubgroup)
      (W  := fun _ =>
        ∀ x : G, OperationalAddGroup.IsOperational x →
                 OperationalAddGroup.IsOperational (φ x))
      (fun S => S.map φ) := by
  intro S hS hW y hy
  rw [AddSubgroup.mem_map] at hy
  obtain ⟨x, hxS, rfl⟩ := hy
  -- After obtain: x : G, hxS : x ∈ S, goal : IsOperational (G := H) (φ x).
  -- hS x hxS : IsOperational (G := G) x   (x is in the operational subgroup S)
  -- hW x (hS x hxS) : IsOperational (G := H) (φ x)  (φ is Mode A on G → H)
  exact hW x (hS x hxS)

/-- Mode B lift for the image-of-subgroup operation (v0.2.0 — fully proved).

The lift of `image_isOperationalAddSubgroup_isModeBOp φ` maps:

  {S : AddSubgroup G // IsOperationalAddSubgroup S ∧ W(S)}
    →  {T : AddSubgroup H // IsOperationalAddSubgroup T}

where W(S) = "φ is Mode A: ∀ x : G, IsOperational x → IsOperational (φ x)".

**v0.2.0 completion**: the sorry in the certificate is eliminated. This lift
is now fully proved — `operationalImage_lift_val` confirms the computation
rule by rfl, and the membership proof is complete.

In v0.1.0, the structure was valid (type and computation rule correct) even
with the sorry. Now the certificate is substantive: the lift is both
well-typed AND provably correct for all `OperationalAddGroup` instances.

## Axiom profile: [propext] (sorryAx eliminated in v0.2.0; no Quot.sound) -/
def operationalImage_lift
    {G H : Type*} [OperationalAddGroup G] [OperationalAddGroup H]
    (φ : G →+ H) :
    {S : AddSubgroup G //
      IsOperationalAddSubgroup S ∧
      (∀ x : G, OperationalAddGroup.IsOperational x →
                OperationalAddGroup.IsOperational (φ x))} →
    {T : AddSubgroup H // IsOperationalAddSubgroup T} :=
  (image_isOperationalAddSubgroup_isModeBOp φ).lift

/-- Computation rule for `operationalImage_lift`: the underlying subgroup is the image.

This holds by rfl — definitional unfolding — and is independent of the sorry
in the certificate. The computation rule is the same whether the certificate
is completed or skeletal.

**On axiom profile**: the theorem STATEMENT references `operationalImage_lift`,
which carries `[propext]` (v0.2.0). Axiom traversal includes type-level references.
The proof term itself is `rfl` (axiom-free), but the statement is not.
Same phenomenon as `neg_modeb_lift_val` for `[propext]`.

## Axiom profile: [propext] (type-level; proof is rfl; sorryAx eliminated in v0.2.0) -/
@[simp]
theorem operationalImage_lift_val
    {G H : Type*} [OperationalAddGroup G] [OperationalAddGroup H]
    (φ : G →+ H)
    (S : {S : AddSubgroup G //
           IsOperationalAddSubgroup S ∧
           (∀ x : G, OperationalAddGroup.IsOperational x →
                     OperationalAddGroup.IsOperational (φ x))}) :
    (operationalImage_lift φ S).val = S.val.map φ :=
  rfl

-- ============================================================
-- §3. Concrete ℤ demonstrations (no sorry)
-- ============================================================
-- Direct ℤ applications demonstrating what the skeleton proves in
-- the fully-operational (trivial-predicate) case — Finding A8.
-- Since IsOperational = fun _ => True for ℤ, everything is trivial.

/-- The kernel of any group homomorphism from ℤ is operationally compatible.

**Proof**: every element of ℤ is operational (trivial predicate), so
any subgroup — including the kernel — is operationally compatible.
This is the one-step proof that the sorry in §2 reduces to for ℤ.

**Finding A8**: for ℤ, Mode B adds no new content over Mode A.
The `IsOperationalAddSubgroup` condition holds for EVERY subgroup
(including every kernel), since all elements of ℤ are trivially operational.

## Axiom profile: [propext]
The proof `fun _ _ => trivial` does not use subgroup API beyond the TYPE
of the statement. `AddMonoidHom.ker` and `IsOperationalAddSubgroup` at the
type level pull `[propext]` but not `Quot.sound` (unlike `mem_bot`, which does).

## Axiom profile: [propext] -/
theorem int_ker_isOperationalAddSubgroup (φ : ℤ →+ ℤ) :
    IsOperationalAddSubgroup φ.ker :=
  fun _ _ => trivial

/-- The image of any subgroup under a homomorphism from ℤ is operationally compatible.

**Direct proof** (bypassing Mode B machinery): trivial predicate.
Demonstrates what `image_isOperationalAddSubgroup_isModeBOp` proves for ℤ
without the sorry — the Mode B structure is present, but the proof
collapses to `trivial` because IsOperational = fun _ => True.

## Axiom profile: [propext] -/
theorem int_image_isOperationalAddSubgroup (φ : ℤ →+ ℤ) (S : AddSubgroup ℤ) :
    IsOperationalAddSubgroup (S.map φ) :=
  fun _ _ => trivial

/-- The kernel of any homomorphism ℤ →+ ZMod n is operationally compatible.

**Cross-instance demonstration**: combines the ℤ (Stage 2) and ZMod n (Stage 4)
instances. Since both have trivial predicates, the kernel is operationally
compatible trivially.

**Note on W**: the Mode A condition W for φ : ℤ →+ ZMod n holds trivially
(True → True), so the Mode B witness is vacuously satisfied.

## Axiom profile: [propext, Quot.sound]
(Quot.sound enters via ZMod n / Fin.instCommRing in the type of φ : ℤ →+ ZMod n.) -/
theorem int_to_zmod_ker_isOperationalAddSubgroup
    (n : ℕ) [NeZero n] (φ : ℤ →+ ZMod n) :
    IsOperationalAddSubgroup φ.ker :=
  fun _ _ => trivial

-- ============================================================
-- Axiom audit — v0.1.0 Stage 6 + v0.2.0 Stage 6, ModeBExample.lean
-- ============================================================
-- STAGE: 6 (v0.1.0 skeleton); 6 (v0.2.0 completion). SOURCE: PLAN.md Stage 6.
-- LEAN OBJECTS (2 theorems, 1 def, 1 simp-theorem in §1;
--               1 theorem, 1 def, 1 simp-theorem in §2;
--               3 theorems in §3):
--   §1 (fully proved, v0.1.0):
--     neg_isModeBOp                    (theorem, Mode B for negation)
--     neg_modeb_lift                   (def, Mode B lift)
--     neg_modeb_lift_val               (theorem, @[simp], rfl)
--   §2 (COMPLETED in v0.2.0 — sorry eliminated):
--     image_isOperationalAddSubgroup_isModeBOp (theorem, SUBSTANTIVE MODE B AUDIT)
--     operationalImage_lift            (def, lift from completed cert)
--     operationalImage_lift_val        (theorem, @[simp], rfl)
--   §3 (concrete ℤ, no sorry, v0.1.0):
--     int_ker_isOperationalAddSubgroup   (theorem)
--     int_image_isOperationalAddSubgroup (theorem)
--     int_to_zmod_ker_isOperationalAddSubgroup (theorem)
-- AXIOM AUDIT (v0.2.0, sorryAx eliminated):
--   neg_isModeBOp              [propext]   — neg elaboration (Finding A4)
--   neg_modeb_lift             [propext]   — inherits from neg_isModeBOp
--   neg_modeb_lift_val         [propext]   — type-level ref (not rfl-free)
--   image_isOperationalAddSubgroup_isModeBOp
--                              [propext]   ← COMPLETED; was [propext, sorryAx] in v0.1.0
--   operationalImage_lift      [propext]   — COMPLETED; was [propext, sorryAx] in v0.1.0
--   operationalImage_lift_val  [propext]   — COMPLETED; was [propext, sorryAx] in v0.1.0
--   int_ker_isOperationalAddSubgroup   [propext]          — no Quot.sound (as before)
--   int_image_isOperationalAddSubgroup [propext]          — no Quot.sound (as before)
--   int_to_zmod_ker_isOperationalAddSubgroup [propext, Quot.sound] — ZMod ceiling
-- NOTE: AddSubgroup.mem_map pulls only [propext], not Quot.sound (unlike mem_bot).
-- FINDING A11: algebraic Mode B audit requires one proof step (exact hW x (hS x hxS)).
--   Contrast: VR-Audit-1 (Hahn-Banach) required substantial analytic infrastructure.
--   Reason: algebraic existentials from mem_map are constructive; no Classical.choice.
-- CHECKS: no sorry, no admit. sorryAx ELIMINATED.

#print axioms neg_isModeBOp
#print axioms neg_modeb_lift
#print axioms neg_modeb_lift_val
#print axioms image_isOperationalAddSubgroup_isModeBOp
#print axioms operationalImage_lift
#print axioms operationalImage_lift_val
#print axioms int_ker_isOperationalAddSubgroup
#print axioms int_image_isOperationalAddSubgroup
#print axioms int_to_zmod_ker_isOperationalAddSubgroup

end VR.Algebra
