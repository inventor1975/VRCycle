-- Example E03: InterApparatusMorphism — cross-apparatus maps
-- VRCycle tutorial for Lean developers.
--
-- Import this file as: import VRCycle.Examples.E03_InterMorphism
--
-- Demonstrates: constructing and lifting an InterApparatusMorphism.
-- Source: VRCycle.Apparatus.InterMorphism, VRCycle.Apparatus.Numbers.
--
-- WHAT THIS SHOWS:
-- An `InterApparatusMorphism f` is a map between two setoids that
-- respects both equivalence relations:
--   f : Q1 → Q2 such that a ≈₁ b → f a ≈₂ f b.
-- It lifts to a well-defined function Quotient s1 → Quotient s2.
--
-- KEY ARCHITECTURAL POINT ([Quot.sound] tier — Finding S2-B):
-- `InterApparatusMorphism.lift` and `lift_mk` use ONLY `Quot.sound`,
-- not `propext` or `Classical.choice`. This is the intermediate axiom
-- tier discovered in VR-Apparatus: between [] and [propext, Quot.sound].
--
-- Audience: Lean developers already familiar with Lean 4 syntax.
-- See VR-Apparatus preprint (DOI 10.5281/zenodo.20381417) Section V.

import VRCycle.Apparatus.Numbers  -- includes InterMorphism + von Neumann example

namespace VRCycle.Examples.E03

open VR.Apparatus

-- ============================================================
-- §1. The built-in example: von Neumann ordinals
-- ============================================================

-- `nat_vonNeumann_isInterApparatus` (Numbers.lean):
-- PSet.ofNat : ℕ → PSet is an IAM from (ℕ, =) to (PSet, PSet.Equiv).
-- Each natural n maps to the n-th von Neumann ordinal as a pre-set.
-- Profile: [] — axiom-free (PSet.Equiv.refl is structural recursion).
#check nat_vonNeumann_isInterApparatus
-- : @InterApparatusMorphism ℕ PSet natEqSetoid PSet.setoid PSet.ofNat

-- ============================================================
-- §2. A simple custom IAM: parity-respecting function
-- ============================================================

-- Parity equivalence on ℕ: n ≈ m ↔ n % 2 = m % 2.
-- Declared as a local instance so that `Quotient` and `.lift` can find it.
local instance paritySetoid : Setoid ℕ where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

-- "Round to even" map: n ↦ n - n % 2.
-- IAM condition: n % 2 = m % 2 → (n - n%2) % 2 = (m - m%2) % 2.
theorem roundEven_isIAM :
    @InterApparatusMorphism ℕ ℕ paritySetoid paritySetoid
      (fun n => n - n % 2) :=
  fun a b (hab : a % 2 = b % 2) => show (a - a % 2) % 2 = (b - b % 2) % 2 by omega

-- ============================================================
-- §3. Lifting to quotients
-- ============================================================

-- The lift: Quotient paritySetoid → Quotient paritySetoid.
-- `paritySetoid` is in scope as a local instance, so Lean finds it.
-- `noncomputable` because Quotient.lift is noncomputable in Lean 4.
noncomputable def roundEvenLifted : Quotient paritySetoid → Quotient paritySetoid :=
  roundEven_isIAM.lift

-- Computation rule: at representative ⟦n⟧, lift gives ⟦n - n % 2⟧.
-- Holds by `rfl` — lift_mk is @[simp].
example (n : ℕ) : roundEvenLifted ⟦n⟧ = ⟦n - n % 2⟧ := rfl

-- Concrete computation: ⟦3⟧ rounds to ⟦2⟧ (since 3 - 3%2 = 2).
example : roundEvenLifted (⟦3⟧ : Quotient paritySetoid) =
    (⟦2⟧ : Quotient paritySetoid) := rfl

-- ============================================================
-- §4. Composition of IAMs
-- ============================================================

-- `InterApparatusMorphism.compose`: IAMs compose. Profile: [].
theorem roundEven_twice_isIAM :
    @InterApparatusMorphism ℕ ℕ paritySetoid paritySetoid
      ((fun n => n - n % 2) ∘ (fun n => n - n % 2)) :=
  roundEven_isIAM.compose roundEven_isIAM

-- Lifted composition at a representative:
example (n : ℕ) :
    (roundEven_isIAM.compose roundEven_isIAM).lift (⟦n⟧ : Quotient paritySetoid) =
    roundEven_isIAM.lift (roundEven_isIAM.lift ⟦n⟧) := rfl

-- ============================================================
-- §5. Axiom audit
-- ============================================================

-- IAM definition: axiom-free.
#print axioms InterApparatusMorphism
-- Expected: does not depend on any axioms

-- IAM lift/lift_mk: [Quot.sound] only — the new tier (Finding S2-B).
#print axioms InterApparatusMorphism.lift
-- Expected: [Quot.sound]
#print axioms InterApparatusMorphism.lift_mk
-- Expected: [Quot.sound]

-- IAM composition: axiom-free.
#print axioms InterApparatusMorphism.compose
-- Expected: does not depend on any axioms

-- Von Neumann embedding: axiom-free.
#print axioms nat_vonNeumann_isInterApparatus
-- Expected: does not depend on any axioms

-- Custom example: [propext, Quot.sound] — omega on ℕ subtraction within
-- the Setoid wrapper pulls these (Setoid definition involves Prop equality).
#print axioms roundEven_isIAM
-- Actual: [propext, Quot.sound]

end VRCycle.Examples.E03
