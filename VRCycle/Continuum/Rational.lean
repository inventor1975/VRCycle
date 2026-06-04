-- VRCycle/Continuum/Rational.lean
-- Operational ℚ, BELOW the Classical.choice floor — the DECIDABLE anchor of the operational
-- number spectrum.
--
-- Built by hand from ℤ (never mathlib ℚ, which is entirely Tier-3 — Finding CONT-7), so the whole
-- construction stays `[propext, Quot.sound]`, choice-free.  The point (M3): a TOTAL inverse,
-- choice-free → a genuine `Field`, because zero is DECIDABLE on ℚ.  This is exactly where the
-- Markov wall that blocks the operational `Real` dissolves:
--   • operational `Real` (Continuum/Real.lean): inverse only apartness-witnessed (¬(x≈0) gives no
--     modulus — Markov), NOT a total Field choice-free;
--   • operational `Qop` (here): zero is decidable, so the inverse is total and choice-free — a Field.
-- The Field/CommRing boundary across the operational number spectrum is precisely DECIDABILITY OF ZERO.
--
-- Stages: M1 type+setoid+0/1/ofInt | M2 add/neg/mul → CommRing | M3 inv (decidable zero) → Field
--         | M4 le + DecidableEq/LE + trichotomy | M5 contrast-with-Real exhibit (DependsOn).

import Mathlib

namespace VRCycle.Continuum

/-- A pre-rational: integer numerator over a strictly positive integer denominator.
Value = `num / den`.  Unreduced (no gcd) — equality is handled by the cross-multiplication
quotient below, keeping every proof in pure `ℤ`. -/
structure PreQ where
  num : ℤ
  den : ℤ
  den_pos : 0 < den

namespace PreQ

/-- Cross-multiplication equivalence: `a/b ≈ c/d ⟺ a·d = c·b`. -/
def equiv (a b : PreQ) : Prop := a.num * b.den = b.num * a.den

theorem equiv_refl (a : PreQ) : equiv a a := rfl

theorem equiv_symm {a b : PreQ} (h : equiv a b) : equiv b a := h.symm

theorem equiv_trans {a b c : PreQ} (hab : equiv a b) (hbc : equiv b c) : equiv a c := by
  -- Goal: a.num * c.den = c.num * a.den.  Establish it times b.den, then cancel b.den (> 0).
  have hbd : b.den ≠ 0 := by have := b.den_pos; omega
  have key : (a.num * c.den) * b.den = (c.num * a.den) * b.den := by
    have e1 : (a.num * c.den) * b.den = (a.num * b.den) * c.den := by ring
    have e2 : (c.num * a.den) * b.den = (c.num * b.den) * a.den := by ring
    rw [e1, e2, hab, ← hbc]; ring
  calc a.num * c.den
      = (a.num * c.den) * b.den / b.den := (Int.mul_ediv_cancel _ hbd).symm
    _ = (c.num * a.den) * b.den / b.den := by rw [key]
    _ = c.num * a.den := Int.mul_ediv_cancel _ hbd

/-- The operational-rational setoid (cross-multiplication). -/
instance setoid : Setoid PreQ := ⟨equiv, ⟨equiv_refl, equiv_symm, equiv_trans⟩⟩

/-- Embed an integer as `z / 1`. -/
def ofInt (z : ℤ) : PreQ := ⟨z, 1, by omega⟩

end PreQ

/-- The operational rationals: `PreQ` up to cross-multiplication, below the choice floor. -/
def Qop : Type := Quotient PreQ.setoid

namespace Qop

/-- Integer embedding into `Qop`. -/
def ofInt (z : ℤ) : Qop := Quotient.mk PreQ.setoid (PreQ.ofInt z)

instance : Zero Qop := ⟨ofInt 0⟩
instance : One Qop := ⟨ofInt 1⟩

end Qop

end VRCycle.Continuum

-- M1 axiom check (expected: [propext, Quot.sound], choice-free)
#print axioms VRCycle.Continuum.PreQ.equiv_trans
#print axioms VRCycle.Continuum.Qop.ofInt
