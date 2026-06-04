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

-- ## Operations (denominators stay positive via `Int.mul_pos`, choice-free)

/-- `a/b + c/d = (a·d + c·b)/(b·d)`. -/
def add (a b : PreQ) : PreQ :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

/-- `-(a/b) = (-a)/b`. -/
def neg (a : PreQ) : PreQ := ⟨-a.num, a.den, a.den_pos⟩

/-- `(a/b)·(c/d) = (a·c)/(b·d)`. -/
def mul (a b : PreQ) : PreQ :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩

-- ## Congruence: each operation respects the equivalence (cross-mult identity via `sub_eq_zero`)

theorem add_respects {a a' b b' : PreQ} (ha : equiv a a') (hb : equiv b b') :
    equiv (add a b) (add a' b') := by
  change (a.num * b.den + b.num * a.den) * (a'.den * b'.den)
     = (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den)
  have ha' : a.num * a'.den = a'.num * a.den := ha
  have hb' : b.num * b'.den = b'.num * b.den := hb
  apply sub_eq_zero.mp
  have key : (a.num * b.den + b.num * a.den) * (a'.den * b'.den)
           - (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den)
      = (a.num * a'.den - a'.num * a.den) * (b.den * b'.den)
      + (b.num * b'.den - b'.num * b.den) * (a.den * a'.den) := by ring
  rw [key, sub_eq_zero.mpr ha', sub_eq_zero.mpr hb']; ring

theorem neg_respects {a a' : PreQ} (ha : equiv a a') : equiv (neg a) (neg a') := by
  change (-a.num) * a'.den = (-a'.num) * a.den
  have ha' : a.num * a'.den = a'.num * a.den := ha
  apply sub_eq_zero.mp
  have key : (-a.num) * a'.den - (-a'.num) * a.den = -(a.num * a'.den - a'.num * a.den) := by ring
  rw [key, sub_eq_zero.mpr ha']; ring

theorem mul_respects {a a' b b' : PreQ} (ha : equiv a a') (hb : equiv b b') :
    equiv (mul a b) (mul a' b') := by
  change (a.num * b.num) * (a'.den * b'.den) = (a'.num * b'.num) * (a.den * b.den)
  have ha' : a.num * a'.den = a'.num * a.den := ha
  have hb' : b.num * b'.den = b'.num * b.den := hb
  apply sub_eq_zero.mp
  have key : (a.num * b.num) * (a'.den * b'.den) - (a'.num * b'.num) * (a.den * b.den)
      = (a.num * a'.den - a'.num * a.den) * (b.num * b'.den)
      + (a'.num * a.den) * (b.num * b'.den - b'.num * b.den) := by ring
  rw [key, sub_eq_zero.mpr ha', sub_eq_zero.mpr hb']; ring

-- ## Ring laws at the representative level (pure `ℤ` ring identities, no hypotheses)

theorem add_comm (a b : PreQ) : equiv (add a b) (add b a) := by
  change (a.num * b.den + b.num * a.den) * (b.den * a.den)
     = (b.num * a.den + a.num * b.den) * (a.den * b.den)
  ring

theorem add_assoc (a b c : PreQ) : equiv (add (add a b) c) (add a (add b c)) := by
  change ((a.num * b.den + b.num * a.den) * c.den + c.num * (a.den * b.den))
         * (a.den * (b.den * c.den))
     = (a.num * (b.den * c.den) + (b.num * c.den + c.num * b.den) * a.den)
         * ((a.den * b.den) * c.den)
  ring

theorem zero_add (a : PreQ) : equiv (add (ofInt 0) a) a := by
  change (0 * a.den + a.num * 1) * a.den = a.num * (1 * a.den)
  ring

theorem add_zero (a : PreQ) : equiv (add a (ofInt 0)) a := by
  change (a.num * 1 + 0 * a.den) * a.den = a.num * (a.den * 1)
  ring

theorem neg_add_cancel (a : PreQ) : equiv (add (neg a) a) (ofInt 0) := by
  change ((-a.num) * a.den + a.num * a.den) * 1 = 0 * (a.den * a.den)
  ring

theorem mul_comm (a b : PreQ) : equiv (mul a b) (mul b a) := by
  change (a.num * b.num) * (b.den * a.den) = (b.num * a.num) * (a.den * b.den)
  ring

theorem mul_assoc (a b c : PreQ) : equiv (mul (mul a b) c) (mul a (mul b c)) := by
  change ((a.num * b.num) * c.num) * (a.den * (b.den * c.den))
     = (a.num * (b.num * c.num)) * ((a.den * b.den) * c.den)
  ring

theorem mul_one (a : PreQ) : equiv (mul a (ofInt 1)) a := by
  change (a.num * 1) * a.den = a.num * (a.den * 1)
  ring

theorem mul_add (a b c : PreQ) : equiv (mul a (add b c)) (add (mul a b) (mul a c)) := by
  change (a.num * (b.num * c.den + c.num * b.den)) * ((a.den * b.den) * (a.den * c.den))
     = ((a.num * b.num) * (a.den * c.den) + (a.num * c.num) * (a.den * b.den))
         * (a.den * (b.den * c.den))
  ring

theorem zero_mul (a : PreQ) : equiv (mul (ofInt 0) a) (ofInt 0) := by
  change (0 * a.num) * 1 = 0 * (1 * a.den)
  ring

end PreQ

/-- The operational rationals: `PreQ` up to cross-multiplication, below the choice floor. -/
def Qop : Type := Quotient PreQ.setoid

namespace Qop

/-- Integer embedding into `Qop`. -/
def ofInt (z : ℤ) : Qop := Quotient.mk PreQ.setoid (PreQ.ofInt z)

instance : Zero Qop := ⟨ofInt 0⟩
instance : One Qop := ⟨ofInt 1⟩

/-- `+` on `Qop`, lifted from `PreQ.add`. -/
def add : Qop → Qop → Qop :=
  Quotient.lift₂ (fun x y => (⟦PreQ.add x y⟧ : Qop))
    (fun _ _ _ _ hx hy => Quotient.sound (PreQ.add_respects hx hy))

/-- `-` on `Qop`, lifted from `PreQ.neg`. -/
def neg : Qop → Qop :=
  Quotient.lift (fun x => (⟦PreQ.neg x⟧ : Qop)) (fun _ _ h => Quotient.sound (PreQ.neg_respects h))

/-- `×` on `Qop`, lifted from `PreQ.mul`. -/
def mul : Qop → Qop → Qop :=
  Quotient.lift₂ (fun x y => (⟦PreQ.mul x y⟧ : Qop))
    (fun _ _ _ _ hx hy => Quotient.sound (PreQ.mul_respects hx hy))

instance : Add Qop := ⟨add⟩
instance : Neg Qop := ⟨neg⟩
instance : Mul Qop := ⟨mul⟩

end Qop

-- The ring laws, lifted from `PreQ` to `Qop` (`Quotient.inductionOn` + `Quotient.sound` of the
-- corresponding `PreQ` lemma).  Each inherits `[propext, Quot.sound]`, choice-free.  Named with the
-- `Qop.` prefix at the enclosing-namespace level to avoid clashing with root `add_comm`, etc.

theorem Qop.add_assoc (a b c : Qop) : a + b + c = a + (b + c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (PreQ.add_assoc x y z))

theorem Qop.zero_add (a : Qop) : 0 + a = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (PreQ.zero_add x))

theorem Qop.add_zero (a : Qop) : a + 0 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (PreQ.add_zero x))

theorem Qop.neg_add_cancel (a : Qop) : -a + a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (PreQ.neg_add_cancel x))

theorem Qop.add_comm (a b : Qop) : a + b = b + a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (PreQ.add_comm x y))

theorem Qop.mul_assoc (a b c : Qop) : a * b * c = a * (b * c) :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (PreQ.mul_assoc x y z))

theorem Qop.mul_one (a : Qop) : a * 1 = a :=
  Quotient.inductionOn a (fun x => Quotient.sound (PreQ.mul_one x))

theorem Qop.mul_comm (a b : Qop) : a * b = b * a :=
  Quotient.inductionOn₂ a b (fun x y => Quotient.sound (PreQ.mul_comm x y))

theorem Qop.one_mul (a : Qop) : 1 * a = a := by rw [Qop.mul_comm]; exact Qop.mul_one a

theorem Qop.left_distrib (a b c : Qop) : a * (b + c) = a * b + a * c :=
  Quotient.inductionOn₃ a b c (fun x y z => Quotient.sound (PreQ.mul_add x y z))

theorem Qop.right_distrib (a b c : Qop) : (a + b) * c = a * c + b * c := by
  rw [Qop.mul_comm, Qop.left_distrib, Qop.mul_comm c a, Qop.mul_comm c b]

theorem Qop.zero_mul (a : Qop) : 0 * a = 0 :=
  Quotient.inductionOn a (fun x => Quotient.sound (PreQ.zero_mul x))

theorem Qop.mul_zero (a : Qop) : a * 0 = 0 := by rw [Qop.mul_comm]; exact Qop.zero_mul a

/-- **The operational rationals form a commutative ring** — `+`, `−`, `×`, `0`, `1` with all ring
laws, choice-free `[propext, Quot.sound]`, entirely below the ℚ `Classical.choice` floor (built from
ℤ, never mathlib ℚ). -/
instance : CommRing Qop where
  add_assoc := Qop.add_assoc
  zero_add := Qop.zero_add
  add_zero := Qop.add_zero
  neg_add_cancel := Qop.neg_add_cancel
  add_comm := Qop.add_comm
  mul_assoc := Qop.mul_assoc
  one_mul := Qop.one_mul
  mul_one := Qop.mul_one
  left_distrib := Qop.left_distrib
  right_distrib := Qop.right_distrib
  zero_mul := Qop.zero_mul
  mul_zero := Qop.mul_zero
  mul_comm := Qop.mul_comm
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

end VRCycle.Continuum

-- Axiom check (expected: [propext, Quot.sound], choice-free — below the floor)
#print axioms VRCycle.Continuum.PreQ.equiv_trans
#print axioms VRCycle.Continuum.Qop.ofInt
#print axioms VRCycle.Continuum.Qop.mul_assoc
#print axioms VRCycle.Continuum.Qop.left_distrib
