-- VR/SetsNaive/Syntax.lean
-- VR-Sets, naive edition — Stage N1: the language of NAIVE comprehension.
--
-- Terms are variables and set abstracts `{x : φ}` with NO restriction on `φ`; formulas are
-- built from `⊤`, membership, negation, conjunction and the universal quantifier.  Binders
-- are de Bruijn (index 0 = the innermost bound variable).  The universe of discourse is the
-- type of CLOSED terms: an inductive type, every element a finite record built by rules —
-- potential infinity, as VR reads ℕ.  Nothing completed is assumed anywhere.  (Quantifiers
-- range over the CLOSED terms only — `Cl`; an open term is not an object of the universe.)
--
-- Why naive: ZTL's thesis is that the classical laws hold in every CLEAN cell and fail only at
-- a dirty parameter; then unrestricted comprehension is a LAW wherever membership is clean, and
-- a paradox finds itself as a dirty cell instead of exploding the theory.  This file is only
-- the syntax; the semantics (the least fixed point) is `Ground.lean`, the passport that tells
-- a paradox from an underdetermined cell is `Passport.lean`.
--
-- Self-contained: no imports.  Target: the empty axiom list (guarded by `VR/Guard.lean`).

namespace VRCycle.SetsNaive

-- No auto-generated `injEq` lemmas (they carry `propext`; the guard rejects them). Proofs use
-- `cases` on constructor equalities (noConfusion), which is axiom-free.
set_option genInjectivity false

mutual
/-- Terms: a (de Bruijn) variable, or the set abstract `{x : φ}` binding index 0. -/
inductive Tm where
  | var : Nat → Tm
  | abs : Fm → Tm
/-- Formulas.  `all φ` binds index 0 and ranges over closed terms. -/
inductive Fm where
  | top : Fm
  | mem : Tm → Tm → Fm
  | neg : Fm → Fm
  | and : Fm → Fm → Fm
  | all : Fm → Fm
end

mutual
/-- Substitute the closed term `c` for index `k`. -/
def Tm.subst (k : Nat) (c : Tm) : Tm → Tm
  | .var n => if n = k then c else .var n
  | .abs φ => .abs (Fm.subst (k + 1) c φ)
/-- Substitute the closed term `c` for index `k` (under a binder, `k + 1`). -/
def Fm.subst (k : Nat) (c : Tm) : Fm → Fm
  | .top => .top
  | .mem a b => .mem (Tm.subst k c a) (Tm.subst k c b)
  | .neg φ => .neg (Fm.subst k c φ)
  | .and φ ψ => .and (Fm.subst k c φ) (Fm.subst k c ψ)
  | .all φ => .all (Fm.subst (k + 1) c φ)
end

mutual
/-- `t` has no free index `≥ d`. -/
def Tm.closedAt (d : Nat) : Tm → Bool
  | .var n => Nat.blt n d
  | .abs φ => Fm.closedAt (d + 1) φ
/-- `φ` has no free index `≥ d`. -/
def Fm.closedAt (d : Nat) : Fm → Bool
  | .top => true
  | .mem a b => Tm.closedAt d a && Tm.closedAt d b
  | .neg φ => Fm.closedAt d φ
  | .and φ ψ => Fm.closedAt d φ && Fm.closedAt d ψ
  | .all φ => Fm.closedAt (d + 1) φ
end

/-- A closed term: an object of the universe. -/
def Cl (t : Tm) : Prop := Tm.closedAt 0 t = true

/-- Boolean `<` against `≤` (hand-rolled: `Nat.succ_ne_zero` and friends carry `propext`). -/
theorem blt_ble_absurd : ∀ k d : Nat, Nat.ble (k + 1) d = true → Nat.ble d k = true → False
  | _, 0, h, _ => Bool.noConfusion h
  | 0, _ + 1, _, h => Bool.noConfusion h
  | k + 1, d + 1, h1, h2 => blt_ble_absurd k d h1 h2

theorem band_l : ∀ {x y : Bool}, (x && y) = true → x = true
  | true, _, _ => rfl
  | false, _, h => Bool.noConfusion h

theorem band_r : ∀ {x y : Bool}, (x && y) = true → y = true
  | _, true, _ => rfl
  | true, false, h => Bool.noConfusion h
  | false, false, h => Bool.noConfusion h

theorem ble_zero : ∀ k : Nat, Nat.ble 0 k = true
  | 0 => rfl
  | _ + 1 => rfl

mutual
/-- A term with no free index `≥ d` is untouched by substitution at any `k ≥ d`. -/
theorem Tm.subst_closed (c : Tm) : ∀ (t : Tm) (d k : Nat),
    Tm.closedAt d t = true → Nat.ble d k = true → Tm.subst k c t = t
  | .var n, d, k, h, hk => by
      show (if n = k then c else .var n) = .var n
      have hne : ¬ (n = k) := fun e => by subst e; exact blt_ble_absurd n d h hk
      rw [if_neg hne]
  | .abs φ, d, k, h, hk => by
      show Tm.abs (Fm.subst (k + 1) c φ) = .abs φ
      rw [Fm.subst_closed c φ (d + 1) (k + 1) h hk]
theorem Fm.subst_closed (c : Tm) : ∀ (φ : Fm) (d k : Nat),
    Fm.closedAt d φ = true → Nat.ble d k = true → Fm.subst k c φ = φ
  | .top, _, _, _, _ => rfl
  | .mem a b, d, k, h, hk => by
      show Fm.mem (Tm.subst k c a) (Tm.subst k c b) = .mem a b
      rw [Tm.subst_closed c a d k (band_l h) hk, Tm.subst_closed c b d k (band_r h) hk]
  | .neg φ, d, k, h, hk => by
      show Fm.neg (Fm.subst k c φ) = .neg φ
      rw [Fm.subst_closed c φ d k h hk]
  | .and φ ψ, d, k, h, hk => by
      show Fm.and (Fm.subst k c φ) (Fm.subst k c ψ) = .and φ ψ
      rw [Fm.subst_closed c φ d k (band_l h) hk, Fm.subst_closed c ψ d k (band_r h) hk]
  | .all φ, d, k, h, hk => by
      show Fm.all (Fm.subst (k + 1) c φ) = .all φ
      rw [Fm.subst_closed c φ (d + 1) (k + 1) h hk]
end

/-- A closed term is untouched by every substitution. -/
theorem Cl.subst {t : Tm} (h : Cl t) (k : Nat) (c : Tm) : Tm.subst k c t = t :=
  Tm.subst_closed c t 0 k h (ble_zero k)

/-- Instantiate the outermost bound variable of a body with `c`. -/
abbrev Fm.inst (φ : Fm) (c : Tm) : Fm := φ.subst 0 c

/-- Disjunction, defined (de Morgan). -/
def Fm.or (φ ψ : Fm) : Fm := .neg (.and (.neg φ) (.neg ψ))
/-- The excluded middle for `φ`. -/
def Fm.em (φ : Fm) : Fm := Fm.or φ (.neg φ)

/-- The bound variable of a body. -/
abbrev x0 : Tm := .var 0

/-- The universal set `V = {x : ⊤}`. -/
def V : Tm := .abs .top
/-- Russell's set `R = {x : x ∉ x}`. -/
def R : Tm := .abs (.neg (.mem x0 x0))
/-- The truth-teller set `S = {x : x ∈ x}` (the set-theoretic Quine/truth-teller twin). -/
def S : Tm := .abs (.mem x0 x0)

theorem R_inst : (Fm.neg (.mem x0 x0)).inst R = .neg (.mem R R) := rfl
theorem S_inst : (Fm.mem x0 x0).inst S = .mem S S := rfl

end VRCycle.SetsNaive
