-- VR/SetsNaive/Syntax.lean
-- VR-Sets, naive edition — Stage N1: the language of NAIVE comprehension.
--
-- Terms are variables and set abstracts `{x : φ}` with NO restriction on `φ`; formulas are
-- built from `⊤`, membership, negation, conjunction and the universal quantifier.  Binders
-- are de Bruijn (index 0 = the innermost bound variable).  The universe of discourse is the
-- type of CLOSED terms: an inductive type, every element a finite record built by rules —
-- potential infinity, as VR reads ℕ.  Nothing completed is assumed anywhere.
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
