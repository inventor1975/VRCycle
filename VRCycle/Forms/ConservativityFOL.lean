-- VR-Forms: Conservativity, FOL storey — Theorem III.1 with quantifiers, terms, functions.
--
-- COURSE: A. Propositional floor: `Conservativity.lean`. Here: quantifiers + terms with
-- variables, constants AND unary function symbols (e.g. succ `t`, the VR generator). Unary
-- functions keep recursion structural — the nested List-recursion shoal (n-ary functions) is
-- still deferred. Self-contained (no Mathlib). π still commutes with substitution trivially:
-- operational atoms are preserved by π, formal atoms are 0-ARY, each `tr b` is CLOSED.
--
-- ## The setup
--   * `Tm F C`   — terms: `var n` (de Bruijn), `const k`, `app1 f s` (unary function `f` of a term).
--   * `Fml A B F C` — FOL formulas: `op a ts` (operational predicate at a list of terms — any
--                  arity), `form b` (formal 0-ary atom), ⊥, →, ∀ (binds de Bruijn 0).
--   * L₀ = `Fml A Empty F C`;  L₁ = `Fml A B F C`.
--   * `embed`, `piTr tr` (form b ↦ its closed operational meaning `tr b`).
--   * `Provable T` — classical Hilbert: K, S, Peirce, MP, ∀-elim (instantiates a TERM),
--     ∀-distribution, generalization.
--
-- ## Theorem III.1 (conservativity), FOL storey
--   If each `tr b` is closed and π of every T₁-axiom is T₀-provable, every operational formula
--   provable in T₁ — under quantifiers, with terms (variables, constants like ∅, function terms
--   like t(x)) — is provable in T₀.

universe u v w x

namespace VR.Forms.ConservativityFOL

-- ============================================================
-- §1. Terms (de Bruijn variables, constants, unary functions); lift and substitution
-- ============================================================

/-- Terms: a de Bruijn variable, a constant (0-ary, e.g. ∅), or an n-ary function applied to a
list of terms (e.g. `succ` t(x), `vadd` x+y).  The argument list nests `Tm`, so `lift`/`subst`
are defined by mutual recursion with their list versions (Lean sees the structural decrease). -/
inductive Tm (F : Type x) (C : Type w) where
  | var   : Nat → Tm F C
  | const : C → Tm F C
  | app   : F → List (Tm F C) → Tm F C

-- Lift free variables `≥ c` by one in a term (mutual with the list version).
mutual
def Tm.lift {F : Type x} {C : Type w} (c : Nat) : Tm F C → Tm F C
  | .var n    => .var (if n < c then n else n + 1)
  | .const k  => .const k
  | .app f ts => .app f (Tm.liftList c ts)
def Tm.liftList {F : Type x} {C : Type w} (c : Nat) : List (Tm F C) → List (Tm F C)
  | []        => []
  | s :: rest => Tm.lift c s :: Tm.liftList c rest
end

-- Substitute de Bruijn variable `j` by term `t`, decrementing free variables `> j`
-- (mutual with the list version).
mutual
def Tm.subst {F : Type x} {C : Type w} (j : Nat) (t : Tm F C) : Tm F C → Tm F C
  | .var n    => if n = j then t else .var (if j < n then n - 1 else n)
  | .const k  => .const k
  | .app f ts => .app f (Tm.substList j t ts)
def Tm.substList {F : Type x} {C : Type w} (j : Nat) (t : Tm F C) :
    List (Tm F C) → List (Tm F C)
  | []        => []
  | s :: rest => Tm.subst j t s :: Tm.substList j t rest
end

-- ============================================================
-- §2. FOL formulas; lift and term-substitution
-- ============================================================

/-- FOL formulas: operational predicate `op a ts` (symbol `a` applied to a list of terms — any
arity, e.g. binary `∈`), formal 0-ary atom `form b`, ⊥, →, ∀ (binding de Bruijn index 0). -/
inductive Fml (A : Type u) (B : Type v) (F : Type x) (C : Type w) where
  | op   : A → List (Tm F C) → Fml A B F C
  | form : B → Fml A B F C
  | bot  : Fml A B F C
  | imp  : Fml A B F C → Fml A B F C → Fml A B F C
  | all  : Fml A B F C → Fml A B F C

/-- Substitute de Bruijn variable `j` by term `t` (lifting `t` under each binder).
`subst 0 t` is the ∀-elim instantiation. Formal atoms (0-ary) are untouched. -/
def Fml.subst {A : Type u} {B : Type v} {F : Type x} {C : Type w} (j : Nat) (t : Tm F C) :
    Fml A B F C → Fml A B F C
  | .op a ts => .op a (ts.map (Tm.subst j t))
  | .form b  => .form b
  | .bot     => .bot
  | .imp p q => .imp (p.subst j t) (q.subst j t)
  | .all p   => .all (p.subst (j + 1) (t.lift 0))

-- ============================================================
-- §3. embed (L₀ → L₁) and the translation π (L₁ → L₀)
-- ============================================================

/-- Embed an operational (L₀ = `Fml A Empty F C`) formula into L₁. The `form` case is vacuous. -/
def embed {A : Type u} {B : Type v} {F : Type x} {C : Type w} : Fml A Empty F C → Fml A B F C
  | .op a ts => .op a ts
  | .form e  => e.elim
  | .bot     => .bot
  | .imp p q => .imp (embed p) (embed q)
  | .all p   => .all (embed p)

/-- π: a formal atom `b` becomes its closed operational meaning `tr b`; operational atoms (with
their terms), connectives and ∀ are preserved. -/
def piTr {A : Type u} {B : Type v} {F : Type x} {C : Type w} (tr : B → Fml A Empty F C) :
    Fml A B F C → Fml A Empty F C
  | .op a ts => .op a ts
  | .form b  => tr b
  | .bot     => .bot
  | .imp p q => .imp (piTr tr p) (piTr tr q)
  | .all p   => .all (piTr tr p)

/-- π is a left inverse of `embed`: on an L₀-formula the translation is the identity. -/
theorem piTr_embed {A : Type u} {B : Type v} {F : Type x} {C : Type w}
    (tr : B → Fml A Empty F C) (φ : Fml A Empty F C) :
    piTr tr (embed φ) = φ := by
  induction φ with
  | op a ts => rfl
  | form e => exact e.elim
  | bot => rfl
  | imp p q ihp ihq => simp only [embed, piTr, ihp, ihq]
  | all p ih => simp only [embed, piTr, ih]

/-- **π commutes with (term-)substitution** — given each `tr b` closed (subst-invariant).
Operational atoms: π is the identity, so substitution matches; formal atoms: 0-ary (subst no-op)
and `tr b` closed. No de-Bruijn substitution-composition. -/
theorem piTr_subst {A : Type u} {B : Type v} {F : Type x} {C : Type w} (tr : B → Fml A Empty F C)
    (htr : ∀ b j t, Fml.subst j t (tr b) = tr b) :
    ∀ (φ : Fml A B F C) (j : Nat) (t : Tm F C),
      piTr tr (Fml.subst j t φ) = Fml.subst j t (piTr tr φ) := by
  intro φ
  induction φ with
  | op a ts => intro j t; rfl
  | form b => intro j t; simp only [Fml.subst, piTr, htr b j t]
  | bot => intro j t; rfl
  | imp p q ihp ihq => intro j t; simp only [Fml.subst, piTr, ihp, ihq]
  | all p ih => intro j t; simp only [Fml.subst, piTr, ih]

-- ============================================================
-- §4. Classical Hilbert provability (quantifiers, term instantiation)
-- ============================================================

/-- Classical FOL provability from a theory `T`: propositional base (K, S, Peirce, MP), ∀-elim
(instantiating a term), ∀-distribution, generalization.  (`gen` without the eigenvariable
side-condition — a floor simplification; only π-commutation, not soundness, is needed for the
conservativity transport.) -/
inductive Provable {A : Type u} {B : Type v} {F : Type x} {C : Type w} (T : Fml A B F C → Prop) :
    Fml A B F C → Prop where
  | ax {φ}        : T φ → Provable T φ
  | k {φ ψ}       : Provable T (.imp φ (.imp ψ φ))
  | s {φ ψ χ}     : Provable T (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | peirce {φ ψ}  : Provable T (.imp (.imp (.imp φ ψ) φ) φ)
  | mp {φ ψ}      : Provable T (.imp φ ψ) → Provable T φ → Provable T ψ
  | allElim {φ t} : Provable T (.all φ) → Provable T (Fml.subst 0 t φ)
  | allDistrib {φ ψ} : Provable T (.imp (.all (.imp φ ψ)) (.imp (.all φ) (.all ψ)))
  | gen {φ}       : Provable T φ → Provable T (.all φ)

-- ============================================================
-- §5. π transports T₁-provability to T₀-provability of π-images
-- ============================================================

/-- **The π-translation lemma (FOL).**  If each `tr b` is closed and π of every T₁-axiom is
T₀-provable, then π sends any T₁-proof to a T₀-proof of the π-image.  ∀-elim uses `piTr_subst`;
the rest commute with π directly. -/
theorem piTr_provable {A : Type u} {B : Type v} {F : Type x} {C : Type w}
    (tr : B → Fml A Empty F C)
    (htr : ∀ b j t, Fml.subst j t (tr b) = tr b)
    (T₁ : Fml A B F C → Prop) (T₀ : Fml A Empty F C → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piTr tr α)) :
    ∀ {ψ : Fml A B F C}, Provable T₁ ψ → Provable T₀ (piTr tr ψ) := by
  intro ψ h
  induction h with
  | ax hmem        => exact haxioms _ hmem
  | k              => exact Provable.k
  | s              => exact Provable.s
  | peirce         => exact Provable.peirce
  | mp _ _ ih₁ ih₂ => exact Provable.mp ih₁ ih₂
  | @allElim φ t _ ih =>
      rw [piTr_subst tr htr]
      exact Provable.allElim ih
  | allDistrib     => exact Provable.allDistrib
  | gen _ ih       => exact Provable.gen ih

-- ============================================================
-- §6. Theorem III.1 (conservativity) — FOL storey
-- ============================================================

/-- **Conservativity (Theorem III.1, FOL with terms+functions).**  If each formal term's
operational meaning `tr b` is closed, and π of every T₁-axiom is T₀-provable, then every
operational (L₀) formula provable in the two-register theory T₁ — under quantifiers, with terms
(variables, constants like ∅, function terms like t(x)) — is provable in the operational theory
T₀.  The formal register proves no new operational theorems. -/
theorem conservativity {A : Type u} {B : Type v} {F : Type x} {C : Type w}
    (tr : B → Fml A Empty F C)
    (htr : ∀ b j t, Fml.subst j t (tr b) = tr b)
    (T₁ : Fml A B F C → Prop) (T₀ : Fml A Empty F C → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piTr tr α))
    (φ : Fml A Empty F C) (h : Provable T₁ (embed φ)) :
    Provable T₀ φ := by
  have hpi := piTr_provable tr htr T₁ T₀ haxioms h
  rwa [piTr_embed] at hpi

-- ============================================================
-- §7. A concrete VR instance: ∅, membership, successor
-- ============================================================

namespace VRExample

/-- One operational predicate: membership `∈` (binary). -/
inductive OpPred where | mem
/-- One constant: the empty set `∅`. -/
inductive Const where | empty
/-- One unary function: the VR successor `t` (so terms `t(x)`, `t(∅) = 1`, … are available). -/
inductive Func where | succ
/-- One formal term: `⌜∅⌝`. -/
inductive FTerm where | emptyForm

/-- The operational meaning of `⌜∅⌝`: `∀x ¬(x ∈ ∅)` — a CLOSED operational formula. -/
def trEmpty : FTerm → Fml OpPred Empty Func Const
  | .emptyForm => .all (.imp (.op .mem [.var 0, .const .empty]) .bot)

/-- `trEmpty` is closed (substitution-invariant): its only variable is bound by the `∀`.
Choice-free: `simp only` on the definitions, then the bound-variable `if`s are discharged by
`omega` (full `simp` would pull `Classical.choice` on the Nat comparison — Continuum CONT-6). -/
theorem trEmpty_closed : ∀ b j t, Fml.subst j t (trEmpty b) = trEmpty b := by
  intro b j t
  cases b
  simp only [trEmpty, Fml.subst, Tm.subst, List.map_cons, List.map_nil]
  rw [if_neg (by omega : ¬(0 = j + 1)), if_neg (by omega : ¬(j + 1 < 0))]

/-- **Conservativity instantiated at the VR formal term ⌜∅⌝** (with successor available in the
language).  The abstract floor meeting a genuine VR formal term and its operational meaning
`∀x ¬(x ∈ ∅)`: the formal register with `⌜∅⌝` proves no new operational theorem. -/
theorem conservativity_empty
    (T₁ : Fml OpPred FTerm Func Const → Prop) (T₀ : Fml OpPred Empty Func Const → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piTr trEmpty α))
    (φ : Fml OpPred Empty Func Const) (h : Provable T₁ (embed φ)) :
    Provable T₀ φ :=
  conservativity trEmpty trEmpty_closed T₁ T₀ haxioms φ h

-- ---- End-to-end: concrete theories where the conservativity hypothesis is PROVED ----

/-- Operational theory `T₀`: the single emptiness axiom `∀x ¬(x ∈ ∅)`. -/
def T0 : Fml OpPred Empty Func Const → Prop := fun φ => φ = trEmpty .emptyForm

/-- Two-register theory `T₁`: the embedded operational axiom, plus the FORMAL axiom `⌜∅⌝`. -/
def T1 : Fml OpPred FTerm Func Const → Prop :=
  fun φ => φ = embed (trEmpty .emptyForm) ∨ φ = Fml.form .emptyForm

/-- The conservativity hypothesis holds for these concrete theories: π of each T₁-axiom is a
T₀-axiom (the embedded axiom maps back by `piTr_embed`; the formal axiom `⌜∅⌝` maps to `trEmpty`,
which is exactly T₀'s axiom).  Proved, not assumed. -/
theorem T1_haxioms : ∀ α, T1 α → Provable T0 (piTr trEmpty α) := by
  intro α hα
  rcases hα with h | h
  · subst h; rw [piTr_embed]; exact Provable.ax rfl
  · subst h; exact Provable.ax rfl

/-- **End-to-end conservativity for VR's ⌜∅⌝.**  With the concrete `T₀`/`T₁` above, the formal
register (which has the formal axiom `⌜∅⌝`) proves no new operational theorem: anything `T₁`
proves about operational sets, `T₀` already proves.  The conservativity hypothesis is discharged
(`T1_haxioms`), so this is a genuine, non-vacuous instance of Theorem III.1. -/
theorem conservativity_empty_concrete (φ : Fml OpPred Empty Func Const)
    (h : Provable T1 (embed φ)) : Provable T0 φ :=
  conservativity_empty T1 T0 T1_haxioms φ h

end VRExample

-- ============================================================
-- Axiom audit — FOL storey (terms + functions)
-- ============================================================
#print axioms piTr_embed
#print axioms piTr_subst
#print axioms piTr_provable
#print axioms conservativity
#print axioms VRExample.conservativity_empty
#print axioms VRExample.T1_haxioms
#print axioms VRExample.conservativity_empty_concrete

end VR.Forms.ConservativityFOL
