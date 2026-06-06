-- VR-Forms: Conservativity (deep embedding) — Theorem III.1, the syntactic core.
--
-- COURSE: A (full syntactic conservativity) built via C (a minimal floor first).
-- This file is the FLOOR: an abstract propositional deep embedding on which conservativity
-- is a real theorem (`conservativity`), machine-checked and choice-free. The FOL extension
-- (quantifiers, predicates, a VR-Forms instance with translate_pi) is the next storey.
--
-- Self-contained: no imports (no Mathlib), so the axiom profile is guaranteed minimal —
-- only Lean's inductive/structural-recursion framework.
--
-- ## The setup (abstract relative interpretation)
--   * `Form At`            — propositional formulas over atoms `At`, connectives (⊥, →).
--   * L₀ = `Form A`        — the operational language (operational atoms `A`).
--   * L₁ = `Form (Sum A B)`— the two-register language: operational atoms `A` plus formal
--                            atoms `B` (the formal terms).
--   * `embed : L₀ → L₁`    — read an L₀-formula in L₁ (operational atoms via `Sum.inl`).
--   * `piTr tr : L₁ → L₀`  — the translation π: a formal atom `b` goes to its operational
--                            meaning `tr b : Form A`; operational atoms and connectives are
--                            preserved. On L₀ (i.e. on `embed φ`), π is the identity.
--   * `Provable T`         — classical Hilbert provability over (⊥, →): K, S, Peirce, MP, axioms.
--
-- ## Theorem III.1 (conservativity), abstract floor
--   If π of every T₁-axiom is T₀-provable (the formal axioms are operationally harmless —
--   their π-images already hold in T₀), then any L₀-formula provable in T₁ is provable in T₀:
--   the formal register proves no new operational theorems.

universe u v

namespace VR.Forms.Conservativity

-- ============================================================
-- §1. Formulas (propositional, over an atom type)
-- ============================================================

/-- Propositional formulas over atoms `At`, with falsum and implication. -/
inductive Form (At : Type u) where
  | atom : At → Form At
  | bot  : Form At
  | imp  : Form At → Form At → Form At

-- ============================================================
-- §2. embed (L₀ → L₁) and the translation π (L₁ → L₀)
-- ============================================================

/-- Embed an operational (L₀) formula into the two-register language L₁ via `Sum.inl`. -/
def embed {A : Type u} {B : Type v} : Form A → Form (Sum A B)
  | .atom a   => .atom (.inl a)
  | .bot      => .bot
  | .imp p q  => .imp (embed p) (embed q)

/-- The translation π: every formal atom `b : B` is sent to its operational meaning
`tr b : Form A`; operational atoms and the connectives are preserved. -/
def piTr {A : Type u} {B : Type v} (tr : B → Form A) : Form (Sum A B) → Form A
  | .atom (.inl a) => .atom a
  | .atom (.inr b) => tr b
  | .bot           => .bot
  | .imp p q       => .imp (piTr tr p) (piTr tr q)

/-- π is a left inverse of `embed`: on an L₀-formula, the translation is the identity. -/
theorem piTr_embed {A : Type u} {B : Type v} (tr : B → Form A) (φ : Form A) :
    piTr tr (embed φ) = φ := by
  induction φ with
  | atom a => rfl
  | bot => rfl
  | imp p q ihp ihq => simp only [embed, piTr, ihp, ihq]

-- ============================================================
-- §3. Classical Hilbert provability over (⊥, →)
-- ============================================================

/-- Classical propositional provability from a theory `T` (a predicate selecting the axioms),
over `⊥` and `→`: schemas K and S, Peirce's law (classicality), modus ponens, theory axioms.
`¬φ := φ → ⊥`, and `∧`/`∨` are definable, so this is a complete classical base. -/
inductive Provable {At : Type u} (T : Form At → Prop) : Form At → Prop where
  | ax {φ}       : T φ → Provable T φ
  | k {φ ψ}      : Provable T (.imp φ (.imp ψ φ))
  | s {φ ψ χ}    : Provable T (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | peirce {φ ψ} : Provable T (.imp (.imp (.imp φ ψ) φ) φ)
  | mp {φ ψ}     : Provable T (.imp φ ψ) → Provable T φ → Provable T ψ

-- ============================================================
-- §4. π transports T₁-provability to T₀-provability of π-images
-- ============================================================

/-- **The π-translation lemma.**  If the translation of every T₁-axiom is T₀-provable, then π
sends any T₁-proof to a T₀-proof of the π-image.  By induction on the derivation: K/S/Peirce are
preserved because π commutes with `→`; MP likewise; axioms hold by hypothesis. -/
theorem piTr_provable {A : Type u} {B : Type v} (tr : B → Form A)
    (T₁ : Form (Sum A B) → Prop) (T₀ : Form A → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piTr tr α)) :
    ∀ {ψ : Form (Sum A B)}, Provable T₁ ψ → Provable T₀ (piTr tr ψ) := by
  intro ψ h
  induction h with
  | ax hmem        => exact haxioms _ hmem
  | k              => exact Provable.k
  | s              => exact Provable.s
  | peirce         => exact Provable.peirce
  | mp _ _ ih₁ ih₂ => exact Provable.mp ih₁ ih₂

-- ============================================================
-- §5. Theorem III.1 (conservativity) — the floor
-- ============================================================

/-- **Conservativity (Theorem III.1, abstract propositional floor).**  If π of every T₁-axiom is
T₀-provable (the formal axioms are operationally harmless), then every operational (L₀) formula
provable in the two-register theory T₁ is already provable in the operational theory T₀.  The
formal register proves no new operational theorems. -/
theorem conservativity {A : Type u} {B : Type v} (tr : B → Form A)
    (T₁ : Form (Sum A B) → Prop) (T₀ : Form A → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piTr tr α))
    (φ : Form A) (h : Provable T₁ (embed φ)) :
    Provable T₀ φ := by
  have hpi := piTr_provable tr T₁ T₀ haxioms h
  rwa [piTr_embed] at hpi

-- ============================================================
-- Axiom audit
-- ============================================================
#print axioms piTr_embed
#print axioms piTr_provable
#print axioms conservativity

end VR.Forms.Conservativity
