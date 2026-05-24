-- VR-Sets-ZFA: OSetZFA
-- Stage 3: OSetZFA — the ZFA set universe, as quotient of CoPSet by cobisimulation.
--
-- Defines OSetZFA := Quotient CoPSet.instSetoid and exposes the standard
-- Quotient API with OSetZFA-specific names.
--
-- Connection to VR-Sets:
--   OSet    := ZFSet := Quotient PSet.setoid     — ZFC sets, well-founded
--   OSetZFA := Quotient CoPSet.instSetoid        — ZFA sets, all sets
--   Embedding OSet → OSetZFA : Stage 6.
--
-- Source: Aczel 1988 §6 (ZFA universe via AFA).

import VRCycle.SetsZFA.Cobisimulation

namespace VR.SetsZFA

universe u v

-- ============================================================
-- §1. OSetZFA — the ZFA set universe
-- ============================================================

/-- OSetZFA: the universe of ZFA sets, as cobisimulation classes of CoPSet.

**Definition**: `OSetZFA := Quotient CoPSet.instSetoid` — the quotient of
CoPSet by extensional bisimulation (cobisimulation). Elements are
equivalence classes of CoPSet pre-set trees under cobisimulation.

**Parallel with OSet**:
    OSet    := ZFSet := Quotient PSet.setoid     — ZFC, PSet.Equiv as ≈
    OSetZFA := Quotient CoPSet.instSetoid        — ZFA, CoPSet.Equiv as ≈

Both are quotient constructions. OSetZFA adds non-well-founded elements:
Quine atoms, cyclic sets, infinite descending chains.

**Equality in OSetZFA** is cobisimulation: `OSetZFA.mk x = OSetZFA.mk y ↔ x ≈ y`
(iff `CoPSet.Equiv x y`, by `OSetZFA.eq_iff`). This makes cobisimulation
into definitional equality — the core of the ZFA construction.

**Universe**: `OSetZFA.{u} : Type (u+1)`, matching `CoPSet.{u} : Type (u+1)`
and `OSet : Type 1` (u=0). -/
def OSetZFA : Type (u + 1) :=
  Quotient (CoPSet.instSetoid.{u})

-- ============================================================
-- §2. OSetZFA.mk and notation
-- ============================================================

/-- `OSetZFA.mk x`: the ZFA set represented by the CoPSet pre-set `x`.

Two pre-sets `x y : CoPSet` represent the same ZFA set iff `x ≈ y`
(iff `CoPSet.Equiv x y`), by `OSetZFA.eq_iff`.

Parallel to `ZFSet.mk : PSet → ZFSet` (OSet constructor). -/
def OSetZFA.mk (x : CoPSet.{u}) : OSetZFA.{u} :=
  Quotient.mk CoPSet.instSetoid x

/-- Equality notation for OSetZFA.

`a ≡_ZFA b` is `a = b : OSetZFA` — equality in the ZFA set universe.
Parallel to VR-Sets notation `a ≡ b` for equality in OSet.

By `OSetZFA.eq_iff`, `OSetZFA.mk x ≡_ZFA OSetZFA.mk y ↔ x ≈ y`.

Used in AFA theorem statement (Stage 5):
    ∃! (f : V → OSetZFA), ∀ v, f v ≡_ZFA OSetZFA.mk (...) -/
notation:50 a " ≡_ZFA " b:51 => @Eq OSetZFA a b

-- ============================================================
-- §3. eq_iff — the fundamental quotient property
-- ============================================================

/-- **Fundamental property of OSetZFA**: representatives are equal iff
cobisimilar.

`OSetZFA.mk x ≡_ZFA OSetZFA.mk y ↔ x ≈ y`

where `x ≈ y` is `CoPSet.Equiv x y` via `CoPSet.instSetoid`.

This iff is the characterisation of equality in OSetZFA as cobisimulation.
It is the OSetZFA-level version of `Quotient.eq`. -/
theorem OSetZFA.eq_iff {x y : CoPSet.{u}} :
    OSetZFA.mk x ≡_ZFA OSetZFA.mk y ↔ x ≈ y :=
  ⟨Quotient.exact, Quotient.sound⟩

-- ============================================================
-- §4. sound — cobisimulation implies equality
-- ============================================================

/-- If `x ≈ y` (cobisimilar), then `OSetZFA.mk x ≡_ZFA OSetZFA.mk y`.

Direct delegation to `Quotient.sound`. -/
theorem OSetZFA.sound {x y : CoPSet.{u}} (h : x ≈ y) :
    OSetZFA.mk x ≡_ZFA OSetZFA.mk y :=
  Quotient.sound h

-- ============================================================
-- §5. exact — equality implies cobisimulation
-- ============================================================

/-- If `OSetZFA.mk x ≡_ZFA OSetZFA.mk y`, then `x ≈ y` (cobisimilar).

Direct delegation to `Quotient.exact`. -/
theorem OSetZFA.exact {x y : CoPSet.{u}}
    (h : OSetZFA.mk x ≡_ZFA OSetZFA.mk y) : x ≈ y :=
  Quotient.exact h

-- ============================================================
-- §6. ind — induction / every element has a representative
-- ============================================================

/-- **Induction principle**: to prove `P q` for all `q : OSetZFA`, it
suffices to prove `P (OSetZFA.mk x)` for all `x : CoPSet`.

Every ZFA set has at least one CoPSet representative. -/
theorem OSetZFA.ind {P : OSetZFA.{u} → Prop}
    (h : ∀ x : CoPSet.{u}, P (OSetZFA.mk x)) :
    ∀ q : OSetZFA.{u}, P q :=
  Quotient.ind h

-- ============================================================
-- §7. mk_surjective — surjectivity
-- ============================================================

/-- `OSetZFA.mk` is surjective: every ZFA set is represented by some CoPSet.

Immediate from `OSetZFA.ind`. -/
theorem OSetZFA.mk_surjective : Function.Surjective (OSetZFA.mk.{u}) :=
  Quotient.ind (fun x => ⟨x, rfl⟩)

-- ============================================================
-- §8. lift — unary function lifting
-- ============================================================

/-- Lift a function `f : CoPSet → α` to `OSetZFA → α`.

**Requires**: `hf` — `f` is well-defined on cobisimulation classes
(`x ≈ y → f x = f y`).

**Computation rule**: `OSetZFA.lift f hf (OSetZFA.mk x) = f x` (by `lift_mk`).

Used in Stage 4 to lift unary set-theoretic functions to OSetZFA. -/
def OSetZFA.lift {α : Sort v} (f : CoPSet.{u} → α)
    (hf : ∀ x y : CoPSet.{u}, x ≈ y → f x = f y) :
    OSetZFA.{u} → α :=
  Quotient.lift f hf

/-- Computation rule for `lift`: applying to `OSetZFA.mk x` recovers `f x`. -/
@[simp]
theorem OSetZFA.lift_mk {α : Sort v} (f : CoPSet.{u} → α)
    (hf : ∀ x y : CoPSet.{u}, x ≈ y → f x = f y)
    (x : CoPSet.{u}) :
    OSetZFA.lift f hf (OSetZFA.mk x) = f x :=
  rfl

-- ============================================================
-- §9. liftOn₂ — binary function lifting
-- ============================================================

/-- Lift a binary function `f : CoPSet → CoPSet → α` to
`OSetZFA → OSetZFA → α`.

**Requires**: `hf` — `f` is well-defined on cobisimulation classes in both
arguments. Note the ordering of variables matches `Quotient.liftOn₂`:
`a₁ a₂ b₁ b₂` where `a₁ ≈ b₁` (equivalents for the first argument)
and `a₂ ≈ b₂` (equivalents for the second argument).

**Stage 4 use**: membership is defined via `liftOn₂`:
    `x ∈ y := liftOn₂ x y (fun a b => ∃ i : b.shape, b.children i ≈ a) (...)`
where the consistency condition `(...)` follows from `CoPSet.isBisim_Equiv`
(Stage 2, §6). -/
def OSetZFA.liftOn₂ {α : Sort v} (q₁ q₂ : OSetZFA.{u})
    (f : CoPSet.{u} → CoPSet.{u} → α)
    (hf : ∀ a₁ a₂ b₁ b₂ : CoPSet.{u},
          a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : α :=
  Quotient.liftOn₂ q₁ q₂ f hf

/-- Computation rule for `liftOn₂`. -/
@[simp]
theorem OSetZFA.liftOn₂_mk {α : Sort v}
    (f : CoPSet.{u} → CoPSet.{u} → α)
    (hf : ∀ a₁ a₂ b₁ b₂ : CoPSet.{u}, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (x y : CoPSet.{u}) :
    OSetZFA.liftOn₂ (OSetZFA.mk x) (OSetZFA.mk y) f hf = f x y :=
  rfl

/-
-- ============================================================
-- §10. Stage 6 embedding placeholder
-- ============================================================

Stage 6 will define the faithful embedding OSet → OSetZFA:

  def embedOSet : OSet → OSetZFA

by structural recursion on rank (ZFSet.rank). Well-foundedness of OSet
(IsWellFounded (· ∈ ·)) guarantees termination.

The embedding preserves:
  - Equality:    embedOSet x = embedOSet y ↔ x = y       (faithfulness)
  - Membership:  x ∈ y ↔ embedOSet x ∈ embedOSet y      (Stage 4 ∈)
  - Operations:  union, pair, power set, ω

This establishes OSet (ZFC) as a faithful sub-universe of OSetZFA (ZFA):
well-founded sets are a proper sub-collection of all sets.
-/

end VR.SetsZFA
