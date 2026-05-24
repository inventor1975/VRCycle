-- VR-Sets-ZFA: Membership
-- Stage 4: OSetZFA.Mem — membership relation on OSetZFA.
--
-- Defines ∈ on OSetZFA via CoPSet.mem lifted through liftOn₂.
-- Proves well-definedness (mem_congr), the unfolding lemma (mem_mk),
-- and extensionality (ext, ext_iff).
--
-- Architecture:
--   CoPSet.mem   — membership predicate at the CoPSet level
--   OSetZFA.Mem  — lifted to OSetZFA via OSetZFA.liftOn₂
--   mem_mk       — @[simp] unfolding: OSetZFA.mk a ∈ OSetZFA.mk b ↔ ...
--   ext          — extensionality: same members → equal sets
--
-- Dependency chain:
--   CoPSet.isBisim_Equiv (Stage 2, §6) — used in mem_congr
--   OSetZFA.liftOn₂ (Stage 3, §9)      — used in OSetZFA.Mem
--   OSetZFA.sound (Stage 3, §4)         — used in ext
--   CoPSet.bisim_imp_Equiv (Stage 2, §8) — used in ext
--
-- **Implementation note**: `instMembership` is marked `@[reducible]` so that
-- `Membership.mem` (i.e., `∈`) is transparent to Lean's definitional equality
-- checker. Without this, `show`/`Iff.rfl` cannot see through the typeclass
-- dispatch to `OSetZFA.Mem`. This is standard practice for notation-only
-- typeclass instances.
--
-- Source: Aczel 1988 §6; mathlib ZFSet.mem parallel.

import VRCycle.SetsZFA.OSetZFA

namespace VR.SetsZFA

universe u

-- ============================================================
-- §1. CoPSet.mem — membership predicate at the CoPSet level
-- ============================================================

/-- `CoPSet.mem x y`: `x` is a member of `y` at the CoPSet level.

**Definition**: `x ∈ y` iff `x` is cobisimilar to some child of `y`:
  `∃ i : y.shape, CoPSet.Equiv x (y.children i)`

**Coinductive parallel of PSet.mem** (mathlib `Mathlib.SetTheory.ZFC.Basic`):
  `PSet.mem x y  := ∃ i : y.type, PSet.Equiv x (y.func i)`
  `CoPSet.mem x y := ∃ i : y.shape, CoPSet.Equiv x (y.children i)`

Same structural definition; difference is CoPSet.Equiv (greatest fixpoint)
vs PSet.Equiv (mutual induction).

**Lifted to OSetZFA** via `OSetZFA.Mem` (§3). -/
def CoPSet.mem (x y : CoPSet.{u}) : Prop :=
  ∃ i : y.shape, CoPSet.Equiv x (y.children i)

-- ============================================================
-- §2. CoPSet.mem_congr — well-definedness
-- ============================================================

/-- **Well-definedness of membership under cobisimulation**.

If `a₁ ≈ b₁` (the element changes) and `a₂ ≈ b₂` (the set changes),
then `CoPSet.mem a₁ a₂ = CoPSet.mem b₁ b₂`.

The `liftOn₂` congr hypothesis has the form
  `∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂`
where `a₁, b₁` are representatives of the element, `a₂, b₂` of the set.

**Proof**: `propext` reduces to `↔`. Both directions use
`CoPSet.isBisim_Equiv` (Stage 2, §6) to transfer children across
the bisimulation on the set argument, then Equiv transitivity. -/
theorem CoPSet.mem_congr {a₁ a₂ b₁ b₂ : CoPSet.{u}}
    (ha : a₁ ≈ b₁) (hb : a₂ ≈ b₂) :
    CoPSet.mem a₁ a₂ = CoPSet.mem b₁ b₂ := by
  apply propext
  constructor
  · -- Forward: ∃ i : a₂.shape, a₁ ≈ a₂.children i → ∃ j : b₂.shape, b₁ ≈ b₂.children j
    rintro ⟨i, hi⟩
    -- isBisim_Equiv on a₂ ≈ b₂: every child of a₂ has an Equiv-related child in b₂
    obtain ⟨fwd, _⟩ := CoPSet.isBisim_Equiv a₂ b₂ hb
    obtain ⟨j, hj⟩ := fwd i   -- hj : a₂.children i ≈ b₂.children j
    -- chain: b₁ ≈ a₁ ≈ a₂.children i ≈ b₂.children j
    exact ⟨j, CoPSet.Equiv.trans
              (CoPSet.Equiv.trans (CoPSet.Equiv.symm ha) hi) hj⟩
  · -- Backward: ∃ j : b₂.shape, b₁ ≈ b₂.children j → ∃ i : a₂.shape, a₁ ≈ a₂.children i
    rintro ⟨j, hj⟩
    -- isBisim_Equiv on b₂ ≈ a₂: fwd takes k : b₂.shape, gives l : a₂.shape
    obtain ⟨fwd, _⟩ := CoPSet.isBisim_Equiv b₂ a₂ (CoPSet.Equiv.symm hb)
    obtain ⟨i, hi⟩ := fwd j   -- hi : b₂.children j ≈ a₂.children i
    -- chain: a₁ ≈ b₁ ≈ b₂.children j ≈ a₂.children i
    exact ⟨i, CoPSet.Equiv.trans
              (CoPSet.Equiv.trans ha hj) hi⟩

-- ============================================================
-- §3. OSetZFA.Mem — membership lifted to OSetZFA
-- ============================================================

/-- `OSetZFA.Mem x y`: membership on OSetZFA.

Defined by lifting `CoPSet.mem` through `OSetZFA.liftOn₂`. Well-defined
by `CoPSet.mem_congr`.

**Computation rule**: `OSetZFA.mem_mk` (§5) gives
  `OSetZFA.mk a ∈ OSetZFA.mk b ↔ ∃ i : b.shape, a ≈ b.children i`. -/
def OSetZFA.Mem (x y : OSetZFA.{u}) : Prop :=
  OSetZFA.liftOn₂ x y CoPSet.mem
    (fun _ _ _ _ ha hb => CoPSet.mem_congr ha hb)

-- ============================================================
-- §4. Membership instance
-- ============================================================

/-- `Membership` typeclass instance for OSetZFA.

Makes `x ∈ y` notation available for `x y : OSetZFA`.

**Lean 4 `Membership` convention**: In Lean 4, `class Membership (α :
outParam Type u) (γ : Type v)` has `mem : γ → α → Prop` where `γ` is
the CONTAINER type (first argument) and `α` is the ELEMENT type (second
argument, `outParam`). The notation `a ∈ b` elaborates to `Membership.mem b a`
(container `b` first, element `a` second).

Empirically confirmed: `set_option pp.all true in #check fun (a : Nat)
(l : List Nat) => a ∈ l` shows `@Membership.mem Nat (List Nat) inst l a`
(list `l` first, element `a` second).

Therefore `instMembership.mem` must take the container first and the element
second: `mem container element = OSetZFA.Mem element container`. This ensures
`a ∈ b = inst.mem b a = OSetZFA.Mem a b = "a is a member of b"`.

The mathlib `ZFSet` membership instance follows the same pattern. -/
instance OSetZFA.instMembership : Membership OSetZFA.{u} OSetZFA.{u} :=
  ⟨fun container element => OSetZFA.Mem element container⟩

-- ============================================================
-- §5. mem_mk — @[simp] unfolding lemma
-- ============================================================

/-- **Unfolding lemma for membership**:
`OSetZFA.mk a ∈ OSetZFA.mk b ↔ ∃ i : b.shape, a ≈ b.children i`

Unfolds the chain:
  `a ∈ b` → `instMembership.mem b a` → `OSetZFA.Mem a b`
           → `liftOn₂_mk` → `CoPSet.mem a b` → definition.

**Proof strategy**: `show` forces elaboration of `∈` to
`OSetZFA.Mem (mk a) (mk b)` (using the container-first convention of
`instMembership`). Then `simp only [OSetZFA.Mem, OSetZFA.liftOn₂_mk,
CoPSet.mem]` reduces to `(∃ i, CoPSet.Equiv a (b.children i)) ↔
∃ i, a ≈ b.children i`. Finally `rfl` closes the goal: the kernel
evaluates `a ≈ x` to `CoPSet.Equiv a x` via `CoPSet.instSetoid`.

Used in all downstream proofs to access CoPSet structure. -/
@[simp]
theorem OSetZFA.mem_mk (a b : CoPSet.{u}) :
    OSetZFA.mk a ∈ OSetZFA.mk b ↔ ∃ i : b.shape, a ≈ b.children i := by
  change OSetZFA.Mem (OSetZFA.mk a) (OSetZFA.mk b) ↔ _
  simp only [OSetZFA.Mem, OSetZFA.liftOn₂_mk, CoPSet.mem]
  rfl

-- ============================================================
-- §6. OSetZFA.ext — extensionality
-- ============================================================

/-- **Extensionality for OSetZFA**: two ZFA sets with the same members
are equal.

`(∀ z : OSetZFA, z ∈ x ↔ z ∈ y) → x = y`

**Proof**: Construct the bisimulation
  `R c d := ∀ z : OSetZFA, z ∈ OSetZFA.mk c ↔ z ∈ OSetZFA.mk d`
and show `isBisim R`. By `bisim_imp_Equiv`, `R a b → a ≈ b`;
by `eq_iff`, `OSetZFA.mk a = OSetZFA.mk b`.

**Bisimulation argument (forward)**: Given `R c d` and `i : c.shape`:
- `OSetZFA.mk (c.children i) ∈ OSetZFA.mk c` holds (use `i` itself).
- By `R c d`: also `∈ OSetZFA.mk d`; extract `j : d.shape` with
  `c.children i ≈ d.children j` (via `mem_mk`).
- `OSetZFA.sound hj : OSetZFA.mk (c.children i) = OSetZFA.mk (d.children j)`;
  substitution gives `R (c.children i) (d.children j)`. ✓

Backward is symmetric.

**Non-circularity**: `R` uses `OSetZFA.Mem` (defined in §3), but only
inside the proof of `ext`, not in the definition of `Mem` itself. -/
theorem OSetZFA.ext {x y : OSetZFA.{u}}
    (h : ∀ z : OSetZFA.{u}, z ∈ x ↔ z ∈ y) : x = y := by
  obtain ⟨a, rfl⟩ := OSetZFA.mk_surjective x
  obtain ⟨b, rfl⟩ := OSetZFA.mk_surjective y
  rw [OSetZFA.eq_iff]
  apply CoPSet.bisim_imp_Equiv
      (fun c d => ∀ z : OSetZFA.{u}, z ∈ OSetZFA.mk c ↔ z ∈ OSetZFA.mk d)
  · intro c d hcd
    refine ⟨fun i => ?_, fun j => ?_⟩
    · -- Forward: i : c.shape → ∃ j : d.shape, R (c.children i) (d.children j)
      have hmem_c : OSetZFA.mk (c.children i) ∈ OSetZFA.mk c :=
        (OSetZFA.mem_mk _ _).mpr ⟨i, CoPSet.Equiv.refl _⟩
      obtain ⟨j, hj⟩ := (OSetZFA.mem_mk _ _).mp ((hcd _).mp hmem_c)
      exact ⟨j, fun z => OSetZFA.sound hj ▸ Iff.rfl⟩
    · -- Backward: j : d.shape → ∃ i : c.shape, R (c.children i) (d.children j)
      have hmem_d : OSetZFA.mk (d.children j) ∈ OSetZFA.mk d :=
        (OSetZFA.mem_mk _ _).mpr ⟨j, CoPSet.Equiv.refl _⟩
      obtain ⟨i, hi⟩ := (OSetZFA.mem_mk _ _).mp ((hcd _).mpr hmem_d)
      -- hi : d.children j ≈ c.children i
      exact ⟨i, fun z => OSetZFA.sound hi ▸ Iff.rfl⟩
  · exact h

-- ============================================================
-- §7. OSetZFA.ext_iff — biconditional extensionality
-- ============================================================

/-- **Extensionality iff**: `x = y ↔ ∀ z, z ∈ x ↔ z ∈ y`.

`→`: by substitution. `←`: `OSetZFA.ext`. -/
theorem OSetZFA.ext_iff {x y : OSetZFA.{u}} :
    x = y ↔ ∀ z : OSetZFA.{u}, z ∈ x ↔ z ∈ y :=
  ⟨fun h _ => h ▸ Iff.rfl, OSetZFA.ext⟩

end VR.SetsZFA
