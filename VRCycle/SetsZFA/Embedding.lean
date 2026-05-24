-- VR-Sets-ZFA: Embedding
-- Stage 6: embedOSet : OSet → OSetZFA — faithful embedding of well-founded sets.
--
-- Embeds well-founded sets (OSet = ZFSet = Quotient PSet.setoid) into the
-- ZFA universe (OSetZFA = Quotient CoPSet.cobisim):
--
--   PSet --[embedPSet]--> CoPSet
--     |                      |
--     | ZFSet.mk             | OSetZFA.mk
--     ↓                      ↓
--   OSet ---[embedOSet]--> OSetZFA
--
-- All squares commute. The embedding is faithful (injective) and
-- membership-preserving.
--
-- Architecture:
--   embedPSet           — structural recursion PSet → CoPSet
--   embedPSet_dest      — computation rule (rfl)
--   embedPSet_congr     — PSet.Equiv x y → CoPSet.Equiv (embedPSet x) (embedPSet y)
--   embedPSet_faithful  — CoPSet.Equiv (embedPSet x) (embedPSet y) → PSet.Equiv x y
--   embedOSet           — Quotient.lift of embedPSet
--   embedOSet_mk        — computation rule (rfl)
--   embedOSet_injective — Function.Injective embedOSet
--   embedOSet_mem       — embedOSet x ∈ embedOSet a ↔ x ∈ a
--
-- Key methodological asymmetry (preprint material):
--   Forward (embedPSet_congr): pure bisimulation — no induction on PSet.
--   Backward (embedPSet_faithful): structural induction on PSet.
-- The forward direction is a coinductive free lunch: providing a single
-- bisimulation suffices. The backward direction uses PSet's well-foundedness
-- as a proof resource to descend through the coinductive equivalence.
--
-- Dependency chain:
--   CoPSet.mk, CoPSet.dest_mk (Stage 1, §5,6)
--   CoPSet.isBisim_Equiv, CoPSet.bisim_imp_Equiv (Stage 2)
--   OSetZFA.mk, OSetZFA.sound, OSetZFA.exact, OSetZFA.mem_mk (Stages 3,4)
--   PSet, ZFSet, ZFSet.mk_mem_iff (Mathlib.SetTheory.ZFC.Basic)
--
-- Source: Aczel 1988 §6.

import Mathlib.SetTheory.ZFC.Basic
import VRCycle.SetsZFA.Membership

namespace VR.SetsZFA

universe u

-- ============================================================
-- §1. embedPSet — structural recursion into CoPSet
-- ============================================================

/-- Embed a well-founded pre-set into the coinductive pre-set type.

`embedPSet (PSet.mk α A) = CoPSet.mk α (fun i => embedPSet (A i))`

The same branching type `α` and recursively embedded children. The
embedding witnesses that every well-founded set is a special case
of the coinductive universe: a well-founded tree is a particular
(necessarily finite-depth) element of the coinductive type where
infinite trees are also permitted.

**Termination**: structural recursion on the inductive `PSet`. Each
`A i` is a strict sub-term of `PSet.mk α A`, so Lean's termination
checker accepts this without annotation. -/
def embedPSet : PSet.{u} → CoPSet.{u}
  | PSet.mk α A => CoPSet.mk α (fun i => embedPSet (A i))

-- ============================================================
-- §2. embedPSet_dest — computation rule
-- ============================================================

/-- **Computation rule**: `embedPSet` unfolds by one level.

`CoPSet.dest (embedPSet (PSet.mk α A)) = ⟨α, fun i => embedPSet (A i)⟩`

**Proof**: `rfl`. Both `embedPSet`'s equation and `CoPSet.dest_mk`
are definitional in Lean 4's kernel. Parallel to `graphCoPSet_dest`
in Stage 5. -/
theorem embedPSet_dest (α : Type u) (A : α → PSet.{u}) :
    CoPSet.dest (embedPSet (PSet.mk α A)) = ⟨α, fun i => embedPSet (A i)⟩ := rfl

-- ============================================================
-- §3. embedPSet_congr — PSet.Equiv → CoPSet.Equiv
-- ============================================================

/-- **Forward faithfulness**: `embedPSet` respects pre-set equivalence.

`PSet.Equiv x y → CoPSet.Equiv (embedPSet x) (embedPSet y)`

**Proof**: pure bisimulation, no induction on PSet.

Define `R c d := ∃ x y : PSet, PSet.Equiv x y ∧ c = embedPSet x ∧ d = embedPSet y`.

This is a CoPSet bisimulation: given `c = embedPSet (PSet.mk α A)`,
`d = embedPSet (PSet.mk β B)`, `PSet.Equiv x y` (where x = PSet.mk α A,
y = PSet.mk β B):
- `c.shape = α`, `c.children i = embedPSet (A i)` (definitionally)
- `d.shape = β`, `d.children j = embedPSet (B j)` (definitionally)
- Forward `i : α`: `PSet.Equiv` gives `j : β` with `PSet.Equiv (A i) (B j)`;
  conclude `R (embedPSet (A i)) (embedPSet (B j))` via `rfl` witnesses. ✓

**Asymmetry**: no induction on PSet required. The coinductive framework
absorbs the proof obligation via a single bisimulation. Contrast with
`embedPSet_faithful` (§4) which DOES require structural induction. -/
theorem embedPSet_congr {x y : PSet.{u}} (h : PSet.Equiv x y) :
    CoPSet.Equiv (embedPSet x) (embedPSet y) := by
  apply CoPSet.bisim_imp_Equiv
    (fun c d => ∃ x y : PSet.{u}, PSet.Equiv x y ∧ c = embedPSet x ∧ d = embedPSet y)
  · -- Show CoPSet.isBisim R
    intro c d ⟨x', y', hxy, hcx, hdy⟩
    rcases x' with ⟨α, A⟩
    rcases y' with ⟨β, B⟩
    -- After substitution: c = embedPSet (PSet.mk α A), d = embedPSet (PSet.mk β B)
    -- Shapes and children resolve definitionally:
    --   c.shape = α, c.children i = embedPSet (A i)
    --   d.shape = β, d.children j = embedPSet (B j)
    subst hcx; subst hdy
    constructor
    · -- Forward: i : α → ∃ j : β, R (embedPSet (A i)) (embedPSet (B j))
      intro i
      obtain ⟨j, hj⟩ := hxy.1 i
      exact ⟨j, A i, B j, hj, rfl, rfl⟩
    · -- Backward: j : β → ∃ i : α, R (embedPSet (A i)) (embedPSet (B j))
      intro j
      obtain ⟨i, hi⟩ := hxy.2 j
      exact ⟨i, A i, B j, hi, rfl, rfl⟩
  · -- Initial witness: R (embedPSet x) (embedPSet y)
    exact ⟨x, y, h, rfl, rfl⟩

-- ============================================================
-- §4. embedPSet_faithful — CoPSet.Equiv → PSet.Equiv
-- ============================================================

/-- **Backward faithfulness**: CoPSet equivalence of embedded pre-sets implies
PSet equivalence.

`CoPSet.Equiv (embedPSet x) (embedPSet y) → PSet.Equiv x y`

**Proof**: structural induction on `x` (PSet is well-founded).

Given `CoPSet.Equiv (CoPSet.mk α (embedPSet ∘ A)) (CoPSet.mk β (embedPSet ∘ B))`,
`isBisim_Equiv` gives: for each `i : α`, some `j : β` with
`CoPSet.Equiv (embedPSet (A i)) (embedPSet (B j))`. By IH at `i`:
`PSet.Equiv (A i) (B j)`. Hence `PSet.Equiv (PSet.mk α A) (PSet.mk β B)`.

**Asymmetry**: requires structural induction because `CoPSet.Equiv` is the
greatest fixpoint — descending through children of a `CoPSet.Equiv` proof
to extract `PSet.Equiv` at deeper levels requires PSet's well-foundedness
to guarantee termination of the induction. -/
theorem embedPSet_faithful (x : PSet.{u}) :
    ∀ y : PSet.{u}, CoPSet.Equiv (embedPSet x) (embedPSet y) → PSet.Equiv x y := by
  induction x with
  | mk α A ih =>
    intro y h
    cases y with
    | mk β B =>
      -- h : CoPSet.Equiv (embedPSet (PSet.mk α A)) (embedPSet (PSet.mk β B))
      -- All shapes and children resolve definitionally:
      --   (embedPSet (PSet.mk α A)).shape   = α
      --   (embedPSet (PSet.mk α A)).children i = embedPSet (A i)
      --   (embedPSet (PSet.mk β B)).shape   = β
      --   (embedPSet (PSet.mk β B)).children j = embedPSet (B j)
      -- ih : ∀ i : α, ∀ z : PSet, CoPSet.Equiv (embedPSet (A i)) (embedPSet z) → PSet.Equiv (A i) z
      have hbisim := CoPSet.isBisim_Equiv _ _ h
      -- hbisim.1 : ∀ i : α, ∃ j : β, CoPSet.Equiv (embedPSet (A i)) (embedPSet (B j))
      -- hbisim.2 : ∀ j : β, ∃ i : α, CoPSet.Equiv (embedPSet (A i)) (embedPSet (B j))
      constructor
      · -- Forward: ∀ i : α, ∃ j : β, PSet.Equiv (A i) (B j)
        intro i
        obtain ⟨j, hj⟩ := hbisim.1 i
        exact ⟨j, ih i (B j) hj⟩
      · -- Backward: ∀ j : β, ∃ i : α, PSet.Equiv (A i) (B j)
        intro j
        obtain ⟨i, hi⟩ := hbisim.2 j
        exact ⟨i, ih i (B j) hi⟩

-- ============================================================
-- §5. embedOSet — lift to OSetZFA
-- ============================================================

/-- Embed well-founded sets (ZFSet) into OSetZFA.

`embedOSet (ZFSet.mk p) = OSetZFA.mk (embedPSet p)`

Defined by `Quotient.lift`: well-defined by `embedPSet_congr`
(which ensures the output is independent of the PSet representative).

`noncomputable`: quotient lifting is noncomputable in Lean 4's kernel. -/
noncomputable def embedOSet : ZFSet.{u} → OSetZFA.{u} :=
  Quotient.lift (fun p => OSetZFA.mk (embedPSet p))
    (fun _p _q h => OSetZFA.sound (embedPSet_congr h))

-- ============================================================
-- §6. embedOSet_mk — computation rule
-- ============================================================

/-- **Computation rule**: `embedOSet (ZFSet.mk p) = OSetZFA.mk (embedPSet p)`.

**Proof**: `rfl`. `Quotient.lift` applied to `⟦p⟧` reduces definitionally
to the function at `p`. -/
@[simp]
theorem embedOSet_mk (p : PSet.{u}) :
    embedOSet (ZFSet.mk p) = OSetZFA.mk (embedPSet p) := rfl

-- ============================================================
-- §7. embedOSet_injective — injectivity
-- ============================================================

/-- **Injectivity**: `embedOSet` is injective.

`embedOSet a = embedOSet b → a = b`

Equivalently: different well-founded sets map to different ZFA sets.

**Proof**: reduce to PSet representatives, extract `CoPSet.Equiv` via
`OSetZFA.exact`, apply `embedPSet_faithful` to get `PSet.Equiv`, lift
to quotient equality via `Quotient.sound`. -/
theorem embedOSet_injective : Function.Injective embedOSet := by
  intro a b hpq
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  obtain ⟨q, rfl⟩ := Quotient.exists_rep b
  -- hpq : embedOSet ⟦p⟧ = embedOSet ⟦q⟧
  -- Definitionally: OSetZFA.mk (embedPSet p) = OSetZFA.mk (embedPSet q)
  -- OSetZFA.exact accepts via kernel definitional equality
  exact Quotient.sound (embedPSet_faithful p q (OSetZFA.exact hpq))

-- ============================================================
-- §8. embedOSet_mem — membership preservation
-- ============================================================

/-- **Membership preservation**: `embedOSet` preserves the membership relation.

`embedOSet x ∈ embedOSet a ↔ x ∈ a`

The embedding is a morphism of membership structures: `(OSet, ∈)` embeds
faithfully into `(OSetZFA, ∈)` with the same membership structure.

**Proof**: reduce to PSet representatives. With `a = ZFSet.mk (PSet.mk β B)`:
- LHS unfolds (via `mem_mk`) to `∃ j : β, CoPSet.Equiv (embedPSet p) (embedPSet (B j))`
- RHS unfolds (via `ZFSet.mk_mem_iff`) to `∃ j : β, PSet.Equiv p (B j)`
- Equivalence: apply `embedPSet_faithful` (→) and `embedPSet_congr` (←). -/
theorem embedOSet_mem (x a : ZFSet.{u}) :
    embedOSet x ∈ embedOSet a ↔ x ∈ a := by
  refine Quotient.inductionOn₂ x a (fun p q => ?_)
  cases q with
  | mk β B =>
    -- All reductions are definitional (Quotient.lift, embedPSet equation,
    -- CoPSet.dest_mk, PSet.Mem) so change reaches the kernel-level form directly:
    --   LHS: ∃ j : β, CoPSet.Equiv (embedPSet p) (embedPSet (B j))
    --   RHS: ∃ j : β, PSet.Equiv p (B j)
    change (∃ j : β, CoPSet.Equiv (embedPSet p) (embedPSet (B j))) ↔
           (∃ j : β, PSet.Equiv p (B j))
    exact ⟨fun ⟨j, hj⟩ => ⟨j, embedPSet_faithful p (B j) hj⟩,
           fun ⟨j, hj⟩ => ⟨j, embedPSet_congr hj⟩⟩

end VR.SetsZFA
