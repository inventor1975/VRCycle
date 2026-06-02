-- VRCycle/Continuum/Spread.lean
-- Operational Continuum (Path 1) — Stage A: the binary spread.
--
-- STAGE: A (of A→B→C). SOURCE: PLAN_OPERATIONAL_CONTINUUM.md.
--
-- ## What this file does (Stage A — the safe, constructive, "thin" core)
-- Builds `binarySpread : FormalTopology` — the formal topology of finite binary
-- strings `List Bool`, ordered by refinement (longer = more determined), with the
-- basic cover "a node is covered by its two children".  This is the tree 2^<ω as a
-- pointfree space, reusing the VR-Topology Coquand-coverage machinery
-- (`FormalTopology.ofPresentation` / `CoverGen`).
--
-- ## The three registers (the VR-specific reading — recognition anchor)
--   * a NODE `s : List Bool` = a **finite performed segment** = an operational act
--     (operational register; the node type is countable — the "done");
--   * a BRANCH (an infinite path; NOT an object here, only referred to via its finite
--     approximations) = a **becoming / potential** sequence — lawless tail (the NEW
--     register).  Branches as objects, continuity, and the fan theorem are Stage B,
--     where the consistency hazard (cannot `axiom` WC-N over classical mathlib) is
--     handled by hypothesis-tracking / a model — NOT here;
--   * the space of all branches is non-enumerable, witnessed structurally by the
--     spread's infinite branching, not by any enumeration.
--
-- ## Axiom profile: expected constructive (no `Classical.choice`)
-- `CoverGen` is a `Prop`-valued inductive; the spread carries no choice.  This is the
-- "safe core is genuinely constructive" check (cf. VR-Topology binary Tychonoff).

import VRCycle.Topology.FormalTopology
import VRCycle.Topology.Operational
import Mathlib.Data.List.Infix

namespace VRCycle.Continuum

open VRCycle.Topology

-- ============================================================
-- §A1–A2.  Order on nodes: refinement = reverse prefix
-- ============================================================

/-- Refinement order on tree nodes: `nodeLe s t` means `t` is a prefix of `s`,
i.e. `s` extends `t`, i.e. `s` is **more determined** (a smaller neighbourhood).
A child `s ++ [b]` refines its parent `s`. -/
def nodeLe (s t : List Bool) : Prop := t <+: s

theorem nodeLe_refl (s : List Bool) : nodeLe s s := List.prefix_refl s

theorem nodeLe_trans (s t u : List Bool) :
    nodeLe s t → nodeLe t u → nodeLe s u :=
  fun (hst : t <+: s) (htu : u <+: t) => htu.trans hst

-- ============================================================
-- §A3.  Basic cover: a node is covered by its two children
-- ============================================================

/-- The two immediate children of a node `s`: append `false` or `true`. -/
def children (s : List Bool) : Set (List Bool) := {s ++ [false], s ++ [true]}

/-- Basic cover of the binary spread: a node `s` is basic-covered exactly by the
set of its two children.  This single datum, closed under the Coquand coverage
axioms (`CoverGen`), is the whole spread. -/
def spreadBasicCov (s : List Bool) (U : Set (List Bool)) : Prop := U = children s

-- ============================================================
-- §A4.  The binary spread as a FormalTopology
-- ============================================================

/-- **The binary spread** `2^{<ω}` as a formal topology: nodes `List Bool`,
refinement order, children-cover, closed under the Coquand coverage axioms. -/
def binarySpread : FormalTopology :=
  FormalTopology.ofPresentation
    (S := List Bool)
    (le := nodeLe)
    (le_refl := nodeLe_refl)
    (le_trans := nodeLe_trans)
    (basicCov := spreadBasicCov)

-- ============================================================
-- §A5.  Bars, and smoke lemmas
-- ============================================================

/-- A **bar** is a set of nodes that covers the root `[]` (the not-yet-started
sequence).  Operationally: every becoming-sequence eventually enters `B` after a
finite performed segment.  This is the Stage-A staging point for the fan theorem
(Stage B): a bar's existence vs a *uniform* finite bound. -/
def IsBar (B : Set (List Bool)) : Prop := binarySpread.cov [] B

/-- Every node is covered by its two children (the defining branching of the spread). -/
theorem cover_children (s : List Bool) :
    binarySpread.cov s (children s) :=
  CoverGen.basic (rfl : children s = children s)

/-- A node covers any set it belongs to (reflexivity of coverage). -/
theorem cover_self {s : List Bool} {U : Set (List Bool)} (h : s ∈ U) :
    binarySpread.cov s U :=
  CoverGen.mem h

/-- The singleton `{s}` is a bar for `s` itself: a sequence sitting at `s` has
already entered `{s}`.  (Smoke test of `IsBar` at a node via `cover_self`.) -/
theorem bar_root_self : binarySpread.cov [] ({[]} : Set (List Bool)) :=
  cover_self (rfl : ([] : List Bool) ∈ ({[]} : Set (List Bool)))

-- ============================================================
-- §A-op.  Operational register: the node space is describable
-- ============================================================

/-- Bijective binary code of a node: `[] ↦ 0`, `false :: l ↦ 2·e+1`, `true :: l ↦ 2·e+2`.
Hand-rolled (not mathlib `Encodable`) so the operational register stays genuinely
choice-free — in this import context `Encodable (List Bool)` resolves through a
`Classical.choice` path (Finding CONT-1). -/
def encodeNode : List Bool → ℕ
  | [] => 0
  | false :: l => 2 * encodeNode l + 1
  | true :: l => 2 * encodeNode l + 2

/-- Inverse of `encodeNode`, by well-founded recursion on `n / 2`. -/
def decodeNode : ℕ → List Bool
  | 0 => []
  | (n + 1) => decide (n % 2 = 1) :: decodeNode (n / 2)
decreasing_by omega

/-- Round-trip: `decodeNode` is a left inverse of `encodeNode`. -/
theorem decodeNode_encodeNode : ∀ l : List Bool, decodeNode (encodeNode l) = l
  | [] => by simp only [encodeNode, decodeNode]
  | false :: l => by
      have ih := decodeNode_encodeNode l
      change decodeNode (2 * encodeNode l + 1) = false :: l
      simp only [decodeNode]
      have h1 : (2 * encodeNode l) % 2 = 0 := by omega
      have h2 : (2 * encodeNode l) / 2 = encodeNode l := by omega
      rw [h1, h2, ih]; rfl
  | true :: l => by
      have ih := decodeNode_encodeNode l
      change decodeNode (2 * encodeNode l + 2) = true :: l
      have e : 2 * encodeNode l + 2 = (2 * encodeNode l + 1) + 1 := by omega
      rw [e]
      simp only [decodeNode]
      have h1 : (2 * encodeNode l + 1) % 2 = 1 := by omega
      have h2 : (2 * encodeNode l + 1) / 2 = encodeNode l := by omega
      rw [h1, h2, ih]; rfl

/-- **The space of performed acts is describable.**  The set of all nodes
(`Set.univ : Set (List Bool)`) carries an explicit, hand-rolled enumeration
`ℕ → Option (List Bool)` — choice-free.  This places the *operational register*
(finite performed segments = the "done") on a formal footing: the nodes are countable
and constructively listable.  Contrast the non-enumerable space of branches (the
becoming register), which carries no such instance — and structurally cannot. -/
instance nodes_describable : IsDescribable (Set.univ : Set (List Bool)) where
  enumerator n := some (decodeNode n)
  enumerator_some_mem _ a _ := Set.mem_univ a
  enumerator_surj x _ := ⟨encodeNode x, by rw [decodeNode_encodeNode x]⟩

-- ============================================================
-- Axiom audit — Stage A
-- ============================================================
-- Expect constructive: no `Classical.choice`.  `CoverGen` is Prop-inductive;
-- `Encodable (List Bool)` is fully computable.

#print axioms binarySpread
#print axioms cover_children
#print axioms IsBar
#print axioms decodeNode_encodeNode
#print axioms nodes_describable

end VRCycle.Continuum
