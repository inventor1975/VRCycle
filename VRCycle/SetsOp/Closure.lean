-- VRCycle/SetsOp/Closure.lean
-- VR-Sets, Brouwer edition — Stage S2b: membership respects identity, union, successor.
-- Self-contained continuation.  Target: axiom-free / choice-free ([propext] from `rw` is fine).
--
--   * `mem_congr`      — membership respects operational identity on the container.
--   * `union` / `mem_union`     — the big union ⋃x, with the ZF membership law.
--   * `binUnion` / `mem_binUnion` — binary union a ∪ b.
--   * `succ` / `mem_succ`         — the von Neumann successor a ∪ {a}.

import VRCycle.SetsOp.Builder

namespace VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  Membership respects operational identity
-- ============================================================

/-- If `y ≈ y'` then every member of `y` is a member of `y'`. -/
theorem OpSet.mem_congr {z y y' : OpSet.{u}} (hy : y.Equiv y') (h : z.Mem y) : z.Mem y' := by
  obtain ⟨a, ha, hza⟩ := h
  obtain ⟨R, hpt, hbi⟩ := hy
  obtain ⟨fwd, _⟩ := hbi y.pt y'.pt hpt
  obtain ⟨b', hb', hab'⟩ := fwd a ha
  exact ⟨b', hb', hza.trans ⟨R, hab', hbi⟩⟩

/-- Membership is invariant under operational identity on the left too. -/
theorem OpSet.mem_congr_left {z z' y : OpSet.{u}} (hz : z.Equiv z') (h : z.Mem y) : z'.Mem y := by
  obtain ⟨a, ha, hza⟩ := h
  exact ⟨a, ha, hz.symm.trans hza⟩

-- ============================================================
-- §2.  Union ⋃x
-- ============================================================

/-- The big union `⋃ x`: members are the members of members of `x`.  Indexed by the pairs of
reveal-edges `pt → a → a'` of `x`; the `a'`-component is the witnessed member. -/
def OpSet.union (x : OpSet.{u}) : OpSet.{u} :=
  OpSet.sup (fun p : { q : x.V × x.V // x.E q.1 x.pt ∧ x.E q.2 q.1 } => x.child p.1.2)

/-- **Union membership law**: `z ∈ ⋃x ↔ ∃ y, y ∈ x ∧ z ∈ y`. -/
theorem OpSet.mem_union (x z : OpSet.{u}) :
    z.Mem x.union ↔ ∃ y, y.Mem x ∧ z.Mem y := by
  rw [OpSet.union, OpSet.mem_sup]
  constructor
  · rintro ⟨⟨⟨a, a'⟩, ha, ha'⟩, hz⟩
    exact ⟨x.child a, ⟨a, ha, OpSet.Equiv.refl _⟩, ⟨a', ha', hz⟩⟩
  · rintro ⟨y, ⟨a, ha, hya⟩, hzy⟩
    obtain ⟨a', ha', hz⟩ := OpSet.mem_congr hya hzy
    exact ⟨⟨⟨a, a'⟩, ha, ha'⟩, hz⟩

-- ============================================================
-- §3.  Binary union and the von Neumann successor
-- ============================================================

/-- Binary union `a ∪ b := ⋃{a, b}`. -/
def OpSet.binUnion (a b : OpSet.{u}) : OpSet.{u} := (OpSet.pair a b).union

theorem OpSet.mem_binUnion (z a b : OpSet.{u}) :
    z.Mem (OpSet.binUnion a b) ↔ z.Mem a ∨ z.Mem b := by
  rw [OpSet.binUnion, OpSet.mem_union]
  constructor
  · rintro ⟨y, hy, hzy⟩
    rw [OpSet.mem_pair] at hy
    cases hy with
    | inl h => exact Or.inl (OpSet.mem_congr h hzy)
    | inr h => exact Or.inr (OpSet.mem_congr h hzy)
  · rintro (h | h)
    · exact ⟨a, (OpSet.mem_pair a a b).2 (Or.inl (OpSet.Equiv.refl a)), h⟩
    · exact ⟨b, (OpSet.mem_pair b a b).2 (Or.inr (OpSet.Equiv.refl b)), h⟩

/-- The von Neumann successor `succ a := a ∪ {a}`. -/
def OpSet.succ (a : OpSet.{u}) : OpSet.{u} := OpSet.binUnion a (OpSet.singleton a)

theorem OpSet.mem_succ (z a : OpSet.{u}) :
    z.Mem (OpSet.succ a) ↔ z.Mem a ∨ z.Equiv a := by
  rw [OpSet.succ, OpSet.mem_binUnion, OpSet.mem_singleton]

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S2b) — MEASURED
#print axioms OpSet.mem_congr
#print axioms OpSet.mem_union
#print axioms OpSet.mem_binUnion
#print axioms OpSet.mem_succ

end VRCycle.SetsOp
