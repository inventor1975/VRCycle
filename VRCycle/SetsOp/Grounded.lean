-- VRCycle/SetsOp/Grounded.lean
-- VR-Sets, Brouwer edition — Stage S7 (polish): groundedness is a well-defined,
-- hereditary property of operational sets.
--   * `acc_bisim`        — accessibility transports along a bisimulation;
--   * `isGrounded_congr` / `isGrounded_iff` — `IsGrounded` respects `≈` (so "well-founded
--     / ZFC-mode" is a property of the SET, not of the particular graph presenting it);
--   * `mem_grounded`     — a member of a grounded set is grounded (ZFC-mode is hereditary).
-- Self-contained (only `Acc`, from core).  Target: axiom-free / choice-free.

import VRCycle.SetsOp.Pointed

namespace VRCycle.SetsOp

universe u

/-- Accessibility transports along a bisimulation: if `R` is a bisimulation between `a` and
`b`, and `R v w`, then `v` accessible in `a` forces `w` accessible in `b`. -/
theorem acc_bisim {a b : OpSet.{u}} {R : a.V → b.V → Prop} (hbi : IsBisim a b R) :
    ∀ (v : a.V), Acc a.E v → ∀ (w : b.V), R v w → Acc b.E w := by
  intro v hacc
  induction hacc with
  | intro v _ ih =>
      intro w hvw
      refine Acc.intro w (fun w' hw' => ?_)
      obtain ⟨v', hv'v, hRv'w'⟩ := (hbi v w hvw).2 w' hw'
      exact ih v' hv'v w' hRv'w'

/-- `IsGrounded` respects operational identity (one direction). -/
theorem OpSet.isGrounded_congr {a b : OpSet.{u}} (h : a.Equiv b)
    (ha : a.IsGrounded) : b.IsGrounded := by
  obtain ⟨R, hpt, hbi⟩ := h
  exact acc_bisim hbi a.pt ha b.pt hpt

/-- **Groundedness is a property of the set, not the graph**: `a ≈ b → (a` grounded `↔ b`
grounded`)`.  So "well-founded / ZFC-mode" is `≈`-invariant. -/
theorem OpSet.isGrounded_iff {a b : OpSet.{u}} (h : a.Equiv b) :
    a.IsGrounded ↔ b.IsGrounded :=
  ⟨OpSet.isGrounded_congr h, OpSet.isGrounded_congr h.symm⟩

/-- **ZFC-mode is hereditary**: a member of a grounded set is grounded. -/
theorem OpSet.mem_grounded {x z : OpSet.{u}} (hx : x.IsGrounded) (hz : z.Mem x) :
    z.IsGrounded := by
  obtain ⟨a, ha, hza⟩ := hz
  cases hx with
  | intro _ h => exact (OpSet.isGrounded_iff hza).2 (h a ha)

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S7) — MEASURED
#print axioms acc_bisim
#print axioms OpSet.isGrounded_iff
#print axioms OpSet.mem_grounded

end VRCycle.SetsOp
