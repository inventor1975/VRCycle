-- VRCycle/SetsOp/Omega.lean
-- VR-Sets, Brouwer edition — Stage S2c: the operational ω (infinity).
-- The von Neumann naturals as operational sets, and ω as their sup.  At universe 0
-- (indexed by `Nat`).  Target: axiom-free / choice-free.
-- (Uses `Nat.zero`/`Nat.succ` directly: the operational files import nothing, so numeral
-- literals/`OfNat` are not in scope — the constructors are cleaner here anyway.)

import VRCycle.SetsOp.Closure

namespace VRCycle.SetsOp

/-- The von Neumann naturals as operational sets: `0 = ∅`, `n+1 = succ n`. -/
def OpSet.vn : Nat → OpSet.{0}
  | .zero   => OpSet.emptySup
  | .succ n => OpSet.succ (OpSet.vn n)

/-- The operational ω: the set whose members are exactly the von Neumann naturals. -/
def OpSet.omega : OpSet.{0} := OpSet.sup OpSet.vn

/-- Membership law of ω: its members are exactly the `vn n` (up to operational identity). -/
theorem OpSet.mem_omega (z : OpSet.{0}) :
    z.Mem OpSet.omega ↔ ∃ n, z.Equiv (OpSet.vn n) :=
  OpSet.mem_sup OpSet.vn z

/-- Infinity, part 1: `∅ ∈ ω`. -/
theorem OpSet.empty_mem_omega : (OpSet.vn Nat.zero).Mem OpSet.omega :=
  (OpSet.mem_omega _).2 ⟨Nat.zero, OpSet.Equiv.refl _⟩

/-- Infinity, part 2: ω is closed under successor (on the naturals it generates). -/
theorem OpSet.succ_mem_omega (n : Nat) :
    (OpSet.succ (OpSet.vn n)).Mem OpSet.omega :=
  (OpSet.mem_omega _).2 ⟨Nat.succ n, OpSet.Equiv.refl _⟩

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S2c) — MEASURED
#print axioms OpSet.mem_omega
#print axioms OpSet.empty_mem_omega
#print axioms OpSet.succ_mem_omega

end VRCycle.SetsOp
