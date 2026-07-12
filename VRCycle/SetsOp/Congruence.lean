-- VRCycle/SetsOp/Congruence.lean
-- VR-Sets, Brouwer edition — Stage S3b: the set operations respect operational identity.
-- All via strong extensionality (`ext`) + the membership laws.  Then the clean form of
-- Infinity: ω is closed under successor for ANY member (not just the generating `vn n`).
-- Target: axiom-free / choice-free — ACHIEVED at the empty axiom list
-- (2026-07-12 tier pass: Iff-`rw` replaced by Iff.trans combinators).

import VRCycle.SetsOp.Extensionality
import VRCycle.SetsOp.Omega

namespace VRCycle.SetsOp

universe u

theorem OpSet.singleton_congr {x y : OpSet.{u}} (h : x.Equiv y) :
    (OpSet.singleton x).Equiv (OpSet.singleton y) := by
  apply OpSet.ext; intro z
  exact Iff.trans (OpSet.mem_singleton z x)
    (Iff.trans ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
      (OpSet.mem_singleton z y).symm)

theorem OpSet.pair_congr {a a' b b' : OpSet.{u}} (ha : a.Equiv a') (hb : b.Equiv b') :
    (OpSet.pair a b).Equiv (OpSet.pair a' b') := by
  apply OpSet.ext; intro z
  refine Iff.trans (OpSet.mem_pair z a b)
    (Iff.trans ⟨?_, ?_⟩ (OpSet.mem_pair z a' b').symm)
  · rintro (h | h)
    · exact Or.inl (h.trans ha)
    · exact Or.inr (h.trans hb)
  · rintro (h | h)
    · exact Or.inl (h.trans ha.symm)
    · exact Or.inr (h.trans hb.symm)

theorem OpSet.binUnion_congr {a a' b b' : OpSet.{u}} (ha : a.Equiv a') (hb : b.Equiv b') :
    (OpSet.binUnion a b).Equiv (OpSet.binUnion a' b') := by
  apply OpSet.ext; intro z
  refine Iff.trans (OpSet.mem_binUnion z a b)
    (Iff.trans ⟨?_, ?_⟩ (OpSet.mem_binUnion z a' b').symm)
  · rintro (h | h)
    · exact Or.inl (OpSet.mem_congr ha h)
    · exact Or.inr (OpSet.mem_congr hb h)
  · rintro (h | h)
    · exact Or.inl (OpSet.mem_congr ha.symm h)
    · exact Or.inr (OpSet.mem_congr hb.symm h)

theorem OpSet.succ_congr {x y : OpSet.{u}} (h : x.Equiv y) :
    (OpSet.succ x).Equiv (OpSet.succ y) := by
  apply OpSet.ext; intro z
  refine Iff.trans (OpSet.mem_succ z x)
    (Iff.trans ⟨?_, ?_⟩ (OpSet.mem_succ z y).symm)
  · rintro (hz | hz)
    · exact Or.inl ((OpSet.equiv_iff_same_mem.1 h z).1 hz)
    · exact Or.inr (hz.trans h)
  · rintro (hz | hz)
    · exact Or.inl ((OpSet.equiv_iff_same_mem.1 h z).2 hz)
    · exact Or.inr (hz.trans h.symm)

/-- **Infinity, clean form**: ω is closed under successor for ANY of its members — not only
the generating `vn n`.  (Needs `succ_congr`, hence strong extensionality.) -/
theorem OpSet.omega_succ_closed {x : OpSet.{0}} (hx : x.Mem OpSet.omega) :
    (OpSet.succ x).Mem OpSet.omega := by
  obtain ⟨n, hn⟩ := (OpSet.mem_omega x).1 hx
  exact (OpSet.mem_omega _).2 ⟨Nat.succ n, OpSet.succ_congr hn⟩

-- CHECKS: no sorry, no admit; self-contained.

-- Axiom audit (Stage S3b) — MEASURED
#print axioms OpSet.singleton_congr
#print axioms OpSet.pair_congr
#print axioms OpSet.binUnion_congr
#print axioms OpSet.succ_congr
#print axioms OpSet.omega_succ_closed

end VRCycle.SetsOp
