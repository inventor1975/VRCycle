-- VR-Sets: VR-Numbers bridge (DOI 10.5281/zenodo.20303536)
-- Part V. VR Numbers as von Neumann Ordinals in VR-Sets.
--
-- Stage 12: Embedding VRObj into OSet as von Neumann ordinals,
--           Theorem V.1 (well-foundedness) and Theorem V.2 (isomorphism).
-- Source: Part V §V.1–§V.4.

import VRCycle.Sets.Modes
import VRCycle.VR

namespace VR.Sets

-- ============================================================
-- §V.1 — Von Neumann successor in OSet
-- ============================================================

/-- The von Neumann successor of s: `s ∪ {s}`.

§V.1 (preprint): «The successor operation is s↦s∪{s}.»
Membership: `x ∈ osetSuccOp s ↔ x = s ∨ x ∈ s` (ZFSet.mem_insert_iff).
Parallel: `VRObj.succ x` (A3: t(x) = x ∪ {x}, VR.lean). -/
def osetSuccOp (s : OSet.{0}) : OSet.{0} := insert s s

/-- The canonical embedding of VR objects as von Neumann ordinals.

§V.1 (preprint, Definition V.1):
«φ(O₀) = ∅,  φ(O_{n+1}) = φ(O_n) ∪ {φ(O_n)}.»

Structural recursion on VRObj. `noncomputable` because ZFSet is a
quotient type. -/
noncomputable def embedVR : VRObj → OSet.{0}
  | VRObj.base   => ∅
  | VRObj.succ x => osetSuccOp (embedVR x)

theorem embedVR_zero : embedVR VRObj.base = (∅ : OSet.{0}) := rfl

theorem embedVR_succ (x : VRObj) :
    embedVR (VRObj.succ x) = osetSuccOp (embedVR x) := rfl

-- ============================================================
-- §V.2 — Theorem V.1
-- ============================================================

/-- §V.2, Theorem V.1: every embedded VR number is in ZFC-mode. -/
theorem Theorem_V_1_WellFounded (x : VRObj) : isZFCmode (embedVR x) :=
  isZFCmode_all (embedVR x)

-- ============================================================
-- §V.3 — Auxiliary lemmas (constructive, no Classical.choice)
-- ============================================================

private abbrev ZFSet_wf : WellFounded (· ∈ · : OSet.{0} → OSet.{0} → Prop) :=
  IsWellFounded.wf

private theorem oset_mem_irrefl (s : OSet.{0}) : ¬ s ∈ s :=
  (WellFounded.irrefl ZFSet_wf).irrefl s

private theorem oset_mem_asymm {s t : OSet.{0}} (h : s ∈ t) : ¬ t ∈ s :=
  WellFounded.asymmetric ZFSet_wf s t h

/-- `osetSuccOp` is injective.
Proof: extract membership from both sides, then case-split;
all three non-trivial cases contradict `oset_mem_irrefl` or `oset_mem_asymm`. -/
private theorem osetSuccOp_injective : Function.Injective osetSuccOp := by
  intro s t h
  simp only [osetSuccOp] at h
  have hs : s ∈ (insert t t : OSet.{0}) := by rw [← h]; exact ZFSet.mem_insert s s
  have ht : t ∈ (insert s s : OSet.{0}) := by rw [h]; exact ZFSet.mem_insert t t
  rcases ZFSet.mem_insert_iff.mp hs with rfl | hst
  · rfl
  · rcases ZFSet.mem_insert_iff.mp ht with rfl | hts
    · exact absurd hst (oset_mem_irrefl t)
    · exact absurd hst (oset_mem_asymm hts)

-- ============================================================
-- §V.3 — Joint induction
-- ============================================================

-- Abbreviation to reduce line noise in the induction proof.
private noncomputable def ev (x : VRObj) : OSet.{0} := embedVR x

private theorem embedVR_mem_iff_and_inj (y : VRObj) :
    (∀ x : VRObj, VR.mem x y ↔ ev x ∈ ev y) ∧
    (∀ x : VRObj, ev x = ev y → x = y) := by
  induction y with
  | base =>
    simp only [ev, embedVR]
    exact ⟨
      fun x => ⟨fun h => h.elim, fun h => (ZFSet.notMem_empty _ h).elim⟩,
      fun x hx => by
        cases x with
        | base => rfl
        | succ z =>
          simp only [embedVR, osetSuccOp] at hx
          exact absurd (hx ▸ ZFSet.mem_insert (embedVR z) (embedVR z))
                       (ZFSet.notMem_empty _)⟩
  | succ y' ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    simp only [ev, embedVR, osetSuccOp]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · -- membership iff
      rw [ZFSet.mem_insert_iff]
      constructor
      · rintro (rfl | hmem)
        · exact Or.inl rfl
        · exact Or.inr ((ihP x).mp hmem)
      · rintro (heq | hmem)
        · exact Or.inl (ihQ x heq)
        · exact Or.inr ((ihP x).mpr hmem)
    · -- injectivity
      cases x with
      | base =>
        simp only [embedVR] at hx
        exact absurd (hx.symm ▸ ZFSet.mem_insert (embedVR y') (embedVR y'))
                     (ZFSet.notMem_empty _)
      | succ z =>
        simp only [embedVR, osetSuccOp] at hx
        exact congrArg VRObj.succ (ihQ z (osetSuccOp_injective hx))

/-- `embedVR` preserves membership: `VR.mem x y ↔ embedVR x ∈ embedVR y`. -/
theorem embedVR_mem_iff (x y : VRObj) :
    VR.mem x y ↔ embedVR x ∈ embedVR y :=
  (embedVR_mem_iff_and_inj y).1 x

/-- `embedVR` is injective. -/
theorem embedVR_injective : Function.Injective embedVR :=
  fun x y h => (embedVR_mem_iff_and_inj y).2 x h

-- ============================================================
-- §V.4 — Theorem V.2: VR_OSet_iso
-- ============================================================

/-- The structural isomorphism between VRObj and its image in OSet.

## §V.4, Theorem V.2 (preprint, verbatim)
«The embedding φ : VR → VR-Sets is injective, maps ∅ to ∅, commutes
with the successor operation, and preserves the membership relation ∈.
Together these properties constitute an isomorphism of the ordinal
structure (zero, successor, membership graph) of VR numbers into VR-Sets.»

## Scope: ordinal structure only — arithmetic preservation by composition

`VR_OSet_iso` covers zero, successor, and membership only. Arithmetic
preservation (vadd, vmul, vpow at OSet level) is deliberately excluded.

Preprint §V.4 (verbatim): «VR-Numbers (Integers, Rationals, Reals,
Complex) transfer analogously, by reduction to VR numbers. No re-proof
at the VR-Sets level is needed.»

In Lean, arithmetic preservation follows by **composition**:

    VRObj ──Theorem_11_VR_PA──▶ ℕ ──(embedVR ∘ O)──▶ OSet

`Theorem_11_VR_PA` (file: VRCycle/VR.lean, §11) establishes
VRObj ≅ ℕ with preservation of `+`, `×`, `^` (via O_add, O_mul, O_pow).
Re-proving this at the OSet level would duplicate VR.lean without adding
mathematical content.

## Parallel with VR_PA_iso (VR.lean §11)

- `VR_PA_iso`:   bijection VRObj ≅ ℕ + zero, succ, +, ×, ^ preservation.
- `VR_OSet_iso`: embedding VRObj ↪ OSet + zero, succ, ∈ preservation.
Difference: `VR_PA_iso` is a bijection; `VR_OSet_iso` is an embedding
(OSet contains all ordinals, infinite sets, non-well-founded objects,
etc., vastly more than the image of VRObj). -/
structure VR_OSet_iso where
  embed : VRObj → OSet.{0}
  preserve_zero : embed VRObj.base = ∅
  preserve_succ : ∀ x, embed (VRObj.succ x) = insert (embed x) (embed x)
  preserve_mem : ∀ x y : VRObj, VR.mem x y ↔ embed x ∈ embed y
  injective : Function.Injective embed

/-- §V.4, Theorem V.2: the explicit `VR_OSet_iso` instance. -/
noncomputable def Theorem_V_2 : VR_OSet_iso where
  embed := embedVR
  preserve_zero := embedVR_zero
  preserve_succ := fun x => by simp [embedVR_succ, osetSuccOp]
  preserve_mem := embedVR_mem_iff
  injective := embedVR_injective

end VR.Sets
