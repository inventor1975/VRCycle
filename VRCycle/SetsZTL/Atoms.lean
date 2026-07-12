-- VRCycle/SetsZTL/Atoms.lean
-- VR Part II, step (а): witnessed identity of the operational sets as
-- ZTL atoms — the Lean half of the measured stand ZTL/zopsets.py (E21).
--
-- The stitch, in one sentence: SetsOp carries identity as a witnessed
-- bisimulation (no quotient, no choice), and ZTL is the logic whose T
-- must be earned — so an identity atom x ≈ y IS a ZTL atom: earned T
-- carries the bisimulation, earned F carries the refutation, and the
-- unexamined atom is the input mark Z. Nothing is translated; the two
-- disciplines are the same discipline.
--
-- Machine-checked here (each measured by the stand first):
--   * EqVerdict — the verdict carried WITH its certificate; soundness
--     is definitional (val = T extracts a bisimulation, val = F a
--     refutation); the zero-trust start is `unexamined` (val = Z).
--   * The alive rules are witness constructors: refl / symm /
--     composeT (= Equiv.trans on the carried witnesses).
--   * The vn register is TOTAL and classical: every identity atom of
--     the operational naturals decides (T ⟺ n = m; never Z) — the
--     Lean twin of "identity is totally earnable" (E21 §1).
--   * Groundedness ⊥ earnability (E21 §6): the Quine atom Ω earns its
--     identity (and its apartness from ∅) while ¬IsGrounded Ω — the
--     cycle that dooms a sentence is harmless in a set.
--   * The fully-earned register is CLASSICAL (E21 §4 endpoint): if
--     every atom of a formula is decided (T-with-fact or F-with-
--     refutation), the greedy ZTL value of the formula is T exactly
--     on the classically true formulas — verdicts over verified
--     identity atoms never lie and never refuse.
--
-- Axiom target: [] for the kernel/verdict layer; [propext] where
-- vn_inj enters (measured at the bottom).

import VRCycle.SetsOp
import VRCycle.SetsZTL.Kernel

namespace VRCycle.SetsZTL

open VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  The verdict carried with its certificate
-- ============================================================

/-- A ZTL verdict on the identity atom `x ≈ y`, carried WITH its
certificate: earned T holds the bisimulation witness, earned F holds
the refutation, `unexamined` is the input mark Z. Soundness is not a
theorem ABOUT this type — it is its shape. -/
inductive EqVerdict (x y : OpSet.{u}) : Type u where
  | earnedT (w : x.Equiv y) : EqVerdict x y
  | earnedF (w : ¬ x.Equiv y) : EqVerdict x y
  | unexamined : EqVerdict x y

namespace EqVerdict

/-- The ZTL value of the verdict. -/
def val {x y : OpSet.{u}} : EqVerdict x y → V
  | earnedT _  => V.T
  | earnedF _  => V.F
  | unexamined => V.Z

/-- The zero-trust start: before examination the atom is worth Z. -/
theorem zero_trust_start (x y : OpSet.{u}) :
    (unexamined : EqVerdict x y).val = V.Z := rfl

/-- Soundness of T, definitionally: an earned T yields the bisimulation. -/
def sound_T {x y : OpSet.{u}} : (v : EqVerdict x y) → v.val = V.T → x.Equiv y
  | earnedT w,  _ => w
  | earnedF _,  h => nomatch h
  | unexamined, h => nomatch h

/-- Soundness of F, definitionally: an earned F yields the refutation. -/
def sound_F {x y : OpSet.{u}} : (v : EqVerdict x y) → v.val = V.F → ¬ x.Equiv y
  | earnedF w,  _ => w
  | earnedT _,  h => nomatch h
  | unexamined, h => nomatch h

-- ============================================================
-- §2.  The alive rules are witness constructors (E21 §3)
-- ============================================================

/-- refl: the diagonal witness — identity with oneself is always earnable. -/
def refl (x : OpSet.{u}) : EqVerdict x x := earnedT (OpSet.Equiv.refl x)

theorem refl_val (x : OpSet.{u}) : (refl x).val = V.T := rfl

/-- symm: the converse witness / the converse refutation. Verdicts are
preserved — symmetry costs nothing. -/
def symm {x y : OpSet.{u}} : EqVerdict x y → EqVerdict y x
  | earnedT w  => earnedT w.symm
  | earnedF w  => earnedF (fun h => w h.symm)
  | unexamined => unexamined

theorem symm_val {x y : OpSet.{u}} (v : EqVerdict x y) :
    v.symm.val = v.val := by cases v <;> rfl

/-- trans on earned T: composition of the carried witnesses
(`Equiv.trans` composes the bisimulations). Two earned identities
earn the third — the rule is not table luck. -/
def composeT {x y z : OpSet.{u}} (v : EqVerdict x y) (w : EqVerdict y z)
    (hv : v.val = V.T) (hw : w.val = V.T) : EqVerdict x z :=
  earnedT ((v.sound_T hv).trans (w.sound_T hw))

theorem composeT_val {x y z : OpSet.{u}} (v : EqVerdict x y)
    (w : EqVerdict y z) (hv : v.val = V.T) (hw : w.val = V.T) :
    (composeT v w hv hw).val = V.T := rfl

end EqVerdict

-- ============================================================
-- §3.  The vn register is total and classical (E21 §1 twin)
-- ============================================================

/-- The identity verdict on the operational naturals: decided for every
pair — T with the diagonal witness on n = m, F by `vn_inj` otherwise. -/
def vnVerdict (n m : Nat) : EqVerdict (OpSet.vn n) (OpSet.vn m) :=
  if h : n = m then
    EqVerdict.earnedT (by cases h; exact OpSet.Equiv.refl _)
  else
    EqVerdict.earnedF (fun e => h (OpSet.vn_inj e))

/-- TOTALITY: on the vn register no identity atom stays Z — identity of
the operational naturals is totally earnable. -/
theorem vnVerdict_ne_Z (n m : Nat) : (vnVerdict n m).val ≠ V.Z := by
  unfold vnVerdict
  split
  · exact fun h => V.noConfusion h
  · exact fun h => V.noConfusion h

/-- CLASSICALITY: the earned verdict is T exactly on the true identities. -/
theorem vnVerdict_T_iff (n m : Nat) :
    (vnVerdict n m).val = V.T ↔ n = m := by
  unfold vnVerdict
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hv => V.noConfusion hv, fun hm => absurd hm h⟩

-- ============================================================
-- §4.  Groundedness ⊥ earnability (E21 §6 twin)
-- ============================================================

/-- The Quine atom Ω = {Ω} earns its identity while being ungrounded:
the cycle that dooms a sentence (the liar) is harmless in a set.
Groundedness of the SET and earnability of its IDENTITY are orthogonal. -/
theorem quine_orthogonality :
    ¬ OpSet.quine.{u}.IsGrounded ∧
      (EqVerdict.refl OpSet.quine.{u}).val = V.T :=
  ⟨OpSet.quine_not_grounded, rfl⟩

/-- Apartness across the divide: Ω is refutably distinct from ∅ —
Ω reveals a member, ∅ reveals none. -/
theorem quine_not_equiv_vn0 : ¬ OpSet.quine.{0}.Equiv (OpSet.vn 0) := by
  intro h
  have hmem : OpSet.Mem OpSet.quine (OpSet.vn 0) :=
    (OpSet.equiv_iff_same_mem.1 h OpSet.quine).1 OpSet.quine_self_mem
  exact OpSet.not_mem_emptySup _ hmem

/-- The earned F verdict across the grounded/ungrounded divide. -/
def quineVsEmpty : EqVerdict OpSet.quine.{0} (OpSet.vn 0) :=
  EqVerdict.earnedF quine_not_equiv_vn0

theorem quineVsEmpty_val : quineVsEmpty.val = V.F := rfl

-- ============================================================
-- §5.  The fully-earned register is classical (E21 §4 endpoint)
-- ============================================================

/-- Formulas over abstract atoms (the identity atoms will be the
instances); the connectives are ZTL's six. -/
inductive Fm (α : Type v) where
  | atom (a : α)
  | not (φ : Fm α)
  | and (φ ψ : Fm α)
  | or (φ ψ : Fm α)
  | imp (φ ψ : Fm α)
  | xor (φ ψ : Fm α)
  | xnor (φ ψ : Fm α)

/-- Greedy ZTL evaluation over a valued environment. -/
def evalV {α : Type v} (env : α → V) : Fm α → V
  | .atom a   => env a
  | .not φ    => V.znot (evalV env φ)
  | .and φ ψ  => V.zand (evalV env φ) (evalV env ψ)
  | .or φ ψ   => V.zor (evalV env φ) (evalV env ψ)
  | .imp φ ψ  => V.zimp (evalV env φ) (evalV env ψ)
  | .xor φ ψ  => V.zxor (evalV env φ) (evalV env ψ)
  | .xnor φ ψ => V.zxnor (evalV env φ) (evalV env ψ)

/-- The classical reading of a formula over the facts. -/
def Truth {α : Type v} (fact : α → Prop) : Fm α → Prop
  | .atom a   => fact a
  | .not φ    => ¬ Truth fact φ
  | .and φ ψ  => Truth fact φ ∧ Truth fact ψ
  | .or φ ψ   => Truth fact φ ∨ Truth fact ψ
  | .imp φ ψ  => Truth fact φ → Truth fact ψ
  | .xor φ ψ  => ¬ (Truth fact φ ↔ Truth fact ψ)
  | .xnor φ ψ => Truth fact φ ↔ Truth fact ψ

/-- `Decided v P`: the value `v` is an earned, truthful verdict on `P` —
classical (never Z) and sound in both directions. -/
def Decided (v : V) (P : Prop) : Prop :=
  (v = V.T ∧ P) ∨ (v = V.F ∧ ¬ P)

namespace Decided

theorem dnot {a : V} {P : Prop} (h : Decided a P) :
    Decided (V.znot a) (¬ P) := by
  rcases h with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · exact Or.inr ⟨rfl, fun hn => hn hp⟩
  · exact Or.inl ⟨rfl, hp⟩

theorem dand {a b : V} {P Q : Prop} (ha : Decided a P) (hb : Decided b Q) :
    Decided (V.zand a b) (P ∧ Q) := by
  rcases ha with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · exact Or.inl ⟨rfl, hp, hq⟩
  · exact Or.inr ⟨rfl, fun h => hq h.2⟩
  · exact Or.inr ⟨rfl, fun h => hp h.1⟩
  · exact Or.inr ⟨rfl, fun h => hp h.1⟩

theorem dor {a b : V} {P Q : Prop} (ha : Decided a P) (hb : Decided b Q) :
    Decided (V.zor a b) (P ∨ Q) := by
  rcases ha with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · exact Or.inl ⟨rfl, Or.inl hp⟩
  · exact Or.inl ⟨rfl, Or.inl hp⟩
  · exact Or.inl ⟨rfl, Or.inr hq⟩
  · exact Or.inr ⟨rfl, fun h => h.elim hp hq⟩

theorem dimp {a b : V} {P Q : Prop} (ha : Decided a P) (hb : Decided b Q) :
    Decided (V.zimp a b) (P → Q) := by
  rcases ha with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · exact Or.inl ⟨rfl, fun _ => hq⟩
  · exact Or.inr ⟨rfl, fun h => hq (h hp)⟩
  · exact Or.inl ⟨rfl, fun hp' => absurd hp' hp⟩
  · exact Or.inl ⟨rfl, fun hp' => absurd hp' hp⟩

theorem dxor {a b : V} {P Q : Prop} (ha : Decided a P) (hb : Decided b Q) :
    Decided (V.zxor a b) (¬ (P ↔ Q)) := by
  rcases ha with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · exact Or.inr ⟨rfl, fun hn => hn ⟨fun _ => hq, fun _ => hp⟩⟩
  · exact Or.inl ⟨rfl, fun hiff => hq (hiff.1 hp)⟩
  · exact Or.inl ⟨rfl, fun hiff => hp (hiff.2 hq)⟩
  · exact Or.inr ⟨rfl, fun hn =>
      hn ⟨fun hp' => absurd hp' hp, fun hq' => absurd hq' hq⟩⟩

theorem dxnor {a b : V} {P Q : Prop} (ha : Decided a P) (hb : Decided b Q) :
    Decided (V.zxnor a b) (P ↔ Q) := by
  rcases ha with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> rcases hb with ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · exact Or.inl ⟨rfl, ⟨fun _ => hq, fun _ => hp⟩⟩
  · exact Or.inr ⟨rfl, fun hiff => hq (hiff.1 hp)⟩
  · exact Or.inr ⟨rfl, fun hiff => hp (hiff.2 hq)⟩
  · exact Or.inl ⟨rfl, ⟨fun hp' => absurd hp' hp,
                        fun hq' => absurd hq' hq⟩⟩

end Decided

/-- **The fully-earned register is classical.** If every atom carries a
decided, truthful verdict, then the greedy ZTL value of EVERY formula
is decided and truthful: T exactly on the classically true formulas,
F exactly on the false ones, Z nowhere. Over verified identity atoms
the zero-trust connectives neither lie nor refuse. -/
theorem earned_register_classical {α : Type v} (env : α → V)
    (fact : α → Prop) (h : ∀ a, Decided (env a) (fact a)) :
    ∀ φ : Fm α, Decided (evalV env φ) (Truth fact φ)
  | .atom a   => h a
  | .not φ    => (earned_register_classical env fact h φ).dnot
  | .and φ ψ  => (earned_register_classical env fact h φ).dand
                   (earned_register_classical env fact h ψ)
  | .or φ ψ   => (earned_register_classical env fact h φ).dor
                   (earned_register_classical env fact h ψ)
  | .imp φ ψ  => (earned_register_classical env fact h φ).dimp
                   (earned_register_classical env fact h ψ)
  | .xor φ ψ  => (earned_register_classical env fact h φ).dxor
                   (earned_register_classical env fact h ψ)
  | .xnor φ ψ => (earned_register_classical env fact h φ).dxnor
                   (earned_register_classical env fact h ψ)

/-- Corollary: over a fully-earned register no formula refuses. -/
theorem earned_register_ne_Z {α : Type v} (env : α → V) (fact : α → Prop)
    (h : ∀ a, Decided (env a) (fact a)) (φ : Fm α) :
    evalV env φ ≠ V.Z := by
  rcases earned_register_classical env fact h φ with ⟨he, _⟩ | ⟨he, _⟩ <;>
    · rw [he]; exact fun hz => V.noConfusion hz

/-- Corollary: over a fully-earned register T means exactly truth. -/
theorem earned_register_T_iff {α : Type v} (env : α → V) (fact : α → Prop)
    (h : ∀ a, Decided (env a) (fact a)) (φ : Fm α) :
    evalV env φ = V.T ↔ Truth fact φ := by
  rcases earned_register_classical env fact h φ with ⟨he, hp⟩ | ⟨he, hp⟩
  · exact ⟨fun _ => hp, fun _ => he⟩
  · rw [he]
    exact ⟨fun hf => V.noConfusion hf, fun ht => absurd ht hp⟩

-- CHECKS: no sorry, no admit.

-- Axiom audit — MEASURED per object (VR discipline).
-- Target: [] for the verdict layer, [propext] where vn_inj enters.
#print axioms EqVerdict.val
#print axioms EqVerdict.sound_T
#print axioms EqVerdict.sound_F
#print axioms EqVerdict.refl_val
#print axioms EqVerdict.symm_val
#print axioms EqVerdict.composeT_val
#print axioms vnVerdict_ne_Z
#print axioms vnVerdict_T_iff
#print axioms quine_orthogonality
#print axioms quine_not_equiv_vn0
#print axioms quineVsEmpty_val
#print axioms earned_register_classical
#print axioms earned_register_ne_Z
#print axioms earned_register_T_iff

end VRCycle.SetsZTL
