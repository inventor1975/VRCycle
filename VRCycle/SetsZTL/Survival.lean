-- VRCycle/SetsZTL/Survival.lean
-- VR Part II, step (в): spot-checks of the survival criterion C2
-- (curator's decision 2026-07-12; the ledger is ZTL_SURVIVAL.md).
--
-- The criterion: a proof SURVIVES the move onto ZTL iff it stands
-- below the classical floor (no Classical.choice) — because ZTL's
-- fallen laws are exactly the laws of free truth, their Lean
-- fingerprint is classical case-splitting, and a constructive proof
-- from earned premises IS a chain of ZTL-alive rules, i.e. a witness
-- constructor (measured: E20 rules 14/14, E21 §3, E22 §1). The audit
-- bounds the given proof, never the theorem ("auditor, not
-- separator").
--
-- Here three flagship operational theorems are exhibited in the moved
-- form — as certificate constructors over ZTL atoms:
--   1. Strong extensionality (the heart of VR-Sets): from the
--      member-matching data the identity certificate is CONSTRUCTED —
--      `extVerdict`, earned T.
--   2. AFA-as-theorem: two decorations of one graph have EARNED
--      identity at every vertex — `afaVerdict`, earned T.
--   3. Membership itself becomes a carried verdict — `MemVerdict`
--      (closing the membership-atom gap of step (а)): the vn register
--      is total and classical, and earned ∈ transports along earned ≈
--      (`memCongrVerdict` — the rule form of `mem_congr`).
-- (Spot-check 4, the continuum apartness, already lives in
-- Stages.lean: `apart_earned`.)
--
-- Axiom profile: MEASURED at the bottom — the empty list throughout.

import VRCycle.SetsZTL.Atoms

namespace VRCycle.SetsZTL

open VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  Membership as a carried verdict
-- ============================================================

/-- A ZTL verdict on the membership atom `x ∈ y`, carried with its
certificate — the membership twin of `EqVerdict`. -/
inductive MemVerdict (x y : OpSet.{u}) : Type u where
  | earnedT (w : OpSet.Mem x y) : MemVerdict x y
  | earnedF (w : ¬ OpSet.Mem x y) : MemVerdict x y
  | unexamined : MemVerdict x y

namespace MemVerdict

def val {x y : OpSet.{u}} : MemVerdict x y → V
  | earnedT _  => V.T
  | earnedF _  => V.F
  | unexamined => V.Z

def sound_T {x y : OpSet.{u}} :
    (v : MemVerdict x y) → v.val = V.T → OpSet.Mem x y
  | earnedT w,  _ => w
  | earnedF _,  h => nomatch h
  | unexamined, h => nomatch h

def sound_F {x y : OpSet.{u}} :
    (v : MemVerdict x y) → v.val = V.F → ¬ OpSet.Mem x y
  | earnedF w,  _ => w
  | earnedT _,  h => nomatch h
  | unexamined, h => nomatch h

end MemVerdict

/-- The vn membership register is TOTAL and CLASSICAL: every membership
atom of the operational naturals decides — T with the constructed chain
for k < m, F by the membership law plus distinctness otherwise. -/
def vnMemVerdict (k m : Nat) : MemVerdict (OpSet.vn k) (OpSet.vn m) :=
  if h : k < m then
    MemVerdict.earnedT (OpSet.vn_lt_mem h)
  else
    MemVerdict.earnedF (fun hmem => by
      obtain ⟨j, hj, he⟩ := (OpSet.vn_mem_iff _ m).1 hmem
      exact h (by rw [OpSet.vn_inj he]; exact hj))

theorem vnMemVerdict_ne_Z (k m : Nat) : (vnMemVerdict k m).val ≠ V.Z := by
  unfold vnMemVerdict
  split
  · exact fun h => V.noConfusion h
  · exact fun h => V.noConfusion h

theorem vnMemVerdict_T_iff (k m : Nat) :
    (vnMemVerdict k m).val = V.T ↔ k < m := by
  unfold vnMemVerdict
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hv => V.noConfusion hv, fun hk => absurd hk h⟩

/-- Earned membership transports along earned identity — the
witness-constructor (rule) form of `mem_congr`: two carried
certificates yield the third. -/
def memCongrVerdict {x y z : OpSet.{u}} (v : EqVerdict x y)
    (w : MemVerdict z x) (hv : v.val = V.T) (hw : w.val = V.T) :
    MemVerdict z y :=
  MemVerdict.earnedT (OpSet.mem_congr (v.sound_T hv) (w.sound_T hw))

theorem memCongrVerdict_val {x y z : OpSet.{u}} (v : EqVerdict x y)
    (w : MemVerdict z x) (hv : v.val = V.T) (hw : w.val = V.T) :
    (memCongrVerdict v w hv hw).val = V.T := rfl

-- ============================================================
-- §2.  Spot-check: strong extensionality moves
-- ============================================================

/-- **Strong extensionality, moved.** In the classical register
extensionality is a LAW (a biconditional over all z); operationally it
is a RULE: from the member-matching data the identity certificate is
constructed (`OpSet.ext` builds the bisimulation). Premised, earned,
choice-free — it survives verbatim. -/
def extVerdict {x y : OpSet.{u}} (h : ∀ z : OpSet.{u}, z.Mem x ↔ z.Mem y) :
    EqVerdict x y :=
  EqVerdict.earnedT (OpSet.ext h)

theorem extVerdict_val {x y : OpSet.{u}}
    (h : ∀ z : OpSet.{u}, z.Mem x ↔ z.Mem y) :
    (extVerdict h).val = V.T := rfl

-- ============================================================
-- §3.  Spot-check: AFA-as-theorem moves
-- ============================================================

/-- **AFA uniqueness, moved.** Any two decorations of one graph carry
EARNED identity at every vertex: the certificate is the composed
bisimulation of `decoration_unique`. The non-well-founded universe
moves onto ZTL with its identities earned, not postulated. -/
def afaVerdict {G : Type u} {E : G → G → Prop} {d d' : G → OpSet.{u}}
    (hd : IsDecoration E d) (hd' : IsDecoration E d')
    (v : G) : EqVerdict (d v) (d' v) :=
  EqVerdict.earnedT (OpSet.decoration_unique hd hd' v)

theorem afaVerdict_val {G : Type u} {E : G → G → Prop}
    {d d' : G → OpSet.{u}} (hd : IsDecoration E d)
    (hd' : IsDecoration E d') (v : G) :
    (afaVerdict hd hd' v).val = V.T := rfl

-- CHECKS: no sorry, no admit.

-- Axiom audit — MEASURED per object (VR discipline). Target: [].
#print axioms MemVerdict.val
#print axioms MemVerdict.sound_T
#print axioms MemVerdict.sound_F
#print axioms vnMemVerdict_ne_Z
#print axioms vnMemVerdict_T_iff
#print axioms memCongrVerdict_val
#print axioms extVerdict_val
#print axioms afaVerdict_val

end VRCycle.SetsZTL
