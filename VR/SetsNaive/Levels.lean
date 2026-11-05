-- VR/SetsNaive/Levels.lean
-- VR-Sets, naive edition — Stage N12: the LEVELS attempt at native identity, measured honestly.
--
-- The idea (2026-11-05): identity cannot be earned while the graph grows, so earn it a level
-- later.  Level 0 is the language with the identity atom unexamined; level n+1 values the atom
-- `x ≈ y` from the COMPLETE level-n verdicts: T if x and y have the same signed extension at level
-- n (every probe: T where T, F where F), F if some probe is decided oppositely.  Probes range over
-- all closed terms — so the language stays naive (R, V, x∈x all expressible).
--
-- Measured here (`revoked`): the identity verdict is NOT monotone across levels.  With
-- `x = {z : z ≈ ∅}` and `y = {z : z ≈ V}`, at level 0 every membership in either is unexamined, so
-- they have the same signed extension and `x ≈ y` is EARNED at level 1; at level 1, `∅ ∈ x` is T
-- and `∅ ∈ y` is F, so `x ≈ y` is REFUTED at level 2.  An earned identity is revoked.
--
-- The diagnosis: "same signed extension" counts Z against Z as agreement — identity earned THROUGH
-- THE MARK, which ZTL forbids (`ZEqGeneric`: equality is never earned through a mark).  The
-- ZTL-correct sameness demands decided agreement at every probe — and that is N10: only trivial
-- sets.  The third exit — probes of LOWER level only — is monotone but is Russell's type theory:
-- `x ∈ x` is ill-formed, naivety is lost (by construction; not formalised here).
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Named

namespace VRCycle.SetsNaive.Lv

set_option genInjectivity false

mutual
inductive ETm where
  | var : Nat → ETm
  | abs : EFm → ETm
inductive EFm where
  | top : EFm
  | mem : ETm → ETm → EFm
  | eq : ETm → ETm → EFm
  | neg : EFm → EFm
  | and : EFm → EFm → EFm
  | all : EFm → EFm
end

mutual
def ETm.subst (k : Nat) (c : ETm) : ETm → ETm
  | .var n => if n = k then c else .var n
  | .abs φ => .abs (EFm.subst (k + 1) c φ)
def EFm.subst (k : Nat) (c : ETm) : EFm → EFm
  | .top => .top
  | .mem a b => .mem (ETm.subst k c a) (ETm.subst k c b)
  | .eq a b => .eq (ETm.subst k c a) (ETm.subst k c b)
  | .neg φ => .neg (EFm.subst k c φ)
  | .and φ ψ => .and (EFm.subst k c φ) (EFm.subst k c ψ)
  | .all φ => .all (EFm.subst (k + 1) c φ)
end

abbrev EFm.inst (φ : EFm) (c : ETm) : EFm := φ.subst 0 c

mutual
def ETm.closedAt (d : Nat) : ETm → Bool
  | .var n => Nat.blt n d
  | .abs φ => EFm.closedAt (d + 1) φ
def EFm.closedAt (d : Nat) : EFm → Bool
  | .top => true
  | .mem a b => ETm.closedAt d a && ETm.closedAt d b
  | .eq a b => ETm.closedAt d a && ETm.closedAt d b
  | .neg φ => EFm.closedAt d φ
  | .and φ ψ => EFm.closedAt d φ && EFm.closedAt d ψ
  | .all φ => EFm.closedAt (d + 1) φ
end

def ECl (t : ETm) : Prop := ETm.closedAt 0 t = true

/-- An identity oracle: which identity atoms are earned T, which earned F. -/
structure Oracle where
  eqT : ETm → ETm → Prop
  eqF : ETm → ETm → Prop

/-- The grounded register relative to an identity oracle. -/
inductive OVal (O : Oracle) : Bool → EFm → Prop where
  | top : OVal O true .top
  | memT {a φ} : OVal O true (φ.inst a) → OVal O true (.mem a (.abs φ))
  | memF {a φ} : OVal O false (φ.inst a) → OVal O false (.mem a (.abs φ))
  | eqT {a b} : O.eqT a b → OVal O true (.eq a b)
  | eqF {a b} : O.eqF a b → OVal O false (.eq a b)
  | negT {φ} : OVal O false φ → OVal O true (.neg φ)
  | negF {φ} : OVal O true φ → OVal O false (.neg φ)
  | andT {φ ψ} : OVal O true φ → OVal O true ψ → OVal O true (.and φ ψ)
  | andFl {φ ψ} : OVal O false φ → OVal O false (.and φ ψ)
  | andFr {φ ψ} : OVal O false ψ → OVal O false (.and φ ψ)
  | allT {φ} : (∀ c, ECl c → OVal O true (φ.inst c)) → OVal O true (.all φ)
  | allF {φ} (c : ETm) : ECl c → OVal O false (φ.inst c) → OVal O false (.all φ)

/-- Same signed extension at a level (Z against Z counts as agreement). -/
def SameExt (O : Oracle) (x y : ETm) : Prop :=
  ∀ z, ECl z → (OVal O true (.mem z x) ↔ OVal O true (.mem z y)) ∧
               (OVal O false (.mem z x) ↔ OVal O false (.mem z y))

/-- Apart at a level: some probe decided oppositely. -/
def Apart (O : Oracle) (x y : ETm) : Prop :=
  ∃ z, ECl z ∧ ((OVal O true (.mem z x) ∧ OVal O false (.mem z y)) ∨
                (OVal O false (.mem z x) ∧ OVal O true (.mem z y)))

/-- The levels: level 0 examines no identity; level n+1 reads identity off level n. -/
def level : Nat → Oracle
  | 0 => ⟨fun _ _ => False, fun _ _ => False⟩
  | n + 1 => ⟨SameExt (level n), Apart (level n)⟩

def eE : ETm := .abs (.neg .top)               -- ∅
def eV : ETm := .abs .top                       -- V
def ex : ETm := .abs (.eq (.var 0) eE)          -- {z : z ≈ ∅}
def ey : ETm := .abs (.eq (.var 0) eV)          -- {z : z ≈ V}

/-- At level 0 no membership in `ex` or `ey` is grounded (their bodies are identity atoms). -/
theorem level0_silent (z : ETm) (b : Bool) (t : ETm) (ht : t = ex ∨ t = ey) :
    ¬ OVal (level 0) b (.mem z t) := by
  intro h
  cases ht with
  | inl e => subst e; cases b with
    | true => cases h with | memT h => cases h with | eqT h => exact h
    | false => cases h with | memF h => cases h with | eqF h => exact h
  | inr e => subst e; cases b with
    | true => cases h with | memT h => cases h with | eqT h => exact h
    | false => cases h with | memF h => cases h with | eqF h => exact h

/-- **Level 1 earns `ex ≈ ey`**: same (empty) signed extension at level 0. -/
theorem level1_earns : OVal (level 1) true (.eq ex ey) := by
  apply OVal.eqT
  intro z _
  exact ⟨⟨fun h => absurd h (level0_silent z true ex (Or.inl rfl)),
          fun h => absurd h (level0_silent z true ey (Or.inr rfl))⟩,
         ⟨fun h => absurd h (level0_silent z false ex (Or.inl rfl)),
          fun h => absurd h (level0_silent z false ey (Or.inr rfl))⟩⟩

/-- At level 1: `∅ ∈ ex` is T (∅ ≈ ∅ at level 0)… -/
theorem level1_E_in_x : OVal (level 1) true (.mem eE ex) := by
  apply OVal.memT
  apply OVal.eqT
  intro z _
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- …and `∅ ∈ ey` is F (∅ and V apart at level 0: ∅ ∉ ∅, ∅ ∈ V). -/
theorem level1_E_in_y : OVal (level 1) false (.mem eE ey) := by
  apply OVal.memF
  apply OVal.eqF
  exact ⟨eE, rfl, Or.inr ⟨.memF (.negF .top), .memT .top⟩⟩

/-- **Revocation**: `ex ≈ ey` is EARNED at level 1 and REFUTED at level 2 — identity read off a
complete lower level, with Z-against-Z as agreement, is not monotone. -/
theorem revoked : OVal (level 1) true (.eq ex ey) ∧ OVal (level 2) false (.eq ex ey) :=
  ⟨level1_earns, .eqF ⟨eE, rfl, Or.inl ⟨level1_E_in_x, level1_E_in_y⟩⟩⟩

end VRCycle.SetsNaive.Lv

#print axioms VRCycle.SetsNaive.Lv.level1_earns
#print axioms VRCycle.SetsNaive.Lv.level1_E_in_x
#print axioms VRCycle.SetsNaive.Lv.level1_E_in_y
#print axioms VRCycle.SetsNaive.Lv.revoked
