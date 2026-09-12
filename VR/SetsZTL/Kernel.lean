-- VRCycle/SetsZTL/Kernel.lean
-- VR Part II — the ZTL value kernel, VENDORED.
--
-- Provenance (the pin of the stitch): this is the value core of
-- ZTL — Zero-Trust Logic, vendored verbatim (subset) from
--   github.com/inventor1975/ZTL  lean/ZTL.lean  @ 3c5ff34 (2026-07-12),
-- where the full corpus (tables, entailment, certified tableaux,
-- grounding) is machine-checked on the EMPTY axiom list. One small
-- file is vendored rather than lake-depended: the dependency direction
-- of Part II is one-way (ZTL never depends on VR), and the honesty of
-- the stitch is carried by this pin, not by build plumbing.
--
-- Values T/F (verdicts are two-valued) + the input mark Z; the
-- generating principle "truth is not granted on credit": a connective
-- returns T only if T is forced under every classical reading of Z.
-- No imports; target: empty axiom list (measured at the bottom).

namespace VRCycle.SetsZTL

inductive V where
  | T
  | F
  | Z
deriving DecidableEq, Repr

namespace V

/-- Classical readings of a value: Z reads both as truth and as falsehood. -/
def subs : V → List Bool
  | T => [true]
  | F => [false]
  | Z => [true, false]

/-- Lift of a unary classical connective: T only if T is forced
under every reading. -/
def lift1 (f : Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a) then T else F

/-- Lift of a binary classical connective (each occurrence of Z independent). -/
def lift2 (f : Bool → Bool → Bool) (x y : V) : V :=
  if (subs x).all (fun a => (subs y).all (fun b => f a b)) then T else F

def znot  : V → V     := lift1 (fun a => !a)
def zand  : V → V → V := lift2 (fun a b => a && b)
def zor   : V → V → V := lift2 (fun a b => a || b)
def zimp  : V → V → V := lift2 (fun a b => !a || b)
def zxor  : V → V → V := lift2 (fun a b => a != b)
def zxnor : V → V → V := lift2 (fun a b => a == b)

/-- The quarantine detector, expressible inside the language: isZ x = ¬(x↔x). -/
def isZ (x : V) : V := znot (zxnor x x)

/-- Enumeration of the three values is decidable. -/
instance (p : V → Prop) [DecidablePred p] : Decidable (∀ x : V, p x) :=
  decidable_of_iff (p T ∧ p F ∧ p Z)
    ⟨fun ⟨hT, hF, hZ⟩ x => by cases x <;> assumption,
     fun h => ⟨h T, h F, h Z⟩⟩

/-! ## The anchor cells (ZTL design axioms of 2026-07-10) — theorems here -/

theorem ax_not_Z    : znot Z = F := by decide
theorem ax_notnot_Z : znot (znot Z) = T := by decide
theorem ax_xnor_ZZ  : zxnor Z Z = F := by decide
theorem ax_xor_ZZ   : zxor Z Z = F := by decide

/-! ## Greediness: compound values are classical, Z lives only on atoms -/

theorem lift1_classical (f : Bool → Bool) (x : V) :
    lift1 f x = T ∨ lift1 f x = F := by
  unfold lift1; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem lift2_classical (f : Bool → Bool → Bool) (x y : V) :
    lift2 f x y = T ∨ lift2 f x y = F := by
  unfold lift2; split
  · exact Or.inl rfl
  · exact Or.inr rfl

end V

-- Axiom audit — MEASURED, not claimed (the vendored kernel must stand
-- on the empty list, as it does at home in the ZTL repository).
#print axioms V.znot
#print axioms V.ax_not_Z
#print axioms V.ax_xnor_ZZ
#print axioms V.lift2_classical

end VRCycle.SetsZTL
