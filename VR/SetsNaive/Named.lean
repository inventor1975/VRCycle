-- VR/SetsNaive/Named.lean
-- VR-Sets, naive edition — Stage N11: the BRIDGE carrier → naive language.  Naive comprehension
-- over NAMES of operational sets: a term `nm X` names an `OpSet` of SetsOp, and an identity atom
-- `a ≈ b` joins the language.  The values of the atoms between NAMES come from the carrier —
-- membership `OpSet.Mem`, identity `OpSet.Equiv` (witnessed bisimulation) — fixed in advance, so
-- the jump stays monotone and nothing is circular.  An atom with a naive (non-name) side is not
-- examined by the carrier: Z.
--
-- Machine-checked here:
--   * `nconsistent`, `ncomprehension` — the naive laws survive the extension;
--   * `reflect_mem` / `reflect_eq` — on names the language REFLECTS the carrier exactly;
--   * `seg_reflects` — the naive segment `seg n = {x : x ≈ 0 ∨ … ∨ x ≈ n−1}` (over the carrier's
--     numerals) has EARNED membership at every carrier numeral, exactly as `vn n`: k ∈ seg n is T
--     iff (vn k) ∈ (vn n), F otherwise.  The wall of N10 (1 ∈ 2 quarantined) is gone ON CARRIER
--     PROBES: identity is supplied by the carrier, not by the unbounded `≐`;
--   * `omega_named` — every carrier numeral is an earned member of the named ω;
--   * `quine_named` — the carrier's Ω: `Ω ∈ Ω` and `Ω ≈ Ω` EARNED, while the naive truth-teller
--     set S∈S is UNDERDETERMINED (N3): the carrier supplies the stipulation (AFA) that naive
--     comprehension leaves open.
-- What is NOT done: identifying a naive TERM with a carrier set (an atom `{x : φ} ≈ nm X` stays Z).
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Numerals

namespace VRCycle.SetsNaive

open VRCycle.SetsOp

set_option genInjectivity false

mutual
/-- Terms: variables, set abstracts, and NAMES of operational sets. -/
inductive NTm where
  | var : Nat → NTm
  | abs : NFm → NTm
  | nm : OpSet.{0} → NTm
/-- Formulas, now with an identity atom. -/
inductive NFm where
  | top : NFm
  | mem : NTm → NTm → NFm
  | eq : NTm → NTm → NFm
  | neg : NFm → NFm
  | and : NFm → NFm → NFm
  | all : NFm → NFm
end

mutual
def NTm.subst (k : Nat) (c : NTm) : NTm → NTm
  | .var n => if n = k then c else .var n
  | .abs φ => .abs (NFm.subst (k + 1) c φ)
  | .nm X => .nm X
def NFm.subst (k : Nat) (c : NTm) : NFm → NFm
  | .top => .top
  | .mem a b => .mem (NTm.subst k c a) (NTm.subst k c b)
  | .eq a b => .eq (NTm.subst k c a) (NTm.subst k c b)
  | .neg φ => .neg (NFm.subst k c φ)
  | .and φ ψ => .and (NFm.subst k c φ) (NFm.subst k c ψ)
  | .all φ => .all (NFm.subst (k + 1) c φ)
end

abbrev NFm.inst (φ : NFm) (c : NTm) : NFm := φ.subst 0 c

mutual
def NTm.closedAt (d : Nat) : NTm → Bool
  | .var n => Nat.blt n d
  | .abs φ => NFm.closedAt (d + 1) φ
  | .nm _ => true
def NFm.closedAt (d : Nat) : NFm → Bool
  | .top => true
  | .mem a b => NTm.closedAt d a && NTm.closedAt d b
  | .eq a b => NTm.closedAt d a && NTm.closedAt d b
  | .neg φ => NFm.closedAt d φ
  | .and φ ψ => NFm.closedAt d φ && NFm.closedAt d ψ
  | .all φ => NFm.closedAt (d + 1) φ
end

def NCl (t : NTm) : Prop := NTm.closedAt 0 t = true

mutual
theorem NTm.subst_closed (c : NTm) : ∀ (t : NTm) (d k : Nat),
    NTm.closedAt d t = true → Nat.ble d k = true → NTm.subst k c t = t
  | .var n, d, k, h, hk => by
      show (if n = k then c else .var n) = .var n
      have hne : ¬ (n = k) := fun e => by subst e; exact blt_ble_absurd n d h hk
      rw [if_neg hne]
  | .abs φ, d, k, h, hk => by
      show NTm.abs (NFm.subst (k + 1) c φ) = .abs φ
      rw [NFm.subst_closed c φ (d + 1) (k + 1) h hk]
  | .nm _, _, _, _, _ => rfl
theorem NFm.subst_closed (c : NTm) : ∀ (φ : NFm) (d k : Nat),
    NFm.closedAt d φ = true → Nat.ble d k = true → NFm.subst k c φ = φ
  | .top, _, _, _, _ => rfl
  | .mem a b, d, k, h, hk => by
      show NFm.mem (NTm.subst k c a) (NTm.subst k c b) = .mem a b
      rw [NTm.subst_closed c a d k (band_l h) hk, NTm.subst_closed c b d k (band_r h) hk]
  | .eq a b, d, k, h, hk => by
      show NFm.eq (NTm.subst k c a) (NTm.subst k c b) = .eq a b
      rw [NTm.subst_closed c a d k (band_l h) hk, NTm.subst_closed c b d k (band_r h) hk]
  | .neg φ, d, k, h, hk => by
      show NFm.neg (NFm.subst k c φ) = .neg φ
      rw [NFm.subst_closed c φ d k h hk]
  | .and φ ψ, d, k, h, hk => by
      show NFm.and (NFm.subst k c φ) (NFm.subst k c ψ) = .and φ ψ
      rw [NFm.subst_closed c φ d k (band_l h) hk, NFm.subst_closed c ψ d k (band_r h) hk]
  | .all φ, d, k, h, hk => by
      show NFm.all (NFm.subst (k + 1) c φ) = .all φ
      rw [NFm.subst_closed c φ (d + 1) (k + 1) h hk]
end

theorem NCl.subst {t : NTm} (h : NCl t) (k : Nat) (c : NTm) : NTm.subst k c t = t :=
  NTm.subst_closed c t 0 k h (ble_zero k)

/-- The grounded register of the named language. -/
inductive NVal : Bool → NFm → Prop where
  | top : NVal true .top
  | memT {a φ} : NVal true (φ.inst a) → NVal true (.mem a (.abs φ))
  | memF {a φ} : NVal false (φ.inst a) → NVal false (.mem a (.abs φ))
  | memNT {X Y : OpSet.{0}} : X.Mem Y → NVal true (.mem (.nm X) (.nm Y))
  | memNF {X Y : OpSet.{0}} : ¬ X.Mem Y → NVal false (.mem (.nm X) (.nm Y))
  | eqNT {X Y : OpSet.{0}} : X.Equiv Y → NVal true (.eq (.nm X) (.nm Y))
  | eqNF {X Y : OpSet.{0}} : ¬ X.Equiv Y → NVal false (.eq (.nm X) (.nm Y))
  | negT {φ} : NVal false φ → NVal true (.neg φ)
  | negF {φ} : NVal true φ → NVal false (.neg φ)
  | andT {φ ψ} : NVal true φ → NVal true ψ → NVal true (.and φ ψ)
  | andFl {φ ψ} : NVal false φ → NVal false (.and φ ψ)
  | andFr {φ ψ} : NVal false ψ → NVal false (.and φ ψ)
  | allT {φ} : (∀ c, NCl c → NVal true (φ.inst c)) → NVal true (.all φ)
  | allF {φ} (c : NTm) : NCl c → NVal false (φ.inst c) → NVal false (.all φ)

/-- Consistency survives the extension. -/
theorem nconsistent : ∀ {b φ}, NVal b φ → NVal (!b) φ → False := by
  intro b φ h
  induction h with
  | top => intro h'; cases h'
  | memT _ ih => intro h'; cases h' with | memF h'' => exact ih h''
  | memF _ ih => intro h'; cases h' with | memT h'' => exact ih h''
  | memNT h => intro h'; cases h' with | memNF h'' => exact h'' h
  | memNF h => intro h'; cases h' with | memNT h'' => exact h h''
  | eqNT h => intro h'; cases h' with | eqNF h'' => exact h'' h
  | eqNF h => intro h'; cases h' with | eqNT h'' => exact h h''
  | negT _ ih => intro h'; cases h' with | negF h'' => exact ih h''
  | negF _ ih => intro h'; cases h' with | negT h'' => exact ih h''
  | andT _ _ ih1 ih2 => intro h'; cases h' with
      | andFl h'' => exact ih1 h''
      | andFr h'' => exact ih2 h''
  | andFl _ ih => intro h'; cases h' with | andT h'' _ => exact ih h''
  | andFr _ ih => intro h'; cases h' with | andT _ h'' => exact ih h''
  | allT _ ih => intro h'; cases h' with | allF c hc h'' => exact ih c hc h''
  | allF c hc _ ih => intro h'; cases h' with | allT h'' => exact ih (h'' c hc)

/-- Naive comprehension is still a law in every cell. -/
theorem ncomprehension (b : Bool) (a : NTm) (φ : NFm) :
    NVal b (.mem a (.abs φ)) ↔ NVal b (φ.inst a) := by
  constructor
  · intro h
    cases b with
    | true => cases h with | memT h => exact h
    | false => cases h with | memF h => exact h
  · intro h
    cases b with
    | true => exact .memT h
    | false => exact .memF h

/-- **On names the language reflects the carrier**: membership… -/
theorem reflect_mem (X Y : OpSet.{0}) :
    (NVal true (.mem (.nm X) (.nm Y)) ↔ X.Mem Y) ∧ (NVal false (.mem (.nm X) (.nm Y)) ↔ ¬ X.Mem Y) :=
  ⟨⟨fun h => by cases h with | memNT h => exact h, .memNT⟩,
   ⟨fun h => by cases h with | memNF h => exact h, .memNF⟩⟩

/-- …and identity. -/
theorem reflect_eq (X Y : OpSet.{0}) :
    (NVal true (.eq (.nm X) (.nm Y)) ↔ X.Equiv Y) ∧ (NVal false (.eq (.nm X) (.nm Y)) ↔ ¬ X.Equiv Y) :=
  ⟨⟨fun h => by cases h with | eqNT h => exact h, .eqNT⟩,
   ⟨fun h => by cases h with | eqNF h => exact h, .eqNF⟩⟩

/-! ## The carrier's numerals in the naive language -/

/-- The name of the carrier numeral `n`. -/
def N (n : Nat) : NTm := .nm (OpSet.vn n)

def NFm.or (φ ψ : NFm) : NFm := .neg (.and (.neg φ) (.neg ψ))

/-- `x ≈ 0 ∨ … ∨ x ≈ n−1` (x = index 0). -/
def segBody : Nat → NFm
  | 0 => .neg .top
  | n + 1 => NFm.or (segBody n) (.eq (.var 0) (N n))

/-- The naive segment `{x : x ≈ 0 ∨ … ∨ x ≈ n−1}`. -/
def seg (n : Nat) : NTm := .abs (segBody n)

theorem segBody_inst (n : Nat) (c : NTm) :
    (segBody (n + 1)).inst c = NFm.or ((segBody n).inst c) (.eq c (N n)) := rfl

/-! ## Boolean `Nat` order, hand-rolled (the core order lemmas carry propext) -/

theorem blt_zero_false (k : Nat) : ¬ Nat.blt k 0 = true := fun h => Bool.noConfusion h

theorem ble_refl : ∀ k : Nat, Nat.ble k k = true
  | 0 => rfl
  | k + 1 => ble_refl k

theorem blt_self_succ (k : Nat) : Nat.blt k (k + 1) = true := ble_refl k

theorem ble_succ_right : ∀ a b : Nat, Nat.ble a b = true → Nat.ble a (b + 1) = true
  | 0, b, _ => ble_zero (b + 1)
  | _ + 1, 0, h => Bool.noConfusion h
  | a + 1, b + 1, h => ble_succ_right a b h

theorem blt_succ_of_blt (k n : Nat) (h : Nat.blt k n = true) : Nat.blt k (n + 1) = true :=
  ble_succ_right (k + 1) n h

theorem ble_cases : ∀ k n : Nat, Nat.ble k n = true → Nat.ble (k + 1) n = true ∨ k = n
  | 0, 0, _ => Or.inr rfl
  | 0, n + 1, _ => Or.inl (ble_zero n)
  | _ + 1, 0, h => Bool.noConfusion h
  | k + 1, n + 1, h =>
      match ble_cases k n h with
      | Or.inl h => Or.inl h
      | Or.inr e => Or.inr (congrArg (· + 1) e)

theorem blt_succ_cases (k n : Nat) (h : Nat.blt k (n + 1) = true) : Nat.blt k n = true ∨ k = n :=
  ble_cases k n h

/-- Boolean `<` on the carrier side: `vn k ∈ vn n` iff `k < n` (as `Nat.blt`). -/
theorem vn_mem_iff : ∀ (n k : Nat),
    ((OpSet.vn k).Mem (OpSet.vn n) → Nat.blt k n = true) ∧
    (Nat.blt k n = true → (OpSet.vn k).Mem (OpSet.vn n))
  | 0, k => ⟨fun h => absurd h (OpSet.not_mem_emptySup _), fun h => absurd h (blt_zero_false k)⟩
  | n + 1, k => by
      have ih := vn_mem_iff n k
      constructor
      · intro h
        cases (OpSet.mem_succ (OpSet.vn k) (OpSet.vn n)).1 h with
        | inl h => exact blt_succ_of_blt k n (ih.1 h)
        | inr h => have e := OpSet.vn_inj h; subst e; exact blt_self_succ k
      · intro h
        apply (OpSet.mem_succ (OpSet.vn k) (OpSet.vn n)).2
        cases blt_succ_cases k n h with
        | inl h => exact Or.inl (ih.2 h)
        | inr e => subst e; exact Or.inr (OpSet.Equiv.refl _)

/-- **The naive segment reflects the carrier numeral** on every carrier numeral probe: EARNED
membership exactly where `k < n`, EARNED non-membership elsewhere. -/
theorem seg_decides : ∀ (n k : Nat),
    (Nat.blt k n = true → NVal true (.mem (N k) (seg n))) ∧
    (Nat.blt k n = false → NVal false (.mem (N k) (seg n)))
  | 0, k => ⟨fun h => absurd h (blt_zero_false k), fun _ => .memF (.negF .top)⟩
  | n + 1, k => by
      have ih := seg_decides n k
      constructor
      · intro h
        apply NVal.memT
        rw [segBody_inst]
        apply NVal.negT
        cases blt_succ_cases k n h with
        | inl h => exact .andFl (.negF ((ncomprehension true _ _).1 (ih.1 h)))
        | inr e => subst e; exact .andFr (.negF (.eqNT (OpSet.Equiv.refl _)))
      · intro h
        apply NVal.memF
        rw [segBody_inst]
        apply NVal.negF
        have hn : Nat.blt k n = false := by
          cases hb : Nat.blt k n with
          | false => rfl
          | true => have := blt_succ_of_blt k n hb; rw [h] at this; exact Bool.noConfusion this
        have hne : ¬ k = n := by
          intro e; subst e; have := blt_self_succ k; rw [h] at this; exact Bool.noConfusion this
        exact .andT (.negT ((ncomprehension false _ _).1 (ih.2 hn)))
          (.negT (.eqNF (fun e => hne (OpSet.vn_inj e))))

/-- **Bridge theorem**: on carrier numerals, `k ∈ seg n` is EARNED exactly when `vn k ∈ vn n` in the
carrier, and REFUTED exactly when not. -/
theorem seg_reflects (n k : Nat) :
    (NVal true (.mem (N k) (seg n)) ↔ (OpSet.vn k).Mem (OpSet.vn n)) ∧
    (NVal false (.mem (N k) (seg n)) ↔ ¬ (OpSet.vn k).Mem (OpSet.vn n)) := by
  have hc := vn_mem_iff n k
  have hd := seg_decides n k
  constructor
  · constructor
    · intro h
      cases hb : Nat.blt k n with
      | true => exact hc.2 hb
      | false => exact absurd h (fun h => nconsistent (hd.2 hb) h)
    · intro h; exact hd.1 (hc.1 h)
  · constructor
    · intro h hm; exact nconsistent (hd.1 (hc.1 hm)) h
    · intro h
      cases hb : Nat.blt k n with
      | true => exact absurd (hc.2 hb) h
      | false => exact hd.2 hb

/-- N10's wall is gone on carrier probes: `1 ∈ seg 2` is EARNED. -/
theorem one_in_seg_two : NVal true (.mem (N 1) (seg 2)) := (seg_decides 2 1).1 rfl

/-- Every carrier numeral is an earned member of the named ω. -/
theorem omega_named (k : Nat) : NVal true (.mem (N k) (.nm OpSet.omega)) :=
  .memNT ((OpSet.mem_omega _).2 ⟨k, OpSet.Equiv.refl _⟩)

/-! ## The carrier supplies the stipulation naive comprehension leaves open -/

/-- The name of the carrier's Quine atom Ω = {Ω}. -/
def Om : NTm := .nm OpSet.quine.{0}

/-- **Ω ∈ Ω and Ω ≈ Ω are EARNED** — whereas the naive truth-teller set's `S ∈ S` is
UNDERDETERMINED (`S_underdetermined`): the carrier (AFA, a theorem of SetsOp) supplies the
stipulation. -/
theorem quine_named : NVal true (.mem Om Om) ∧ NVal true (.eq Om Om) ∧ Underdetermined (.mem S S) :=
  ⟨.memNT OpSet.quine_self_mem, .eqNT (OpSet.Equiv.refl _), S_underdetermined⟩

/-! ## The boundary: a naive term is not identified with a carrier set -/

/-- The naive empty set of the named language. -/
def NE : NTm := .abs (.neg .top)

/-- `NE ∈ seg 1` is quarantined: the identity atom `NE ≈ 0` has a naive side and is not examined
by the carrier.  Identifying naive terms with carrier sets is the open next step. -/
theorem naive_not_identified (b : Bool) : ¬ NVal b (.mem NE (seg 1)) := by
  intro h
  cases b with
  | true =>
    cases h with
    | memT h =>
      rw [segBody_inst] at h
      cases h with
      | negT h =>
        cases h with
        | andFl h => cases h with | negF h => cases h with | negT h => cases h
        | andFr h => cases h with | negF h => cases h
  | false =>
    cases h with
    | memF h =>
      rw [segBody_inst] at h
      cases h with
      | negF h => cases h with | andT _ h2 => cases h2 with | negT h2 => cases h2

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.nconsistent
#print axioms VRCycle.SetsNaive.ncomprehension
#print axioms VRCycle.SetsNaive.reflect_mem
#print axioms VRCycle.SetsNaive.reflect_eq
#print axioms VRCycle.SetsNaive.vn_mem_iff
#print axioms VRCycle.SetsNaive.seg_reflects
#print axioms VRCycle.SetsNaive.one_in_seg_two
#print axioms VRCycle.SetsNaive.omega_named
#print axioms VRCycle.SetsNaive.quine_named
#print axioms VRCycle.SetsNaive.naive_not_identified
