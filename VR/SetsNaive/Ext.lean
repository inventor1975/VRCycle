-- VR/SetsNaive/Ext.lean
-- VR-Sets, naive edition — Stage N5: EXTENSIONALITY as a congruence of the grounded register.
--
-- Naive comprehension and extensionality have a bad history (Gilmore: partial set theory is
-- consistent without extensionality and inconsistent with it, as an object-language axiom with
-- a substitutive `=`; Grishin: in contraction-free logic extensionality brings contraction
-- back).  Here identity is NOT put into the object language.  It is asked as a META question
-- about the model: if two sets have the same three-valued extension — every member-wise
-- verdict carried over, members compared up to the same relation — are they indiscernible by
-- EVERY naive formula?
--
-- Machine-checked here:
--   * `TC`/`FC` — the congruence closure of a relation ρ on terms through the whole syntax;
--     `FC.subst` — it commutes with substitution (for ρ-pairs inert under substitution);
--   * `val_cong` — **extensionality as a congruence**: if ρ is co-extensional (`Ext ρ`), every
--     grounded verdict is carried along the closure — T to T, F to F (and so Z to Z when ρ is
--     symmetric too);
--   * `E_E'_indiscernible` — two syntactically different clean empty sets `{x : ¬⊤}` and
--     `{x : ¬(x∈V)}` are indiscernible by every formula, both ways;
--   * the boundary: the clean ∅ and the DIRTY set `D` are NOT co-extensional, and they are
--     discerned (`Bridge.carrier_forgets_mark`) — the mark is part of the extension.
-- What is NOT claimed: an object-language `=` with substitutivity — Gilmore's setting — is not
-- treated here.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Bridge

namespace VRCycle.SetsNaive

set_option genInjectivity false

mutual
inductive TC (ρ : Tm → Tm → Prop) : Tm → Tm → Prop where
  | base {s s'} : ρ s s' → TC ρ s s'
  | var (n : Nat) : TC ρ (.var n) (.var n)
  | abs {φ φ'} : FC ρ φ φ' → TC ρ (.abs φ) (.abs φ')
inductive FC (ρ : Tm → Tm → Prop) : Fm → Fm → Prop where
  | top : FC ρ .top .top
  | mem {a a' b b'} : TC ρ a a' → TC ρ b b' → FC ρ (.mem a b) (.mem a' b')
  | neg {φ φ'} : FC ρ φ φ' → FC ρ (.neg φ) (.neg φ')
  | and {φ φ' ψ ψ'} : FC ρ φ φ' → FC ρ ψ ψ' → FC ρ (.and φ ψ) (.and φ' ψ')
  | all {φ φ'} : FC ρ φ φ' → FC ρ (.all φ) (.all φ')
end

/-- ρ-pairs are inert under substitution (closed terms). -/
def Inert (ρ : Tm → Tm → Prop) : Prop :=
  ∀ s s', ρ s s' → ∀ k c, Tm.subst k c s = s ∧ Tm.subst k c s' = s'

mutual
theorem TC.subst {ρ} (hρ : Inert ρ) {c c'} (hc : TC ρ c c') :
    ∀ {t t'} (k : Nat), TC ρ t t' → TC ρ (Tm.subst k c t) (Tm.subst k c' t')
  | _, _, k, .base h => by
      have e := hρ _ _ h k c; have e' := hρ _ _ h k c'
      rw [e.1, e'.2]; exact .base h
  | _, _, k, .var n => by
      show TC ρ (if n = k then c else .var n) (if n = k then c' else .var n)
      by_cases h : n = k
      · rw [if_pos h, if_pos h]; exact hc
      · rw [if_neg h, if_neg h]; exact .var n
  | _, _, k, .abs h => .abs (FC.subst hρ hc (k+1) h)
theorem FC.subst {ρ} (hρ : Inert ρ) {c c'} (hc : TC ρ c c') :
    ∀ {φ φ'} (k : Nat), FC ρ φ φ' → FC ρ (φ.subst k c) (φ'.subst k c')
  | _, _, _, .top => .top
  | _, _, k, .mem ha hb => .mem (TC.subst hρ hc k ha) (TC.subst hρ hc k hb)
  | _, _, k, .neg h => .neg (FC.subst hρ hc k h)
  | _, _, k, .and h1 h2 => .and (FC.subst hρ hc k h1) (FC.subst hρ hc k h2)
  | _, _, k, .all h => .all (FC.subst hρ hc (k+1) h)
end


mutual
theorem TC.refl (ρ : Tm → Tm → Prop) : ∀ t : Tm, TC ρ t t
  | .var n => .var n
  | .abs φ => .abs (FC.refl ρ φ)
theorem FC.refl (ρ : Tm → Tm → Prop) : ∀ φ : Fm, FC ρ φ φ
  | .top => .top
  | .mem a b => .mem (TC.refl ρ a) (TC.refl ρ b)
  | .neg φ => .neg (FC.refl ρ φ)
  | .and φ ψ => .and (FC.refl ρ φ) (FC.refl ρ ψ)
  | .all φ => .all (FC.refl ρ φ)
end

/-- ρ is **co-extensional**: a ρ-pair carries every grounded membership verdict, members
compared up to the closure. -/
def Ext (ρ : Tm → Tm → Prop) : Prop :=
  ∀ s s', ρ s s' → ∀ a a', TC ρ a a' → ∀ b, Val b (.mem a s) → Val b (.mem a' s')

/-- **Extensionality as a congruence**: along a co-extensional relation, every grounded
verdict is carried through every formula. -/
theorem val_cong {ρ : Tm → Tm → Prop} (hρ : Inert ρ) (H : Ext ρ) :
    ∀ {b φ}, Val b φ → ∀ {ψ}, FC ρ φ ψ → Val b ψ := by
  intro b φ h
  induction h with
  | top => intro ψ hψ; cases hψ; exact .top
  | @memT a φ h ih =>
      intro ψ hψ
      cases hψ with
      | mem ha hb =>
        cases hb with
        | base hr => exact H _ _ hr _ _ ha true (.memT h)
        | abs hφ => exact .memT (ih (FC.subst hρ ha 0 hφ))
  | @memF a φ h ih =>
      intro ψ hψ
      cases hψ with
      | mem ha hb =>
        cases hb with
        | base hr => exact H _ _ hr _ _ ha false (.memF h)
        | abs hφ => exact .memF (ih (FC.subst hρ ha 0 hφ))
  | negT _ ih => intro ψ hψ; cases hψ with | neg h' => exact .negT (ih h')
  | negF _ ih => intro ψ hψ; cases hψ with | neg h' => exact .negF (ih h')
  | andT _ _ ih1 ih2 => intro ψ hψ; cases hψ with | and h1 h2 => exact .andT (ih1 h1) (ih2 h2)
  | andFl _ ih => intro ψ hψ; cases hψ with | and h1 _ => exact .andFl (ih h1)
  | andFr _ ih => intro ψ hψ; cases hψ with | and _ h2 => exact .andFr (ih h2)
  | allT _ ih =>
      intro ψ hψ
      cases hψ with
      | all h' => exact .allT (fun c hc => ih c hc (FC.subst hρ (TC.refl ρ c) 0 h'))
  | allF c hc _ ih =>
      intro ψ hψ
      cases hψ with
      | all h' => exact .allF c hc (ih (FC.subst hρ (TC.refl ρ c) 0 h'))

/-- **Indiscernibility**: substituting a ρ-partner into any context carries every verdict. -/
theorem indiscernible {ρ : Tm → Tm → Prop} (hρ : Inert ρ) (H : Ext ρ) {s s' : Tm}
    (hs : ρ s s') (χ : Fm) (b : Bool) : Val b (χ.inst s) → Val b (χ.inst s') :=
  fun h => val_cong hρ H h (FC.subst hρ (.base hs) 0 (FC.refl ρ χ))

/-! ## Two clean empty sets are one set -/

/-- A second clean empty set, `{x : ¬(x∈V)}`. -/
def E' : Tm := .abs (.neg (.mem x0 V))

theorem E_inert (k : Nat) (c : Tm) : Tm.subst k c E = E := rfl
theorem E'_inert (k : Nat) (c : Tm) : Tm.subst k c E' = E' := by
  show Tm.abs (.neg (.mem (Tm.subst (k + 1) c (.var 0)) V)) = E'
  show Tm.abs (.neg (.mem (if 0 = k + 1 then c else .var 0) V)) = E'
  have hne : ¬ (0 = k + 1) := fun h => Nat.noConfusion h  -- not `Nat.succ_ne_zero`: it carries propext
  rw [if_neg hne]
  rfl

theorem E'_no_member (a : Tm) : ¬ Val true (.mem a E') := by
  intro h
  cases h with | memT h => cases h with | negT h => cases h with | memF h => cases h

/-- The pair (E, E'). -/
def rEE' : Tm → Tm → Prop := fun s s' => s = E ∧ s' = E'
/-- The pair (E', E). -/
def rE'E : Tm → Tm → Prop := fun s s' => s = E' ∧ s' = E

theorem inert_EE' : Inert rEE' := by
  intro s s' h k c; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨E_inert k c, E'_inert k c⟩
theorem inert_E'E : Inert rE'E := by
  intro s s' h k c; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨E'_inert k c, E_inert k c⟩

theorem ext_EE' : Ext rEE' := by
  intro s s' h a a' _ b hv
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2
  cases b with
  | true => exact absurd hv (E_no_member a)
  | false => exact .memF (.negF (.memT .top))

theorem ext_E'E : Ext rE'E := by
  intro s s' h a a' _ b hv
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2
  cases b with
  | true => exact absurd hv (E'_no_member a)
  | false => exact .memF (.negF .top)

/-- **The two clean empty sets are indiscernible by every naive formula**, both ways. -/
theorem E_E'_indiscernible (χ : Fm) (b : Bool) : Val b (χ.inst E) ↔ Val b (χ.inst E') :=
  ⟨indiscernible inert_EE' ext_EE' ⟨rfl, rfl⟩ χ b,
   indiscernible inert_E'E ext_E'E ⟨rfl, rfl⟩ χ b⟩

/-- **The boundary**: the clean ∅ and the dirty set are NOT co-extensional — `E` has the
earned non-member `E`, `D` has no earned non-member at all. -/
theorem E_D_not_coextensional : ¬ Ext (fun s s' => s = E ∧ s' = D) := by
  intro H
  have : Val false (.mem E D) :=
    H E D ⟨rfl, rfl⟩ E E (TC.refl _ E) false (.memF (.negF .top))
  cases this with | memF h => exact russell_quarantine false h

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.FC.subst
#print axioms VRCycle.SetsNaive.val_cong
#print axioms VRCycle.SetsNaive.indiscernible
#print axioms VRCycle.SetsNaive.E_E'_indiscernible
#print axioms VRCycle.SetsNaive.E_D_not_coextensional
