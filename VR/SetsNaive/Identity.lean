-- VR/SetsNaive/Identity.lean
-- VR-Sets, naive edition — Stage N9: IDENTITY by extension (the curator's point 05.11: membership
-- cannot be checked without identity — xnor — and xnor cleans the verdicts).
--
-- Identity is not a new primitive: `a ≐ b := ∀z (z∈a ↔ z∈b)`, built from the language.
-- Gilmore's warning is exactly here: partial set theory with naive comprehension is consistent
-- without extensionality and inconsistent with it (a substitutive `=` as an object-language
-- axiom).  What this file measures is the version ZTL licenses: substitution through an EARNED
-- identity.
--
-- Machine-checked here:
--   * `eq_coext` — an earned identity carries every grounded membership verdict, both ways;
--   * `eq_cong` / `earned_eq_subst` — **an earned identity is substitutive**: replacing `a` by
--     `b` inside ANY closed formula carries every grounded verdict (T to T, F to F) — a META
--     theorem about the model.  Gilmore's axiom is an object-language SENTENCE ranging over all
--     sets, dirty ones included; whether that sentence is earned is NOT claimed here.  What holds
--     is the ZTL form: identity is substitutive where it is earned (cf. ZTL `ZEqGeneric`);
--   * the registers on identity:
--       – `E ≐ E'` (two clean empties) — EARNED;
--       – `D ≐ D` (the dirty set with itself) — quarantined in the lazy register, EARNED IF STABLE
--         under every completion; the greedy kernel value is xnor(Z,Z) = F — "not earned";
--       – `E ≐ D` (clean ∅ vs the dirty set) — quarantined lazily, OPEN under completions (`lem`):
--         the identity verdict KEEPS the mark the two-valued carrier forgot (`carrier_forgets_mark`
--         says the two are one OpSet).
--   So xnor cleans the VALUE (never Z), and the warrant — the disposition — carries the mark.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.Judge
import VR.ZTL.Kernel

namespace VRCycle.SetsNaive

set_option genInjectivity false

/-! ## Closedness under substitution (hand-rolled `Nat` order: the core lemmas carry propext) -/

theorem ble_succ_of_ne : ∀ n d : Nat, Nat.ble n d = true → ¬ (n = d) → Nat.ble (n + 1) d = true
  | 0, 0, _, h => absurd rfl h
  | 0, d + 1, _, _ => ble_zero d
  | _ + 1, 0, h, _ => Bool.noConfusion h
  | n + 1, d + 1, h, hne => ble_succ_of_ne n d h (fun e => hne (congrArg (· + 1) e))

theorem ble_trans : ∀ a b c : Nat, Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, c, _, _ => ble_zero c
  | _ + 1, 0, _, h, _ => Bool.noConfusion h
  | _ + 1, _ + 1, 0, _, h => Bool.noConfusion h
  | a + 1, b + 1, c + 1, h1, h2 => ble_trans a b c h1 h2

theorem band_intro : ∀ {x y : Bool}, x = true → y = true → (x && y) = true
  | true, true, _, _ => rfl

mutual
theorem Tm.closed_mono : ∀ (t : Tm) (d e : Nat), Tm.closedAt d t = true → Nat.ble d e = true →
    Tm.closedAt e t = true
  | .var n, d, e, h, hde => ble_trans (n + 1) d e h hde
  | .abs φ, d, e, h, hde => Fm.closed_mono φ (d + 1) (e + 1) h hde
theorem Fm.closed_mono : ∀ (φ : Fm) (d e : Nat), Fm.closedAt d φ = true → Nat.ble d e = true →
    Fm.closedAt e φ = true
  | .top, _, _, _, _ => rfl
  | .mem a b, d, e, h, hde =>
      band_intro (Tm.closed_mono a d e (band_l h) hde) (Tm.closed_mono b d e (band_r h) hde)
  | .neg φ, d, e, h, hde => Fm.closed_mono φ d e h hde
  | .and φ ψ, d, e, h, hde =>
      band_intro (Fm.closed_mono φ d e (band_l h) hde) (Fm.closed_mono ψ d e (band_r h) hde)
  | .all φ, d, e, h, hde => Fm.closed_mono φ (d + 1) (e + 1) h hde
end

theorem Cl.mono {c : Tm} (h : Cl c) (d : Nat) : Tm.closedAt d c = true :=
  Tm.closed_mono c 0 d h (ble_zero d)

mutual
/-- Substituting a closed term for the top index closes one level. -/
theorem Tm.closed_subst {c : Tm} (hc : Cl c) : ∀ (t : Tm) (d : Nat),
    Tm.closedAt (d + 1) t = true → Tm.closedAt d (Tm.subst d c t) = true
  | .var n, d, h => by
      show Tm.closedAt d (if n = d then c else .var n) = true
      by_cases e : n = d
      · rw [if_pos e]; exact Cl.mono hc d
      · rw [if_neg e]; exact ble_succ_of_ne n d h e
  | .abs φ, d, h => Fm.closed_subst hc φ (d + 1) h
theorem Fm.closed_subst {c : Tm} (hc : Cl c) : ∀ (φ : Fm) (d : Nat),
    Fm.closedAt (d + 1) φ = true → Fm.closedAt d (Fm.subst d c φ) = true
  | .top, _, _ => rfl
  | .mem a b, d, h => band_intro (Tm.closed_subst hc a d (band_l h)) (Tm.closed_subst hc b d (band_r h))
  | .neg φ, d, h => Fm.closed_subst hc φ d h
  | .and φ ψ, d, h => band_intro (Fm.closed_subst hc φ d (band_l h)) (Fm.closed_subst hc ψ d (band_r h))
  | .all φ, d, h => Fm.closed_subst hc φ (d + 1) h
end


mutual
/-- The congruence closure preserves closedness (when the ρ-pairs are closed). -/
theorem TC.closed {ρ : Tm → Tm → Prop} (hρ : ∀ s s', ρ s s' → Cl s') :
    ∀ {t t' : Tm} (d : Nat), TC ρ t t' → Tm.closedAt d t = true → Tm.closedAt d t' = true
  | _, _, d, .base h, _ => Cl.mono (hρ _ _ h) d
  | _, _, _, .var _, h => h
  | _, _, d, .abs h, hc => FC.closed hρ (d + 1) h hc
theorem FC.closed {ρ : Tm → Tm → Prop} (hρ : ∀ s s', ρ s s' → Cl s') :
    ∀ {φ φ' : Fm} (d : Nat), FC ρ φ φ' → Fm.closedAt d φ = true → Fm.closedAt d φ' = true
  | _, _, _, .top, h => h
  | _, _, d, .mem ha hb, h => band_intro (TC.closed hρ d ha (band_l h)) (TC.closed hρ d hb (band_r h))
  | _, _, d, @FC.neg _ p p' h, hc => FC.closed hρ (φ := p) (φ' := p') d h hc
  | _, _, d, .and h1 h2, hc => band_intro (FC.closed hρ d h1 (band_l hc)) (FC.closed hρ d h2 (band_r hc))
  | _, _, d, .all h, hc => FC.closed hρ (d + 1) h hc
end

/-! ## Identity by extension -/

/-- Biconditional, defined. -/
def Fm.iff (φ ψ : Fm) : Fm := .and (Fm.imp φ ψ) (Fm.imp ψ φ)

/-- `a ≐ b := ∀z (z∈a ↔ z∈b)` (for closed `a`, `b`). -/
def Eqv (a b : Tm) : Fm := .all (Fm.iff (.mem x0 a) (.mem x0 b))

theorem Eqv_inst {a b : Tm} (ha : Cl a) (hb : Cl b) (c : Tm) :
    (Fm.iff (.mem x0 a) (.mem x0 b)).inst c = Fm.iff (.mem c a) (.mem c b) := by
  show Fm.and (.neg (.and (.mem (Tm.subst 0 c x0) (Tm.subst 0 c a))
      (.neg (.mem (Tm.subst 0 c x0) (Tm.subst 0 c b)))))
    (.neg (.and (.mem (Tm.subst 0 c x0) (Tm.subst 0 c b))
      (.neg (.mem (Tm.subst 0 c x0) (Tm.subst 0 c a))))) = _
  rw [Cl.subst ha 0 c, Cl.subst hb 0 c]
  rfl

/-- An earned biconditional transports both verdicts. -/
theorem iff_transport {p q : Fm} (h : Val true (Fm.iff p q)) :
    (Val true p → Val true q) ∧ (Val false p → Val false q) := by
  cases h with
  | andT h1 h2 =>
    cases h1 with
    | negT h1 =>
      cases h2 with
      | negT h2 =>
        constructor
        · intro hp
          cases h1 with
          | andFl h1 => exact absurd hp (fun hp => consistent h1 hp)
          | andFr h1 => cases h1 with | negF h1 => exact h1
        · intro hp
          cases h2 with
          | andFl h2 => exact h2
          | andFr h2 => cases h2 with | negF h2 => exact absurd h2 (fun h2 => consistent hp h2)

/-- **An earned identity carries every grounded membership verdict.** -/
theorem eq_coext {a b : Tm} (ha : Cl a) (hb : Cl b) (h : Val true (Eqv a b)) :
    ∀ c, Cl c → ∀ v, Val v (.mem c a) → Val v (.mem c b) := by
  intro c hc v hv
  cases h with
  | allT h =>
    have hi := h c hc
    rw [Eqv_inst ha hb c] at hi
    cases v with
    | true => exact (iff_transport hi).1 hv
    | false => exact (iff_transport hi).2 hv

/-- **An earned identity is substitutive** (one step of the induction: every closed formula). -/
theorem eq_cong {a b : Tm} (ha : Cl a) (hb : Cl b) (hab : Val true (Eqv a b)) :
    ∀ {v φ}, Val v φ → Fm.closedAt 0 φ = true →
      ∀ {ψ}, FC (fun s s' => s = a ∧ s' = b) φ ψ → Val v ψ := by
  have hρ : Inert (fun s s' => s = a ∧ s' = b) := by
    intro s s' h k c; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨Cl.subst ha k c, Cl.subst hb k c⟩
  have hρc : ∀ s s', (fun s s' => s = a ∧ s' = b) s s' → Cl s' := by
    intro s s' h; obtain ⟨_, h2⟩ := h; subst h2; exact hb
  intro v φ h
  induction h with
  | top => intro _ ψ hψ; cases hψ; exact .top
  | @memT x φ h ih =>
      intro hcl ψ hψ
      have hx : Cl x := band_l hcl
      have hφc : Fm.closedAt 1 φ = true := band_r hcl
      cases hψ with
      | @mem _ x' _ t' hxx ht =>
        have hx' : Cl x' := TC.closed hρc 0 hxx hx
        have hinst : Val true (φ.inst x') :=
          ih (Fm.closed_subst hx φ 0 hφc) (FC.subst hρ hxx 0 (FC.refl _ φ))
        cases ht with
        | base hr =>
          obtain ⟨e1, e2⟩ := hr; subst e2
          have hmem : Val true (.mem x' a) := by rw [← e1]; exact .memT hinst
          exact eq_coext ha hb hab x' hx' true hmem
        | abs hφ' =>
          exact .memT (ih (Fm.closed_subst hx φ 0 hφc) (FC.subst hρ hxx 0 hφ'))
  | @memF x φ h ih =>
      intro hcl ψ hψ
      have hx : Cl x := band_l hcl
      have hφc : Fm.closedAt 1 φ = true := band_r hcl
      cases hψ with
      | @mem _ x' _ t' hxx ht =>
        have hx' : Cl x' := TC.closed hρc 0 hxx hx
        have hinst : Val false (φ.inst x') :=
          ih (Fm.closed_subst hx φ 0 hφc) (FC.subst hρ hxx 0 (FC.refl _ φ))
        cases ht with
        | base hr =>
          obtain ⟨e1, e2⟩ := hr; subst e2
          have hmem : Val false (.mem x' a) := by rw [← e1]; exact .memF hinst
          exact eq_coext ha hb hab x' hx' false hmem
        | abs hφ' =>
          exact .memF (ih (Fm.closed_subst hx φ 0 hφc) (FC.subst hρ hxx 0 hφ'))
  | negT _ ih => intro hcl ψ hψ; cases hψ with | neg h' => exact .negT (ih hcl h')
  | negF _ ih => intro hcl ψ hψ; cases hψ with | neg h' => exact .negF (ih hcl h')
  | andT _ _ ih1 ih2 =>
      intro hcl ψ hψ
      cases hψ with | and h1 h2 => exact .andT (ih1 (band_l hcl) h1) (ih2 (band_r hcl) h2)
  | andFl _ ih => intro hcl ψ hψ; cases hψ with | and h1 _ => exact .andFl (ih (band_l hcl) h1)
  | andFr _ ih => intro hcl ψ hψ; cases hψ with | and _ h2 => exact .andFr (ih (band_r hcl) h2)
  | @allT φ _ ih =>
      intro hcl ψ hψ
      cases hψ with
      | all h' =>
        exact .allT (fun c hc => ih c hc (Fm.closed_subst hc φ 0 hcl) (FC.subst hρ (TC.refl _ c) 0 h'))
  | @allF φ c hc _ ih =>
      intro hcl ψ hψ
      cases hψ with
      | all h' => exact .allF c hc (ih (Fm.closed_subst hc φ 0 hcl) (FC.subst hρ (TC.refl _ c) 0 h'))

/-- **Substitution through an earned identity**: in any context closed but for its hole,
replacing `a` by `b` carries every grounded verdict. -/
theorem earned_eq_subst {a b : Tm} (ha : Cl a) (hb : Cl b) (hab : Val true (Eqv a b))
    (χ : Fm) (hχ : Fm.closedAt 1 χ = true) (v : Bool) :
    Val v (χ.inst a) → Val v (χ.inst b) := by
  have hρ : Inert (fun s s' => s = a ∧ s' = b) := by
    intro s s' h k c; obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨Cl.subst ha k c, Cl.subst hb k c⟩
  intro h
  exact eq_cong ha hb hab h (Fm.closed_subst ha χ 0 hχ) (FC.subst hρ (.base ⟨rfl, rfl⟩) 0 (FC.refl _ χ))

/-! ## The registers on identity -/

theorem E'_closed : Cl E' := rfl
theorem E_closed : Cl E := rfl

/-- `E ≐ E'` — EARNED. -/
theorem E_eq_E' : Val true (Eqv E E') := by
  apply Val.allT
  intro c _
  rw [Eqv_inst E_closed E'_closed c]
  have hE : Val false (.mem c E) := .memF (.negF .top)
  have hE' : Val false (.mem c E') := .memF (.negF (.memT .top))
  exact .andT (.negT (.andFl hE)) (.negT (.andFl hE'))

/-- `D ≐ D` — quarantined in the lazy register (neither earned nor refuted). -/
theorem D_eq_D_quarantine (v : Bool) : ¬ Val v (Eqv D D) := by
  intro h
  cases v with
  | true =>
    cases h with
    | allT h =>
      have hi := h E rfl
      rw [Eqv_inst D_closed D_closed E] at hi
      cases hi with
      | andT h1 _ =>
        cases h1 with
        | negT h1 =>
          cases h1 with
          | andFl h1 => exact D_no_value E false h1
          | andFr h1 => cases h1 with | negF h1 => exact D_no_value E true h1
  | false =>
    cases h with
    | allF c _ h =>
      rw [Eqv_inst D_closed D_closed c] at h
      cases h with
      | andFl h => cases h with | negF h => cases h with | andT h _ => exact D_no_value c true h
      | andFr h => cases h with | negF h => cases h with | andT h _ => exact D_no_value c true h

/-- …EARNED IF STABLE: under every completion each instance is `p ↔ p`. -/
theorem D_eq_D_stable : StableT (Eqv D D) := by
  intro M
  apply Rd.allT
  intro c _
  rw [Eqv_inst D_closed D_closed c]
  exact .andT (rd_self_imp M c D) (rd_self_imp M c D)

/-- …and the greedy kernel value of an identity cell over two marks is F: "not earned". -/
theorem greedy_identity_values :
    VRCycle.ZTL.V.zxnor .Z .Z = .F ∧ VRCycle.ZTL.V.zxnor .F .Z = .F ∧
    VRCycle.ZTL.V.zxnor .T .T = .T ∧ VRCycle.ZTL.V.zxnor .F .F = .T := by decide

/-- `E ≐ D` — quarantined in the lazy register. -/
theorem E_eq_D_not_earned : ¬ Val true (Eqv E D) := by
  intro h
  cases h with
  | allT h =>
    have hi := h E rfl
    rw [Eqv_inst E_closed D_closed E] at hi
    cases hi with
    | andT _ h2 =>
      cases h2 with
      | negT h2 =>
        cases h2 with
        | andFl h2 => exact D_no_value E false h2
        | andFr h2 => cases h2 with | negF h2 => cases h2 with | memT h2 => cases h2 with | negT h2 => cases h2

/-- Given excluded middle, a completion that reads the dirty cell `E∈D` as TRUE. -/
def Completion.EinD (lem : LEM) : Completion :=
  ⟨fun a b => Val true (.mem a b) ∨ (a = E ∧ b = D),
   fun _ _ => lem _,
   fun h => Or.inl h,
   fun {a b} h h' => by
     cases h' with
     | inl h' => exact consistent h h'
     | inr e => obtain ⟨e1, e2⟩ := e; subst e1; subst e2; exact D_no_value E false h⟩

/-- **`E ≐ D` is OPEN**: one completion reads it true, another false — the identity verdict keeps
the mark that the two-valued carrier forgot (`carrier_forgets_mark`: one OpSet). -/
theorem E_eq_D_open (lem : LEM) :
    Rd (Completion.lfp lem).o true (Eqv E D) ∧ Rd (Completion.EinD lem).o false (Eqv E D) := by
  constructor
  · apply Rd.allT
    intro c _
    rw [Eqv_inst E_closed D_closed c]
    have hE : ¬ Val true (.mem c E) := E_no_member c
    have hD : ¬ Val true (.mem c D) := D_no_member c
    exact .andT (.negT (.andFl (.memF hE))) (.negT (.andFl (.memF hD)))
  · apply Rd.allF E rfl
    rw [Eqv_inst E_closed D_closed E]
    have hEE : ¬ (Completion.EinD lem).o E E := (Completion.EinD lem).agreeF (.memF (.negF .top))
    have hED : (Completion.EinD lem).o E D := Or.inr ⟨rfl, rfl⟩
    exact .andFr (.negF (.andT (.memT hED) (.negT (.memF hEE))))

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.eq_coext
#print axioms VRCycle.SetsNaive.eq_cong
#print axioms VRCycle.SetsNaive.earned_eq_subst
#print axioms VRCycle.SetsNaive.E_eq_E'
#print axioms VRCycle.SetsNaive.D_eq_D_quarantine
#print axioms VRCycle.SetsNaive.D_eq_D_stable
#print axioms VRCycle.SetsNaive.greedy_identity_values
#print axioms VRCycle.SetsNaive.E_eq_D_not_earned
#print axioms VRCycle.SetsNaive.E_eq_D_open
