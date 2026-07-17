/-
  Verify_Choice_standalone.lean
  =============================
  A SELF-CONTAINED, mathlib-FREE witness for the empty-axiom-list results
  of the preprint "Choice as an Act" (VRCycle/Continuum/{Choice,Cardinal}.lean).

  WHY THIS FILE EXISTS.  The full corpus verifies with `lake build`, but that
  pulls mathlib (a large cache, minutes of compute).  This file depends on
  NOTHING — no mathlib, no lake, no imports.  Any agent, human or machine,
  can check every theorem below in seconds:

      lean Verify_Choice_standalone.lean

  It prints, for each named theorem, `does not depend on any axioms`.  That
  is the strongest form of a zero-trust claim: a verdict re-derived from the
  bare Lean 4 kernel, with no axioms, no library, and no trust in the author
  or the text.  Two parties who share nothing can both run this and agree.

  Toolchain: Lean 4.29.1 (see lean-toolchain).  No other dependency.
-/

namespace VRChoiceStandalone

-- Minimal vocabulary, defined from scratch (no imports) --------------------
def Branch : Type := Nat → Bool

def Inj  {A B : Type} (f : A → B) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂
def Surj {A B : Type} (f : A → B) : Prop := ∀ b, ∃ a, f a = b

-- ============================================================
-- 1. The Cantor–Lawvere diagonal, uniform over every floor
-- ============================================================
theorem cantor_ladder (A : Type) : ¬ ∃ f : A → (A → Bool), Surj f := by
  rintro ⟨f, hf⟩
  obtain ⟨a, ha⟩ := hf (fun x => !(f x x))
  have h := congrFun ha a
  cases hx : f a a with
  | false => rw [hx] at h; exact Bool.noConfusion h
  | true  => rw [hx] at h; exact Bool.noConfusion h

theorem branches_not_enumerable : ¬ ∃ e : Nat → Branch, Surj e :=
  cantor_ladder Nat

-- ============================================================
-- 2. ℕ embeds into Branch (a performed comparison, as data)
-- ============================================================
private theorem beq_self : ∀ a : Nat, Nat.beq a a = true
  | 0     => rfl
  | a + 1 => beq_self a

private theorem eq_of_beq : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0,     0,     _ => rfl
  | 0,     _ + 1, h => Bool.noConfusion h
  | _ + 1, 0,     h => Bool.noConfusion h
  | a + 1, b + 1, h => congrArg Nat.succ (eq_of_beq (a := a) (b := b) h)

def natIntoBranch : Nat → Branch := fun n k => Nat.beq k n

theorem natIntoBranch_inj : Inj natIntoBranch := by
  intro m n h
  have hm : Nat.beq m m = Nat.beq m n := congrFun h m
  rw [beq_self] at hm
  exact eq_of_beq hm.symm

/-- ℕ is strictly below its power floor: the injection up is performed, and
no surjection comes back. -/
theorem nat_strictly_below_branch :
    (∃ f : Nat → Branch, Inj f) ∧ ¬ ∃ e : Nat → Branch, Surj e :=
  ⟨⟨natIntoBranch, natIntoBranch_inj⟩, branches_not_enumerable⟩

-- ============================================================
-- 3. Productive uncountability: the fugitive is computed
-- ============================================================
def escape (e : Nat → Branch) : Branch := fun n => !(e n n)

theorem escape_escapes (e : Nat → Branch) (k : Nat) : escape e ≠ e k := by
  intro h
  have hk : (!(e k k)) = e k k := congrFun h k
  cases hb : e k k with
  | false => rw [hb] at hk; exact Bool.noConfusion hk
  | true  => rw [hb] at hk; exact Bool.noConfusion hk

theorem branches_productive :
    ∀ e : Nat → Branch, ∃ b : Branch, ∀ k, b ≠ e k :=
  fun e => ⟨escape e, escape_escapes e⟩

-- ============================================================
-- 4. Russell's socks: no swap-symmetric selection rule
-- ============================================================
def swapAt (k : Nat) (c : Nat → Bool) : Nat → Bool :=
  fun n => if n = k then !(c n) else c n

theorem no_symmetric_selector :
    ¬ ∃ (c : Nat → Bool) (N : Nat), ∀ k, N ≤ k → swapAt k c = c := by
  rintro ⟨c, N, h⟩
  have h1 : swapAt N c N = c N := congrFun (h N (Nat.le_refl N)) N
  unfold swapAt at h1; rw [if_pos rfl] at h1
  cases hc : c N with
  | false => rw [hc] at h1; exact Bool.noConfusion h1
  | true  => rw [hc] at h1; exact Bool.noConfusion h1

theorem selectors_not_enumerable : ¬ ∃ e : Nat → (Nat → Bool), Surj e :=
  cantor_ladder Nat

-- ============================================================
-- 5. Anonymous determinism cannot break symmetry (Angluin)
-- ============================================================
def netStep {S : Type} (f : S → S → S → S) (L R : Fin m → Fin m)
    (c : Fin m → S) : Fin m → S :=
  fun i => f (c (L i)) (c i) (c (R i))

def netRun {S : Type} (f : S → S → S → S) (L R : Fin m → Fin m) (s0 : S) :
    Nat → Fin m → S
  | 0     => fun _ => s0
  | t + 1 => netStep f L R (netRun f L R s0 t)

theorem twins_never_break {S : Type} (f : S → S → S → S) (L R : Fin m → Fin m)
    (s0 : S) : ∀ t, ∀ i j : Fin m, netRun f L R s0 t i = netRun f L R s0 t j := by
  intro t
  induction t with
  | zero => intro i j; rfl
  | succ t ih =>
    intro i j
    show f _ _ _ = f _ _ _
    rw [ih (L i) (L j), ih i j, ih (R i) (R j)]

/-- "distinguishes a unique node" spelled out, to stay notation-free (no
`∃!` from the library): a `k` with `P` that every other `P`-node equals. -/
theorem no_unique_leader {S : Type} (f : S → S → S → S) (L R : Fin m → Fin m)
    (s0 : S) (P : S → Prop) (i j : Fin m) (hij : i ≠ j) :
    ∀ t, ¬ ∃ k, P (netRun f L R s0 t k)
                ∧ ∀ k', P (netRun f L R s0 t k') → k' = k := by
  rintro t ⟨k, hk, huniq⟩
  have hi : P (netRun f L R s0 t i) := by
    rw [twins_never_break f L R s0 t i k]; exact hk
  have hj : P (netRun f L R s0 t j) := by
    rw [twins_never_break f L R s0 t j k]; exact hk
  exact hij ((huniq i hi).trans (huniq j hj).symm)

-- ============================================================
-- The audit: every line below prints
--   "... does not depend on any axioms"
-- ============================================================
#print axioms cantor_ladder
#print axioms branches_not_enumerable
#print axioms natIntoBranch_inj
#print axioms nat_strictly_below_branch
#print axioms escape_escapes
#print axioms branches_productive
#print axioms no_symmetric_selector
#print axioms selectors_not_enumerable
#print axioms twins_never_break
#print axioms no_unique_leader

end VRChoiceStandalone
