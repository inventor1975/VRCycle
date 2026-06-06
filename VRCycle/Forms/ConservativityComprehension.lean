-- VR-Forms: Conservativity with COMPREHENSION terms — full fidelity to the preprint π.
--
-- COURSE: A, comprehension storey. The FOL floor (`ConservativityFOL.lean`) modelled formal
-- atoms as 0-ary; the preprint's formal terms are set-builders {x : φ}, and π translates
-- ⌜x ∈ {y : ψ}⌝ to ψ(x) (Part III §III.2). That needs terms that NEST formulas — so `Tm` and
-- `Fml` are mutually recursive — and a π that SUBSTITUTES the argument, which forces the
-- substitution-composition lemmas (the shoal the FOL floor avoided). Self-contained (no Mathlib).
--
-- ## Sub-veha 1 (this commit): mutual syntax `Tm`/`Fml` (set-builder) + mutual `lift`.
--   Confirms Lean accepts the mutual inductive and sees structural termination of `lift`.
--   Substitution + composition lemmas + π + conservativity follow in later sub-vehas.

namespace VR.Forms.ConservativityComprehension

-- ============================================================
-- §1. Mutually recursive terms and formulas (de Bruijn)
-- ============================================================

-- Terms and formulas, mutually recursive: a term may be a de Bruijn variable or a set-builder
-- `{x : φ}` (binds de Bruijn 0 in the formula `φ`); a formula is built from membership `a ∈ b`,
-- ⊥, →, and ∀ (binding index 0).
mutual
inductive Tm where
  | var   : Nat → Tm
  | setOf : Fml → Tm        -- {x : φ}, binds de Bruijn 0 in φ
inductive Fml where
  | mem : Tm → Tm → Fml      -- a ∈ b
  | bot : Fml
  | imp : Fml → Fml → Fml
  | all : Fml → Fml          -- ∀, binds de Bruijn 0
end

-- ============================================================
-- §2. de Bruijn lift (mutual)
-- ============================================================

-- Lift free variables `≥ c` by one, going under each binder (`setOf` and `∀` shift the cutoff).
mutual
def Tm.lift (c : Nat) : Tm → Tm
  | .var n   => .var (if n < c then n else n + 1)
  | .setOf φ => .setOf (Fml.lift (c + 1) φ)
def Fml.lift (c : Nat) : Fml → Fml
  | .mem a b => .mem (a.lift c) (b.lift c)
  | .bot     => .bot
  | .imp p q => .imp (p.lift c) (q.lift c)
  | .all p   => .all (p.lift (c + 1))
end

-- ============================================================
-- §3. de Bruijn substitution of a term (mutual)
-- ============================================================

-- Substitute de Bruijn variable `j` by term `t`, decrementing free variables `> j`.
-- Under each binder (`setOf`, `∀`) the cutoff is `j+1` and `t` is lifted. `subst 0 t` is the
-- ∀-elim / comprehension instantiation.  Explicit calls (no dot-notation) to target the right arg.
mutual
def Tm.subst (j : Nat) (t : Tm) : Tm → Tm
  | .var n   => if n = j then t else .var (if j < n then n - 1 else n)
  | .setOf φ => .setOf (Fml.subst (j + 1) (Tm.lift 0 t) φ)
def Fml.subst (j : Nat) (t : Tm) : Fml → Fml
  | .mem a b => .mem (Tm.subst j t a) (Tm.subst j t b)
  | .bot     => .bot
  | .imp p q => .imp (Fml.subst j t p) (Fml.subst j t q)
  | .all p   => .all (Fml.subst (j + 1) (Tm.lift 0 t) p)
end

-- ============================================================
-- §4. Substitution undoes lift (mutual) — first shoal lemma
-- ============================================================

-- `subst k w` undoes `lift k` (the variable freshly inserted by `lift k` is the one removed
-- by `subst k`).  Foundation for the substitution-composition lemma.
mutual
theorem Tm.subst_lift (k : Nat) (w : Tm) (u : Tm) :
    Tm.subst k w (Tm.lift k u) = u := by
  match u with
  | .var n =>
    simp only [Tm.lift, Tm.subst]
    by_cases h : n < k
    · rw [if_pos h, if_neg (show ¬ (n = k) by omega), if_neg (show ¬ (k < n) by omega)]
    · rw [if_neg h, if_neg (show ¬ (n + 1 = k) by omega), if_pos (show k < n + 1 by omega),
        Nat.add_sub_cancel]
  | .setOf φ =>
    simp only [Tm.lift, Tm.subst]
    rw [Fml.subst_lift (k + 1) (Tm.lift 0 w) φ]
theorem Fml.subst_lift (k : Nat) (w : Tm) (φ : Fml) :
    Fml.subst k w (Fml.lift k φ) = φ := by
  match φ with
  | .mem a b =>
    simp only [Fml.lift, Fml.subst, Tm.subst_lift]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.lift, Fml.subst, Fml.subst_lift]
  | .all p =>
    simp only [Fml.lift, Fml.subst]
    rw [Fml.subst_lift (k + 1) (Tm.lift 0 w) p]
end

-- ============================================================
-- §5. lift ∘ lift permutation (mutual) — second shoal lemma
-- ============================================================

-- Two lifts permute when the inner cutoff `d` is below the outer `c`: shifting at `d` first
-- then at `c+1` equals shifting at `c` first then at `d`.  Needed for the binder cases of the
-- substitution-composition lemma (where `lift 0` accumulates under ∀ / set-builder).
mutual
theorem Tm.lift_lift (c d : Nat) (h : d ≤ c) (u : Tm) :
    Tm.lift (c + 1) (Tm.lift d u) = Tm.lift d (Tm.lift c u) := by
  match u with
  | .var n =>
    by_cases h1 : n < d
    · simp only [Tm.lift, if_pos h1, if_pos (show n < c by omega), if_pos (show n < c + 1 by omega)]
    · by_cases h2 : n < c
      · simp only [Tm.lift, if_neg h1, if_pos h2, if_pos (show n + 1 < c + 1 by omega)]
      · simp only [Tm.lift, if_neg h1, if_neg h2,
          if_neg (show ¬ n + 1 < c + 1 by omega), if_neg (show ¬ n + 1 < d by omega)]
  | .setOf φ =>
    simp only [Tm.lift]
    rw [Fml.lift_lift (c + 1) (d + 1) (by omega) φ]
theorem Fml.lift_lift (c d : Nat) (h : d ≤ c) (φ : Fml) :
    Fml.lift (c + 1) (Fml.lift d φ) = Fml.lift d (Fml.lift c φ) := by
  match φ with
  | .mem a b =>
    simp only [Fml.lift, Tm.lift_lift c d h]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.lift, Fml.lift_lift c d h]
  | .all p =>
    simp only [Fml.lift]
    rw [Fml.lift_lift (c + 1) (d + 1) (by omega) p]
end

-- ============================================================
-- §6. lift ∘ subst commutation (mutual) — third shoal lemma
-- ============================================================

-- Pushing a `lift c` past a `subst j` (with the cutoff `c ≤ j`): the lift shifts the
-- substitution point to `j+1` and lifts the substituted term.  Needed for the binder cases of
-- the substitution-composition lemma.
mutual
theorem Tm.lift_subst (c j : Nat) (h : c ≤ j) (t : Tm) (s : Tm) :
    Tm.lift c (Tm.subst j t s) = Tm.subst (j + 1) (Tm.lift c t) (Tm.lift c s) := by
  match s with
  | .var n =>
    by_cases hn : n = j
    · simp only [Tm.subst, Tm.lift, if_pos hn, if_neg (show ¬ n < c by omega),
        if_pos (show n + 1 = j + 1 by omega)]
    · by_cases hlt : j < n
      · simp only [Tm.subst, Tm.lift, if_neg hn, if_pos hlt,
          if_neg (show ¬ n - 1 < c by omega), if_neg (show ¬ n < c by omega),
          if_neg (show ¬ n + 1 = j + 1 by omega), if_pos (show j + 1 < n + 1 by omega)]
        congr 1; omega
      · by_cases hc : n < c
        · simp only [Tm.subst, Tm.lift, if_neg hn, if_neg hlt, if_pos hc,
            if_neg (show ¬ n = j + 1 by omega), if_neg (show ¬ j + 1 < n by omega)]
        · simp only [Tm.subst, Tm.lift, if_neg hn, if_neg hlt, if_neg hc,
            if_neg (show ¬ n + 1 = j + 1 by omega), if_neg (show ¬ j + 1 < n + 1 by omega)]
  | .setOf φ =>
    simp only [Tm.lift, Tm.subst]
    rw [Fml.lift_subst (c + 1) (j + 1) (by omega) (Tm.lift 0 t) φ,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
theorem Fml.lift_subst (c j : Nat) (h : c ≤ j) (t : Tm) (φ : Fml) :
    Fml.lift c (Fml.subst j t φ) = Fml.subst (j + 1) (Tm.lift c t) (Fml.lift c φ) := by
  match φ with
  | .mem a b =>
    simp only [Fml.lift, Fml.subst, Tm.lift_subst c j h]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.lift, Fml.subst, Fml.lift_subst c j h]
  | .all p =>
    simp only [Fml.lift, Fml.subst]
    rw [Fml.lift_subst (c + 1) (j + 1) (by omega) (Tm.lift 0 t) p,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
end

-- ============================================================
-- §7. Substitution-composition lemma (mutual) — the main shoal
-- ============================================================

-- The de Bruijn substitution lemma: an outer substitution at `a` commutes past an inner one at
-- `k ≤ a`, pushing `u` into the inner term `v` and lifting `u` over the inner cutoff.  This is
-- the identity π needs to commute with the comprehension instantiation `x ∈ ⌜{y:ψ}⌝ ↦ ψ(x)`.
mutual
theorem Tm.subst_subst (a k : Nat) (h : k ≤ a) (u v : Tm) (w : Tm) :
    Tm.subst a u (Tm.subst k v w)
      = Tm.subst k (Tm.subst a u v) (Tm.subst (a + 1) (Tm.lift k u) w) := by
  match w with
  | .var n =>
    by_cases hn1 : n = k
    · simp only [Tm.subst, if_pos hn1, if_neg (show ¬ n = a + 1 by omega),
        if_neg (show ¬ a + 1 < n by omega)]
    · by_cases hn2 : n = a + 1
      · simp only [Tm.subst, if_neg hn1, if_pos (show k < n by omega),
          if_pos (show n - 1 = a by omega), if_pos hn2, Tm.subst_lift]
      · by_cases hlt : k < n
        · by_cases hb : a + 1 < n
          · simp only [Tm.subst, if_neg hn1, if_pos hlt, if_neg (show ¬ n - 1 = a by omega),
              if_pos (show a < n - 1 by omega), if_neg hn2, if_pos hb,
              if_neg (show ¬ n - 1 = k by omega), if_pos (show k < n - 1 by omega)]
          · simp only [Tm.subst, if_neg hn1, if_pos hlt, if_neg (show ¬ n - 1 = a by omega),
              if_neg (show ¬ a < n - 1 by omega), if_neg hn2, if_neg hb]
        · simp only [Tm.subst, if_neg hn1, if_neg hlt, if_neg (show ¬ n = a by omega),
            if_neg (show ¬ a < n by omega), if_neg hn2, if_neg (show ¬ a + 1 < n by omega)]
  | .setOf φ =>
    simp only [Tm.subst]
    rw [Fml.subst_subst (a + 1) (k + 1) (by omega) (Tm.lift 0 u) (Tm.lift 0 v) φ,
        Tm.lift_lift k 0 (Nat.zero_le k) u,
        ← Tm.lift_subst 0 a (Nat.zero_le a) u v]
theorem Fml.subst_subst (a k : Nat) (h : k ≤ a) (u v : Tm) (φ : Fml) :
    Fml.subst a u (Fml.subst k v φ)
      = Fml.subst k (Tm.subst a u v) (Fml.subst (a + 1) (Tm.lift k u) φ) := by
  match φ with
  | .mem x y =>
    simp only [Fml.subst, Tm.subst_subst a k h u v]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.subst, Fml.subst_subst a k h u v]
  | .all p =>
    simp only [Fml.subst]
    rw [Fml.subst_subst (a + 1) (k + 1) (by omega) (Tm.lift 0 u) (Tm.lift 0 v) p,
        Tm.lift_lift k 0 (Nat.zero_le k) u,
        ← Tm.lift_subst 0 a (Nat.zero_le a) u v]
end

-- ============================================================
-- §8. lift ∘ subst, cutoff above the substitution point (mutual)
-- ============================================================

-- The companion to §6: when the lift cutoff `c` is at or above the substitution index `j`
-- (`j ≤ c`), the lift passes through keeping the substitution index and lifting the body cutoff.
-- Needed for π-commutes-with-lift (π substitutes at index 0; the lift cutoff is arbitrary).
mutual
theorem Tm.lift_subst' (j c : Nat) (h : j ≤ c) (t : Tm) (s : Tm) :
    Tm.lift c (Tm.subst j t s) = Tm.subst j (Tm.lift c t) (Tm.lift (c + 1) s) := by
  match s with
  | .var n =>
    by_cases hn : n = j
    · simp only [Tm.subst, Tm.lift, if_pos hn, if_pos (show n < c + 1 by omega)]
    · by_cases hlt : j < n
      · by_cases hb : n ≤ c
        · simp only [Tm.subst, Tm.lift, if_neg hn, if_pos hlt,
            if_pos (show n - 1 < c by omega), if_pos (show n < c + 1 by omega)]
        · simp only [Tm.subst, Tm.lift, if_neg hn, if_pos hlt,
            if_neg (show ¬ n - 1 < c by omega), if_neg (show ¬ n < c + 1 by omega),
            if_neg (show ¬ n + 1 = j by omega), if_pos (show j < n + 1 by omega)]
          congr 1; omega
      · simp only [Tm.subst, Tm.lift, if_neg hn, if_neg hlt,
          if_pos (show n < c by omega), if_pos (show n < c + 1 by omega)]
  | .setOf φ =>
    simp only [Tm.lift, Tm.subst]
    rw [Fml.lift_subst' (j + 1) (c + 1) (by omega) (Tm.lift 0 t) φ,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
theorem Fml.lift_subst' (j c : Nat) (h : j ≤ c) (t : Tm) (φ : Fml) :
    Fml.lift c (Fml.subst j t φ) = Fml.subst j (Tm.lift c t) (Fml.lift (c + 1) φ) := by
  match φ with
  | .mem a b =>
    simp only [Fml.lift, Fml.subst, Tm.lift_subst' j c h]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.lift, Fml.subst, Fml.lift_subst' j c h]
  | .all p =>
    simp only [Fml.lift, Fml.subst]
    rw [Fml.lift_subst' (j + 1) (c + 1) (by omega) (Tm.lift 0 t) p,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
end

-- ============================================================
-- §9. The interpretation π (course A: comprehension on the RHS of ∈)
-- ============================================================

-- π (preprint §III.2, rule 595, course A): π(x ∈ {y:ψ}) = ψ(x), substituting the LEFT term for
-- the bound variable; on operational membership it recurses; on ⊥/→/∀ it is a homomorphism.
-- Set-builders are unfolded only as the RHS of ∈ (the left member is operational), so π is a
-- terminating STRUCTURAL recursion — it never re-expands a substituted result, which is exactly
-- why self-membered formal terms (Russell ⌜{x:x∉x}⌝, would-be `R ∈ R`) cannot diverge: the
-- grammar keeps the left member operational, so such a formula is not in the language at all.
mutual
def piTm : Tm → Tm
  | .var n   => .var n
  | .setOf ψ => .setOf (piFml ψ)
def piFml : Fml → Fml
  | .mem a b =>
      match b with
      | .setOf ψ => Fml.subst 0 (piTm a) (piFml ψ)   -- comprehension: a ∈ {y:ψ} ↦ ψ(a)
      | .var m   => .mem (piTm a) (.var m)            -- operational membership a ∈ m
  | .bot     => .bot
  | .imp p q => .imp (piFml p) (piFml q)
  | .all p   => .all (piFml p)
end

-- ============================================================
-- §10. π commutes with lift (mutual)
-- ============================================================

mutual
theorem piTm_lift (c : Nat) (u : Tm) : piTm (Tm.lift c u) = Tm.lift c (piTm u) := by
  match u with
  | .var n => simp only [Tm.lift, piTm]
  | .setOf ψ =>
    simp only [Tm.lift, piTm]
    rw [piFml_lift (c + 1) ψ]
theorem piFml_lift (c : Nat) (φ : Fml) : piFml (Fml.lift c φ) = Fml.lift c (piFml φ) := by
  match φ with
  | .mem a b =>
    match b with
    | .setOf ψ =>
      simp only [Fml.lift, Tm.lift, piFml]
      rw [piTm_lift c a, piFml_lift (c + 1) ψ,
          Fml.lift_subst' 0 c (Nat.zero_le c) (piTm a) (piFml ψ)]
    | .var m =>
      simp only [Fml.lift, Tm.lift, piFml]
      rw [piTm_lift c a]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.lift, piFml]
    rw [piFml_lift c p, piFml_lift c q]
  | .all p =>
    simp only [Fml.lift, piFml]
    rw [piFml_lift (c + 1) p]
end

-- ============================================================
-- §11. π commutes with substitution of a variable (mutual) — the keystone
-- ============================================================

-- Lifting a variable past cutoff 0 is just incrementing it.
theorem liftz (i : Nat) : Tm.lift 0 (Tm.var i) = Tm.var (i + 1) := by
  simp only [Tm.lift, if_neg (Nat.not_lt_zero i)]

-- π commutes with substituting a VARIABLE for a de Bruijn index.  This is exactly the
-- ∀-elimination case of the conservativity transport (course A instantiates operational terms,
-- i.e. variables; substituting a set-builder for a variable would put it left of ∈ — Russell,
-- excluded by the grammar).  The comprehension case closes via the substitution lemma §7.
mutual
theorem piTm_subst (j i : Nat) (u : Tm) :
    piTm (Tm.subst j (Tm.var i) u) = Tm.subst j (Tm.var i) (piTm u) := by
  match u with
  | .var n =>
    by_cases hn : n = j
    · simp only [Tm.subst, if_pos hn, piTm]
    · simp only [Tm.subst, if_neg hn, piTm]
  | .setOf ψ =>
    simp only [Tm.subst, piTm, liftz]
    rw [piFml_subst (j + 1) (i + 1) ψ]
theorem piFml_subst (j i : Nat) (φ : Fml) :
    piFml (Fml.subst j (Tm.var i) φ) = Fml.subst j (Tm.var i) (piFml φ) := by
  match φ with
  | .mem a b =>
    match b with
    | .setOf ψ =>
      simp only [Tm.subst, Fml.subst, piFml, liftz]
      rw [piTm_subst j i a, piFml_subst (j + 1) (i + 1) ψ,
          Fml.subst_subst j 0 (Nat.zero_le j) (Tm.var i) (piTm a) (piFml ψ)]
      simp only [liftz]
    | .var m =>
      by_cases hm : m = j
      · simp only [Tm.subst, Fml.subst, piFml, if_pos hm]
        rw [piTm_subst j i a]
      · simp only [Tm.subst, Fml.subst, piFml, if_neg hm]
        rw [piTm_subst j i a]
  | .bot => rfl
  | .imp p q =>
    simp only [Fml.subst, piFml]
    rw [piFml_subst j i p, piFml_subst j i q]
  | .all p =>
    simp only [Fml.subst, piFml, liftz]
    rw [piFml_subst (j + 1) (i + 1) p]
end

-- ============================================================
-- §12. Operational fragment L₀, π = id on L₀, Hilbert calculus, conservativity
-- ============================================================

-- A term is operational iff it is a variable (the minimal language has no set-builders in L₀).
def Tm.IsOp : Tm → Prop
  | .var _   => True
  | .setOf _ => False

-- An operational formula L₀ contains no set-builders: every membership is between operational
-- terms, and ⊥/→/∀ are operational when their parts are.
def Fml.IsL0 : Fml → Prop
  | .mem a b => a.IsOp ∧ b.IsOp
  | .bot     => True
  | .imp p q => p.IsL0 ∧ q.IsL0
  | .all p   => p.IsL0

-- π is the identity on the operational fragment (preprint Step 2: π(φ)=φ for φ∈L₀).
theorem piTm_id {u : Tm} (h : u.IsOp) : piTm u = u := by
  match u, h with
  | .var n, _   => rfl
  | .setOf _, h => exact h.elim

theorem piFml_id {φ : Fml} (h : φ.IsL0) : piFml φ = φ := by
  match φ, h with
  | .mem a (.var m), h   => simp only [piFml]; rw [piTm_id h.1]
  | .mem a (.setOf _), h => exact h.2.elim
  | .bot, _              => rfl
  | .imp p q, h          => simp only [piFml]; rw [piFml_id h.1, piFml_id h.2]
  | .all p, h            => simp only [piFml]; rw [piFml_id (show p.IsL0 from h)]

-- Classical Hilbert calculus over a theory `T`.  ∀-elimination instantiates a VARIABLE (course A:
-- the operational terms are exactly the variables; instantiating a set-builder would put it left
-- of ∈, which the grammar excludes — see §9/Russell).
inductive Provable (T : Fml → Prop) : Fml → Prop where
  | ax {φ}           : T φ → Provable T φ
  | k {φ ψ}          : Provable T (.imp φ (.imp ψ φ))
  | s {φ ψ χ}        : Provable T (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | peirce {φ ψ}     : Provable T (.imp (.imp (.imp φ ψ) φ) φ)
  | mp {φ ψ}         : Provable T (.imp φ ψ) → Provable T φ → Provable T ψ
  | allElim {φ} (i : Nat) : Provable T (.all φ) → Provable T (Fml.subst 0 (.var i) φ)
  | allDistrib {φ ψ} : Provable T (.imp (.all (.imp φ ψ)) (.imp (.all φ) (.all ψ)))
  | gen {φ}          : Provable T φ → Provable T (.all φ)

-- π transports a T₁-derivation to a T₀-derivation of the π-image, provided π sends every
-- T₁-axiom to a T₀-theorem.  ∀-elim uses the keystone (π commutes with variable substitution);
-- the logical axioms transport because π is a homomorphism on →/∀.
theorem piFml_provable (T₁ T₀ : Fml → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piFml α)) :
    ∀ {ψ}, Provable T₁ ψ → Provable T₀ (piFml ψ) := by
  intro ψ h
  induction h with
  | ax hmem        => exact haxioms _ hmem
  | k              => simp only [piFml]; exact Provable.k
  | s              => simp only [piFml]; exact Provable.s
  | peirce         => simp only [piFml]; exact Provable.peirce
  | mp _ _ ih₁ ih₂ => simp only [piFml] at ih₁; exact Provable.mp ih₁ ih₂
  | @allElim φ i _ ih =>
      simp only [piFml] at ih
      rw [piFml_subst 0 i φ]
      exact Provable.allElim i ih
  | allDistrib     => simp only [piFml]; exact Provable.allDistrib
  | gen _ ih       => simp only [piFml]; exact Provable.gen ih

-- **Theorem III.1 (conservativity), comprehension storey.** If π sends every T₁-axiom to a
-- T₀-theorem, then any operational (L₀) formula provable in T₁ is already provable in T₀ —
-- the formal register's comprehension terms prove no new operational theorems.
theorem conservativity (T₁ T₀ : Fml → Prop)
    (haxioms : ∀ α, T₁ α → Provable T₀ (piFml α))
    (φ : Fml) (hL0 : φ.IsL0) (h : Provable T₁ φ) :
    Provable T₀ φ := by
  have hpi := piFml_provable T₁ T₀ haxioms h
  rwa [piFml_id hL0] at hpi

-- ============================================================
-- §13. End-to-end: a concrete comprehension instance (non-vacuous)
-- ============================================================

-- `φ → φ` is a Hilbert theorem (the standard S-K-K derivation).
theorem imp_self (T : Fml → Prop) (φ : Fml) : Provable T (.imp φ φ) := by
  have h1 : Provable T (.imp (.imp φ (.imp (.imp φ φ) φ))
                             (.imp (.imp φ (.imp φ φ)) (.imp φ φ))) := Provable.s
  have h2 : Provable T (.imp φ (.imp (.imp φ φ) φ)) := Provable.k
  have h4 : Provable T (.imp φ (.imp φ φ)) := Provable.k
  exact Provable.mp (Provable.mp h1 h2) h4

-- A concrete operational predicate ψ(y) = (var₁ ∈ y) and the comprehension axiom
-- `var₀ ∈ {y : ψ} → ψ(var₀)` (one direction; the left member is the variable var₀, course A).
def psi : Fml := .mem (.var 1) (.var 0)
def compAx : Fml := .imp (.mem (.var 0) (.setOf psi)) (Fml.subst 0 (.var 0) psi)

def T1c : Fml → Prop := fun φ => φ = compAx   -- T₁: the comprehension axiom
def T0c : Fml → Prop := fun _ => False        -- T₀: no axioms (π(compAx) is pure logic)

-- The conservativity hypothesis is PROVED, not assumed: π(compAx) = (X → X) with
-- X = subst 0 (var₀) (π ψ), and `X → X` is a T₀-theorem.  This is where the keystone
-- (π commutes with the comprehension substitution) does its work.
theorem T1c_haxioms : ∀ α, T1c α → Provable T0c (piFml α) := by
  intro α hα
  rw [hα]
  simp only [compAx, piFml, piTm]
  rw [piFml_subst 0 0 psi]
  exact imp_self T0c _

-- Non-vacuous Theorem III.1: the comprehension theory T₁ proves no new operational theorem.
theorem conservativity_comprehension_concrete
    (φ : Fml) (hL0 : φ.IsL0) (h : Provable T1c φ) : Provable T0c φ :=
  conservativity T1c T0c T1c_haxioms φ hL0 h

-- ============================================================
-- Axiom audit — full storey (de Bruijn calculus + π + conservativity)
-- ============================================================
#print axioms Tm.subst_subst
#print axioms Fml.subst_subst
#print axioms piTm
#print axioms piFml
#print axioms piFml_lift
#print axioms piFml_subst
#print axioms piFml_provable
#print axioms conservativity
#print axioms T1c_haxioms
#print axioms conservativity_comprehension_concrete

end VR.Forms.ConservativityComprehension
