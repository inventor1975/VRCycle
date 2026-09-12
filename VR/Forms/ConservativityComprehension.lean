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

-- Empty-list sweep (2026-09-12): no auto-generated `injEq` lemmas (they carry `propext`);
-- constructor injectivity, where needed, is obtained by `cases`.
set_option genInjectivity false

-- Hand Nat arithmetic on `[]` — replaces `omega` (which pulls `propext` through Int simp lemmas).
namespace NatAux
theorem not_lt_of_le {a b : Nat} (h : a ≤ b) : ¬ b < a :=
  fun e => Nat.lt_irrefl b (Nat.lt_of_lt_of_le e h)
theorem lt_succ_of_lt {a b : Nat} (h : a < b) : a < b + 1 :=
  Nat.lt_succ_of_le (Nat.le_of_lt h)
theorem sub_one_add_one {n : Nat} (h : 0 < n) : n - 1 + 1 = n :=
  Nat.succ_pred_eq_of_pos h
theorem le_sub_one_of_lt {a n : Nat} (h : a < n) : a ≤ n - 1 :=
  Nat.le_of_succ_le_succ (show a + 1 ≤ n - 1 + 1 by
    rw [sub_one_add_one (Nat.lt_of_le_of_lt (Nat.zero_le a) h)]; exact h)
theorem lt_sub_one_of_succ_lt {a n : Nat} (h : a + 1 < n) : a < n - 1 :=
  Nat.lt_of_succ_lt_succ (show a + 1 < n - 1 + 1 by
    rw [sub_one_add_one (Nat.lt_of_le_of_lt (Nat.zero_le _) h)]; exact h)
end NatAux


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
    · rw [if_pos h, if_neg (Nat.ne_of_lt h), if_neg (NatAux.not_lt_of_le (Nat.le_of_lt h))]
    · have hk : k ≤ n := Nat.le_of_not_lt h
      rw [if_neg h, if_neg (fun (e : n + 1 = k) =>
          Nat.not_succ_le_self n (by rw [← e] at hk; exact hk)),
        if_pos (Nat.lt_succ_of_le hk)]
      rfl
  | .setOf φ =>
    simp only [Tm.lift, Tm.subst]
    rw [Fml.subst_lift (k + 1) (Tm.lift 0 w) φ]
theorem Fml.subst_lift (k : Nat) (w : Tm) (φ : Fml) :
    Fml.subst k w (Fml.lift k φ) = φ := by
  match φ with
  | .mem a b =>
    show Fml.mem (Tm.subst k w (Tm.lift k a)) (Tm.subst k w (Tm.lift k b)) = Fml.mem a b
    rw [Tm.subst_lift k w a, Tm.subst_lift k w b]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (Fml.subst k w (Fml.lift k p)) (Fml.subst k w (Fml.lift k q)) = Fml.imp p q
    rw [Fml.subst_lift k w p, Fml.subst_lift k w q]
  | .all p =>
    show Fml.all (Fml.subst (k + 1) (Tm.lift 0 w) (Fml.lift (k + 1) p)) = Fml.all p
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
    simp only [Tm.lift]
    by_cases h1 : n < d
    · have h1c : n < c := Nat.lt_of_lt_of_le h1 h
      rw [if_pos h1, if_pos h1c, if_pos (NatAux.lt_succ_of_lt h1c), if_pos h1]
    · by_cases h2 : n < c
      · rw [if_neg h1, if_pos h2, if_pos (Nat.succ_lt_succ h2), if_neg h1]
      · rw [if_neg h1, if_neg h2, if_neg (fun e => h2 (Nat.lt_of_succ_lt_succ e)),
          if_neg (fun e => h1 (Nat.lt_of_le_of_lt (Nat.le_succ n) e))]
  | .setOf φ =>
    show Tm.setOf (Fml.lift (c + 1 + 1) (Fml.lift (d + 1) φ))
        = Tm.setOf (Fml.lift (d + 1) (Fml.lift (c + 1) φ))
    rw [Fml.lift_lift (c + 1) (d + 1) (Nat.succ_le_succ h) φ]
theorem Fml.lift_lift (c d : Nat) (h : d ≤ c) (φ : Fml) :
    Fml.lift (c + 1) (Fml.lift d φ) = Fml.lift d (Fml.lift c φ) := by
  match φ with
  | .mem a b =>
    show Fml.mem (Tm.lift (c + 1) (Tm.lift d a)) (Tm.lift (c + 1) (Tm.lift d b))
        = Fml.mem (Tm.lift d (Tm.lift c a)) (Tm.lift d (Tm.lift c b))
    rw [Tm.lift_lift c d h a, Tm.lift_lift c d h b]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (Fml.lift (c + 1) (Fml.lift d p)) (Fml.lift (c + 1) (Fml.lift d q))
        = Fml.imp (Fml.lift d (Fml.lift c p)) (Fml.lift d (Fml.lift c q))
    rw [Fml.lift_lift c d h p, Fml.lift_lift c d h q]
  | .all p =>
    show Fml.all (Fml.lift (c + 1 + 1) (Fml.lift (d + 1) p))
        = Fml.all (Fml.lift (d + 1) (Fml.lift (c + 1) p))
    rw [Fml.lift_lift (c + 1) (d + 1) (Nat.succ_le_succ h) p]
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
    simp only [Tm.subst, Tm.lift]
    by_cases hn : n = j
    · subst hn
      rw [if_pos rfl, if_neg (NatAux.not_lt_of_le h), if_pos rfl]
    · by_cases hlt : j < n
      · have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hlt
        rw [if_neg hn, if_pos hlt, Tm.lift,
          if_neg (NatAux.not_lt_of_le (Nat.le_trans h (NatAux.le_sub_one_of_lt hlt))),
          if_neg (NatAux.not_lt_of_le (Nat.le_trans h (Nat.le_of_lt hlt))),
          if_neg (fun e => hn (Nat.succ.inj e)), if_pos (Nat.succ_lt_succ hlt)]
        exact congrArg Tm.var (NatAux.sub_one_add_one hpos)
      · have hnj : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hn
        by_cases hc : n < c
        · have hnj1 : n < j + 1 := NatAux.lt_succ_of_lt hnj
          rw [if_neg hn, if_neg hlt, Tm.lift, if_pos hc, if_neg (Nat.ne_of_lt hnj1),
            if_neg (NatAux.not_lt_of_le (Nat.le_of_lt hnj1))]
        · rw [if_neg hn, if_neg hlt, Tm.lift, if_neg hc, if_neg (fun e => hn (Nat.succ.inj e)),
            if_neg (fun e => hlt (Nat.lt_of_succ_lt_succ e))]
  | .setOf φ =>
    show Tm.setOf (Fml.lift (c + 1) (Fml.subst (j + 1) (Tm.lift 0 t) φ))
        = Tm.setOf (Fml.subst (j + 1 + 1) (Tm.lift 0 (Tm.lift c t)) (Fml.lift (c + 1) φ))
    rw [Fml.lift_subst (c + 1) (j + 1) (Nat.succ_le_succ h) (Tm.lift 0 t) φ,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
theorem Fml.lift_subst (c j : Nat) (h : c ≤ j) (t : Tm) (φ : Fml) :
    Fml.lift c (Fml.subst j t φ) = Fml.subst (j + 1) (Tm.lift c t) (Fml.lift c φ) := by
  match φ with
  | .mem a b =>
    show Fml.mem (Tm.lift c (Tm.subst j t a)) (Tm.lift c (Tm.subst j t b))
        = Fml.mem (Tm.subst (j + 1) (Tm.lift c t) (Tm.lift c a))
                  (Tm.subst (j + 1) (Tm.lift c t) (Tm.lift c b))
    rw [Tm.lift_subst c j h t a, Tm.lift_subst c j h t b]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (Fml.lift c (Fml.subst j t p)) (Fml.lift c (Fml.subst j t q))
        = Fml.imp (Fml.subst (j + 1) (Tm.lift c t) (Fml.lift c p))
                  (Fml.subst (j + 1) (Tm.lift c t) (Fml.lift c q))
    rw [Fml.lift_subst c j h t p, Fml.lift_subst c j h t q]
  | .all p =>
    show Fml.all (Fml.lift (c + 1) (Fml.subst (j + 1) (Tm.lift 0 t) p))
        = Fml.all (Fml.subst (j + 1 + 1) (Tm.lift 0 (Tm.lift c t)) (Fml.lift (c + 1) p))
    rw [Fml.lift_subst (c + 1) (j + 1) (Nat.succ_le_succ h) (Tm.lift 0 t) p,
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
    simp only [Tm.subst]
    by_cases hn1 : n = k
    · subst hn1
      rw [if_pos rfl, if_neg (Nat.ne_of_lt (Nat.lt_succ_of_le h)),
        if_neg (NatAux.not_lt_of_le (Nat.le_succ_of_le h)), Tm.subst, if_pos rfl]
    · by_cases hn2 : n = a + 1
      · subst hn2
        rw [if_neg hn1, if_pos (Nat.lt_succ_of_le h), Tm.subst,
          if_pos (c := a + 1 - 1 = a) rfl, if_pos (c := a + 1 = a + 1) rfl, Tm.subst_lift]
      · by_cases hlt : k < n
        · have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hlt
          by_cases hb : a + 1 < n
          · have ha : a < n - 1 := NatAux.lt_sub_one_of_succ_lt hb
            have hk : k < n - 1 := Nat.lt_of_le_of_lt h ha
            rw [if_neg hn1, if_pos hlt, Tm.subst, if_neg (Nat.ne_of_gt ha), if_pos ha,
              if_neg hn2, if_pos hb, Tm.subst, if_neg (Nat.ne_of_gt hk), if_pos hk]
          · have hna : n ≤ a := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hb) hn2)
            have hp : n - 1 < n := Nat.sub_one_lt (Nat.ne_of_gt hpos)
            rw [if_neg hn1, if_pos hlt, Tm.subst,
              if_neg (fun (e : n - 1 = a) =>
                Nat.lt_irrefl a (Nat.lt_of_lt_of_le (show a < n by rw [← e]; exact hp) hna)),
              if_neg (NatAux.not_lt_of_le (Nat.le_trans (Nat.le_of_lt hp) hna)),
              if_neg hn2, if_neg hb, Tm.subst, if_neg hn1, if_pos hlt]
        · have hnk : n < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hn1
          have hna : n < a := Nat.lt_of_lt_of_le hnk h
          rw [if_neg hn1, if_neg hlt, Tm.subst, if_neg (Nat.ne_of_lt hna),
            if_neg (NatAux.not_lt_of_le (Nat.le_of_lt hna)), if_neg hn2,
            if_neg (NatAux.not_lt_of_le (Nat.le_succ_of_le (Nat.le_of_lt hna))),
            Tm.subst, if_neg hn1, if_neg hlt]
  | .setOf φ =>
    show Tm.setOf (Fml.subst (a + 1) (Tm.lift 0 u) (Fml.subst (k + 1) (Tm.lift 0 v) φ))
        = Tm.setOf (Fml.subst (k + 1) (Tm.lift 0 (Tm.subst a u v))
            (Fml.subst (a + 1 + 1) (Tm.lift 0 (Tm.lift k u)) φ))
    rw [Fml.subst_subst (a + 1) (k + 1) (Nat.succ_le_succ h) (Tm.lift 0 u) (Tm.lift 0 v) φ,
        Tm.lift_lift k 0 (Nat.zero_le k) u,
        ← Tm.lift_subst 0 a (Nat.zero_le a) u v]
theorem Fml.subst_subst (a k : Nat) (h : k ≤ a) (u v : Tm) (φ : Fml) :
    Fml.subst a u (Fml.subst k v φ)
      = Fml.subst k (Tm.subst a u v) (Fml.subst (a + 1) (Tm.lift k u) φ) := by
  match φ with
  | .mem x y =>
    show Fml.mem (Tm.subst a u (Tm.subst k v x)) (Tm.subst a u (Tm.subst k v y))
        = Fml.mem (Tm.subst k (Tm.subst a u v) (Tm.subst (a + 1) (Tm.lift k u) x))
                  (Tm.subst k (Tm.subst a u v) (Tm.subst (a + 1) (Tm.lift k u) y))
    rw [Tm.subst_subst a k h u v x, Tm.subst_subst a k h u v y]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (Fml.subst a u (Fml.subst k v p)) (Fml.subst a u (Fml.subst k v q))
        = Fml.imp (Fml.subst k (Tm.subst a u v) (Fml.subst (a + 1) (Tm.lift k u) p))
                  (Fml.subst k (Tm.subst a u v) (Fml.subst (a + 1) (Tm.lift k u) q))
    rw [Fml.subst_subst a k h u v p, Fml.subst_subst a k h u v q]
  | .all p =>
    show Fml.all (Fml.subst (a + 1) (Tm.lift 0 u) (Fml.subst (k + 1) (Tm.lift 0 v) p))
        = Fml.all (Fml.subst (k + 1) (Tm.lift 0 (Tm.subst a u v))
            (Fml.subst (a + 1 + 1) (Tm.lift 0 (Tm.lift k u)) p))
    rw [Fml.subst_subst (a + 1) (k + 1) (Nat.succ_le_succ h) (Tm.lift 0 u) (Tm.lift 0 v) p,
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
    simp only [Tm.subst, Tm.lift]
    by_cases hn : n = j
    · subst hn
      rw [if_pos rfl, if_pos (Nat.lt_succ_of_le h), if_pos rfl]
    · by_cases hlt : j < n
      · have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hlt
        by_cases hb : c < n
        · rw [if_neg hn, if_pos hlt, Tm.lift,
            if_neg (NatAux.not_lt_of_le (NatAux.le_sub_one_of_lt hb)),
            if_neg (NatAux.not_lt_of_le (Nat.succ_le_of_lt hb)),
            if_neg (fun e => Nat.not_succ_le_self n
              (Nat.le_trans (show n + 1 ≤ c by rw [e]; exact h) (Nat.le_of_lt hb))),
            if_pos (NatAux.lt_succ_of_lt hlt)]
          exact congrArg Tm.var (NatAux.sub_one_add_one hpos)
        · have hb' : n ≤ c := Nat.le_of_not_lt hb
          rw [if_neg hn, if_pos hlt, Tm.lift,
            if_pos (Nat.lt_of_lt_of_le (Nat.sub_one_lt (Nat.ne_of_gt hpos)) hb'),
            if_pos (Nat.lt_succ_of_le hb'), if_neg hn, if_pos hlt]
      · have hnj : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) hn
        have hnc : n < c := Nat.lt_of_lt_of_le hnj h
        rw [if_neg hn, if_neg hlt, Tm.lift, if_pos hnc, if_pos (NatAux.lt_succ_of_lt hnc),
          if_neg hn, if_neg hlt]
  | .setOf φ =>
    show Tm.setOf (Fml.lift (c + 1) (Fml.subst (j + 1) (Tm.lift 0 t) φ))
        = Tm.setOf (Fml.subst (j + 1) (Tm.lift 0 (Tm.lift c t)) (Fml.lift (c + 1 + 1) φ))
    rw [Fml.lift_subst' (j + 1) (c + 1) (Nat.succ_le_succ h) (Tm.lift 0 t) φ,
        Tm.lift_lift c 0 (Nat.zero_le c) t]
theorem Fml.lift_subst' (j c : Nat) (h : j ≤ c) (t : Tm) (φ : Fml) :
    Fml.lift c (Fml.subst j t φ) = Fml.subst j (Tm.lift c t) (Fml.lift (c + 1) φ) := by
  match φ with
  | .mem a b =>
    show Fml.mem (Tm.lift c (Tm.subst j t a)) (Tm.lift c (Tm.subst j t b))
        = Fml.mem (Tm.subst j (Tm.lift c t) (Tm.lift (c + 1) a))
                  (Tm.subst j (Tm.lift c t) (Tm.lift (c + 1) b))
    rw [Tm.lift_subst' j c h t a, Tm.lift_subst' j c h t b]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (Fml.lift c (Fml.subst j t p)) (Fml.lift c (Fml.subst j t q))
        = Fml.imp (Fml.subst j (Tm.lift c t) (Fml.lift (c + 1) p))
                  (Fml.subst j (Tm.lift c t) (Fml.lift (c + 1) q))
    rw [Fml.lift_subst' j c h t p, Fml.lift_subst' j c h t q]
  | .all p =>
    show Fml.all (Fml.lift (c + 1) (Fml.subst (j + 1) (Tm.lift 0 t) p))
        = Fml.all (Fml.subst (j + 1) (Tm.lift 0 (Tm.lift c t)) (Fml.lift (c + 1 + 1) p))
    rw [Fml.lift_subst' (j + 1) (c + 1) (Nat.succ_le_succ h) (Tm.lift 0 t) p,
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
  | .var n => rfl
  | .setOf ψ =>
    show Tm.setOf (piFml (Fml.lift (c + 1) ψ)) = Tm.setOf (Fml.lift (c + 1) (piFml ψ))
    rw [piFml_lift (c + 1) ψ]
theorem piFml_lift (c : Nat) (φ : Fml) : piFml (Fml.lift c φ) = Fml.lift c (piFml φ) := by
  match φ with
  | .mem a b =>
    match b with
    | .setOf ψ =>
      show Fml.subst 0 (piTm (Tm.lift c a)) (piFml (Fml.lift (c + 1) ψ))
          = Fml.lift c (Fml.subst 0 (piTm a) (piFml ψ))
      rw [piTm_lift c a, piFml_lift (c + 1) ψ,
          Fml.lift_subst' 0 c (Nat.zero_le c) (piTm a) (piFml ψ)]
    | .var m =>
      show Fml.mem (piTm (Tm.lift c a)) (Tm.lift c (Tm.var m))
          = Fml.mem (Tm.lift c (piTm a)) (Tm.lift c (Tm.var m))
      rw [piTm_lift c a]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (piFml (Fml.lift c p)) (piFml (Fml.lift c q))
        = Fml.imp (Fml.lift c (piFml p)) (Fml.lift c (piFml q))
    rw [piFml_lift c p, piFml_lift c q]
  | .all p =>
    show Fml.all (piFml (Fml.lift (c + 1) p)) = Fml.all (Fml.lift (c + 1) (piFml p))
    rw [piFml_lift (c + 1) p]
end

-- ============================================================
-- §11. π commutes with substitution of a variable (mutual) — the keystone
-- ============================================================

-- Lifting a variable past cutoff 0 is just incrementing it.
theorem liftz (i : Nat) : Tm.lift 0 (Tm.var i) = Tm.var (i + 1) := by
  show Tm.var (if i < 0 then i else i + 1) = Tm.var (i + 1)
  rw [if_neg (Nat.not_lt_zero i)]

mutual
theorem piTm_subst (j i : Nat) (u : Tm) :
    piTm (Tm.subst j (Tm.var i) u) = Tm.subst j (Tm.var i) (piTm u) := by
  match u with
  | .var n =>
    show piTm (if n = j then Tm.var i else Tm.var (if j < n then n - 1 else n))
        = (if n = j then Tm.var i else Tm.var (if j < n then n - 1 else n))
    by_cases hn : n = j
    · rw [if_pos hn]; rfl
    · rw [if_neg hn]; rfl
  | .setOf ψ =>
    show Tm.setOf (piFml (Fml.subst (j + 1) (Tm.lift 0 (Tm.var i)) ψ))
        = Tm.setOf (Fml.subst (j + 1) (Tm.lift 0 (Tm.var i)) (piFml ψ))
    rw [liftz, piFml_subst (j + 1) (i + 1) ψ]
theorem piFml_subst (j i : Nat) (φ : Fml) :
    piFml (Fml.subst j (Tm.var i) φ) = Fml.subst j (Tm.var i) (piFml φ) := by
  match φ with
  | .mem a b =>
    match b with
    | .setOf ψ =>
      show Fml.subst 0 (piTm (Tm.subst j (Tm.var i) a))
              (piFml (Fml.subst (j + 1) (Tm.lift 0 (Tm.var i)) ψ))
          = Fml.subst j (Tm.var i) (Fml.subst 0 (piTm a) (piFml ψ))
      rw [liftz, piTm_subst j i a, piFml_subst (j + 1) (i + 1) ψ,
          Fml.subst_subst j 0 (Nat.zero_le j) (Tm.var i) (piTm a) (piFml ψ), liftz]
    | .var m =>
      show piFml (Fml.mem (Tm.subst j (Tm.var i) a)
              (if m = j then Tm.var i else Tm.var (if j < m then m - 1 else m)))
          = Fml.mem (Tm.subst j (Tm.var i) (piTm a))
              (if m = j then Tm.var i else Tm.var (if j < m then m - 1 else m))
      by_cases hm : m = j
      · rw [if_pos hm]
        show Fml.mem (piTm (Tm.subst j (Tm.var i) a)) (Tm.var i)
            = Fml.mem (Tm.subst j (Tm.var i) (piTm a)) (Tm.var i)
        rw [piTm_subst j i a]
      · rw [if_neg hm]
        show Fml.mem (piTm (Tm.subst j (Tm.var i) a)) (Tm.var (if j < m then m - 1 else m))
            = Fml.mem (Tm.subst j (Tm.var i) (piTm a)) (Tm.var (if j < m then m - 1 else m))
        rw [piTm_subst j i a]
  | .bot => rfl
  | .imp p q =>
    show Fml.imp (piFml (Fml.subst j (Tm.var i) p)) (piFml (Fml.subst j (Tm.var i) q))
        = Fml.imp (Fml.subst j (Tm.var i) (piFml p)) (Fml.subst j (Tm.var i) (piFml q))
    rw [piFml_subst j i p, piFml_subst j i q]
  | .all p =>
    show Fml.all (piFml (Fml.subst (j + 1) (Tm.lift 0 (Tm.var i)) p))
        = Fml.all (Fml.subst (j + 1) (Tm.lift 0 (Tm.var i)) (piFml p))
    rw [liftz, piFml_subst (j + 1) (i + 1) p]
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
