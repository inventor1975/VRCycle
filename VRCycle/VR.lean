-- VR. A Formal System (DOI 10.5281/zenodo.20212092)
-- Lean 4 formalisation of the VR formal system

namespace VR

-- ============================================================
-- §1. Primitives (Part I, §1)
-- ============================================================

-- The type of VR objects: all objects generated from ∅ by applying t.
-- Part I, §1 (Primitives) + A4 (Induction): the O_n exhaust the entire domain.
--
-- Constructor void  — primitive ∅ (constant)
-- Constructor succ  — primitive t (unary operator, succession)
--
-- Lean's induction principle (VRObj.rec) expresses A4:
-- any property that holds for void and is inherited through succ
-- holds for all VR objects.
--
-- Preprint, A1: «F is identified with ∅ at the logical level».
-- This is a semantic identification of two points: F in VRBool and void in VRObj —
-- the same base point viewed in two registers (logical and ontological).
-- In this formalisation the identification is not used by any VR theorem.
-- If a future work (VR-Sets, VR-Forms) requires a formal bridge, it will be
-- introduced at that point.
inductive VRObj : Type where
  | void : VRObj           -- ∅  (Def. 4: O₀ := ∅)
  | succ : VRObj → VRObj   -- t  (Def. 5: O_{n+1} := t(O_n))

-- ============================================================
-- §1–§2. Logical layer (Part I, §1 + §2)
-- ============================================================

-- The logical layer of VR: {F, T}.
-- F is identified with ∅ at the logical level (A1).
-- T is defined as impl F F (Def. 1, §4).
inductive VRBool : Type where
  | F : VRBool   -- false / ∅
  | T : VRBool   -- true

-- §1. Binary operator impl (the primitive → of VR).
-- A2 (§2): truth table of classical implication.
-- Notation is intentionally not introduced at this stage
-- to avoid conflicts with reserved mathlib symbols.
def impl : VRBool → VRBool → VRBool
  | VRBool.F, _        => VRBool.T
  | VRBool.T, VRBool.F => VRBool.F
  | VRBool.T, VRBool.T => VRBool.T

-- ============================================================
-- §2. Axioms A1 and A2 (Part I, §2)
-- ============================================================

-- A1 (§2). Generativity.
-- impl F F = T and impl F T = T.
-- From F, via impl, both values {F, T} are reachable.
-- A1 corresponds to the first two rows of the A2 truth table.
theorem A1_1 : impl VRBool.F VRBool.F = VRBool.T := rfl
theorem A1_2 : impl VRBool.F VRBool.T = VRBool.T := rfl

-- A1 (§2). Reachability from F.
-- «From F, via →, both values {F, T} are reachable.»
-- Formalised via predicate closure: {F} generates all of VRBool.
-- Any S containing F and closed under impl contains every element of VRBool.
theorem A1_F_reaches_both : ∀ (b : VRBool) (S : VRBool → Prop),
    S VRBool.F →
    (∀ x y, S x → S y → S (impl x y)) →
    S b := by
  intro b S hF hClosed
  cases b with
  | F => exact hF
  | T => exact hClosed VRBool.F VRBool.F hF hF

-- A1 (§2). Reachability from T.
-- «From T, via →, only T is reachable.»
-- Formalised via predicate closure: {T} is the minimal closed set.
-- If b belongs to every S containing T and closed under impl, then b = T.
theorem A1_T_reaches_only_T : ∀ (b : VRBool),
    (∀ (S : VRBool → Prop),
      S VRBool.T →
      (∀ x y, S x → S y → S (impl x y)) →
      S b) →
    b = VRBool.T := by
  intro b hb
  exact hb (· = VRBool.T) rfl (by intro x y hx hy; subst hx; subst hy; rfl)

-- A2 (§2). Full truth table of implication.
-- impl is the function {F,T}×{F,T} → {F,T} given by the classical truth table.
theorem A2_FF : impl VRBool.F VRBool.F = VRBool.T := rfl
theorem A2_FT : impl VRBool.F VRBool.T = VRBool.T := rfl
theorem A2_TF : impl VRBool.T VRBool.F = VRBool.F := rfl
theorem A2_TT : impl VRBool.T VRBool.T = VRBool.T := rfl

-- ============================================================
-- §3. Basis — derived logical operators (Part I, §3)
-- ============================================================

-- §3. Negation: ¬x := x → F
def vnot (x : VRBool) : VRBool := impl x VRBool.F

-- §3. Disjunction: x ∨ y := (x → y) → y
def vor (x y : VRBool) : VRBool := impl (impl x y) y

-- §3. Conjunction: x ∧ y := ¬(¬x ∨ ¬y)
def vand (x y : VRBool) : VRBool := vnot (vor (vnot x) (vnot y))

-- §3. Biconditional: x ↔ y := (x → y) ∧ (y → x)
def viff (x y : VRBool) : VRBool := vand (impl x y) (impl y x)

-- Truth tables of the derived operators.
-- All proved by rfl: definitions unfold into impl,
-- which unfolds into VRBool constructors.

-- vnot
theorem vnot_F : vnot VRBool.F = VRBool.T := rfl
theorem vnot_T : vnot VRBool.T = VRBool.F := rfl

-- vor
theorem vor_FF : vor VRBool.F VRBool.F = VRBool.F := rfl
theorem vor_FT : vor VRBool.F VRBool.T = VRBool.T := rfl
theorem vor_TF : vor VRBool.T VRBool.F = VRBool.T := rfl
theorem vor_TT : vor VRBool.T VRBool.T = VRBool.T := rfl

-- vand
theorem vand_FF : vand VRBool.F VRBool.F = VRBool.F := rfl
theorem vand_FT : vand VRBool.F VRBool.T = VRBool.F := rfl
theorem vand_TF : vand VRBool.T VRBool.F = VRBool.F := rfl
theorem vand_TT : vand VRBool.T VRBool.T = VRBool.T := rfl

-- viff
theorem viff_FF : viff VRBool.F VRBool.F = VRBool.T := rfl
theorem viff_FT : viff VRBool.F VRBool.T = VRBool.F := rfl
theorem viff_TF : viff VRBool.T VRBool.F = VRBool.F := rfl
theorem viff_TT : viff VRBool.T VRBool.T = VRBool.T := rfl

-- ============================================================
-- §4. Definitions (Part I, §4)
-- ============================================================

-- Def. 1 (§4). T := impl F F.
-- In this formalisation T is a standalone constructor of VRBool;
-- the equality impl F F = T is recorded as a named fact.
theorem T_def : impl VRBool.F VRBool.F = VRBool.T := rfl

-- Def. 2 (§4). Leibnizian Equality.
-- «x = y := ∀p: p(x) ↔ p(y)»
--
-- Quantified over predicates VRObj → Prop (Variant II).
-- Lean's Iff (↔) is used, not viff from VRBool:
--   — the preprint §10 interprets «for all properties» as a schema over all
--     arithmetic formulae (= all Lean predicates);
--   — Lean Iff supports direct inference, making Theorem 4 provable.
-- Named vrEq to avoid collision with Lean's built-in equality =.
--
-- Methodological note on two levels of ↔.
-- In the preprint the symbol ↔ is used in two distinct senses:
--   (1) In §3, ↔ is defined as viff — an operator on VRBool, two-valued.
--   (2) In §4 (Def. 2), ↔ stands between p(x) and p(y), which for structural
--       predicates (used in §5, Th. 3, Th. 4) are metatheoretic propositions,
--       not VRBool values.
-- Structural predicates (e.g. «contains x as an element») are not expressible
-- in VRBool, since mem is recursive over the object's structure. Therefore
-- the actual use of ↔ in Def. 2 is metatheoretic equivalence, distinct from
-- the ↔ of §3. The Lean formalisation makes this explicit by choosing Iff.
def vrEq (x y : VRObj) : Prop := ∀ (p : VRObj → Prop), p x ↔ p y

-- Def. 3 (§4). Distinctness.
-- «x ≠ y := ¬(x = y)»
def vrNe (x y : VRObj) : Prop := ¬ vrEq x y

-- Bridge lemma: Lean equality implies vrEq (one direction).
-- The converse (vrEq → =) will be needed in Theorem 4 (step 5.5); introduced there.
theorem Eq_to_vrEq (x y : VRObj) (h : x = y) : vrEq x y := by
  intro p; subst h; exact Iff.rfl

-- ============================================================
-- §2. Axiom A3 — Succession (Part I, §2)
-- ============================================================

-- A3 (§2). Succession.
-- «The operator t is defined on ∅ and on every object generated from it.
--  For every x in the domain of t: t(x) = x ∪ {x}, so x ∈ t(x) and x ⊂ t(x).»
--
-- In the formalisation t is implemented as constructor succ (see VRObj above).
-- The operations ∪ and {·} are not introduced as primitives:
-- t(x) = x ∪ {x} is the defining equation, not a theorem.
-- The substantive content of A3 (x ∈ t(x) and x ⊂ t(x)) is proved from mem.

-- Membership relation on VRObj.
-- x ∈ void   — false (the empty set contains nothing).
-- x ∈ succ y — x = y (x is y itself) or x ∈ y (x lies deeper).
-- Recursion is structural on the second argument (y decreases from succ y to y).
def mem : VRObj → VRObj → Prop
  | _, VRObj.void   => False
  | x, VRObj.succ y => x = y ∨ mem x y

-- Subset relation on VRObj.
-- x ⊆ y — every element of x belongs to y.
def subset (x y : VRObj) : Prop := ∀ z, mem z x → mem z y

-- A3, part 1 (§2): x ∈ t(x) for every x.
-- «x ∈ t(x)» = mem x (succ x) = (x = x ∨ mem x x) = True.
theorem A3_mem_self : ∀ x : VRObj, mem x (VRObj.succ x) :=
  fun _ => Or.inl rfl

-- A3, part 2 (§2): x ⊆ t(x) for every x.
-- If z ∈ x, then z ∈ succ x = (z = x ∨ z ∈ x), true by Or.inr.
theorem A3_subset_succ : ∀ x : VRObj, subset x (VRObj.succ x) :=
  fun _ _ hz => Or.inr hz

-- ============================================================
-- §2. Axiom A4 — Induction (Part I, §2)
-- ============================================================

-- A4 (§2). Induction.
-- «If P is a property of objects of the system, and:
--  (i) P(O₀) holds,
--  (ii) for every x: P(x) → P(t(x)),
--  then P(O_n) holds for all n.»
--
-- In Lean, A4 is not postulated: it is provable as a theorem,
-- because the recursor VRObj.rec is an automatic consequence of
-- declaring VRObj as an inductive type.
-- This is a methodological strengthening: the VR axiom becomes a Lean theorem.
theorem A4_induction (P : VRObj → Prop)
    (h0 : P VRObj.void)
    (hs : ∀ x, P x → P (VRObj.succ x)) :
    ∀ n, P n := by
  intro n
  induction n with
  | void    => exact h0
  | succ x ih => exact hs x ih

-- A4, equivalent formulation (§2):
-- «The O_n exhaust all objects generated from ∅ via t.»
-- Every VRObj is either void or succ of something — no third option.
theorem A4_exhaustion : ∀ x : VRObj, x = VRObj.void ∨ ∃ y, x = VRObj.succ y := by
  intro x
  cases x with
  | void   => exact Or.inl rfl
  | succ y => exact Or.inr ⟨y, rfl⟩

-- ============================================================
-- §5. Lemma: t(x) ≠ x (Part I, §5)
-- ============================================================

-- The proof of §5 (t(x) ≠ x) is purely structural,
-- without introducing an external measure (depth : VRObj → Nat). Key components:
--   (1) mem_succ_left — a «lowering» lemma;
--   (2) mem_asymm    — antisymmetry of mem by induction on y;
--   (3) not_mem_self — irreflexivity as a consequence of antisymmetry.
-- This confirms that the acyclicity of ∈ in VR is provable using only
-- the internal means of the inductive type VRObj.

-- Auxiliary: succ a ∈ b → a ∈ b.
-- If the «successor» of a belongs to b, then a itself belongs to b.
-- Proved by induction on b; uses only mem and VRObj.rec.
private theorem mem_succ_left (b : VRObj) : ∀ a, mem (VRObj.succ a) b → mem a b := by
  induction b with
  | void => intro a h; exact h.elim
  | succ c ih =>
    intro a h
    have h' : VRObj.succ a = c ∨ mem (VRObj.succ a) c := h
    cases h' with
    | inl hac =>
      subst hac
      -- goal: mem a (succ (succ a)) = a = succ a ∨ mem a (succ a)
      -- mem a (succ a) = a = a ∨ mem a a; take Or.inl rfl
      exact Or.inr (show mem a (VRObj.succ a) from Or.inl rfl)
    | inr hmc =>
      exact Or.inr (ih a hmc)

-- Antisymmetry: x ∈ y and y ∈ x are incompatible.
-- Key step toward not_mem_self; proved by induction on y
-- using mem_succ_left.
private theorem mem_asymm (y : VRObj) : ∀ x, mem x y → ¬ mem y x := by
  induction y with
  | void => intro x h; exact h.elim
  | succ z ih =>
    intro x h hmyx
    have h' : x = z ∨ mem x z := h
    have hzx : mem z x := mem_succ_left x z hmyx
    cases h' with
    | inl hxz =>
      -- hxz : x = z; rewrite x → z in hzx, obtaining mem z z
      rw [hxz] at hzx
      exact ih z hzx hzx
    | inr hxz =>
      -- hxz : mem x z, hzx : mem z x; ih x hxz : ¬ mem z x
      exact ih x hxz hzx

-- Lemma: no object contains itself.
theorem not_mem_self : ∀ x : VRObj, ¬ mem x x :=
  fun x h => (mem_asymm x x h) h

-- §5 (Preprint, Part I, §5): t(x) ≠ x for every x.
-- If vrEq (succ x) x, then with predicate p := mem x we get
-- mem x (succ x) ↔ mem x x. The left side is true (A3_mem_self),
-- the right side is false (not_mem_self). Contradiction.
theorem succ_ne_self : ∀ x : VRObj, vrNe (VRObj.succ x) x :=
  fun x heq => not_mem_self x ((heq (fun y => mem x y)).mp (A3_mem_self x))

-- ============================================================
-- §4, §6. Von Neumann ordinals — Defs. 4–6 (Part I, §4, §6)
-- ============================================================

-- Def. 4–6 (§4, §6). Construction of von Neumann ordinals.
--
-- The function O : Nat → VRObj maps metalanguage indices to VR objects.
-- Lean's Nat serves as an external source of names, not part of VR itself.
-- The VR objects are the image of O in VRObj:
--   O 0 = void, O 1 = succ void, O 2 = succ (succ void), ...
--
-- Surjectivity of O onto VRObj (i.e. ∀ x : VRObj, ∃ n, x = O n) expresses
-- A4_exhaustion at the level of naming. Bijectivity O : Nat → VRObj —
-- a substantive claim proved at Stage 5 (Peano equivalence, Theorem 11).
--
-- At this stage O is a constructive naming, not an identification.
def O : Nat → VRObj
  | 0     => VRObj.void
  | n + 1 => VRObj.succ (O n)

-- ============================================================
-- §4. Concrete values (Part I, §4) — Def. 3.4
-- ============================================================

-- O₁ = {∅}, O₂ = {∅, {∅}}, O₃ = {∅, {∅}, {∅, {∅}}}.
-- In VRObj encoding: successive applications of succ to void.
-- All proved by rfl — direct computation from def O.
theorem O_one   : O 1 = VRObj.succ VRObj.void                               := rfl
theorem O_two   : O 2 = VRObj.succ (VRObj.succ VRObj.void)                  := rfl
theorem O_three : O 3 = VRObj.succ (VRObj.succ (VRObj.succ VRObj.void))     := rfl

-- ============================================================
-- §6. Membership lemma (Part I, §6) — Def. 3.5
-- ============================================================

-- Lemma (§6): O_k ∈ O_n for every k < n.
-- «each O_n contains all previous O₀, ..., O_{n−1}»
--
-- Proved by induction on the proof of k < n, i.e. on
-- the constructors of Nat.le (refl / step).
-- Does not use omega or arithmetic lemmas — only the structure of Nat.le.
theorem O_mem_lt : ∀ k n : Nat, k < n → mem (O k) (O n) := by
  intro k n h
  induction h with
  | refl      => exact A3_mem_self (O k)
  | step _ ih => exact Or.inr ih

-- ============================================================
-- §7. Arithmetic operations (Part I, §7) — Defs. 7–9
-- ============================================================

-- Def. 7 (§7). Addition on VRObj.
-- a + void   := a          (neutral element)
-- a + succ b := succ (a + b)  (recursion step)
-- Structural recursion on the second argument.
def vadd : VRObj → VRObj → VRObj
  | a, VRObj.void   => a
  | a, VRObj.succ b => VRObj.succ (vadd a b)

-- Def. 8 (§7). Multiplication on VRObj.
-- a × void   := void         (absorbing zero)
-- a × succ b := (a × b) + a  (recursion step)
-- Structural recursion on the second argument; uses vadd.
def vmul : VRObj → VRObj → VRObj
  | _, VRObj.void   => VRObj.void
  | a, VRObj.succ b => vadd (vmul a b) a

-- Def. 9 (§7). Exponentiation on VRObj.
-- a ^ void   := succ void  (= O₁ by Def. 4+5; base of exponentiation is one)
-- a ^ succ b := (a ^ b) × a
-- Structural recursion on the exponent (second argument). Uses vmul.
-- Note: succ void here is the same as O₁ in the preprint; the equality
-- vpow a void = O 1 is provable by rfl via O_one, if needed in theorems.
def vpow : VRObj → VRObj → VRObj
  | _, VRObj.void   => VRObj.succ VRObj.void
  | a, VRObj.succ b => vmul (vpow a b) a

-- ============================================================
-- §7. T1 — Commutativity of addition (Part I, §7)
-- ============================================================

-- Auxiliary (for T1): left neutral element of vadd.
-- void + b = b  (right neutral vadd a void = a follows directly from def)
-- Proved by induction on b.
theorem vadd_zero_left : ∀ b : VRObj, vadd VRObj.void b = b := by
  intro b
  induction b with
  | void      => rfl
  | succ c ih => exact congrArg VRObj.succ ih

-- Auxiliary (for T1): left succ passes through vadd.
-- succ a + b = succ (a + b)  (right analogue: vadd a (succ b) = succ (vadd a b) — def)
-- Proved by induction on b.
theorem vadd_succ_left : ∀ a b : VRObj, vadd (VRObj.succ a) b = VRObj.succ (vadd a b) := by
  intro a b
  induction b with
  | void      => rfl
  | succ c ih => exact congrArg VRObj.succ ih

-- T1 (§7): commutativity of addition.
-- a + b = b + a for all VR objects.
-- Proved by induction on b, using vadd_zero_left and vadd_succ_left.
theorem T1_vadd_comm : ∀ a b : VRObj, vadd a b = vadd b a := by
  intro a b
  induction b with
  | void      => exact (vadd_zero_left a).symm
  | succ c ih =>
    rw [vadd_succ_left]
    exact congrArg VRObj.succ ih

-- ============================================================
-- §7. T2 — Associativity of addition (Part I, §7)
-- ============================================================

-- T2 (§7): associativity of addition.
-- (a + b) + c = a + (b + c) for all VR objects.
-- Proved by direct induction on c; no auxiliary lemmas needed.
theorem T2_vadd_assoc : ∀ a b c : VRObj, vadd (vadd a b) c = vadd a (vadd b c) := by
  intro a b c
  induction c with
  | void      => rfl
  | succ d ih => exact congrArg VRObj.succ ih

-- ============================================================
-- §7. T3 — Distributivity (Part I, §7)
-- ============================================================

-- T3 (§7): distributivity of multiplication over addition.
-- a × (b + c) = (a × b) + (a × c) for all VR objects.
-- Proved by induction on c; uses T2_vadd_assoc. No new lemmas.
theorem T3_vmul_distrib : ∀ a b c : VRObj, vmul a (vadd b c) = vadd (vmul a b) (vmul a c) := by
  intro a b c
  induction c with
  | void      => rfl
  | succ d ih =>
    -- after def-reduction:
    -- LHS = vadd (vmul a (vadd b d)) a
    -- RHS = vadd (vmul a b) (vadd (vmul a d) a)
    -- ih rewrites the first summand, T2 closes associativity
    show vadd (vmul a (vadd b d)) a = vadd (vmul a b) (vadd (vmul a d) a)
    rw [ih]
    exact T2_vadd_assoc (vmul a b) (vmul a d) a

-- ============================================================
-- §7. T4 — O₁ + O₁ = O₂ (Part I, §7)
-- ============================================================

-- T4 (§7): O₁ + O₁ = O₂.
-- Proved by rfl: two def-reductions of vadd close the goal.
theorem T4_one_plus_one : vadd (O 1) (O 1) = O 2 := rfl

-- ============================================================
-- §9 (Part II). Peano correspondence — Step 5.1
-- ============================================================

-- Translator ℕ → VR (Part II, §9).
-- The defining equations of O are extracted as named theorems to explicitly
-- record the correspondence «0 ↦ O₀, S ↦ t» from preprint §9.
-- Both proved by rfl from def O.

-- 0 ↦ O₀ = ∅
theorem O_zero : O 0 = VRObj.void := rfl

-- Nat.succ ↦ VRObj.succ (= t)
theorem O_succ : ∀ n : Nat, O (n + 1) = VRObj.succ (O n) := fun _ => rfl

-- ============================================================
-- §10. P1, P2 — absorbed by typing (Part II, §10)
-- ============================================================

-- §10, Theorems P1 and P2 in VR.
--
-- The preprint states:
--   P1: «O₀ is an object of the system»
--   P2: «For every O_n, t(O_n) exists and is an object of the system»
--
-- In a first-order untyped formulation of Peano these claims require
-- existential proof (existence of an object in ℕ).
-- In Lean's typed formalisation they become typing statements:
--   P1: O 0 : VRObj — immediate from the definition of O (def O, first case).
--   P2: VRObj.succ : VRObj → VRObj — a total function by its type signature.
--
-- They are not introduced as separate theorems — they have become syntax.
-- This is a methodological observation: typing absorbs part of the Peano axioms.

-- ============================================================
-- §10. P3 — Theorem 4: t(O_n) ≠ O₀ (Part II, §10)
-- ============================================================

-- §10, Theorem 4 (P3 in VR): t(O_n) ≠ O₀.
-- succ x ≠ void for every x : VRObj.
--
-- Two proof paths:
--   (1) Via the mem property (preprint §5): void contains 0 elements,
--       succ x contains x as an element (A3_mem_self). If succ x = void,
--       then x ∈ void — false. Formally: A3_mem_self x ▸ h ▸ id.
--   (2) Via VRObj.noConfusion (Lean 4): void and succ are distinct
--       constructors; equality between them is refuted automatically.
-- Path (2) is used here; path (1) is recorded in the comment.
theorem P3_succ_ne_zero : ∀ x : VRObj, VRObj.succ x ≠ VRObj.void := by
  intro x h
  exact VRObj.noConfusion h

-- ============================================================
-- §10. P4 — Theorem 5: injectivity of t (Part II, §10)
-- ============================================================

-- §10, Theorem 5 (P4 in VR): injectivity of t under Leibnizian identity.
-- Exact preprint form: = in Theorem 5 is vrEq (Def. 2, §4).
-- Proof via a «revealing» predicate:
--   q z := match z with | void => True | succ w => p w
-- Then q (succ x) = p x and q (succ y) = p y by def-reduction,
-- and vrEq (succ x) (succ y) applied to q gives p x ↔ p y directly.
theorem P4_succ_inj_leibniz :
    ∀ x y : VRObj, vrEq (VRObj.succ x) (VRObj.succ y) → vrEq x y :=
  fun _ _ h p =>
    h (fun z => match z with
      | VRObj.void   => True
      | VRObj.succ w => p w)

-- Practical form of P4 via Lean Eq (needed in Theorem 11, §5.7).
-- Proved independently of P4_succ_inj_leibniz via the projection function
-- that extracts the constructor argument.
-- The reverse bridge vrEq → Eq is not used and not needed.
theorem P4_succ_inj :
    ∀ x y : VRObj, VRObj.succ x = VRObj.succ y → x = y :=
  fun _ _ h =>
    congrArg (fun z => match z with | VRObj.void => VRObj.void | VRObj.succ w => w) h

-- ============================================================
-- §10. P5 — Theorem 6: induction principle (Part II, §10)
-- ============================================================

-- §10, Theorem 6 (P5 in VR): induction principle.
-- P5 is Peano's induction axiom in VR terms.
-- Coincides with A4_induction (§2, Stage 1): no new proof is needed.
-- Introduced as a named alias for explicit correspondence with Peano axioms.
theorem P5_induction : ∀ (P : VRObj → Prop),
    P VRObj.void → (∀ x, P x → P (VRObj.succ x)) → ∀ n, P n :=
  A4_induction

-- ============================================================
-- §11. Theorem 11 — VR–PA equivalence (Part II, §11)
-- ============================================================

-- O_inv : VRObj → Nat — the inverse of O.
--
-- Corresponds to the Gödel encoding in §10 of the preprint:
--   ⌜∅⌝ := 0
--   ⌜t(x)⌝ := ⌜x⌝ + 1
-- The preprint describes this as a metatheoretic procedure.
-- In Lean it is an internal structural function, verified by the compiler.
-- This is a strengthening: the preprint's metatheory becomes a first-order function.
--
-- The existence of O_inv as a function VRObj → Nat does not introduce Nat into VR.
-- VRObj and Nat are two independent types; O and O_inv are the bridge between them.
def O_inv : VRObj → Nat
  | VRObj.void   => 0
  | VRObj.succ x => O_inv x + 1

-- Left inverse: O_inv (O n) = n.
-- Proved by induction on n; congrArg (· + 1) unfolds the step.
theorem O_left_inv : ∀ n : Nat, O_inv (O n) = n := by
  intro n
  induction n with
  | zero      => rfl
  | succ k ih => exact congrArg (· + 1) ih

-- Right inverse: O (O_inv x) = x.
-- Proved by induction on x; congrArg succ unfolds the step.
theorem O_right_inv : ∀ x : VRObj, O (O_inv x) = x := by
  intro x
  induction x with
  | void      => rfl
  | succ y ih => exact congrArg VRObj.succ ih

-- Addition isomorphism: O (m + n) = vadd (O m) (O n).
-- Direct induction on n; T1–T4 not used.
-- The recursion schemes of Nat.add and vadd are symmetric on the right argument.
theorem O_add : ∀ m n : Nat, O (m + n) = vadd (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih => exact congrArg VRObj.succ ih

-- Multiplication isomorphism: O (m * n) = vmul (O m) (O n).
-- Direct induction on n; uses O_add. T1–T4 not used.
theorem O_mul : ∀ m n : Nat, O (m * n) = vmul (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih =>
    -- Nat.mul: m * (k+1) = m*k + m  (def)
    -- vmul:   vmul (O m) (succ (O k)) = vadd (vmul (O m) (O k)) (O m)  (def)
    show O (m * k + m) = vadd (vmul (O m) (O k)) (O m)
    rw [O_add]
    exact congrArg (fun x => vadd x (O m)) ih

-- Exponentiation isomorphism: O (m ^ n) = vpow (O m) (O n).
-- Direct induction on n; uses O_mul. T1–T4 not used.
theorem O_pow : ∀ m n : Nat, O (m ^ n) = vpow (O m) (O n) := by
  intro m n
  induction n with
  | zero      => rfl
  | succ k ih =>
    -- Nat.pow: m^(k+1) = m^k * m  (def)
    -- vpow:   vpow (O m) (succ (O k)) = vmul (vpow (O m) (O k)) (O m)  (def)
    show O (m ^ k * m) = vmul (vpow (O m) (O k)) (O m)
    rw [O_mul]
    exact congrArg (fun x => vmul x (O m)) ih

-- §11 (Part II), Equivalence Theorem.
--
-- Preprint: «VR and PA are arithmetically equivalent: the ℕ-theoretic content
-- of one system corresponds bijectively to the ℕ-theoretic content of the other».
-- Stated as a metatheoretic equivalence of theorem sets.
--
-- Lean gives a strengthened form: a structural isomorphism Nat ≃ VRObj
-- as a concrete constructive object preserving all operations.
-- The preprint's theorem-level equivalence follows trivially:
-- any theorem proved on one side transfers through forward/backward.
--
-- Nine fields cover:
--   the bijection (forward + backward + left_inv + right_inv),
--   preservation of zero and successor (preserve_zero + preserve_succ),
--   preservation of arithmetic (preserve_add + preserve_mul + preserve_pow).
structure VR_PA_iso where
  forward       : Nat → VRObj
  backward      : VRObj → Nat
  left_inv      : ∀ n, backward (forward n) = n
  right_inv     : ∀ x, forward (backward x) = x
  preserve_zero : forward 0 = VRObj.void
  preserve_succ : ∀ n, forward (n + 1) = VRObj.succ (forward n)
  preserve_add  : ∀ m n, forward (m + n) = vadd (forward m) (forward n)
  preserve_mul  : ∀ m n, forward (m * n) = vmul (forward m) (forward n)
  preserve_pow  : ∀ m n, forward (m ^ n) = vpow (forward m) (forward n)

def Theorem_11_VR_PA : VR_PA_iso := {
  forward       := O
  backward      := O_inv
  left_inv      := O_left_inv
  right_inv     := O_right_inv
  preserve_zero := O_zero
  preserve_succ := O_succ
  preserve_add  := O_add
  preserve_mul  := O_mul
  preserve_pow  := O_pow
}

end VR
