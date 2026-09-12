-- VRCycle/Meta/CSRNorm.lean — `csr_ring`: a `ring` on the EMPTY axiom list, up to an equivalence.
--
-- Integrity programme, instrument (2026-09-12).  Mathlib's `ring`, `ac_rfl` and `simp`-closures
-- reach `propext`; `simp`-driven AC-normalisation (ordered rewriting) is axiom-free but blows up on
-- the pair-of-pairs algebra of ℤ_VR/ℚ_VR (a four-pair identity did not finish in 300 s).
--
-- Here: a *commutative ring up to an equivalence* is a structure `CSR α` — a relation `r` that is
-- an equivalence and a congruence for `add`/`mul`/`neg`, plus the ring laws stated up to `r`.
-- Polynomial expressions are reified into `PE`, normalised into sorted signed monomials by a
-- computable `norm`, and `norm_sound : r (evalP (norm e)) (eval e)` is proved ONCE by induction
-- from the fields alone.  Two expressions with the same normal form are then `r`-related by
-- `eq_of_norm`, the equality of normal forms being decided by kernel evaluation (`decide`,
-- `Nat.decEq`/`instDecidableEqList` — both on `[]`).  No cancellation `m + (−m) = 0`: the
-- normaliser is sound for every commutative ring, complete for semiring identities and for ring
-- identities that need no cancellation; the few cancellations are done by hand.
--
-- Instances: `VRObj` (r = Eq), `IntExpr` (r = intEq), `QExpr` (r = qEq) — see Numbers/.
import Lean

namespace VR.CSR

open Lean Meta Elab Tactic

-- No auto-generated `injEq` lemmas (they carry `propext`).
set_option genInjectivity false

/-- A commutative ring up to an equivalence `r` (negation may be the identity for semirings). -/
structure CSR (α : Type) where
  r : α → α → Prop
  refl : ∀ a, r a a
  symm : ∀ {a b}, r a b → r b a
  trans : ∀ {a b c}, r a b → r b c → r a c
  add : α → α → α
  mul : α → α → α
  neg : α → α
  zero : α
  one : α
  add_congr : ∀ {a a' b b'}, r a a' → r b b' → r (add a b) (add a' b')
  mul_congr : ∀ {a a' b b'}, r a a' → r b b' → r (mul a b) (mul a' b')
  neg_congr : ∀ {a a'}, r a a' → r (neg a) (neg a')
  add_comm : ∀ a b, r (add a b) (add b a)
  add_assoc : ∀ a b c, r (add (add a b) c) (add a (add b c))
  zero_add : ∀ a, r (add zero a) a
  mul_comm : ∀ a b, r (mul a b) (mul b a)
  mul_assoc : ∀ a b c, r (mul (mul a b) c) (mul a (mul b c))
  one_mul : ∀ a, r (mul one a) a
  zero_mul : ∀ a, r (mul zero a) zero
  mul_add : ∀ a b c, r (mul a (add b c)) (add (mul a b) (mul a c))
  neg_add : ∀ a b, r (neg (add a b)) (add (neg a) (neg b))
  neg_mul : ∀ a b, r (mul (neg a) b) (neg (mul a b))
  neg_neg : ∀ a, r (neg (neg a)) a
  neg_zero : r (neg zero) zero

namespace CSR

variable {α : Type} (S : CSR α)

instance : Trans S.r S.r S.r := ⟨fun h1 h2 => S.trans h1 h2⟩

theorem add_zero (a : α) : S.r (S.add a S.zero) a := S.trans (S.add_comm _ _) (S.zero_add a)
theorem mul_one (a : α) : S.r (S.mul a S.one) a := S.trans (S.mul_comm _ _) (S.one_mul a)
theorem mul_zero (a : α) : S.r (S.mul a S.zero) S.zero := S.trans (S.mul_comm _ _) (S.zero_mul a)
theorem add_left_comm (a b c : α) : S.r (S.add a (S.add b c)) (S.add b (S.add a c)) :=
  S.trans (S.symm (S.add_assoc a b c))
    (S.trans (S.add_congr (S.add_comm a b) (S.refl c)) (S.add_assoc b a c))
theorem mul_left_comm (a b c : α) : S.r (S.mul a (S.mul b c)) (S.mul b (S.mul a c)) :=
  S.trans (S.symm (S.mul_assoc a b c))
    (S.trans (S.mul_congr (S.mul_comm a b) (S.refl c)) (S.mul_assoc b a c))
theorem add_mul (a b c : α) : S.r (S.mul (S.add a b) c) (S.add (S.mul a c) (S.mul b c)) :=
  S.trans (S.mul_comm _ _)
    (S.trans (S.mul_add c a b) (S.add_congr (S.mul_comm c a) (S.mul_comm c b)))
theorem mul_neg (a b : α) : S.r (S.mul a (S.neg b)) (S.neg (S.mul a b)) :=
  S.trans (S.mul_comm _ _) (S.trans (S.neg_mul b a) (S.neg_congr (S.mul_comm b a)))

-- ------------------------------------------------------------
-- Polynomial expressions and their normal form
-- ------------------------------------------------------------

/-- Polynomial expressions over atoms numbered by `Nat`. -/
inductive PE where
  | atom : Nat → PE
  | zero : PE
  | one : PE
  | add : PE → PE → PE
  | mul : PE → PE → PE
  | neg : PE → PE

/-- Evaluation in `S` under an environment. -/
def eval (env : Nat → α) : PE → α
  | .atom i => env i
  | .zero => S.zero
  | .one => S.one
  | .add p q => S.add (eval env p) (eval env q)
  | .mul p q => S.mul (eval env p) (eval env q)
  | .neg p => S.neg (eval env p)

/-- A signed monomial: sign bit (true = negated) and a sorted list of atom indices. -/
abbrev Mono := Bool × List Nat

/-- Value of a product of atoms. -/
def evalA (env : Nat → α) : List Nat → α
  | [] => S.one
  | i :: m => S.mul (env i) (evalA env m)

/-- Value of a signed monomial. -/
def evalM (env : Nat → α) (m : Mono) : α :=
  match m.1 with
  | false => evalA S env m.2
  | true => S.neg (evalA S env m.2)

/-- Value of a sum of monomials. -/
def evalP (env : Nat → α) : List Mono → α
  | [] => S.zero
  | m :: p => S.add (evalM S env m) (evalP env p)

/-- Lexicographic order on atom lists (Bool; `cond`, not `match` — overlapping-pattern matchers
reach `propext` through their splitters). -/
def leA : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: m, j :: n => cond (Nat.blt i j) true (cond (Nat.blt j i) false (leA m n))

/-- Order on signed monomials: by atoms, then positive before negative. -/
def leM (m n : Mono) : Bool :=
  cond (leA m.2 n.2) (cond (leA n.2 m.2) (cond m.1 (cond n.1 true false) true) true) false

def insertA (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: m => if Nat.ble i j then i :: j :: m else j :: insertA i m

def mergeA : List Nat → List Nat → List Nat
  | [], n => n
  | i :: m, n => insertA i (mergeA m n)

def insertM (m : Mono) : List Mono → List Mono
  | [] => [m]
  | m' :: p => if leM m m' then m :: m' :: p else m' :: insertM m p

def addP : List Mono → List Mono → List Mono
  | [], q => q
  | m :: p, q => insertM m (addP p q)

def mulMono (m n : Mono) : Mono := (xor m.1 n.1, mergeA m.2 n.2)

def mulMP (m : Mono) : List Mono → List Mono
  | [] => []
  | m' :: q => insertM (mulMono m m') (mulMP m q)

def mulP : List Mono → List Mono → List Mono
  | [], _ => []
  | m :: p, q => addP (mulMP m q) (mulP p q)

def negP : List Mono → List Mono
  | [] => []
  | m :: p => insertM (!m.1, m.2) (negP p)

def norm : PE → List Mono
  | .atom i => [(false, [i])]
  | .zero => []
  | .one => [(false, [])]
  | .add p q => addP (norm p) (norm q)
  | .mul p q => mulP (norm p) (norm q)
  | .neg p => negP (norm p)

-- ------------------------------------------------------------
-- Soundness, from the fields alone
-- ------------------------------------------------------------

variable (env : Nat → α)

theorem insertA_sound (i : Nat) :
    ∀ m : List Nat, S.r (evalA S env (insertA i m)) (S.mul (env i) (evalA S env m))
  | [] => S.refl _
  | j :: m => by
      cases h : Nat.ble i j with
      | true =>
        rw [insertA, if_pos h]
        exact S.refl _
      | false =>
        rw [insertA, if_neg (fun e => Bool.noConfusion (h.symm.trans e))]
        exact S.trans (S.mul_congr (S.refl (env j)) (insertA_sound i m))
          (S.mul_left_comm (env j) (env i) (evalA S env m))

theorem mergeA_sound :
    ∀ m n : List Nat, S.r (evalA S env (mergeA m n)) (S.mul (evalA S env m) (evalA S env n))
  | [], n => S.symm (S.one_mul _)
  | i :: m, n =>
      S.trans (insertA_sound S env i (mergeA m n))
        (S.trans (S.mul_congr (S.refl (env i)) (mergeA_sound m n))
          (S.symm (S.mul_assoc (env i) (evalA S env m) (evalA S env n))))

theorem mulMono_sound (m n : Mono) :
    S.r (evalM S env (mulMono m n)) (S.mul (evalM S env m) (evalM S env n)) := by
  obtain ⟨sm, am⟩ := m
  obtain ⟨sn, an⟩ := n
  cases sm <;> cases sn
  · exact mergeA_sound S env am an
  · exact S.trans (S.neg_congr (mergeA_sound S env am an)) (S.symm (S.mul_neg _ _))
  · exact S.trans (S.neg_congr (mergeA_sound S env am an)) (S.symm (S.neg_mul _ _))
  · exact S.trans (mergeA_sound S env am an)
      (S.trans (S.symm (S.neg_neg _))
        (S.trans (S.neg_congr (S.symm (S.neg_mul _ _))) (S.symm (S.mul_neg _ _))))

theorem insertM_sound (m : Mono) :
    ∀ p : List Mono, S.r (evalP S env (insertM m p)) (S.add (evalM S env m) (evalP S env p))
  | [] => S.refl _
  | m' :: p => by
      cases h : leM m m' with
      | true =>
        rw [insertM, if_pos h]
        exact S.refl _
      | false =>
        rw [insertM, if_neg (fun e => Bool.noConfusion (h.symm.trans e))]
        exact S.trans (S.add_congr (S.refl (evalM S env m')) (insertM_sound m p))
          (S.add_left_comm (evalM S env m') (evalM S env m) (evalP S env p))

theorem addP_sound :
    ∀ p q : List Mono, S.r (evalP S env (addP p q)) (S.add (evalP S env p) (evalP S env q))
  | [], q => S.symm (S.zero_add _)
  | m :: p, q =>
      S.trans (insertM_sound S env m (addP p q))
        (S.trans (S.add_congr (S.refl (evalM S env m)) (addP_sound p q))
          (S.symm (S.add_assoc (evalM S env m) (evalP S env p) (evalP S env q))))

theorem mulMP_sound (m : Mono) :
    ∀ q : List Mono, S.r (evalP S env (mulMP m q)) (S.mul (evalM S env m) (evalP S env q))
  | [] => S.symm (S.mul_zero _)
  | m' :: q =>
      S.trans (insertM_sound S env (mulMono m m') (mulMP m q))
        (S.trans (S.add_congr (mulMono_sound S env m m') (mulMP_sound m q))
          (S.symm (S.mul_add (evalM S env m) (evalM S env m') (evalP S env q))))

theorem mulP_sound :
    ∀ p q : List Mono, S.r (evalP S env (mulP p q)) (S.mul (evalP S env p) (evalP S env q))
  | [], q => S.symm (S.zero_mul _)
  | m :: p, q =>
      S.trans (addP_sound S env (mulMP m q) (mulP p q))
        (S.trans (S.add_congr (mulMP_sound S env m q) (mulP_sound p q))
          (S.symm (S.add_mul (evalM S env m) (evalP S env p) (evalP S env q))))

theorem negMono_sound (m : Mono) : S.r (evalM S env (!m.1, m.2)) (S.neg (evalM S env m)) := by
  obtain ⟨s, a⟩ := m
  cases s
  · exact S.refl _
  · exact S.symm (S.neg_neg _)

theorem negP_sound : ∀ p : List Mono, S.r (evalP S env (negP p)) (S.neg (evalP S env p))
  | [] => S.symm S.neg_zero
  | m :: p =>
      S.trans (insertM_sound S env (!m.1, m.2) (negP p))
        (S.trans (S.add_congr (negMono_sound S env m) (negP_sound p))
          (S.symm (S.neg_add (evalM S env m) (evalP S env p))))

theorem norm_sound : ∀ e : PE, S.r (evalP S env (norm e)) (eval S env e)
  | .atom i =>
      -- evalP [(false,[i])] = add (mul (env i) one) zero
      S.trans (S.add_zero _) (S.mul_one (env i))
  | .zero => S.refl _
  | .one => S.add_zero _
  | .add p q => S.trans (addP_sound S env _ _) (S.add_congr (norm_sound p) (norm_sound q))
  | .mul p q => S.trans (mulP_sound S env _ _) (S.mul_congr (norm_sound p) (norm_sound q))
  | .neg p => S.trans (negP_sound S env _) (S.neg_congr (norm_sound p))

/-- **The instrument's theorem**: same normal form ⟹ related by `r`. -/
theorem eq_of_norm (e₁ e₂ : PE) (h : norm e₁ = norm e₂) :
    S.r (eval S env e₁) (eval S env e₂) :=
  S.trans (S.symm (norm_sound S env e₁)) (h ▸ norm_sound S env e₂)

end CSR

/-- Environment from a list of atoms (structural; core's `List.getD` reaches `propext`). -/
def envOf {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: l, n + 1 => envOf d l n

-- ------------------------------------------------------------
-- The tactic: reify, normalise, close
-- ------------------------------------------------------------

/-- An operation is recognised by head constant and total arity (a projection `CSR.add S a b`
has arity 4, a plain constant `vadd a b` arity 2); the operands are the last arguments. -/
structure Ops where
  add : Name × Nat
  mul : Name × Nat
  neg : Option (Name × Nat)
  /-- a unary constant `s` with `one = s zero` is read as `x ↦ x + 1` (VR's `succ`) -/
  succ : Option Name
  zero : Expr
  one : Expr

private def lastArg (e : Expr) : Expr := e.getAppArgs.back!

partial def reify (ops : Ops) (e : Expr) : StateT (Array Expr) MetaM Expr := do
  let e ← instantiateMVars e
  if let some fn := e.getAppFn.constName? then
    let args := e.getAppArgs
    if fn == ops.add.1 && args.size == ops.add.2 then
      let a ← reify ops args[args.size - 2]!
      let b ← reify ops args[args.size - 1]!
      return mkApp2 (mkConst ``CSR.PE.add) a b
    if fn == ops.mul.1 && args.size == ops.mul.2 then
      let a ← reify ops args[args.size - 2]!
      let b ← reify ops args[args.size - 1]!
      return mkApp2 (mkConst ``CSR.PE.mul) a b
    if let some (n, ar) := ops.neg then
      if fn == n && args.size == ar then
        let a ← reify ops (lastArg e)
        return mkApp (mkConst ``CSR.PE.neg) a
  -- no metavariable may be assigned by these checks (`withNewMCtxDepth`)
  if ← withNewMCtxDepth (withReducible (isDefEq e ops.zero)) then return mkConst ``CSR.PE.zero
  if ← withNewMCtxDepth (withReducible (isDefEq e ops.one)) then return mkConst ``CSR.PE.one
  if let some fn := e.getAppFn.constName? then
    if ops.succ == some fn && e.getAppNumArgs == 1 then
      let a ← reify ops e.appArg!
      return mkApp2 (mkConst ``CSR.PE.add) a (mkConst ``CSR.PE.one)
  let atoms ← get
  for i in [:atoms.size] do
    if ← withNewMCtxDepth (withReducible (isDefEq e atoms[i]!)) then
      return mkApp (mkConst ``CSR.PE.atom) (mkNatLit i)
  set (atoms.push e)
  return mkApp (mkConst ``CSR.PE.atom) (mkNatLit atoms.size)

/-- Core of `csr_ring` / `cr_ring`: `S` is the semiring structure used for the operations (for a
ring `R : CR α` this is `R.toCSR`), `mkProof` builds the closing term from
`(env, e₁, e₂)` and the normal-form equation it must decide. -/
def ringCore (S : Expr) (normFn : Expr → Expr) (mkProof : Expr → Expr → Expr → Expr → Expr → MetaM Expr) :
    TacticM Unit := withMainContext do
  let Sty ← whnf (← inferType S)
  let α := Sty.appArg!
  let Sv ← whnf S
  let env ← getEnv
  let fields := getStructureFields env ``VR.CSR.CSR
  let getOp (f : Name) (arity : Nat) : MetaM (Expr × Option (Name × Nat)) := do
    let some idx := fields.idxOf? f | throwError "csr_ring: no field {f}"
    let e ← whnfCore (Expr.proj ``VR.CSR.CSR idx Sv)
    if e.isProj then
      let projFn := ``VR.CSR.CSR ++ f
      let e' := mkApp2 (mkConst projFn) α S
      pure (e', some (projFn, arity + 2))
    else
      match e.constName? with
      | some n => pure (e, some (n, arity))
      | none => pure (e, none)
  let (_, addOp) ← getOp `add 2
  let (_, mulOp) ← getOp `mul 2
  let (negE, negOp) ← getOp `neg 1
  let (zeroE, _) ← getOp `zero 0
  let (oneE, _) ← getOp `one 0
  let some addN := addOp | throwError "csr_ring: no add"
  let some mulN := mulOp | throwError "csr_ring: no mul"
  let negN : Option (Name × Nat) := match negOp with
    | some (n, ar) => if negE.isConstOf ``id then none else some (n, ar)
    | none => none
  let succN : Option Name ← do
    match oneE.getAppFn.constName?, oneE.getAppArgs with
    | some n, #[z] => if ← withNewMCtxDepth (isDefEq z zeroE) then pure (some n) else pure none
    | _, _ => pure none
  let ops : Ops := { add := addN, mul := mulN, neg := negN, succ := succN,
                     zero := zeroE, one := oneE }
  let g ← getMainGoal
  let gt := (← instantiateMVars (← g.getType)).consumeMData
  let gt ← if gt.isApp then pure gt else whnfR gt
  let args := gt.getAppArgs
  unless args.size ≥ 2 do throwError "csr_ring: goal is not a binary relation: {gt}"
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  if lhs.hasExprMVar || rhs.hasExprMVar then
    throwError "csr_ring: the goal still has metavariables (state the equation explicitly): {gt}"
  let ((e₁, e₂), atoms) ← (do
    let a ← reify ops lhs
    let b ← reify ops rhs
    return (a, b)).run #[]
  let envE := mkApp3 (mkConst ``envOf) α zeroE (← mkListLit α atoms.toList)
  let n₁ := normFn e₁
  let n₂ := normFn e₂
  let hEq ← mkEq n₁ n₂
  let inst ← synthInstance (mkApp (mkConst ``Decidable) hEq)
  let dec := mkApp2 (mkConst ``Decidable.decide) hEq inst
  let r ← withDefault (whnf dec)
  unless r.isConstOf ``Bool.true do
    throwError "csr_ring: normal forms differ:\n  {← reduce n₁}\n  {← reduce n₂}"
  let hpf := mkApp3 (mkConst ``of_decide_eq_true) hEq inst
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))
  let pf ← mkProof α envE e₁ e₂ hpf
  let pt ← inferType pf
  unless ← isDefEq gt pt do
    throwError "csr_ring: the goal is not the evaluation of its reification:\n{gt}\n{pt}"
  g.assign pf
  replaceMainGoal []

/-- `csr_ring S` (`S : CSR α`): semiring identities up to `S.r`, no cancellation. -/
syntax (name := csrRing) "csr_ring " term : tactic

@[tactic csrRing] def evalCsrRing : Tactic := fun stx => do
  match stx with
  | `(tactic| csr_ring $St:term) => withMainContext do
    let S ← Tactic.elabTerm St none
    ringCore S (fun e => mkApp (mkConst ``CSR.norm) e)
      (fun α envE e₁ e₂ hpf => pure (mkApp5 (mkApp (mkConst ``CSR.CSR.eq_of_norm) α) S envE e₁ e₂ hpf))
  | _ => throwUnsupportedSyntax

-- ============================================================
-- Rings with cancellation: `a + (−a) ≈ 0` — normal form with integer coefficients
-- ============================================================

/-- A commutative ring up to an equivalence: a `CSR` with cancellation. -/
structure CR (α : Type) extends CSR α where
  add_neg : ∀ a, r (add a (neg a)) zero

namespace CR

variable {α : Type} (S : CR α)

/-- `n` copies of one. -/
def numeral : Nat → α
  | 0 => S.zero
  | n + 1 => S.add S.one (numeral n)

theorem numeral_add : ∀ a b : Nat, S.r (numeral S (a + b)) (S.add (numeral S a) (numeral S b))
  | 0, b => by rw [Nat.zero_add]; exact S.symm (S.zero_add _)
  | a + 1, b => by
      rw [Nat.succ_add]
      exact S.trans (S.add_congr (S.refl _) (numeral_add a b)) (S.symm (S.add_assoc _ _ _))

theorem numeral_mul : ∀ a b : Nat, S.r (numeral S (a * b)) (S.mul (numeral S a) (numeral S b))
  | 0, b => by rw [Nat.zero_mul]; exact S.symm (S.zero_mul _)
  | a + 1, b => by
      rw [Nat.succ_mul]
      exact S.trans (numeral_add S (a * b) b)
        (S.trans (S.add_congr (numeral_mul a b) (S.symm (S.one_mul _)))
          (S.trans (S.add_comm _ _) (S.symm (S.add_mul _ _ _))))

/-- A monomial with an integer coefficient `p − q`. -/
abbrev CMono := List Nat × Nat × Nat

variable (env : Nat → α)

def evalCM (m : CMono) : α :=
  S.add (S.mul (numeral S m.2.1) (CSR.evalA S.toCSR env m.1))
        (S.neg (S.mul (numeral S m.2.2) (CSR.evalA S.toCSR env m.1)))

def evalCP : List CMono → α
  | [] => S.zero
  | m :: p => S.add (evalCM S env m) (evalCP p)

def insertC : CMono → List CMono → List CMono
  | m, [] => [m]
  | (a, p, q), (a', p', q') :: rest =>
    if a = a' then (a, p + p', q + q') :: rest
    else if CSR.leA a a' then (a, p, q) :: (a', p', q') :: rest
    else (a', p', q') :: insertC (a, p, q) rest

def addCP : List CMono → List CMono → List CMono
  | [], q => q
  | m :: p, q => insertC m (addCP p q)

def mulCM (m n : CMono) : CMono :=
  (CSR.mergeA m.1 n.1, m.2.1 * n.2.1 + m.2.2 * n.2.2, m.2.1 * n.2.2 + m.2.2 * n.2.1)

def mulCMP (m : CMono) : List CMono → List CMono
  | [] => []
  | m' :: q => insertC (mulCM m m') (mulCMP m q)

def mulCP : List CMono → List CMono → List CMono
  | [], _ => []
  | m :: p, q => addCP (mulCMP m q) (mulCP p q)

def negCP : List CMono → List CMono
  | [] => []
  | (a, p, q) :: rest => (a, q, p) :: negCP rest

/-- Cancel common copies (no overlapping patterns — those reach `propext`). -/
def cancel : Nat → Nat → Nat × Nat
  | 0, q => (0, q)
  | p + 1, 0 => (p + 1, 0)
  | p + 1, q + 1 => cancel p q

def cancelP : List CMono → List CMono
  | [] => []
  | (a, p, q) :: rest =>
    match cancel p q with
    | (0, 0) => cancelP rest
    | (p', q') => (a, p', q') :: cancelP rest

def normC : CSR.PE → List CMono
  | .atom i => [([i], 1, 0)]
  | .zero => []
  | .one => [([], 1, 0)]
  | .add p q => addCP (normC p) (normC q)
  | .mul p q => mulCP (normC p) (normC q)
  | .neg p => negCP (normC p)

-- soundness

theorem evalCM_merge (a : List Nat) (p₁ q₁ p₂ q₂ : Nat) :
    S.r (evalCM S env (a, p₁ + p₂, q₁ + q₂))
        (S.add (evalCM S env (a, p₁, q₁)) (evalCM S env (a, p₂, q₂))) := by
  dsimp only [evalCM]
  refine S.trans (S.add_congr (S.mul_congr (numeral_add S p₁ p₂) (S.refl _))
    (S.neg_congr (S.mul_congr (numeral_add S q₁ q₂) (S.refl _)))) ?_
  csr_ring S.toCSR

theorem insertC_sound (m : CMono) :
    ∀ p : List CMono, S.r (evalCP S env (insertC m p)) (S.add (evalCM S env m) (evalCP S env p))
  | [] => S.refl _
  | m' :: p => by
      obtain ⟨a, pm, qm⟩ := m
      obtain ⟨a', pm', qm'⟩ := m'
      by_cases heq : a = a'
      · subst heq
        rw [insertC, if_pos rfl]
        exact S.trans (S.add_congr (evalCM_merge S env a pm qm pm' qm') (S.refl _))
          (S.add_assoc _ _ _)
      · rw [insertC, if_neg heq]
        cases h : CSR.leA a a' with
        | true =>
          rw [if_pos rfl]
          exact S.refl _
        | false =>
          rw [if_neg (fun e => Bool.noConfusion e)]
          exact S.trans (S.add_congr (S.refl _) (insertC_sound (a, pm, qm) p))
            (S.add_left_comm _ _ _)

theorem addCP_sound :
    ∀ p q : List CMono, S.r (evalCP S env (addCP p q)) (S.add (evalCP S env p) (evalCP S env q))
  | [], q => S.symm (S.zero_add _)
  | m :: p, q =>
      S.trans (insertC_sound S env m (addCP p q))
        (S.trans (S.add_congr (S.refl _) (addCP_sound p q)) (S.symm (S.add_assoc _ _ _)))

theorem mulCM_sound (m n : CMono) :
    S.r (evalCM S env (mulCM m n)) (S.mul (evalCM S env m) (evalCM S env n)) := by
  obtain ⟨a, p₁, q₁⟩ := m
  obtain ⟨b, p₂, q₂⟩ := n
  dsimp only [mulCM, evalCM]
  refine S.trans (S.add_congr (S.mul_congr (numeral_add S _ _) (CSR.mergeA_sound S.toCSR env a b))
    (S.neg_congr (S.mul_congr (numeral_add S _ _) (CSR.mergeA_sound S.toCSR env a b)))) ?_
  refine S.trans (S.add_congr
      (S.mul_congr (S.add_congr (numeral_mul S p₁ p₂) (numeral_mul S q₁ q₂)) (S.refl _))
      (S.neg_congr (S.mul_congr (S.add_congr (numeral_mul S p₁ q₂) (numeral_mul S q₁ p₂))
        (S.refl _)))) ?_
  csr_ring S.toCSR

theorem mulCMP_sound (m : CMono) :
    ∀ q : List CMono, S.r (evalCP S env (mulCMP m q)) (S.mul (evalCM S env m) (evalCP S env q))
  | [] => S.symm (S.mul_zero _)
  | m' :: q =>
      S.trans (insertC_sound S env (mulCM m m') (mulCMP m q))
        (S.trans (S.add_congr (mulCM_sound S env m m') (mulCMP_sound m q))
          (S.symm (S.mul_add _ _ _)))

theorem mulCP_sound :
    ∀ p q : List CMono, S.r (evalCP S env (mulCP p q)) (S.mul (evalCP S env p) (evalCP S env q))
  | [], q => S.symm (S.zero_mul _)
  | m :: p, q =>
      S.trans (addCP_sound S env (mulCMP m q) (mulCP p q))
        (S.trans (S.add_congr (mulCMP_sound S env m q) (mulCP_sound p q))
          (S.symm (S.add_mul _ _ _)))

theorem negCM_sound (a : List Nat) (p q : Nat) :
    S.r (evalCM S env (a, q, p)) (S.neg (evalCM S env (a, p, q))) := by
  dsimp only [evalCM]
  csr_ring S.toCSR

theorem negCP_sound : ∀ p : List CMono, S.r (evalCP S env (negCP p)) (S.neg (evalCP S env p))
  | [] => S.symm S.neg_zero
  | (a, p, q) :: rest =>
      S.trans (S.add_congr (negCM_sound S env a p q) (negCP_sound rest))
        (S.symm (S.neg_add _ _))

theorem cancel_sound (a : List Nat) :
    ∀ p q : Nat, S.r (evalCM S env (a, cancel p q)) (evalCM S env (a, p, q))
  | 0, q => S.refl _
  | p + 1, 0 => S.refl _
  | p + 1, q + 1 => by
      refine S.trans (cancel_sound a p q) ?_
      have h1 : S.r (evalCM S env (a, p + 1, q + 1))
          (S.add (evalCM S env (a, p, q))
            (S.add (CSR.evalA S.toCSR env a) (S.neg (CSR.evalA S.toCSR env a)))) := by
        dsimp only [evalCM]
        change S.r (S.add (S.mul (S.add S.one (numeral S p)) (CSR.evalA S.toCSR env a))
                          (S.neg (S.mul (S.add S.one (numeral S q)) (CSR.evalA S.toCSR env a)))) _
        csr_ring S.toCSR
      exact S.symm (S.trans h1 (S.trans (S.add_congr (S.refl _) (S.add_neg _)) (S.add_zero _)))

theorem evalCM_zero (a : List Nat) : S.r (evalCM S env (a, 0, 0)) S.zero := by
  dsimp only [evalCM]
  change S.r (S.add (S.mul S.zero (CSR.evalA S.toCSR env a))
                    (S.neg (S.mul S.zero (CSR.evalA S.toCSR env a)))) S.zero
  csr_ring S.toCSR

theorem cancelP_sound : ∀ p : List CMono, S.r (evalCP S env (cancelP p)) (evalCP S env p)
  | [] => S.refl _
  | (a, p, q) :: rest => by
      have hc := cancel_sound S env a p q
      rw [cancelP]
      revert hc
      cases cancel p q with
      | mk p' q' =>
        intro hc
        cases p' with
        | zero =>
          cases q' with
          | zero =>
            exact S.trans (cancelP_sound rest)
              (S.trans (S.symm (S.zero_add _))
                (S.add_congr (S.trans (S.symm (evalCM_zero S env a)) hc) (S.refl _)))
          | succ q'' =>
            exact S.add_congr hc (cancelP_sound rest)
        | succ p'' =>
          exact S.add_congr hc (cancelP_sound rest)

theorem normC_sound : ∀ e : CSR.PE, S.r (evalCP S env (normC e)) (CSR.eval S.toCSR env e)
  | .atom i => by
      -- evalCP [([i],1,0)] = (1·(i·1) + −(0·(i·1))) + 0
      change S.r (S.add (S.add (S.mul (S.add S.one S.zero) (S.mul (env i) S.one))
        (S.neg (S.mul S.zero (S.mul (env i) S.one)))) S.zero) (env i)
      csr_ring S.toCSR
  | .zero => S.refl _
  | .one => by
      change S.r (S.add (S.add (S.mul (S.add S.one S.zero) S.one)
        (S.neg (S.mul S.zero S.one))) S.zero) S.one
      csr_ring S.toCSR
  | .add p q => S.trans (addCP_sound S env _ _) (S.add_congr (normC_sound p) (normC_sound q))
  | .mul p q => S.trans (mulCP_sound S env _ _) (S.mul_congr (normC_sound p) (normC_sound q))
  | .neg p => S.trans (negCP_sound S env _) (S.neg_congr (normC_sound p))

/-- **The instrument's theorem, with cancellation.** -/
theorem eq_of_normC (e₁ e₂ : CSR.PE) (h : cancelP (normC e₁) = cancelP (normC e₂)) :
    S.r (CSR.eval S.toCSR env e₁) (CSR.eval S.toCSR env e₂) :=
  S.trans (S.symm (normC_sound S env e₁))
    (S.trans (S.symm (cancelP_sound S env (normC e₁)))
      (h ▸ S.trans (cancelP_sound S env (normC e₂)) (normC_sound S env e₂)))

end CR

/-- `cr_ring R` (`R : CR α`): ring identities up to `R.r`, with cancellation. -/
syntax (name := crRing) "cr_ring " term : tactic

@[tactic crRing] def evalCrRing : Tactic := fun stx => do
  match stx with
  | `(tactic| cr_ring $Rt:term) => withMainContext do
    let R ← Tactic.elabTerm Rt none
    let Rty ← whnf (← inferType R)
    let α := Rty.appArg!
    let S := mkApp2 (mkConst ``CR.toCSR) α R
    ringCore S (fun e => mkApp (mkConst ``CR.cancelP) (mkApp (mkConst ``CR.normC) e))
      (fun α envE e₁ e₂ hpf => pure (mkApp5 (mkApp (mkConst ``CR.eq_of_normC) α) R envE e₁ e₂ hpf))
  | _ => throwUnsupportedSyntax

end VR.CSR
