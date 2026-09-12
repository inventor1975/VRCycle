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

structure Ops where
  add : Name
  mul : Name
  neg : Option Name
  /-- a unary constant `s` with `one = s zero` is read as `x ↦ x + 1` (VR's `succ`) -/
  succ : Option Name
  zero : Expr
  one : Expr

private def lastArg (e : Expr) : Expr := e.getAppArgs.back!

partial def reify (ops : Ops) (e : Expr) : StateT (Array Expr) MetaM Expr := do
  let e ← instantiateMVars e
  if let some fn := e.getAppFn.constName? then
    let args := e.getAppArgs
    if fn == ops.add && args.size ≥ 2 then
      let a ← reify ops args[args.size - 2]!
      let b ← reify ops args[args.size - 1]!
      return mkApp2 (mkConst ``CSR.PE.add) a b
    if fn == ops.mul && args.size ≥ 2 then
      let a ← reify ops args[args.size - 2]!
      let b ← reify ops args[args.size - 1]!
      return mkApp2 (mkConst ``CSR.PE.mul) a b
    if ops.neg == some fn && args.size ≥ 1 then
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

/-- `csr_ring S` closes a goal `S.r lhs rhs` (with `S.r`, `S.add`, … unfolding to the goal's
constants) when `lhs` and `rhs` have the same normal form. -/
syntax (name := csrRing) "csr_ring " term : tactic

@[tactic csrRing] def evalCsrRing : Tactic := fun stx => do
  match stx with
  | `(tactic| csr_ring $St:term) => withMainContext do
    let S ← Tactic.elabTerm St none
    let Sty ← whnf (← inferType S)
    let α := Sty.appArg!
    -- unfold the structure constant to its literal once, then project WITHOUT further delta
    -- (a plain `whnf` would unfold `iadd` itself into its `match`).
    let Sv ← whnf S
    let env ← getEnv
    let fields := getStructureFields env ``VR.CSR.CSR
    let getOp (f : Name) : MetaM Expr := do
      let some idx := fields.idxOf? f | throwError "csr_ring: no field {f}"
      whnfCore (Expr.proj ``VR.CSR.CSR idx Sv)
    let addE ← getOp `add
    let mulE ← getOp `mul
    let negE ← getOp `neg
    let zeroE ← getOp `zero
    let oneE ← getOp `one
    let some addN := addE.constName? | throwError "csr_ring: add is not a constant: {addE}"
    let some mulN := mulE.constName? | throwError "csr_ring: mul is not a constant: {mulE}"
    let negN : Option Name := match negE.constName? with
      | some n => if n == ``id then none else some n
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
    let n₁ := mkApp (mkConst ``CSR.norm) e₁
    let n₂ := mkApp (mkConst ``CSR.norm) e₂
    let hEq ← mkEq n₁ n₂
    -- decide the equality of normal forms HERE (by evaluation), before building the proof term
    let inst ← synthInstance (mkApp (mkConst ``Decidable) hEq)
    let dec := mkApp2 (mkConst ``Decidable.decide) hEq inst
    let r ← withDefault (whnf dec)
    unless r.isConstOf ``Bool.true do
      throwError "csr_ring: normal forms differ:\n  {← reduce n₁}\n  {← reduce n₂}"
    let hpf := mkApp3 (mkConst ``of_decide_eq_true) hEq inst
      (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true))
    let pf := mkApp5 (mkApp (mkConst ``CSR.CSR.eq_of_norm) α) S envE e₁ e₂ hpf
    let pt ← inferType pf
    unless ← isDefEq gt pt do
      throwError "csr_ring: the goal is not the evaluation of its reification:\n{gt}\n{pt}"
    g.assign pf
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

end VR.CSR
