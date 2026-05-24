-- VR-Sets-ZFA: Cobisimulation
-- Stage 2: CoPSet.Equiv — greatest extensional bisimulation on CoPSet.
--
-- Defines the cobisimulation relation (extensional bisimulation) on CoPSet,
-- proves it is an equivalence relation, and constructs the Setoid instance
-- for Stage 3 (quotient OSetZFA).
--
-- **Terminology**: CoPSet.Equiv is called "cobisimulation" in the preprint
-- (parallel to ZFA literature) and "extensional bisimulation" here (to
-- distinguish from the strong bisimulation in CoPSet.bisim, Stage 1).
--
-- **Approach**: Greatest fixpoint manual — CoPSet.Equiv x y iff there exists
-- a bisimulation relation R with R x y. This gives clean existential-witness
-- proofs for all setoid properties without coinductive tactics.
--
-- **Key architectural note**: CoPSet.Equiv (extensional) ≠ CoPSet.bisim (strong).
-- See §8 for the full analysis.
--
-- Source: Aczel 1988 §2 (bisimulation), §6 (AFA).

import VRCycle.SetsZFA.CoPSet

namespace VR.SetsZFA

universe u

-- ============================================================
-- §1. isBisim — bisimulation predicate
-- ============================================================

/-- `CoPSet.isBisim R`: R is an **extensional bisimulation** if for every
R-related pair (x, y):
- (**forward**) every child of x has an R-related child in y;
- (**backward**) every child of y has an R-related child in x.

This is the set-theoretic bisimulation (coverage condition), NOT the
structural/strong bisimulation used in `CoPSet.bisim` (Stage 1).
Difference:
- **isBisim** (extensional): allows different shapes; checks child
  coverage.
- **M.bisim condition** (strong, Stage 1): requires SAME shape `α` at
  every level.

The greatest fixed point of this predicate is `CoPSet.Equiv` (§2).

**Parallel to PSet**: `PSet.Equiv` is also defined via mutual simulation
(inductive case). `isBisim` captures the same idea for the coinductive
case, but stated as a predicate on arbitrary relations. -/
def CoPSet.isBisim (R : CoPSet.{u} → CoPSet.{u} → Prop) : Prop :=
  ∀ x y, R x y →
    (∀ i : x.shape, ∃ j : y.shape, R (x.children i) (y.children j)) ∧
    (∀ j : y.shape, ∃ i : x.shape, R (x.children i) (y.children j))

-- ============================================================
-- §2. CoPSet.Equiv — greatest extensional bisimulation
-- ============================================================

/-- `CoPSet.Equiv x y`: x and y are **cobisimilar** (extensionally bisimilar).

**Definition**: x ≡ y iff there exists a bisimulation R with R x y.
This is the greatest extensional bisimulation — the union of all
bisimulations.

**Parallel to PSet.Equiv** (mathlib `Mathlib.SetTheory.ZFC.Basic`):
`PSet.Equiv` is defined inductively via mutual simulation. `CoPSet.Equiv`
is defined as the greatest fixed point (union of all bisimulations),
appropriate for the coinductive setting.

**Set-theoretic meaning**: x ≡ y iff x and y represent the same set —
they have the same "member multiset" up to ≡. The quotient `OSetZFA`
(Stage 3) makes ≡ into definitional equality.

**Critical distinction from Stage 1's `CoPSet.bisim`**:
- `CoPSet.bisim` collapses pairs sharing the SAME SHAPE (strong).
- `CoPSet.Equiv` identifies pairs with the SAME MEMBER SET (extensional).
  Shapes may differ. See §8.

**Universe**: `Prop` — quantifies over bisimulation relations
`R : CoPSet.{u} → CoPSet.{u} → Prop`. This is valid in Lean 4 via
impredicativity of Prop. -/
def CoPSet.Equiv (x y : CoPSet.{u}) : Prop :=
  ∃ R : CoPSet.{u} → CoPSet.{u} → Prop, CoPSet.isBisim R ∧ R x y

-- ============================================================
-- §3. Reflexivity
-- ============================================================

/-- `Eq` is a bisimulation: equal elements have the same shape and children. -/
private theorem CoPSet.isBisim_Eq :
    CoPSet.isBisim (Eq : CoPSet.{u} → CoPSet.{u} → Prop) :=
  fun x y h => by subst h; exact ⟨fun i => ⟨i, rfl⟩, fun j => ⟨j, rfl⟩⟩

/-- **Reflexivity**: every CoPSet is cobisimilar to itself.

**Proof**: `Eq` is a bisimulation (by `isBisim_Eq`) and `x = x` (rfl). -/
theorem CoPSet.Equiv.refl (x : CoPSet.{u}) : CoPSet.Equiv x x :=
  ⟨Eq, CoPSet.isBisim_Eq, rfl⟩

-- ============================================================
-- §4. Symmetry
-- ============================================================

/-- **Symmetry**: cobisimilarity is symmetric.

**Proof witness**: if R is a bisimulation with R x y, then the relational
transpose `R' a b := R b a` is a bisimulation with R' y x.

The key observation: the forward condition of R' on (a,b) is exactly the
backward condition of R on (b,a), and vice versa. Swapping forward/backward
gives the new bisimulation. -/
theorem CoPSet.Equiv.symm {x y : CoPSet.{u}} (h : CoPSet.Equiv x y) :
    CoPSet.Equiv y x := by
  obtain ⟨R, hR, hxy⟩ := h
  refine ⟨fun a b => R b a, fun a b hba => ?_, hxy⟩
  obtain ⟨fwd, bwd⟩ := hR b a hba
  -- fwd : ∀ i : b.shape, ∃ j : a.shape, R (b.children i) (a.children j)
  -- bwd : ∀ j : a.shape, ∃ i : b.shape, R (b.children i) (a.children j)
  -- New bisim R' a b = R b a needs:
  --   forward R' on (a,b): ∀ i : a.shape, ∃ j : b.shape, R (b.children j) (a.children i)  = bwd
  --   backward R' on (a,b): ∀ j : b.shape, ∃ i : a.shape, R (b.children j) (a.children i) = fwd
  exact ⟨bwd, fwd⟩

-- ============================================================
-- §5. Transitivity
-- ============================================================

/-- **Transitivity**: cobisimilarity is transitive.

**Proof witness**: the relational composition
`R_trans a c := ∃ b, R₁ a b ∧ R₂ b c`
is a bisimulation if R₁ and R₂ are bisimulations.

**Composition argument** (for forward coverage):
- Given i : a.shape, use R₁-forward to get j : b.shape with R₁ (a.children i, b.children j).
- Use R₂-forward to get k : c.shape with R₂ (b.children j, c.children k).
- Then R_trans (a.children i) (c.children k) with witness b.children j. ✓

Backward coverage is symmetric. The composition technique is standard
in bisimulation literature and requires no coinductive tactics. -/
theorem CoPSet.Equiv.trans {x y z : CoPSet.{u}}
    (h₁ : CoPSet.Equiv x y) (h₂ : CoPSet.Equiv y z) :
    CoPSet.Equiv x z := by
  obtain ⟨R₁, hR₁, hxy⟩ := h₁
  obtain ⟨R₂, hR₂, hyz⟩ := h₂
  refine ⟨fun a c => ∃ b, R₁ a b ∧ R₂ b c, ?_, ⟨y, hxy, hyz⟩⟩
  rintro a c ⟨b, hab, hbc⟩
  obtain ⟨fwd₁, bwd₁⟩ := hR₁ a b hab
  obtain ⟨fwd₂, bwd₂⟩ := hR₂ b c hbc
  constructor
  · -- Forward: every child of a has an R_trans-related child in c
    intro i
    obtain ⟨j, hj⟩ := fwd₁ i    -- j : b.shape, R₁ (a.children i) (b.children j)
    obtain ⟨k, hk⟩ := fwd₂ j    -- k : c.shape, R₂ (b.children j) (c.children k)
    exact ⟨k, b.children j, hj, hk⟩
  · -- Backward: every child of c has an R_trans-related child in a
    intro k
    obtain ⟨j, hj⟩ := bwd₂ k    -- j : b.shape, R₂ (b.children j) (c.children k)
    obtain ⟨i, hi⟩ := bwd₁ j    -- i : a.shape, R₁ (a.children i) (b.children j)
    exact ⟨i, b.children j, hi, hj⟩

-- ============================================================
-- §6. isBisim_Equiv — Equiv is itself a bisimulation
-- ============================================================

/-- **Equiv is a bisimulation**: `CoPSet.isBisim CoPSet.Equiv`.

This is the key lemma for Stage 4 (membership on OSetZFA). When lifting
membership `x ∈ y` to the quotient, we need to show membership is
well-defined under Equiv — which requires knowing Equiv itself is a
bisimulation (so Equiv-related pairs have Equiv-related children).

**Proof**: Given `Equiv x y` with witness `⟨R, hR, hxy⟩`.
- R-forward on (x,y) gives j with `R (x.children i) (y.children j)`.
- Since `R (x.children i) (y.children j)`, we have `Equiv (x.children i) (y.children j)`
  (because R itself witnesses this — any R with isBisim R and R a b gives Equiv a b). -/
theorem CoPSet.isBisim_Equiv : CoPSet.isBisim (CoPSet.Equiv.{u}) := by
  rintro x y ⟨R, hR, hxy⟩
  obtain ⟨fwd, bwd⟩ := hR x y hxy
  exact ⟨
    fun i => by obtain ⟨j, hj⟩ := fwd i; exact ⟨j, R, hR, hj⟩,
    fun j => by obtain ⟨i, hi⟩ := bwd j; exact ⟨i, R, hR, hi⟩⟩

-- ============================================================
-- §7. Setoid instance
-- ============================================================

/-- **CoPSet.Equiv is a setoid**: the cobisimulation equivalence relation.

Used in Stage 3 to form the quotient `OSetZFA := Quotient CoPSet.instSetoid`.
In OSetZFA, equality IS extensional bisimulation — the quotient makes
Equiv into Lean's definitional equality. -/
instance CoPSet.instSetoid : Setoid CoPSet.{u} where
  r     := CoPSet.Equiv
  iseqv := ⟨CoPSet.Equiv.refl, CoPSet.Equiv.symm, CoPSet.Equiv.trans⟩

-- ============================================================
-- §8. Connection with CoPSet.bisim (Stage 1) — architectural note
-- ============================================================

/-- **Extensional bisimulation is the largest bisimulation**.

Any isBisim R with R x y implies Equiv x y. `Equiv` is thus the
GREATEST element among all bisimulation relations — the union of all
bisimulations.

**Trivial proof**: `Equiv` is defined as this union. -/
theorem CoPSet.bisim_imp_Equiv (R : CoPSet.{u} → CoPSet.{u} → Prop)
    (hbisim : CoPSet.isBisim R) {x y : CoPSet.{u}} (h : R x y) :
    CoPSet.Equiv x y :=
  ⟨R, hbisim, h⟩

/- **Strong vs extensional bisimulation — architectural distinction** (block comment).

`CoPSet.bisim` (Stage 1, wrapping `PFunctor.M.bisim`) operates under the
STRONG bisimulation condition: both x and y must share the SAME SHAPE `α`:

    ∃ (α : Type u) (fx fy : α → CoPSet), dest x = ⟨α, fx⟩ ∧ dest y = ⟨α, fy⟩

`CoPSet.isBisim` (this stage) is EXTENSIONAL: any forward/backward child
coverage works, even with DIFFERENT shapes.

**Key example** (different shapes, same "member set"):

    a := CoPSet.mk Bool    (fun _ => ∅)  -- shape = Bool,  members = {∅, ∅}
    b := CoPSet.mk (Fin 1) (fun _ => ∅)  -- shape = Fin 1, members = {∅}

As sets: a ≡ b ≡ {∅} (both represent the singleton containing ∅).
`Equiv a b` holds (each child of a has an Equiv-related child in b and
vice versa, since both have the single member ∅).
But `a ≠ b` as CoPSet M-type elements (Bool ≠ Fin 1 as shapes).
`CoPSet.bisim` (Stage 1) CANNOT prove a = b — the same-shape condition fails.

**More examples requiring quotient**:
- Duplicate indices: `CoPSet.mk (Fin 3) (fun _ => ∅)` ≡ `CoPSet.mk (Fin 1) (fun _ => ∅)`.
  The first has three copies of ∅; as a set, it's still {∅}. Different shapes,
  same membership. The quotient identifies these.
- More generally: any two CoPSets with equivalent "member multisets modulo ≡"
  may have different shape types in their M-type representation.

**Why the Stage 3 quotient is necessary**:
`OSetZFA = Quotient CoPSet.instSetoid` is NOT isomorphic to `CoPSet`.
The quotient genuinely collapses non-equal CoPSets into the same OSetZFA
element. `M.bisim` (strong) would give a quotient isomorphic to `CoPSet`
itself; `Equiv` (extensional) gives the proper set-theoretic universe.

**Chain of implications**:
  (M.bisim condition on R) → isBisim R → Equiv x y ← (but NOT: Equiv x y → x = y in CoPSet)

The last step (Equiv x y ⇏ x = y in CoPSet) is the gap that makes the
quotient necessary. In OSetZFA (Stage 3), `⟦x⟧ = ⟦y⟧ ↔ Equiv x y`.

**Preprint note**: This is Observation 12 (extended) — the M-type
construction collapses strong-bisimilar pairs; the extensional quotient
additionally collapses different-shape representations of the same set.
Both levels are necessary for the full ZFA construction.

**Formal consequence**: `CoPSet.bisim` (Stage 1) + `CoPSet.bisim_imp_Equiv`
gives: if R satisfies the M.bisim (strong) condition and R x y, then
x = y (by `CoPSet.bisim`), hence `Equiv x y` (by reflexivity).
The converse direction — `Equiv x y ⇏ x = y` in CoPSet M-type — is the
gap documented by the different-shape examples above. -/
-- Note: A formal theorem "strong bisim condition → isBisim" is deferred to
-- Stage 8 (API). The proof requires HEq cast manipulation from Sigma equality.

end VR.SetsZFA
