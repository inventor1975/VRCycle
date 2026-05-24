-- VR-Sets-ZFA: AFA
-- Stage 5: AFA_in_OSetZFA — Aczel's Anti-Foundation Axiom as a theorem.
--
-- Every directed graph (V, E) has a unique decoration f : V → OSetZFA:
--   ∀ v, ∀ x, x ∈ f v ↔ ∃ w, E v w ∧ x = f w
--
-- Architecture:
--   isDecoration          — decoration predicate (extensional, via ∈)
--   graphCoalg            — coalgebra V → CoPSetFunctor V
--   graphCoPSet           — CoPSet.corec graphCoalg : V → CoPSet
--   graphCoPSet_dest      — computation rule: dest (graphCoPSet v) = ⟨…⟩
--   graphDecoration       — OSetZFA.mk ∘ graphCoPSet : V → OSetZFA
--   graphDecoration_isDecoration — existence: graphDecoration is a decoration
--   graphDecoration_unique — uniqueness: any decoration equals graphDecoration
--   AFA_in_OSetZFA        — main theorem: ∃! decoration
--
-- Key technique for uniqueness: coinductive bisimulation at CoPSet level.
-- Direct induction is impossible in non-well-founded graphs.
-- PFunctor.M.corec_unique cannot be used directly (requires exact coalgebra
-- equation at CoPSet level; decorations f : V → OSetZFA satisfy it only up
-- to cobisimulation after lifting by Classical.choice). CoPSet.bisim_imp_Equiv
-- is the correct tool.
--
-- Dependency chain:
--   CoPSet.corec, CoPSet.dest_corec (Stage 1, §7)
--   CoPSet.isBisim, CoPSet.isBisim_Equiv, CoPSet.bisim_imp_Equiv (Stage 2, §1,6,8)
--   OSetZFA.mem_mk (Stage 4, §5)
--   OSetZFA.sound, OSetZFA.exact (Stage 3, §4,5)
--
-- Source: Aczel 1988 §5.

import VRCycle.SetsZFA.Membership

namespace VR.SetsZFA

universe u

section AFA

variable {V : Type u}

-- ============================================================
-- §1. isDecoration — decoration predicate
-- ============================================================

/-- `isDecoration E f`: `f : V → OSetZFA` is a decoration of the directed
graph `(V, E)`.

**Definition (extensional, formulation A)**: for every vertex `v`, the
ZFA set `f v` has exactly `{f w | E v w}` as its members:
  `∀ v, ∀ x : OSetZFA, x ∈ f v ↔ ∃ w, E v w ∧ x = f w`

Uses Stage 4 membership `∈` on OSetZFA directly (formulation A).
Avoids building explicit CoPSet representatives inside the predicate.

**AFA** (Aczel 1988 §5): every directed graph has a unique decoration. -/
def isDecoration (E : V → V → Prop) (f : V → OSetZFA.{u}) : Prop :=
  ∀ v : V, ∀ x : OSetZFA.{u}, x ∈ f v ↔ ∃ w : V, E v w ∧ x = f w

-- ============================================================
-- §2. graphCoalg — coalgebra structure for (V, E)
-- ============================================================

/-- The `CoPSetFunctor`-coalgebra whose corecursive fixpoint decorates `(V, E)`.

`graphCoalg E v = ⟨{w // E v w}, Subtype.val⟩`:
- Shape: the out-neighbourhood `{w // E v w}` of vertex `v`.
- Children: `Subtype.val` — each neighbour maps to itself (to be
  recursively decorated by `CoPSet.corec`).

The corecursor `CoPSet.corec (graphCoalg E)` unfolds each vertex into
the CoPSet tree whose level-k nodes are the vertices reachable from v
in exactly k steps. -/
def graphCoalg (E : V → V → Prop) (v : V) : CoPSetFunctor.{u} V :=
  ⟨{w // E v w}, Subtype.val⟩

-- ============================================================
-- §3. graphCoPSet — CoPSet representation via corec
-- ============================================================

/-- The CoPSet pre-set representing each vertex of `(V, E)`.

`graphCoPSet E = CoPSet.corec (graphCoalg E) : V → CoPSet` is the
unique coalgebra morphism from `(V, graphCoalg E)` to the final
coalgebra `(CoPSet, CoPSet.dest)`.

**Computation** (§4): `dest (graphCoPSet E v) = ⟨{w // E v w}, fun i ↦ graphCoPSet E i.val⟩`.

`noncomputable`: M-type corecursor uses Classical infrastructure. -/
noncomputable def graphCoPSet (E : V → V → Prop) : V → CoPSet.{u} :=
  CoPSet.corec (graphCoalg E)

-- ============================================================
-- §4. graphCoPSet_dest — computation rule
-- ============================================================

/-- **Computation rule**: unfolding `graphCoPSet E v` by one level.

`CoPSet.dest (graphCoPSet E v) = ⟨{w // E v w}, fun i ↦ graphCoPSet E i.val⟩`

- Shape: `{w // E v w}` — out-neighbourhood of `v`.
- Children at index `i : {w // E v w}`: `graphCoPSet E i.val` — the
  CoPSet representation of the neighbour `i`.

**Proof**: `rfl`. `PFunctor.M.dest_corec` holds definitionally in
mathlib's M-type implementation, so the coalgebra morphism equation is
transparent to the kernel. No simp rewriting needed. -/
theorem graphCoPSet_dest (E : V → V → Prop) (v : V) :
    CoPSet.dest (graphCoPSet E v) =
    ⟨{w // E v w}, fun i => graphCoPSet E i.val⟩ := rfl

-- ============================================================
-- §5. graphDecoration — lift to OSetZFA
-- ============================================================

/-- The candidate AFA decoration: `graphDecoration E v = OSetZFA.mk (graphCoPSet E v)`.

Lifts `graphCoPSet E : V → CoPSet` through the quotient `OSetZFA.mk`.
Existence (§6) and uniqueness (§7) are proved separately and combined
in `AFA_in_OSetZFA` (§8). -/
noncomputable def graphDecoration (E : V → V → Prop) : V → OSetZFA.{u} :=
  fun v => OSetZFA.mk (graphCoPSet E v)

-- ============================================================
-- §6. graphDecoration_isDecoration — existence
-- ============================================================

/-- **AFA existence**: `graphDecoration E` is a decoration of `(V, E)`.

**Proof strategy**: For `x = OSetZFA.mk a`:
- `x ∈ graphDecoration E v` unfolds (via `mem_mk`, `CoPSet.shape`,
  `CoPSet.children`) to `∃ i : {w // E v w}, a ≈ graphCoPSet E i.val`.
  The shape `{w // E v w}` is resolved definitionally because
  `PFunctor.M.dest_corec` is transparent to the kernel.
- `→`: index `i = ⟨w, hw⟩` gives `w`, `E v w`, and `a ≈ graphCoPSet E w`;
  conclude `x = graphDecoration E w` via `OSetZFA.sound`.
- `←`: from `E v w` and `x = graphDecoration E w`, get `a ≈ graphCoPSet E w`
  via `OSetZFA.exact`; use index `⟨w, hw⟩`. -/
theorem graphDecoration_isDecoration (E : V → V → Prop) :
    isDecoration E (graphDecoration E) := by
  intro v x
  obtain ⟨a, rfl⟩ := OSetZFA.mk_surjective x
  simp only [graphDecoration, OSetZFA.mem_mk, CoPSet.shape, CoPSet.children]
  -- Goal: (∃ i : {w // E v w}, a ≈ graphCoPSet E i.val) ↔
  --       ∃ w, E v w ∧ OSetZFA.mk a = OSetZFA.mk (graphCoPSet E w)
  constructor
  · rintro ⟨⟨w, hw⟩, h⟩
    exact ⟨w, hw, OSetZFA.sound h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w, hw⟩, OSetZFA.exact h⟩

-- ============================================================
-- §7. graphDecoration_unique — uniqueness
-- ============================================================

/-- **AFA uniqueness**: any decoration of `(V, E)` equals `graphDecoration E`.

**Why not `PFunctor.M.corec_unique`**: that requires an exact coalgebra
equation `(f x).dest = P.map f (coalgFun x)` at the CoPSet level.
For `f : V → OSetZFA`, lifting to CoPSet via `Classical.choose` gives
representatives satisfying the equation only up to cobisimulation (not
exactly). The same-shape requirement of `PFunctor.M.bisim` (used inside
`corec_unique`) does not hold in general. Extensional bisimulation is correct.

**Proof**: coinductive bisimulation at CoPSet level.
1. Choose `fRep : V → CoPSet` with `OSetZFA.mk (fRep v) = f v` (Classical.choice).
2. Define `R c d := ∃ v, c ≈ fRep v ∧ d ≈ graphCoPSet E v`.
3. Prove `CoPSet.isBisim R`:
   - Forward (child `i` of `c`): trace through the decoration condition
     on `f` and `graphDecoration_isDecoration` to find matching child `j`
     of `d` with witness vertex `w`.
   - Backward (`j : d.shape`): symmetric argument using `hf` backward.
4. `CoPSet.bisim_imp_Equiv` gives `fRep v ≈ graphCoPSet E v`.
5. Conclude `f v = OSetZFA.mk (fRep v) = OSetZFA.mk (graphCoPSet E v) = graphDecoration E v`. -/
theorem graphDecoration_unique (E : V → V → Prop)
    (f : V → OSetZFA.{u}) (hf : isDecoration E f) :
    f = graphDecoration E := by
  -- Step 1: Classical choice of CoPSet representatives for f
  let fRep : V → CoPSet.{u} := fun v => Classical.choose (OSetZFA.mk_surjective (f v))
  have hfRep : ∀ v, OSetZFA.mk (fRep v) = f v :=
    fun v => Classical.choose_spec (OSetZFA.mk_surjective (f v))
  -- Step 2: Bisimulation at CoPSet level
  -- R c d iff ∃ v, c cobisimilar to fRep v AND d cobisimilar to graphCoPSet E v
  let R : CoPSet.{u} → CoPSet.{u} → Prop :=
    fun c d => ∃ v : V, CoPSet.Equiv c (fRep v) ∧ CoPSet.Equiv d (graphCoPSet E v)
  -- Step 3: R is a bisimulation
  have hR : CoPSet.isBisim R := by
    intro c d ⟨v, hcf, hdg⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · -- Forward: child i of c → matching child j of d with R (c.child i) (d.child j)
      -- (a) c ≈ fRep v gives child i' of fRep v with c.child i ≈ (fRep v).child i'
      obtain ⟨i', hi'⟩ := (CoPSet.isBisim_Equiv c (fRep v) hcf).1 i
      -- (b) OSetZFA.mk ((fRep v).child i') is a member of f v
      have hmem_f : OSetZFA.mk ((fRep v).children i') ∈ f v := by
        rw [← hfRep v, OSetZFA.mem_mk]
        exact ⟨i', CoPSet.Equiv.refl _⟩
      -- (c) Decoration of f: extract neighbour w and proof E v w
      obtain ⟨w, hvw, hfw⟩ := (hf v _).mp hmem_f
      -- hfw : OSetZFA.mk ((fRep v).child i') = f w
      -- (d) (fRep v).child i' ≈ fRep w  (from hfw and hfRep w)
      have h_eq : CoPSet.Equiv ((fRep v).children i') (fRep w) :=
        OSetZFA.exact (hfw.trans (hfRep w).symm)
      -- (e) graphCoPSet E w ∈ graphDecoration E v  (by graphDecoration_isDecoration)
      have hmem_g : OSetZFA.mk (graphCoPSet E w) ∈ graphDecoration E v :=
        (graphDecoration_isDecoration E v _).mpr ⟨w, hvw, rfl⟩
      -- (f) Unfold to mem_mk: get l : (graphCoPSet E v).shape
      --     with graphCoPSet E w ≈ (graphCoPSet E v).child l
      rw [show graphDecoration E v = OSetZFA.mk (graphCoPSet E v) from rfl,
          OSetZFA.mem_mk] at hmem_g
      obtain ⟨l, hl⟩ := hmem_g
      -- hl : graphCoPSet E w ≈ (graphCoPSet E v).child l
      -- (g) d ≈ graphCoPSet E v (backward direction of isBisim_Equiv):
      --     get j : d.shape with d.child j ≈ (graphCoPSet E v).child l
      obtain ⟨j, hj⟩ := (CoPSet.isBisim_Equiv d (graphCoPSet E v) hdg).2 l
      -- hj : d.child j ≈ (graphCoPSet E v).child l
      -- Conclude: R (c.child i) (d.child j) witnessed by w
      --   c.child i ≈ fRep w  : Equiv.trans hi' h_eq
      --   d.child j ≈ graphCoPSet E w  : Equiv.trans hj (Equiv.symm hl)
      exact ⟨j, w, CoPSet.Equiv.trans hi' h_eq,
                   CoPSet.Equiv.trans hj (CoPSet.Equiv.symm hl)⟩
    · -- Backward: child j of d → matching child i of c with R (c.child i) (d.child j)
      -- (a) d ≈ graphCoPSet E v (forward): child l of graphCoPSet E v
      --     with d.child j ≈ (graphCoPSet E v).child l
      obtain ⟨l, hl⟩ := (CoPSet.isBisim_Equiv d (graphCoPSet E v) hdg).1 j
      -- (b) OSetZFA.mk ((graphCoPSet E v).child l) ∈ graphDecoration E v
      have hmem_g2 : OSetZFA.mk ((graphCoPSet E v).children l) ∈ graphDecoration E v := by
        rw [show graphDecoration E v = OSetZFA.mk (graphCoPSet E v) from rfl,
            OSetZFA.mem_mk]
        exact ⟨l, CoPSet.Equiv.refl _⟩
      -- (c) Decoration of graphDecoration: get neighbour w and E v w
      obtain ⟨w, hvw, hgw⟩ := (graphDecoration_isDecoration E v _).mp hmem_g2
      -- hgw : OSetZFA.mk ((graphCoPSet E v).child l) = graphDecoration E w
      -- (d) (graphCoPSet E v).child l ≈ graphCoPSet E w
      have h_gl : CoPSet.Equiv ((graphCoPSet E v).children l) (graphCoPSet E w) :=
        OSetZFA.exact hgw
      -- (e) OSetZFA.mk (fRep w) ∈ f v  (decoration of f backward with E v w)
      -- hfRep w : OSetZFA.mk (fRep w) = f w, so the decoration witness is hfRep w
      have hmem_f2 : OSetZFA.mk (fRep w) ∈ f v :=
        (hf v _).mpr ⟨w, hvw, hfRep w⟩
      -- (f) Unfold to mem_mk: get k : (fRep v).shape
      --     with fRep w ≈ (fRep v).child k
      rw [← hfRep v, OSetZFA.mem_mk] at hmem_f2
      obtain ⟨k, hk⟩ := hmem_f2
      -- hk : fRep w ≈ (fRep v).child k
      -- (g) c ≈ fRep v (backward): get i : c.shape
      --     with c.child i ≈ (fRep v).child k
      obtain ⟨i, hi⟩ := (CoPSet.isBisim_Equiv c (fRep v) hcf).2 k
      -- Conclude: R (c.child i) (d.child j) witnessed by w
      --   c.child i ≈ fRep w  : Equiv.trans hi (Equiv.symm hk)
      --   d.child j ≈ graphCoPSet E w  : Equiv.trans hl h_gl
      exact ⟨i, w, CoPSet.Equiv.trans hi (CoPSet.Equiv.symm hk),
                   CoPSet.Equiv.trans hl h_gl⟩
  -- Step 4: bisim_imp_Equiv gives fRep v ≈ graphCoPSet E v for each v
  have hequiv : ∀ v, CoPSet.Equiv (fRep v) (graphCoPSet E v) :=
    fun v => CoPSet.bisim_imp_Equiv R hR ⟨v, CoPSet.Equiv.refl _, CoPSet.Equiv.refl _⟩
  -- Step 5: Conclude f = graphDecoration E
  funext v
  calc f v = OSetZFA.mk (fRep v)           := (hfRep v).symm
       _ = OSetZFA.mk (graphCoPSet E v) := OSetZFA.sound (hequiv v)
       _ = graphDecoration E v           := rfl

-- ============================================================
-- §8. AFA_in_OSetZFA — main theorem
-- ============================================================

/-- **Aczel's Anti-Foundation Axiom as a theorem in OSetZFA**.

Every directed graph `(V, E)` has a unique decoration `f : V → OSetZFA`:
a function assigning to each vertex `v` the ZFA set whose members are
exactly `{f w | E v w}`.

  `∃! f : V → OSetZFA, isDecoration E f`

**Foundation**: CoPSet (coinductive, final coalgebra of `CoPSetFunctor`)
makes AFA provable without axioms beyond `[propext, Classical.choice,
Quot.sound]`. Existence: `CoPSet.corec` (final coalgebra universality).
Uniqueness: `CoPSet.bisim_imp_Equiv` (extensional coinduction).

**Contrast with VR-Sets**: In `VRCycle.Sets`, `quineAtom_impossible` and
`AFA_Refuted` hold because PSet is inductive (well-founded). OSetZFA
resolves `Conjecture_IV_2_Statement` (VRCycle.Sets.Conjectures): it is
the type U with AFA-membership satisfying Aczel's anti-foundation axiom. -/
theorem AFA_in_OSetZFA (E : V → V → Prop) :
    ∃! f : V → OSetZFA.{u}, isDecoration E f :=
  ⟨graphDecoration E,
   graphDecoration_isDecoration E,
   fun f hf => graphDecoration_unique E f hf⟩

end AFA

end VR.SetsZFA
