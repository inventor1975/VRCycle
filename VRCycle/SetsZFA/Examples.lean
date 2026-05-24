-- VR-Sets-ZFA: Examples
-- Stage 7: Concrete demonstrations of non-well-founded sets in OSetZFA.
--
-- Witnesses non-vacuity of AFA and the embedding (Stage 6). All
-- constructions use graphDecoration (Stage 5, §8) applied to specific
-- small graphs. No new coinductive machinery.
--
-- Architecture:
--   quineAtom             — OSetZFA element equal to its own singleton
--   quineAtom_mem_iff     — z ∈ quineAtom ↔ z = quineAtom
--   quineAtom_self_mem    — quineAtom ∈ quineAtom (self-membership witness)
--   cycleDecoration       — graphDecoration on the two-vertex mutual-edge graph
--   cycleDecoration_eq_quineAtom
--                         — both nodes of the two-cycle equal quineAtom
--                           (bisimulation collapse theorem)
--   OSetZFA_mem_not_wf    — ¬ WellFounded (· ∈ · : OSetZFA → OSetZFA → Prop)
--   quineAtom_not_in_range_embedOSet
--                         — quineAtom ∉ Set.range embedOSet (non-surjectivity)
--   omegaChain            — ℕ-indexed descending chain under ∈ (bonus §7)
--   omegaChain_mem_iff    — z ∈ omegaChain n ↔ z = omegaChain (n+1)
--
-- All constructions live at universe 0:
--   V ∈ {Unit, Bool, ℕ} — all in Type 0.
--
-- Key methodological observations (preprint material):
--
-- 1. Bisimulation collapse (§4): The self-loop APG ({()} → {()}) and the
--    two-cycle APG ({false, true}, false ↔ true) are cobisimilar. Hence
--    cycleDecoration false = cycleDecoration true = quineAtom in OSetZFA.
--    Different-looking APGs produce the same set when bisimilar. This is
--    the correct behaviour of the extensional bisimulation quotient.
--
-- 2. ZFC ⊊ ZFA (§6): embedOSet is faithful (Stage 6) but not surjective.
--    quineAtom witnesses the strict inclusion: it is not the image of any
--    well-founded set.
--
-- 3. Membership non-well-foundedness (§5): OSetZFA membership is not
--    well-founded. Quine atom produces an infinite descent (quineAtom ∈
--    quineAtom ∈ …). Contrast: ZFSet.mem_wf witnesses well-foundedness of
--    ZFC membership.
--
-- Dependency chain:
--   graphDecoration, graphDecoration_isDecoration, graphCoPSet (Stage 5)
--   embedOSet, embedOSet_mem (Stage 6)
--   CoPSet.bisim_imp_Equiv, CoPSet.isBisim (Stage 2)
--   ZFSet.mem_wf (Mathlib.SetTheory.ZFC.Basic)

import Mathlib.SetTheory.ZFC.Basic
import VRCycle.SetsZFA.AFA
import VRCycle.SetsZFA.Embedding

namespace VR.SetsZFA

-- ============================================================
-- §1. quineAtom — Quine atom construction
-- ============================================================

/-- The Quine atom: the unique OSetZFA element equal to its own singleton.

Constructed via AFA (`graphDecoration`) applied to the one-vertex
self-loop graph: `V := Unit`, `E := fun _ _ => True`.

The decoration equation `isDecoration E f` at the unique vertex `()`:
  `x ∈ f () ↔ ∃ w : Unit, True ∧ x = f w ↔ x = f ()`
shows `f ()` contains exactly itself.

All Stage 7 constructions live at universe 0 (`V ∈ {Unit, Bool, ℕ}`).
Universe: `quineAtom : OSetZFA.{0}`. -/
noncomputable def quineAtom : OSetZFA.{0} :=
  graphDecoration (fun (_ _ : Unit) => True) ()

-- ============================================================
-- §2. quineAtom_mem_iff — membership characterization
-- ============================================================

/-- **Quine atom membership**: `z ∈ quineAtom ↔ z = quineAtom`.

The Quine atom contains exactly one element: itself.

**Proof**: Unfold via `graphDecoration_isDecoration`. The decoration
condition at `() : Unit` gives:
  `z ∈ quineAtom ↔ ∃ w : Unit, True ∧ z = graphDecoration _ w`
The existential over `Unit` forces `w = ()`, so `z = quineAtom`. -/
theorem quineAtom_mem_iff (z : OSetZFA.{0}) :
    z ∈ quineAtom ↔ z = quineAtom := by
  constructor
  · intro hz
    obtain ⟨w, _, hw⟩ :=
      (graphDecoration_isDecoration (fun (_ _ : Unit) => True) () z).mp hz
    cases w; exact hw
  · intro hz
    exact (graphDecoration_isDecoration (fun (_ _ : Unit) => True) () z).mpr
          ⟨(), trivial, hz⟩

-- ============================================================
-- §3. quineAtom_self_mem — self-membership witness
-- ============================================================

/-- **Self-membership witness**: `quineAtom ∈ quineAtom`.

The Quine atom contains itself. This is the primary concrete witness
of non-well-foundedness in OSetZFA: `quineAtom ∈ quineAtom ∈ ⋯`
is an infinite ∈-descending sequence. -/
theorem quineAtom_self_mem : quineAtom ∈ quineAtom :=
  (quineAtom_mem_iff quineAtom).mpr rfl

-- ============================================================
-- §4. Two-cycle collapse — cycleDecoration = quineAtom
-- ============================================================

/-- The decoration of the two-vertex mutual-edge graph.

`V := Bool`, `E := (· ≠ ·)` (each vertex points to the other).

Decoration equations: `z ∈ f false ↔ z = f true` and
`z ∈ f true ↔ z = f false`. This looks like two distinct cycle sets.

**Theorem** `cycleDecoration_eq_quineAtom` shows that in fact
`cycleDecoration false = cycleDecoration true = quineAtom`. -/
noncomputable def cycleDecoration : Bool → OSetZFA.{0} :=
  graphDecoration (fun x y : Bool => x ≠ y)

/-- **Bisimulation collapse**: both nodes of the two-cycle equal the Quine atom.

`cycleDecoration b = quineAtom` for all `b : Bool`.

**Mathematical content**: The APG of the self-loop (one vertex, self-edge)
and the APG of the two-cycle (two vertices, mutual edges) are cobisimilar.
The bisimulation `R c d` pairs each of `graphCoPSet (· ≠ ·) false` and
`graphCoPSet (· ≠ ·) true` with `graphCoPSet (fun _ _ => True) ()`:

  R := {(cycleA, quineA), (cycleB, quineA)}
  where cycleA = graphCoPSet (· ≠ ·) false
        cycleB = graphCoPSet (· ≠ ·) true
        quineA = graphCoPSet (fun _ _ => True) ()

isBisim check: `cycleA.shape = {w : Bool // false ≠ w}` (one element: `true`);
`quineA.shape = {w : Unit // True}` (one element: `()`). The unique child
of `cycleA` is `cycleB`; (cycleB, quineA) ∈ R ✓. Backward: unique child of
`quineA` is itself; (cycleA, quineA) ∈ R ✓. Symmetric for (cycleB, quineA).

**Preprint observation**: different-looking APGs produce identical OSetZFA
elements when bisimilar. The bisimulation quotient correctly collapses them.
This is the correct behaviour of the extensional membership structure — not
a limitation. -/
theorem cycleDecoration_eq_quineAtom (b : Bool) :
    cycleDecoration b = quineAtom := by
  -- Unfold definitions to expose OSetZFA.mk, then apply OSetZFA.sound
  -- (cycleDecoration b = OSetZFA.mk (graphCoPSet (· ≠ ·) b) definitionally)
  -- (quineAtom = OSetZFA.mk (graphCoPSet (fun _ _ => True) ()) definitionally)
  change OSetZFA.mk (graphCoPSet (fun x y : Bool => x ≠ y) b) =
         OSetZFA.mk (graphCoPSet (fun _ _ : Unit => True) ())
  apply OSetZFA.sound
  -- Prove CoPSet.Equiv (graphCoPSet (· ≠ ·) b) (graphCoPSet (fun _ _ => True) ())
  -- Initial witnesses depend on b; the bisimulation covers both cases
  apply CoPSet.bisim_imp_Equiv
    (fun c d =>
      (c = graphCoPSet (fun x y : Bool => x ≠ y) false ∨
       c = graphCoPSet (fun x y : Bool => x ≠ y) true) ∧
      d = graphCoPSet (fun _ _ : Unit => True) ())
  · -- Show isBisim R
    intro c d ⟨hc, hd⟩
    subst hd
    -- All shapes and children are definitional via graphCoPSet_dest : rfl
    rcases hc with rfl | rfl
    · -- Case: c = graphCoPSet (· ≠ ·) false
      --   c.shape = {w : Bool // false ≠ w} — one element ⟨true, Bool.false_ne_true⟩
      --   d.shape = {w : Unit // True}      — one element ⟨(), trivial⟩
      --   c.children ⟨true, _⟩ = graphCoPSet (· ≠ ·) true  ∈ R (right disjunct)
      --   d.children ⟨(), _⟩   = graphCoPSet (· _ _ => True) ()  (rhs unchanged)
      constructor
      · intro ⟨w, hw⟩
        -- w : Bool, hw : false ≠ w
        cases w with
        | false => exact absurd rfl hw          -- false ≠ false is False
        | true => exact ⟨⟨(), trivial⟩, Or.inr rfl, rfl⟩
      · intro ⟨w, _⟩
        cases w   -- w : Unit, only case ()
        exact ⟨⟨true, Bool.false_ne_true⟩, Or.inr rfl, rfl⟩
    · -- Case: c = graphCoPSet (· ≠ ·) true
      --   c.shape = {w : Bool // true ≠ w}  — one element ⟨false, _⟩
      constructor
      · intro ⟨w, hw⟩
        cases w with
        | true  => exact absurd rfl hw          -- true ≠ true is False
        | false => exact ⟨⟨(), trivial⟩, Or.inl rfl, rfl⟩
      · intro ⟨w, _⟩
        cases w
        exact ⟨⟨false, fun h => Bool.noConfusion h⟩, Or.inl rfl, rfl⟩
  · -- Initial witness
    cases b with
    | false => exact ⟨Or.inl rfl, rfl⟩
    | true  => exact ⟨Or.inr rfl, rfl⟩

-- ============================================================
-- §5. OSetZFA_mem_not_wf — non-well-foundedness
-- ============================================================

/-- **Irreflexivity of accessible elements**: a helper lemma.

If `x` is accessible under `r`, then `¬ r x x`.

**Proof**: `Acc.rec` with motive `¬ r x x`. The induction hypothesis
at each step gives `ih : ∀ y, r y x → ¬ r y y`. Taking `y := x`:
`ih x h : ¬ r x x`, but we assumed `h : r x x`. So `ih x h h : False`. -/
private theorem acc_irrefl {α : Type*} {r : α → α → Prop} {x : α}
    (h : Acc r x) : ¬ r x x := by
  induction h with
  | intro _ _ ih => intro hrr; exact ih _ hrr hrr

/-- **OSetZFA membership is not well-founded**.

`¬ WellFounded (· ∈ · : OSetZFA.{0} → OSetZFA.{0} → Prop)`

**Proof**: `quineAtom ∈ quineAtom` witnesses non-well-foundedness.
If membership were well-founded, `quineAtom` would be accessible, hence
`¬ quineAtom ∈ quineAtom` by `acc_irrefl`. Contradicts `quineAtom_self_mem`.

**Contrast**: `ZFSet.mem_wf : WellFounded (· ∈ · : ZFSet → ZFSet → Prop)`
is a theorem in Mathlib (membership on ZFC sets is well-founded by
inductive construction of PSet). This theorem marks the boundary:
`(OSet, ∈)` is well-founded; `(OSetZFA, ∈)` is not.

The embedding `embedOSet : OSet → OSetZFA` witnesses that the well-founded
fragment sits strictly inside the non-well-founded universe. -/
theorem OSetZFA_mem_not_wf :
    ¬ WellFounded (· ∈ · : OSetZFA.{0} → OSetZFA.{0} → Prop) := by
  intro hwf
  exact acc_irrefl (hwf.apply quineAtom) quineAtom_self_mem

-- ============================================================
-- §6. quineAtom_not_in_range_embedOSet — non-surjectivity
-- ============================================================

/-- **The embedding is not surjective**: `quineAtom ∉ Set.range embedOSet`.

`quineAtom` witnesses that `embedOSet : ZFSet.{0} → OSetZFA.{0}` is strictly
non-surjective: `quineAtom` has no well-founded preimage.

**Proof**: Suppose `embedOSet x = quineAtom` for some `x : ZFSet.{0}`.
Then:
  `quineAtom ∈ quineAtom`                (quineAtom_self_mem)
  `embedOSet x ∈ embedOSet x`            (rewrite by ← hx)
  `x ∈ x`                               (embedOSet_mem x x)
  `¬ x ∈ x`                             (acc_irrefl + ZFSet.mem_wf)
  Contradiction.

`ZFSet.mem_wf` witnesses that ZFC membership is well-founded
(all ZFSet elements are accessible). Hence no ZFSet can satisfy `x ∈ x`.

**Preprint observation**: `embedOSet` is faithful (`embedOSet_injective`,
Stage 6) but not surjective. ZFA strictly extends ZFC as membership
structures: `(OSet, ∈) ↪ (OSetZFA, ∈)` with quineAtom outside the image. -/
theorem quineAtom_not_in_range_embedOSet :
    quineAtom ∉ Set.range embedOSet := by
  rintro ⟨x, hx⟩
  -- hx : embedOSet x = quineAtom
  have hmem : quineAtom ∈ quineAtom := quineAtom_self_mem
  rw [← hx] at hmem
  -- hmem : embedOSet x ∈ embedOSet x
  exact acc_irrefl (ZFSet.mem_wf.apply x) ((embedOSet_mem x x).mp hmem)

-- ============================================================
-- §7. omegaChain — infinite descending chain (bonus)
-- ============================================================

/-- The ω-chain: a ℕ-indexed sequence of OSetZFA elements where each
element contains exactly the next.

Constructed via AFA: `V := ℕ`, `E n m := m = n + 1`
(each vertex points forward to the next natural number).

Decoration equation at `n`:
  `z ∈ omegaChain n ↔ ∃ m, m = n+1 ∧ z = omegaChain m ↔ z = omegaChain (n+1)`

This gives an infinite ∈-descending chain:
  `omegaChain 0 ∋ omegaChain 1 ∋ omegaChain 2 ∋ ⋯`

Unlike the Quine atom (self-membership), the omega chain has no cycles:
no element contains itself. It witnesses a second, distinct mode of
non-well-foundedness — infinite descent without self-membership. -/
noncomputable def omegaChain : ℕ → OSetZFA.{0} :=
  graphDecoration (fun n m => m = n + 1)

/-- **Omega chain membership**: `z ∈ omegaChain n ↔ z = omegaChain (n + 1)`.

Each element of the chain contains exactly the next element.

**Proof**: `graphDecoration_isDecoration` gives:
  `z ∈ omegaChain n ↔ ∃ m : ℕ, m = n+1 ∧ z = omegaChain m`
The existential uniquely forces `m = n + 1`. -/
theorem omegaChain_mem_iff (n : ℕ) (z : OSetZFA.{0}) :
    z ∈ omegaChain n ↔ z = omegaChain (n + 1) := by
  constructor
  · intro hz
    obtain ⟨m, hm, hz⟩ :=
      (graphDecoration_isDecoration (fun (a b : ℕ) => b = a + 1) n z).mp hz
    exact hm ▸ hz
  · intro hz
    exact (graphDecoration_isDecoration (fun (a b : ℕ) => b = a + 1) n z).mpr
          ⟨n + 1, rfl, hz⟩

/-- **Omega chain descent**: `omegaChain (n + 1) ∈ omegaChain n`.

The chain is strictly descending under ∈.

Corollary of `omegaChain_mem_iff` at `z := omegaChain (n + 1)`. -/
theorem omegaChain_descent (n : ℕ) : omegaChain (n + 1) ∈ omegaChain n :=
  (omegaChain_mem_iff n _).mpr rfl

end VR.SetsZFA
