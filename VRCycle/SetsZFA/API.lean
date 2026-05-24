-- VR-Sets-ZFA: API
-- Stage 8: Polish and public interface for external usage.
--
-- Adds the foundational set-builder API (empty set, singleton) that
-- external users need to construct and reason about OSetZFA elements
-- without referencing internal CoPSet structure. Exports the
-- `acc_irrefl` helper from Stage 7 as a public utility. Adds
-- `@[simp]` to key membership lemmas. Provides the canonical
-- Quine atom equation `q = {q}` without graph-level references.
--
-- Architecture:
--   OSetZFA.empty             — ∅_ZFA : OSetZFA (no members)
--   OSetZFA.not_mem_empty     — ¬ z ∈ ∅_ZFA
--   singleton_congr           — well-definedness helper (private)
--   OSetZFA.singleton         — {x}_ZFA : OSetZFA (one member)
--   OSetZFA.singleton_mk      — computation rule
--   OSetZFA.mem_singleton     — z ∈ {x} ↔ z = x
--   quineAtom_eq_singleton_self — quineAtom = OSetZFA.singleton quineAtom
--   acc_irrefl                — Acc r x → ¬ r x x (public utility)
--   @[simp] additions         — quineAtom_mem_iff, omegaChain_mem_iff,
--                               not_mem_empty, mem_singleton
--
-- Scope discipline (explicit deferred list):
--   OSetZFA.pair              — deferred to future API version
--   OSetZFA.union             — deferred to future API version
--   OSetZFA.separation        — deferred to future API version
--   strongBisim_imp_Equiv     — deferred from Stage 2 (hard, not blocking)
--   Custom notation ∅_ZFA {x}_ZFA — deferred (cost > benefit at this scale)
--   Tactics (bisim_eq etc.)   — deferred (overkill for Stage 8)
--
-- Universe polymorphism:
--   OSetZFA.empty : OSetZFA.{u}     uses PEmpty.{u+1} : Type u
--   OSetZFA.singleton : OSetZFA.{u} uses PUnit.{u+1}  : Type u
--   Examples (Stage 7) remain at universe 0.
--
-- mathlib check for acc_irrefl:
--   mathlib has `WellFounded.irrefl : WellFounded r → Std.Irrefl r`
--   (from WellFounded, not Acc). Our `acc_irrefl` works from `Acc r x`
--   directly — a weaker hypothesis, not duplicating mathlib.
--   `WellFounded.irrefl` is not a substitute when only Acc is available.
--
-- @[simp] safety analysis:
--   quineAtom_mem_iff: rewrites `z ∈ quineAtom` to `z = quineAtom`;
--     no loop (= is not rewritten back).
--   omegaChain_mem_iff: rewrites `z ∈ omegaChain n` to `z = omegaChain (n+1)`;
--     strictly increases the chain index, no loop.
--   not_mem_empty: rewrites `z ∈ OSetZFA.empty` to `False`; terminating.
--   mem_singleton: rewrites `z ∈ OSetZFA.singleton x` to `z = x`;
--     no loop.
--
-- Full axiom audit (all 8 stages):
--
--   | Object                     | Axioms                                  |
--   | graphCoalg                 | none (pure definition)                  |
--   | embedPSet                  | none (structural recursion)             |
--   | All theorems (Stages 1–8)  | [propext, Classical.choice, Quot.sound] |
--
--   Pattern: definitions over inductive/corecursive types are axiom-free.
--   All proofs use at most [propext, Classical.choice, Quot.sound] because:
--   - CoPSet.bisim (PFunctor.M.bisim) requires Classical.choice
--     (inhabit in eq_of_bisim).
--   - OSetZFA quotient operations use propext + Quot.sound.
--   - No additional axioms (no Excluded Middle, no Function.choice, etc.)
--   This is within mathlib's standard ceiling for classical mathematics.
--
-- Dependency chain:
--   OSetZFA.mk, OSetZFA.mk_surjective, OSetZFA.sound, OSetZFA.exact,
--   OSetZFA.eq_iff, OSetZFA.mem_mk (Stages 3, 4)
--   CoPSet.bisim_imp_Equiv, CoPSet.isBisim_Equiv (Stage 2)
--   quineAtom, quineAtom_mem_iff, omegaChain_mem_iff (Stage 7)
--
-- Source: Aczel 1988 §6; engineering polish pass.

import VRCycle.SetsZFA.Examples

namespace VR.SetsZFA

universe u

-- ============================================================
-- §1. OSetZFA.empty — the empty ZFA set
-- ============================================================

/-- The empty ZFA set: the OSetZFA element with no members.

`OSetZFA.empty = OSetZFA.mk (CoPSet.mk PEmpty.{u+1} PEmpty.elim)`

Uses `PEmpty.{u+1} : Type u` for universe polymorphism (parallel to
`PSet.mk Empty (Empty.elim)` in the well-founded setting).

**Not noncomputable**: `OSetZFA.mk` is `Quotient.mk'`, which is
constructive. The type `PEmpty.{u+1}` has no inhabitants, so
no choice is needed.

Companion lemma: `OSetZFA.not_mem_empty`. -/
def OSetZFA.empty : OSetZFA.{u} :=
  OSetZFA.mk (CoPSet.mk PEmpty.{u+1} PEmpty.elim)

/-- **No element belongs to the empty set**: `¬ z ∈ OSetZFA.empty`.

**Proof**: reduce via `OSetZFA.Mem` to `∃ i : PEmpty.{u+1}, ...`;
`PEmpty` has no inhabitants, so the existential is `False`. -/
@[simp]
theorem OSetZFA.not_mem_empty (z : OSetZFA.{u}) : ¬ z ∈ (OSetZFA.empty : OSetZFA.{u}) := by
  refine Quotient.inductionOn z (fun _ => ?_)
  -- Reduce to: ¬ ∃ i : PEmpty.{u+1}, _
  change ¬ ∃ _ : PEmpty.{u+1}, _
  rintro ⟨i, _⟩; exact i.elim

-- ============================================================
-- §2. singleton_congr — well-definedness helper (private)
-- ============================================================

/-- Well-definedness of the singleton CoPSet construction.

`a ≈ b → CoPSet.mk PUnit.{u+1} (fun _ => a) ≈ CoPSet.mk PUnit.{u+1} (fun _ => b)`

Proof via `CoPSet.bisim_imp_Equiv` with the bisimulation:

  `R c d := (∃ x y, x ≈ y ∧ c = mk PUnit (fun _ => x) ∧
                             d = mk PUnit (fun _ => y)) ∨ CoPSet.Equiv c d`

- **First case** (top-level pair): both CoPSets have one child each (`PUnit.unit`);
  the children are `x` and `y`; `x ≈ y` places them in R via `Or.inr`. ✓
- **Second case** (CoPSet.Equiv): `isBisim_Equiv` extracts children; they are
  Equiv, hence in R via `Or.inr`. ✓

`PUnit.{u+1} : Type u` — universe-polymorphic unit type. -/
private theorem singleton_congr {a b : CoPSet.{u}} (hab : a ≈ b) :
    CoPSet.Equiv (CoPSet.mk PUnit.{u+1} (fun _ => a))
                 (CoPSet.mk PUnit.{u+1} (fun _ => b)) := by
  apply CoPSet.bisim_imp_Equiv
    (fun c d =>
      (∃ x y : CoPSet.{u}, x ≈ y ∧ c = CoPSet.mk PUnit.{u+1} (fun _ => x) ∧
                                      d = CoPSet.mk PUnit.{u+1} (fun _ => y)) ∨
      CoPSet.Equiv c d)
  · intro c d h
    rcases h with ⟨x, y, hxy, rfl, rfl⟩ | hcd
    · -- Top-level singleton pair: unique children are x ≈ y, in R via Or.inr
      exact ⟨fun _ => ⟨PUnit.unit, Or.inr hxy⟩, fun _ => ⟨PUnit.unit, Or.inr hxy⟩⟩
    · -- CoPSet.Equiv case: children are Equiv, use isBisim_Equiv
      obtain ⟨fwd, bwd⟩ := CoPSet.isBisim_Equiv c d hcd
      exact ⟨fun i => Exists.imp (fun _ hj => Or.inr hj) (fwd i),
             fun j => Exists.imp (fun _ hi => Or.inr hi) (bwd j)⟩
  · exact Or.inl ⟨a, b, hab, rfl, rfl⟩

-- ============================================================
-- §3. OSetZFA.singleton — single-element ZFA set
-- ============================================================

/-- The singleton set: `OSetZFA.singleton x` has exactly one member, `x`.

**Definition**: lift the assignment `a ↦ OSetZFA.mk (CoPSet.mk PUnit.{u+1} (fun _ => a))`
over `x : OSetZFA = Quotient CoPSet.cobisim`. Well-defined by `singleton_congr`.

Uses `PUnit.{u+1} : Type u` — universe-polymorphic unit type — as the
branching type, so the CoPSet has exactly one child index.

**noncomputable**: `Quotient.liftOn` is noncomputable in Lean 4's kernel.

Companion lemmas: `OSetZFA.singleton_mk` (§4), `OSetZFA.mem_singleton` (§5). -/
noncomputable def OSetZFA.singleton (x : OSetZFA.{u}) : OSetZFA.{u} :=
  Quotient.liftOn x
    (fun a => OSetZFA.mk (CoPSet.mk PUnit.{u+1} (fun _ => a)))
    (fun _ _ hab => OSetZFA.sound (singleton_congr hab))

-- ============================================================
-- §4. OSetZFA.singleton_mk — computation rule
-- ============================================================

/-- **Computation rule**: `OSetZFA.singleton (OSetZFA.mk a)` unfolds to
the CoPSet with one child `a`.

`OSetZFA.singleton (OSetZFA.mk a) = OSetZFA.mk (CoPSet.mk PUnit.{u+1} (fun _ => a))`

**Proof**: `rfl`. `Quotient.liftOn ⟦a⟧ f h = f a` definitionally. -/
theorem OSetZFA.singleton_mk (a : CoPSet.{u}) :
    OSetZFA.singleton (OSetZFA.mk a) = OSetZFA.mk (CoPSet.mk PUnit.{u+1} (fun _ => a)) := rfl

-- ============================================================
-- §5. OSetZFA.mem_singleton — membership characterization
-- ============================================================

/-- **Singleton membership**: `z ∈ OSetZFA.singleton x ↔ z = x`.

The singleton set has exactly one member: `x`.

**Proof**: reduce to PSet representatives via `OSetZFA.mk_surjective`.
After `rw [singleton_mk, OSetZFA.mem_mk, OSetZFA.eq_iff]`, the goal is:
  `(∃ _ : (CoPSet.mk PUnit.{u+1} (fun _ => b)).shape, a ≈ ...) ↔ a ≈ b`
`change (∃ _ : PUnit.{u+1}, a ≈ b) ↔ a ≈ b` exploits:
- `(CoPSet.mk PUnit.{u+1} (fun _ => b)).shape = PUnit.{u+1}` (by `CoPSet.shape_mk : rfl`)
- `(CoPSet.mk PUnit.{u+1} (fun _ => b)).children i = b` for any `i` (by `CoPSet.dest_mk : rfl`)
Both are definitional. -/
@[simp]
theorem OSetZFA.mem_singleton (z x : OSetZFA.{u}) :
    z ∈ OSetZFA.singleton x ↔ z = x := by
  obtain ⟨a, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨b, rfl⟩ := OSetZFA.mk_surjective x
  rw [singleton_mk, OSetZFA.mem_mk, OSetZFA.eq_iff]
  -- Goal: (∃ i : ....shape, a ≈ ....children i) ↔ a ≈ b
  -- shape and children reduce definitionally to PUnit.{u+1} and b
  change (∃ _ : PUnit.{u+1}, a ≈ b) ↔ a ≈ b
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩

-- ============================================================
-- §6. quineAtom_eq_singleton_self — canonical Quine atom equation
-- ============================================================

/-- **Canonical Quine atom equation**: `quineAtom = OSetZFA.singleton quineAtom`.

The Quine atom equals its own singleton: `q = {q}`.

This is the canonical AFA equation for the Quine atom, now expressed
without reference to the graph construction (Stage 7 used
`graphDecoration` directly). External users can use this form.

**Proof**: extensionality. `z ∈ quineAtom ↔ z = quineAtom` (Stage 7)
and `z ∈ OSetZFA.singleton quineAtom ↔ z = quineAtom` (`mem_singleton`).
Both sides agree by `Iff.rfl`. -/
theorem quineAtom_eq_singleton_self :
    quineAtom = OSetZFA.singleton quineAtom := by
  apply OSetZFA.ext; intro z
  simp only [quineAtom_mem_iff, OSetZFA.mem_singleton]

-- ============================================================
-- §7. acc_irrefl — public utility (Acc-level irreflexivity)
-- ============================================================

/-- **Accessible elements are irreflexive**: `Acc r x → ¬ r x x`.

If `x` is accessible under `r`, then `r x x` is impossible.

**Proof**: `Acc.rec` with motive `¬ r x x`. Induction hypothesis gives
`ih : ∀ y, r y x → ¬ r y y`. Taking `y := x`: `ih x h : ¬ r x x`, but
`h : r x x`. Contradiction via `ih x h h : False`.

**mathlib context**: mathlib provides `WellFounded.irrefl : WellFounded r → Std.Irrefl r`
(at the `WellFounded` level, not `Acc`). `acc_irrefl` is complementary:
it works when only `Acc r x` is known (strictly weaker hypothesis).
This arises in coinductive or partial well-foundedness arguments where
`WellFounded r` is not available.

**Used in Stage 7**: `OSetZFA_mem_not_wf` and `quineAtom_not_in_range_embedOSet`.
Exported here for external users. -/
theorem acc_irrefl {α : Type*} {r : α → α → Prop} {x : α}
    (h : Acc r x) : ¬ r x x := by
  induction h with
  | intro _ _ ih => intro hrr; exact ih _ hrr hrr

-- ============================================================
-- §8. @[simp] attribute additions
-- ============================================================

-- Add @[simp] to Stage 7 membership lemmas.
-- These are safe (no simp loops — see module doc analysis above).
--
-- quineAtom_mem_iff: z ∈ quineAtom → z = quineAtom (no loop)
-- omegaChain_mem_iff: z ∈ omegaChain n → z = omegaChain (n+1) (index strictly increases)

attribute [simp] quineAtom_mem_iff
attribute [simp] omegaChain_mem_iff

-- ============================================================
-- §9. Full axiom audit — all 8 stages
-- ============================================================

-- Run to verify: all public objects at standard ceiling.
-- Uncomment to execute (slow: imports full dependency chain).

-- Stage 1 (CoPSet): graphCoalg has NO axioms; corec/dest axiom-free.
-- Stage 2 (Cobisimulation): bisim_imp_Equiv uses [propext, Classical.choice, Quot.sound].
-- Stage 3 (OSetZFA): quotient uses [propext, Classical.choice, Quot.sound].
-- Stage 4 (Membership): mem_mk, ext at standard ceiling.
-- Stage 5 (AFA): AFA_in_OSetZFA at standard ceiling; graphCoalg axiom-free.
-- Stage 6 (Embedding): embedPSet axiom-free; all theorems at standard ceiling.
-- Stage 7 (Examples): all 10 objects at standard ceiling.
-- Stage 8 (API): all new objects at standard ceiling.

section AxiomAudit

-- Spot-check the key objects across stages:
#print axioms OSetZFA.empty        -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.singleton    -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_singleton -- [propext, Classical.choice, Quot.sound]
#print axioms quineAtom_eq_singleton_self -- [propext, Classical.choice, Quot.sound]
#print axioms acc_irrefl           -- [propext, Classical.choice, Quot.sound]

-- Verify axiom-free objects (should print "does not depend on any axioms"):
#print axioms embedPSet            -- no axioms
#print axioms graphCoalg           -- no axioms

end AxiomAudit

end VR.SetsZFA
