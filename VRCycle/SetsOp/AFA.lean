-- VRCycle/SetsOp/AFA.lean
-- VR-Sets, Brouwer edition — Stage S8: Anti-Foundation as a near-free theorem on OpSet.
--
-- On the pointed-graph carrier, Aczel's AFA is almost definitional. A graph (V,E) is
-- decorated by `decorate E v := (V,E,v)` — the graph re-pointed at v — and this satisfies the
-- decoration equation by `rfl` (membership in OpSet IS the decoration condition). Uniqueness
-- up to operational identity `≈` is choice-free: the witnessing bisimulation
-- `R a w := (d v).child a ≈ d w` is EXHIBITED, not selected (contrast the M-type register,
-- SetsZFA, whose uniqueness picks representatives with `Classical.choice` and runs
-- `PFunctor.M.bisim` through the choice-pulling `dest`). This is the stitch point with
-- VR-Sets-ZFA: the same anti-foundational content, here relational and choice-free, there
-- quotiented and Tier-3 — a theorem about the cost of forming the quotient.
--
-- With this, OpSet holds ZFC and ZFA natively (Foundation = the predicate IsGrounded; AFA = a
-- theorem) on one carrier under one identity. Target: choice-free.

import VRCycle.SetsOp.Closure

namespace VRCycle.SetsOp

universe u

-- ============================================================
-- §1.  Decoration
-- ============================================================

/-- The canonical decoration of a graph `(V,E)`: the vertex `v` decorated by the graph
re-pointed at `v`. (`E a b` reads ``a is revealed as a member at b''.) -/
def OpSet.decorate {V : Type u} (E : V → V → Prop) (v : V) : OpSet.{u} := ⟨V, E, v⟩

/-- `d` decorates `(V,E)`: the members of `d v` are exactly the `d w` with `E w v`. -/
def IsDecoration {V : Type u} (E : V → V → Prop) (d : V → OpSet.{u}) : Prop :=
  ∀ v z, OpSet.Mem z (d v) ↔ ∃ w, E w v ∧ z.Equiv (d w)

/-- Membership in a re-pointed graph, definitionally. -/
theorem OpSet.mem_child {x : OpSet.{u}} (a : x.V) (z : OpSet.{u}) :
    OpSet.Mem z (x.child a) ↔ ∃ b, x.E b a ∧ z.Equiv (x.child b) := Iff.rfl

-- ============================================================
-- §2.  Existence (definitional)
-- ============================================================

/-- **AFA existence.** The canonical decoration decorates the graph --- by `rfl`: membership in
`decorate E v` *is* the decoration condition. -/
theorem OpSet.decorate_isDecoration {V : Type u} (E : V → V → Prop) :
    IsDecoration E (OpSet.decorate E) :=
  fun _ _ => Iff.rfl

-- ============================================================
-- §3.  Uniqueness up to ≈ (choice-free bisimulation)
-- ============================================================

/-- Any decoration is pointwise `≈` to the canonical one. The bisimulation
`R a w := (d v).child a ≈ d w` is exhibited; no representative is chosen, so the proof stays
below the choice floor. -/
theorem OpSet.decoration_equiv_decorate {V : Type u} {E : V → V → Prop}
    {d : V → OpSet.{u}} (hd : IsDecoration E d) (v : V) :
    (d v).Equiv (OpSet.decorate E v) := by
  refine ⟨fun a w => ((d v).child a).Equiv (d w), ?_, ?_⟩
  · -- the points: (d v).child (d v).pt = d v, so R relates them by reflexivity
    show ((d v).child (d v).pt).Equiv (d v)
    exact OpSet.Equiv.refl _
  · intro a w hR
    refine ⟨?_, ?_⟩
    · -- forward: a child of (d v) at a maps to some E-predecessor of w
      intro a' ha'
      have hmem : OpSet.Mem ((d v).child a') ((d v).child a) :=
        (OpSet.mem_child a _).mpr ⟨a', ha', OpSet.Equiv.refl _⟩
      have hmem' : OpSet.Mem ((d v).child a') (d w) := OpSet.mem_congr hR hmem
      obtain ⟨w', hw', heq⟩ := (hd w _).mp hmem'
      exact ⟨w', hw', heq⟩
    · -- backward: an E-predecessor of w maps to some child of (d v) at a
      intro w' hw'
      have hmem : OpSet.Mem (d w') (d w) := (hd w _).mpr ⟨w', hw', OpSet.Equiv.refl _⟩
      have hmem' : OpSet.Mem (d w') ((d v).child a) := OpSet.mem_congr hR.symm hmem
      obtain ⟨a', ha', heq⟩ := (OpSet.mem_child a _).mp hmem'
      exact ⟨a', ha', heq.symm⟩

/-- **AFA uniqueness.** Any two decorations of the same graph are pointwise operationally
identical. (Through the canonical decoration; choice-free.) -/
theorem OpSet.decoration_unique {V : Type u} {E : V → V → Prop} {d d' : V → OpSet.{u}}
    (hd : IsDecoration E d) (hd' : IsDecoration E d') (v : V) :
    (d v).Equiv (d' v) :=
  (OpSet.decoration_equiv_decorate hd v).trans
    (OpSet.decoration_equiv_decorate hd' v).symm

-- ============================================================
-- §4.  AFA
-- ============================================================

/-- **Anti-Foundation on OpSet.** Every graph has a decoration, unique up to operational
identity `≈`. A theorem, not an axiom: existence is definitional, uniqueness a choice-free
bisimulation. Together with Foundation-as-predicate (`IsGrounded`), OpSet holds ZFC and ZFA
natively on one carrier. -/
theorem OpSet.afa {V : Type u} (E : V → V → Prop) :
    ∃ d : V → OpSet.{u}, IsDecoration E d ∧
      ∀ d' : V → OpSet.{u}, IsDecoration E d' → ∀ v, (d v).Equiv (d' v) :=
  ⟨OpSet.decorate E, OpSet.decorate_isDecoration E,
   fun _ hd' v => (OpSet.decoration_equiv_decorate hd' v).symm⟩

-- CHECKS: no sorry, no admit; self-contained; identity stays a witnessed bisimulation.

-- Axiom audit (Stage S8) — MEASURED.  Target: choice-free.
#print axioms OpSet.decorate_isDecoration
#print axioms OpSet.decoration_equiv_decorate
#print axioms OpSet.decoration_unique
#print axioms OpSet.afa

end VRCycle.SetsOp
