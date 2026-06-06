-- VRCycle/Continuum/Cantor.lean
-- Operational Continuum (Path 1) — the Cantor diagonal, reframed operationally.
--
-- STAGE: B (consolidation). SOURCE: VR-LOGIC.md §1 (diagonal "with a different character").
--
-- ## What this file does
-- Collects the three already-proved facts into ONE citable statement, `operational_cantor`,
-- and names the operational reading of Cantor's diagonal:
--
--   (1) the OPERATIONAL register (performed nodes `List Bool`, the "done") is COUNTABLE
--       — `operational_register_countable` (witness: `decodeNode`, hand-rolled, choice-free);
--   (2) the BECOMING register (lawless branches `ℕ → Bool`, the "potential") is NON-ENUMERABLE
--       — `branches_not_enumerable` (the Cantor diagonal itself, choice-free);
--   (3) the countable done cannot exhaust the becoming — `no_node_surjection`.
--
-- ## The reframe (VR-LOGIC §1, §2)
-- Classically, Cantor's diagonal proves |℘(ℕ)| > |ℕ| by selecting an element from the
-- COMPLETED totality ℘(ℕ). Here there is no completed totality: the diagonal still cuts, but
-- between the countable PERFORMED and the non-enumerable BECOMING — `no_node_surjection` is
-- that cut as a theorem. The diagonal is REINTERPRETED, not removed: from a theorem about a
-- finished uncountable set to a witness of the gap between done and becoming.
--
-- Bridge to ℘(ℕ) / the absence of a completed totality is the NEXT step (essay-level in part;
-- see VR-LOGIC §3) and is NOT claimed here. This file is the machine-checked core only.
--
-- ## Axiom profile: choice-free throughout (verified by #print axioms below).
--   operational_register_countable : [propext, Quot.sound] (via decodeNode round-trip)
--   operational_cantor             : [propext, Quot.sound] (carries no_node_surjection's tier)

import VRCycle.Continuum.Registers

namespace VRCycle.Continuum

/-- **The operational register is countable.**  The performed-node space `List Bool` (the
"done") is enumerated by `decodeNode : ℕ → List Bool`, which is surjective (left-inverse of the
hand-rolled `encodeNode`).  Choice-free — the operational register is constructively listable. -/
theorem operational_register_countable : ∃ e : ℕ → List Bool, Function.Surjective e :=
  ⟨decodeNode, fun s => ⟨encodeNode s, decodeNode_encodeNode s⟩⟩

/-- **The operational Cantor statement.**  The diagonal, read in the three registers:
the *done* is countable (1), the *becoming* is non-enumerable (2, the diagonal proper), and
the countable done cannot exhaust the becoming (3).  This is the cut between performed and
becoming — not the selection of an element from a completed uncountable totality (there is
none operationally).  All three conjuncts are independently machine-checked and choice-free. -/
theorem operational_cantor :
    (∃ e : ℕ → List Bool, Function.Surjective e) ∧
    (¬ ∃ e : ℕ → Branch, Function.Surjective e) ∧
    (¬ ∃ f : List Bool → Branch, Function.Surjective f) :=
  ⟨operational_register_countable, branches_not_enumerable, no_node_surjection⟩

-- ============================================================
-- §Bridge to ℘(ℕ): the diagonal separates describable from completed
-- ============================================================
--
-- A subset of ℕ is its characteristic function `ℕ → Bool` (= a `Branch`); the space of all
-- such functions IS ℘(ℕ).  "Operational / describable family of subsets" = an ENUMERABLE
-- family `e : ℕ → (ℕ → Bool)`.  The diagonal escapes every such family; the full ℘(ℕ) is
-- non-enumerable.  Hence the uncountability of ℘(ℕ) rests on the non-describable diagonal
-- subset — it lives in the COMPLETED totality, not in the operational (enumerable) layer.
-- No model of computability is fixed: the honest content is "no countable description-family
-- is complete." That ℘(ℕ) as a completed totality is operationally absent is essay-level
-- (meta, VR-LOGIC §3), NOT claimed in the code.

/-- **The diagonal escapes any enumeration of subsets.**  For every countable (describable)
family `e : ℕ → (ℕ → Bool)` of subsets of ℕ, the diagonal subset `d n = !(e n n)` differs from
every `e k`.  Choice-free — Cantor's diagonal, on characteristic functions. -/
theorem diagonal_escapes_enumeration (e : ℕ → (ℕ → Bool)) :
    ∃ d : ℕ → Bool, ∀ k, d ≠ e k := by
  refine ⟨fun n => !(e n n), ?_⟩
  intro k hk
  have h : (!(e k k)) = e k k := congrFun hk k
  cases hb : e k k <;> rw [hb] at h <;> simp at h

/-- **℘(ℕ), as characteristic functions, is non-enumerable.**  No `e : ℕ → (ℕ → Bool)` is
surjective — its diagonal subset is missed.  Choice-free. -/
theorem powerset_not_enumerable : ¬ ∃ e : ℕ → (ℕ → Bool), Function.Surjective e := by
  rintro ⟨e, he⟩
  obtain ⟨d, hd⟩ := diagonal_escapes_enumeration e
  obtain ⟨k, hk⟩ := he d
  exact hd k hk.symm

/-- **The ℘(ℕ) bridge.**  The full powerset (characteristic space) is non-enumerable (1), yet
every countable/describable family of subsets misses its own diagonal (2).  So the
uncountability of ℘(ℕ) requires the non-describable diagonal subset: it lives in the completed
totality, not in the operational (enumerable) layer.  Machine-checked, choice-free; the
operational absence of the completed ℘(ℕ) is essay-level (VR-LOGIC §3), not asserted here. -/
theorem powerset_diagonal :
    (¬ ∃ e : ℕ → (ℕ → Bool), Function.Surjective e) ∧
    (∀ e : ℕ → (ℕ → Bool), ∃ d : ℕ → Bool, ∀ k, d ≠ e k) :=
  ⟨powerset_not_enumerable, diagonal_escapes_enumeration⟩

-- ============================================================
-- Axiom audit
-- ============================================================
#print axioms operational_register_countable
#print axioms operational_cantor
#print axioms diagonal_escapes_enumeration
#print axioms powerset_not_enumerable
#print axioms powerset_diagonal

end VRCycle.Continuum
