-- VR-Transit: Conservativity (v0.1.0, Stage 2)
-- Transit conservativity (thesis I), EXHIBITED by axiom attribution — a recognition
-- stage: no new axioms, no new public theorems, only #print axioms + attribution prose.
--
-- STAGE: Stage 2. SOURCE: PLAN.md Stage 2 (reformulated brief).
--
-- ## Position statement
-- Thesis (I) — "the apparatus is an inert, axiom-free spine; the profile of any
-- transited object equals the profile of its operation plus its witness; the
-- apparatus contributes nothing" — is a RECOGNITION result, not a construction. Its
-- internal content is already proved and already stands on `[]`:
--   • operand_determines_operational, factorisable_implies_isModeBOp,
--     IsModeBOp_of_factorisable — the apparatus reductions, all `[]`.
--   • Factorisable.lift_val — `[]`, and it is `rfl`: the transited operation
--     definitionally *is* `f` on the operational subtype (transparency).
--   • IsModeBOp.compose — `[]`: the composition combinator injects no axiom.
-- There is nothing to re-prove. This file therefore does NOT introduce a renamed
-- duplicate "conservativity" theorem (that would be abstraction for show), and does
-- NOT plant a synthetic `axiom` probe (that would pollute the very profile the
-- programme rests on). The real instances of the cycle ARE the probe.
--
-- ## What this stage produces — an axiom-attribution audit (exhibition)
-- The universal form ("∀ f, profile(transit f) = profile(f)") is a kernel-level meta
-- fact (`#print axioms` is not an internal predicate), so it is EXHIBITED by
-- representatives, machine-checked and named, as the honest substitute. The new
-- content is the synthesis: a per-representative attribution showing that the
-- **apparatus column is empty everywhere**, and that each transit profile decomposes
-- into the four sources Stage 1 surfaced —
--   OPERATION ⊕ POINTWISE-WITNESS ⊕ AGGREGATION ⊕ CARRIER-ENCODING.
--
-- ## Gate (kill-criterion, PLAN.md Stage 2)
-- If any transited object carried an axiom NOT attributable to its operation, its
-- witness, aggregation, or carrier-encoding — i.e. if the "apparatus" column were
-- non-empty — thesis (I) would be false. The audit below shows it empty. This is the
-- cheap gate run BEFORE investing in further providers (Stage 3).
--
-- ## Axiom profile overview
--   This file declares NO new public objects. It cites existing profiles via
--   #print axioms; the only declarations are `private` exhibits used by the audit
--   (a compositional-conservativity demo and a carrier-encoding reproducer).

import VRCycle.Apparatus
import VRCycle.Algebra
import VRCycle.Transit.FiniteWitness

namespace VR.Transit

open VR.Apparatus VR.Algebra Finset

-- ============================================================
-- §1. Internal carriers of conservativity (already proved, cited — not re-proved)
-- ============================================================
-- The apparatus path from a witness to a Mode B operation, and the transparency of
-- the lift, are axiom-free. The apparatus contributes nothing to any transit.

#print axioms operand_determines_operational
-- 'VR.Apparatus.operand_determines_operational' does not depend on any axioms
--   ATTRIBUTION: apparatus reduction — []. Apparatus contributes nothing.
#print axioms factorisable_implies_isModeBOp
-- 'VR.Apparatus.factorisable_implies_isModeBOp' does not depend on any axioms
--   ATTRIBUTION: apparatus reduction — []. Apparatus contributes nothing.
#print axioms IsModeBOp_of_factorisable
-- 'VR.Apparatus.IsModeBOp_of_factorisable' does not depend on any axioms
--   ATTRIBUTION: apparatus reduction — []. Apparatus contributes nothing.
#print axioms Factorisable.lift_val
-- 'VR.Apparatus.Factorisable.lift_val' does not depend on any axioms
--   ATTRIBUTION: transparency (rfl: lift.val = f on the operational subtype) — [].
#print axioms IsModeBOp.compose
-- 'VR.Apparatus.IsModeBOp.compose' does not depend on any axioms
--   ATTRIBUTION: composition combinator — []. Composing transits injects no axiom.

-- ============================================================
-- §2. Cycle representatives + source attribution
-- ============================================================
-- Each representative's profile is attributed to ONE of the four sources (or none).
-- The "apparatus" column is empty in every row.

#print axioms riesz_extension_isModeBOp
-- 'VR.Apparatus.riesz_extension_isModeBOp' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
--   SOURCE: OPERATION (analytic — Riesz/Hahn-Banach uses Classical.choice). Not apparatus.
#print axioms image_isOperationalAddSubgroup_isModeBOp
-- 'VR.Algebra.image_isOperationalAddSubgroup_isModeBOp' depends on axioms: [propext]
--   SOURCE: OPERATION (algebraic — OperationalAddGroup/subgroup infrastructure, propext).
--   Not apparatus. ⚠ NOTE: the Stage-2 brief assumed []; actual is [propext]. The
--   apparatus column is still empty — propext attributes to the operation's own
--   algebraic infrastructure, not to transit. (See report / TR-C1.)
#print axioms separability_provides_factorisable
-- 'VR.Apparatus.separability_provides_factorisable' does not depend on any axioms
--   SOURCE: none — [] (POINTWISE witness; evaluated at one named operand, no aggregation).
#print axioms finiteGen_provides_factorisable
-- 'VR.Transit.finiteGen_provides_factorisable' does not depend on any axioms
--   SOURCE: none — [] (POINTWISE witness, Stage 1a).
#print axioms finiteSpan_provides_factorisable
-- 'VR.Transit.finiteSpan_provides_factorisable' depends on axioms: [propext, Quot.sound]
--   SOURCE: AGGREGATION (Finset.sum over operand data, Stage 1b). Choice-free. Not apparatus.

-- ============================================================
-- §3. Compositional conservativity (the optional clean demonstration)
-- ============================================================
-- Two axiom-free Mode B operations compose to an axiom-free Mode B operation: the
-- composite profile is the union of the component profiles, with NO inflation by the
-- apparatus. Demonstrated on schematic []-operations (no custom axiom, no synthetic
-- probe). The general statement is §1's `IsModeBOp.compose` (itself []); this is the
-- end-to-end witness that a composed transit injects nothing.

private theorem demoMB_left :
    IsModeBOp (fun _ : ℕ => True) (fun _ : ℕ => True) (fun _ => True) id :=
  fun _ _ _ => trivial

private theorem demoMB_right :
    IsModeBOp (fun _ : ℕ => True) (fun _ : ℕ => True) (fun _ => True) id :=
  fun _ _ _ => trivial

private def demoMB_composite := demoMB_left.compose demoMB_right

#print axioms demoMB_composite
-- '..demoMB_composite' does not depend on any axioms
--   ATTRIBUTION: [] ⊕ [] = []; composition injects nothing. Apparatus conservative.

-- ============================================================
-- §4. Carrier-encoding source reproducer (local, private)
-- ============================================================
-- The fourth source — CARRIER-ENCODING — reproduced locally (the FiniteWitness
-- exhibit is `private` and not reachable cross-file). A `Fintype`/`Finset.univ` index
-- over `Fin n` inflates even a `rfl` identity to the full standard ceiling: the
-- Classical.choice is from the index encoding, NOT from the apparatus or the algebra.

private theorem enc_exhibit_univ_pulls_choice {B : Type*} [AddCommGroup B]
    (w : Fin 3 → B) : (∑ i, w i) = ∑ i, w i := rfl

#print axioms enc_exhibit_univ_pulls_choice
-- '..enc_exhibit_univ_pulls_choice' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
--   SOURCE: CARRIER-ENCODING (Fintype (Fin n) / Finset.univ artefact, FINDING TR-FW1).
--   Removable by an explicit Finset (see finiteSpan, [propext, Quot.sound]). Not apparatus.

-- ============================================================
-- §5. Attribution synthesis — the exhibited classification
-- ============================================================
--
--   object                                   profile        source         apparatus
--   ──────────────────────────────────────────────────────────────────────────────
--   operand_determines_operational           []             (reduction)    ∅
--   factorisable_implies_isModeBOp           []             (reduction)    ∅
--   IsModeBOp_of_factorisable                []             (reduction)    ∅
--   Factorisable.lift_val                    []             (transparency) ∅
--   IsModeBOp.compose                        []             (combinator)   ∅
--   separability_provides_factorisable       []             pointwise      ∅
--   finiteGen_provides_factorisable          []             pointwise      ∅
--   image_isOperationalAddSubgroup_isModeBOp [propext]      operation/alg  ∅
--   finiteSpan_provides_factorisable         [P,Q]          aggregation    ∅
--   riesz_extension_isModeBOp                [P,C,Q]        operation/anal ∅
--   enc_exhibit (carrier-encoding artefact)  [P,C,Q]        encoding       ∅
--
-- READING: the "apparatus" column is empty in every row. Every transit profile
-- decomposes as OPERATION ⊕ POINTWISE-WITNESS ⊕ AGGREGATION ⊕ CARRIER-ENCODING, and
-- the apparatus injects nothing in any case. The OPERATION source is itself a
-- spectrum: algebraic infrastructure contributes [propext] (subgroup image), analytic
-- operations contribute [propext, Classical.choice, Quot.sound] (Riesz) — both are
-- operation-side, neither is apparatus.
--
-- GATE VERDICT: apparatus column empty ⇒ thesis (I) holds, exhibited on real cycle
-- data. The library may grow (Stage 3) on this confirmed footing. Thesis (I) is a
-- clarity result (cost attributed by source), not new mathematical power.
--
-- ============================================================
-- Axiom audit — Stage 2, Conservativity.lean
-- ============================================================
-- STAGE: Stage 2. SOURCE: PLAN.md Stage 2.
-- PUBLIC OBJECTS: none. This is an exhibition file (only #print axioms + private
--   exhibits). Private declarations: demoMB_left, demoMB_right, demoMB_composite
--   (compositional demo), enc_exhibit_univ_pulls_choice (encoding reproducer).
-- KEY DISCREPANCY FROM BRIEF: image_isOperationalAddSubgroup_isModeBOp is [propext]
--   (brief assumed []); attributed to the operation's algebraic infrastructure, gate
--   still passes. Recorded as TR-C1.
-- CHECKS: no sorry, no admit.

end VR.Transit
