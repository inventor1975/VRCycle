-- VR-Transit: Located (v0.1.0, Stage 3)
-- Located witness provider: the analytic-completeness family of the witness library.
-- The located subspace structure SUPPLIES the operational witness (g = f ∘ P_M),
-- not merely the evaluation points — this is its leverage over separability.
--
-- STAGE: Stage 3. SOURCE: PLAN.md Stage 3 brief.
--
-- ## Position statement
-- Third provider in the witness library, second of the two analytic providers
-- (separability = density; this = located/completeness). For an operational normable
-- functional `f` on an operational located subspace `M ≤ E`, the orthogonal
-- projection `P_M` (free from `M`'s closedness + `CompleteSpace E`) yields a
-- STRUCTURALLY-SUPPLIED witness `g := fun e => f.toFun (P_M e)`: the located structure
-- provides both the witness function and a proof it is globally operational
-- (`located_witness_operational`, via the public `fn_computable_everywhere`). The
-- bridge `located_provides_factorisable` then certifies any operation agreeing with
-- `g` on the ambient dense sequence as `Factorisable` at those points.
--
-- ## Novelty — NOT a re-skin (recognition-discipline gate, PLAN.md Stage 3)
-- This provider is genuinely distinct from the two nearest objects:
--   • vs `riesz_extension_factorisable` (Apparatus): that is SELF-witnessing (g = f,
--     operand level). Here the witness `g = f ∘ P_M` is built from the located
--     projection and is NOT the operation itself; it lives at the evaluation-point
--     level (operand = `denseSeq n : E`). This is the Level-B Factorisable that
--     `Separability.lean` §5 left DEFERRED — now realised through the located
--     structure.
--   • vs `separability_provides_factorisable` (Apparatus): that is fully generic —
--     the witness is a caller-supplied parameter and the bridge is `[]`. Here the
--     located structure CONSTRUCTS the witness (`f ∘ P_M`) and CERTIFIES its global
--     operationality; the caller supplies only the agreement on `denseSeq`. Supplying
--     an operational witness (not just naming points) is the added leverage.
-- The witness `g` is structurally built from `P_M` and differs from the self-witness;
-- the provider therefore counts. (Had `g` collapsed to the operation itself, this
-- would be a re-skin → drop and report; it does not.)
--
-- ## Reuse, not re-proof (recon 3.0)
-- The projection identity `g(denseSeq n) = f(P_M(denseSeq n))` is locked inside the
-- proof of `HahnBanachOperational_Hilbert` (HahnBanach.lean §6 Part 1, as a local
-- `have hchain`); it is the AGREEMENT hypothesis of the bridge, supplied caller-side,
-- exactly as in the separability provider. The reusable structural piece — the
-- witness's global operationality — is already public as `fn_computable_everywhere`
-- (Functional.lean), so nothing is re-proved. Non-vacuity: the real Riesz extension
-- of `HahnBanachOperational_Hilbert` satisfies the agreement (that IS its `hchain`),
-- so the bridge fires on the genuine Hahn-Banach operation; exposing that `g` as a
-- named object would require refactoring prior work (HahnBanach's existential), which
-- this stage does not do.
--
-- ## Axiom profile overview
--   located_witness_operational            [propext, Classical.choice, Quot.sound]
--   located_provides_factorisable          [propext, Classical.choice, Quot.sound]
-- Both are CHOICE-bearing, and that is faithful, not a failure (Stage-2 framing):
-- the source is the OPERATION (orthogonal projection via `CompleteSpace`/`toDual`, and
-- `fn_computable_everywhere`'s `Classical.choose`), NOT the apparatus. Apparatus ∅.

import VRCycle.Apparatus
import VRCycle.Audit

namespace VR.Transit

open VR.Apparatus VR.Audit

-- ============================================================
-- §1. Structural operationality of the located witness (reused, not re-proved)
-- ============================================================

/-- The located witness `f ∘ P_M` is globally operational: for every ambient point
`e : E`, the value `f.toFun (P_M e)` is a computable real.

This is the reusable structural piece of the located provider (recon 3.1). The
orthogonal projection `P_M e` lands in `M.toSubmodule` (closedness of `M` +
`CompleteSpace E` give `HasOrthogonalProjection` for free), and the public
`fn_computable_everywhere` (Functional.lean) makes every value of `f` on
`M.toSubmodule` a computable real. Nothing is re-proved.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  SOURCE: OPERATION — orthogonal projection (`CompleteSpace`/`HasOrthogonalProjection`)
  and `fn_computable_everywhere` (`Classical.choose`). Apparatus contributes nothing. -/
theorem located_witness_operational {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    {M : OperationalLocatedSubspace E}
    (f : OperationalNormableFunctional E M) (e : E) :
    IsComputableReal (f.toFun (M.toSubmodule.orthogonalProjection e)) := by
  haveI hK_proj : M.toSubmodule.HasOrthogonalProjection := inferInstance
  exact fn_computable_everywhere f (M.toSubmodule.orthogonalProjection e)

-- ============================================================
-- §2. Located bridge: located structure provides a Factorisable witness
-- ============================================================

/-- Located provider: if an operation `op : E → ℝ` agrees, on every ambient dense
point, with the located witness `f ∘ P_M`, then `op` is `Factorisable` at each dense
point, the witness being `f ∘ P_M` supplied (and certified operational) by the located
structure.

**Statement.**
  [OperationalHilbertSpace E] {M : OperationalLocatedSubspace E}
  + (f : OperationalNormableFunctional E M)
  + hagree : ∀ n, op (denseSeq n) = f.toFun (P_M (denseSeq n))   (agreement on denseSeq)
  → Factorisable (fun _ => True) IsComputableReal op (denseSeq n)

The witness is `g := fun e => f.toFun (P_M e)`; its three `Factorisable` components are
the structural witness `g`, its global operationality
(`located_witness_operational`), and the agreement `hagree n`. The agreement is the
caller's obligation — for the Riesz extension it is exactly `HahnBanachOperational_Hilbert`'s
`hchain` (see file-header "Reuse, not re-proof"). This is the evaluation-point-level
(Level B) Factorisable that `Separability.lean` §5 deferred, now delivered by the
located structure.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  SOURCE: OPERATION (orthogonal projection via completeness + `fn_computable_everywhere`),
  inherited from `located_witness_operational`. Apparatus contributes nothing;
  `Factorisable` itself is `[]`. Faithful per the Stage-2 attribution framing. -/
theorem located_provides_factorisable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    {M : OperationalLocatedSubspace E}
    (f : OperationalNormableFunctional E M)
    {op : E → ℝ}
    (hagree : ∀ n : ℕ, op (OperationalHilbertSpace.denseSeq (E := E) n)
                = f.toFun (M.toSubmodule.orthogonalProjection
                    (OperationalHilbertSpace.denseSeq (E := E) n)))
    (n : ℕ) :
    Factorisable (fun _ : E => True) IsComputableReal op
      (OperationalHilbertSpace.denseSeq (E := E) n) :=
  ⟨fun e => f.toFun (M.toSubmodule.orthogonalProjection e),
   fun e _ => located_witness_operational f e,
   hagree n⟩

-- ============================================================
-- Axiom audit — Stage 3, Located.lean
-- ============================================================
-- STAGE: Stage 3. SOURCE: PLAN.md Stage 3.
-- LEAN OBJECTS (2 public objects):
--   located_witness_operational        (theorem, structural operationality of f ∘ P_M)
--   located_provides_factorisable      (theorem, located → Factorisable bridge)
-- AXIOM AUDIT (target → actual, PLAN.md Stage 3):
--   located_witness_operational    [P,C,Q] → [propext, Classical.choice, Quot.sound] ✓
--   located_provides_factorisable  [P,C,Q] → [propext, Classical.choice, Quot.sound] ✓
-- Choice is FAITHFUL: source is the OPERATION (orthogonal projection via completeness;
-- fn_computable_everywhere's Classical.choose), not the apparatus. The apparatus column
-- is empty (Conservativity.lean §5 framing). Not a re-skin: witness g = f ∘ P_M is
-- structurally built from the located projection, distinct from the self-witness g = f
-- of riesz_extension_factorisable and from the caller-supplied generic witness of
-- separability_provides_factorisable.
-- CHECKS: no sorry, no admit.

#print axioms located_witness_operational
#print axioms located_provides_factorisable

end VR.Transit
