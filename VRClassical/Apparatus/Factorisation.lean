-- VRClassical/Apparatus/Factorisation.lean — the Riesz extension with a Factorisable witness
-- (split out of VRCycle/Apparatus/Factorisation.lean on 2026-09-12: Factorisable and its theorems
-- stay in the VR core on `[]`; the Hilbert-space instance lives here).

import VRCycle.Apparatus.Factorisation
import VRClassical.Apparatus.ModeB

namespace VR.Apparatus

-- ============================================================
-- §5. Concrete instance: Riesz extension with Factorisable witness
-- ============================================================
--
-- ## Setup (parallel to ModeB.lean §5)
--   A  = OperationalNormableFunctional E M
--   B  = E →L[ℝ] ℝ
--   PA = fun _ => True
--   PB = riesz_PB_fact (= riesz_PB from ModeB.lean, private here)
--   f  = riesz_extension_map (= (HahnBanachOperational_Hilbert f).choose)
--
-- ## Self-witnessing: g = riesz_extension_map
-- The natural Factorisable witness for riesz_extension_map at operand f is
-- g = riesz_extension_map itself. Two conditions:
--
--   (1) ∀ x : A, True → riesz_PB_fact (riesz_extension_map x):
--       Proved from HahnBanachOperational_Hilbert.choose_spec, same as
--       riesz_extension_isModeBOp in ModeB.lean.
--
--   (2) riesz_extension_map f = riesz_extension_map f: rfl.
--
-- Self-witnessing (g = f) is valid and mathematically meaningful:
-- riesz_extension_map is globally Mode B (W = True in ModeB.lean), so it
-- witnesses its own Factorisability at every operand. The structural reason
-- is the Riesz geometry: g(denseSeq n) = ⟨denseSeq n, ξ⟩ = f(P_M(denseSeq n)),
-- where ξ is the Riesz representor determined by the operand f.
-- The self-witnessing proof encapsulates this route through HahnBanachOperational_Hilbert
-- without making ξ explicit as a separate term.
--
-- ## Spectrum-of-witnesses comparison (Stage 4 finding)
--
-- v0.1.0 riesz_extension_isModeBOp  (ModeB.lean, W = fun _ => True):
--   Operationality certified directly from choose_spec. Minimal witness.
--   «It works, we don't explain why.»
--
-- v1.0.0 riesz_extension_isModeBOp' (here, W = Factorisable PA PB f):
--   Witness g = riesz_extension_map made explicit. Structural account.
--   «It works because f self-witnesses — f is already an operational function
--   that agrees with itself at every operand.»
--
-- Both witnesses are valid simultaneously. The apparatus structure admits this
-- spectrum from minimal (True) to canonical (Factorisable). Making the witness
-- more informative doesn't change the Mode B instance — it enriches the
-- certificate. This is the spectrum-of-witnesses phenomenon in concrete form.

-- Private copy of PB predicate.
-- riesz_PB in ModeB.lean is `private` — cannot be accessed outside that file.
-- Redefined here identically to avoid modifying v0.1.0 files.
private def riesz_PB_fact {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E] : (E →L[ℝ] ℝ) → Prop :=
  fun g =>
    (∀ n : ℕ, VR.Audit.IsComputableReal
      (g (VR.Audit.OperationalHilbertSpace.denseSeq (E := E) n))) ∧
    VR.Audit.IsComputableReal g.opNorm

/-- The Riesz extension map is Factorisable at every operational functional.

**Witness**: g = riesz_extension_map (self-witnessing).

**Condition (1)** — g preserves riesz_PB_fact:
  ∀ x : OperationalNormableFunctional E M, True → riesz_PB_fact (riesz_extension_map x).
  Proof: from HahnBanachOperational_Hilbert.choose_spec:
    .1  → ∀ n, IsComputableReal (g (denseSeq n))
    .2.1 → IsComputableReal g.opNorm.

**Condition (2)** — agreement at the specific operand:
  riesz_extension_map f = riesz_extension_map f. (rfl)

**Self-witnessing explanation**:
riesz_extension_map is globally Mode B (riesz_extension_isModeBOp, W = True),
so it is an operational function. An operational function g = f always witnesses
Factorisable PA PB f a at every a: g agrees with f (trivially) and is operational.

**Deeper mathematical structure** (from ModeB.lean §5 comment):
The reason riesz_extension_map is operational is the Riesz factorisation:
  g(denseSeq n) = ⟨denseSeq n, ξ⟩ = f(P_M(denseSeq n))
where ξ is the Riesz representor determined by the operand functional f.
The self-witnessing proof encapsulates this route via HahnBanachOperational_Hilbert
without requiring explicit construction of ξ as a separate Lean term.

## Axiom profile: [propext, Classical.choice, Quot.sound]
  Classical.choice: HahnBanachOperational_Hilbert uses .choose (Riesz, toDual).
  propext, Quot.sound: standard ceiling from mathlib. -/
theorem riesz_extension_factorisable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E}
    (f : VR.Audit.OperationalNormableFunctional E M) :
    Factorisable
      (PA := fun (_ : VR.Audit.OperationalNormableFunctional E M) => True)
      (PB := riesz_PB_fact (E := E))
      riesz_extension_map f :=
  ⟨riesz_extension_map,
   fun x _ =>
     let hspec := (VR.Audit.HahnBanachOperational_Hilbert x).choose_spec
     ⟨hspec.1, hspec.2.1⟩,
   rfl⟩

/-- The Riesz extension is Mode B with Factorisable as canonical witness.

**New in v1.0.0**: this is the Factorisable-witness version of
`riesz_extension_isModeBOp` from ModeB.lean (v0.1.0, W = fun _ => True).

**Coexistence**: both theorems hold simultaneously:
  riesz_extension_isModeBOp  (ModeB.lean):  W = fun _ => True (minimal).
  riesz_extension_isModeBOp' (here):        W = Factorisable ... (canonical).

**Spectrum of witnesses** — Stage 4 finding for preprint:
  Old (W = True): operationality certified, no structural account.
  New (W = Factorisable, g = f): structural account — f self-witnesses its
    operationality. The apparatus records that an operational g (= f itself)
    agrees with f at every operand, explaining WHY Mode B holds.
  Both valid. Neither supersedes the other. The apparatus admits a spectrum
  from minimal (True) to canonical (Factorisable). Witnesses can be made
  progressively more informative without breaking apparatus structure or
  requiring modifications to previously proved theorems.

**Proof**: direct from operand_determines_operational — no new mathematics,
only structural repackaging. The Factorisable certificate (W a = hfact) is
passed in by the caller; operand_determines_operational extracts PB (f a).

## Axiom profile: [propext, Classical.choice, Quot.sound]
  riesz_extension_map in the type → inherits Classical.choice from HahnBanach.
  propext, Quot.sound: standard ceiling. -/
theorem riesz_extension_isModeBOp' {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E} :
    IsModeBOp
      (A := VR.Audit.OperationalNormableFunctional E M)
      (B := E →L[ℝ] ℝ)
      (PA := fun _ => True)
      (PB := riesz_PB_fact (E := E))
      (W := Factorisable
        (PA := fun (_ : VR.Audit.OperationalNormableFunctional E M) => True)
        riesz_PB_fact
        riesz_extension_map)
      riesz_extension_map :=
  fun _f _ hfact => operand_determines_operational riesz_extension_map _f trivial hfact

-- ============================================================
-- §6. Consistency check — coexistence of both Riesz witnesses
-- ============================================================

-- Verify: riesz_extension_isModeBOp' is a genuine IsModeBOp certificate,
-- compatible with the machinery from ModeB.lean.
-- This confirms that the two witnesses (W = True, W = Factorisable) coexist
-- as independent Mode B certificates for the same operation.

-- We can lift via Factorisable.lift using riesz_extension_factorisable
-- to produce an operational Subtype element.
-- (noncomputable because riesz_extension_map is noncomputable)
private noncomputable def riesz_factorisable_lift_example {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E}
    (f : VR.Audit.OperationalNormableFunctional E M) :
    {g : E →L[ℝ] ℝ // riesz_PB_fact g} :=
  Factorisable.lift ⟨f, trivial, riesz_extension_factorisable f⟩

-- Computation rule: the lifted value is riesz_extension_map f.
example {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [VR.Audit.OperationalHilbertSpace E]
    {M : VR.Audit.OperationalLocatedSubspace E}
    (f : VR.Audit.OperationalNormableFunctional E M) :
    (riesz_factorisable_lift_example f).val = riesz_extension_map f :=
  rfl

#print axioms riesz_extension_factorisable
#print axioms riesz_extension_isModeBOp'

end VR.Apparatus
