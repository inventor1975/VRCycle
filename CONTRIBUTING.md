# Contributing to VRCycle

This document is for **Lean 4 developers** who want to use, understand, or extend the VRCycle formalisation. For the mathematical and philosophical context, see the companion preprints on [Zenodo](https://zenodo.org/communities/vr-cycle).

---

## Project structure

```
VRCycle/
├── VR.lean                  # VR. A Formal System: primitives, arithmetic, Peano (51 objects)
├── Numbers/                 # VR-Numbers: ℤ_VR, ℚ_VR, ℝ_VR, ℂ_VR as quotient types
├── Sets/                    # VR-Sets: ZFC axioms, ZFA boundary, conjectures
├── Forms/                   # VR-Forms: two-register apparatus, transit pattern
├── Audit/                   # VR-Audit: IsComputableReal, OperationalHilbertSpace, Hahn-Banach
├── SetsZFA/                 # VR-Sets-ZFA: CoPSet coinductive type, OSetZFA, AFA as theorem
├── Apparatus/               # VR-Apparatus: PredicateOperationality, ReferenceOperationality,
│   │                        #   Mode A, Mode B, InterApparatusMorphism, composition
│   └── Examples/            # Tutorial examples (E01–E04)
```

Root-level index files (`VRCycle/Apparatus.lean`, `VRCycle/Audit.lean`, etc.) re-export each subsystem's public API. Import the index to get everything; import individual files for targeted access.

**Conceptual organisation by layer:**

| Lean path | Apparatus concept |
|-----------|-------------------|
| `Apparatus/Identity.lean` | `IdentityNature` (AsPoint vs AsReference) |
| `Apparatus/Wrapping.lean` | `PredicateOperationality` marker class |
| `Apparatus/Reference.lean` | `ReferenceOperationality` (membership + ext) |
| `Apparatus/ModeA.lean` | `IsModeAOp` — closure under operation |
| `Apparatus/ModeB.lean` | `IsModeBOp` — conditional transit with witness |
| `Apparatus/Factorisation.lean` | `Factorisable` — explicit computational witness |
| `Apparatus/Separability.lean` | `HasSeparabilityStructure` — domain structure typeclass |
| `Apparatus/InterMorphism.lean` | `InterApparatusMorphism` — cross-setoid maps |
| `Apparatus/Composition.lean` | Composition laws, identity morphisms |
| `Apparatus/Instances.lean` | Concrete instances (IsComputableReal, instRefOpPSet, ...) |
| `Apparatus/Numbers.lean` | Hybrid lens analysis (ℝ, ℕ) |
| `Apparatus/FormsIntegration.lean` | VR-Forms transit as Mode B |

---

## Build environment

| Component | Version |
|-----------|---------|
| Lean | 4.29.1 |
| mathlib4 | v4.29.1 |
| Lake | bundled with Lean 4.29.1 |

Install Lean via [elan](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Build from scratch:

```bash
git clone https://github.com/inventor1975/VRCycle.git
cd VRCycle
lake build
```

The first build downloads the mathlib4 cache (~1 GB). Subsequent builds are incremental.

**Expected output**: `Build completed successfully (3319 jobs).` with one expected warning (E04 skeleton uses `sorry`).

To build a specific subsystem:

```bash
lake build VRCycle.Apparatus        # VR-Apparatus only
lake build VRCycle.Audit.HahnBanach # Main audit theorem only
lake build VRCycle.Examples.E01_ComputableReals  # Single tutorial example
```

---

## Code conventions

### Module headers

Every implementation file begins with a structured comment block:

```lean
-- VR-SubSystem: SubModule.lean (DOI ... — version)
-- Brief description.
--
-- ## Position statement
-- What this file does and does not do.
--
-- ## Key findings (if any)
-- Label format: S<stage>-<letter> (e.g., S2-A, S4-B).
--
-- ## Lean content
-- List of public objects with types.
--
-- ## Axiom profile
-- Expected #print axioms result for each public object.
```

### Per-theorem documentation

Every public theorem or definition has a `/-- ... -/` doc-comment including:
- What the object is (one sentence)
- Proof idea or construction
- Axiom profile annotation: `## Axiom profile: [propext, Quot.sound]`

### Axiom profile discipline

Every public object must have a documented axiom profile. After writing a new theorem, run:

```lean
#print axioms myNewTheorem
```

The profile must match one of the four established tiers:

| Tier | Profile | Description |
|------|---------|-------------|
| 1 | `[]` | Axiom-free (pure structural) |
| 2 | `[Quot.sound]` | Quotient machinery only (IAM lift tier) |
| 3 | `[propext, Quot.sound]` | Quotient + proposition extensionality |
| 4 | `[propext, Classical.choice, Quot.sound]` | Standard ceiling (analysis) |

Ceiling `[propext, Classical.choice, Quot.sound]` is **accepted** for objects touching `ℝ`, `Cauchy`, mathlib Hilbert spaces, or ZFA coinductive infrastructure. No axioms beyond this ceiling are permitted.

**Note on common classical triggers** (from project experience):
- `linarith` → pulls `Classical.choice`. Use `omega` or `ring` instead when possible.
- `ring` on ℕ → `[propext]`. Acceptable.
- `omega` on ℕ naturals → `[]`. Preferred.
- `Classical.choice` enters through `ℝ` or `ℚ` type elaboration, not just explicit `Classical.choice` calls.

### Namespace conventions

| Subsystem | Namespace |
|-----------|-----------|
| VR. A Formal System | `VR` |
| VR-Numbers | `VR.Numbers` |
| VR-Sets | `VR.Sets` |
| VR-Forms | `VR.Forms` |
| VR-Audit | `VR.Audit` |
| VR-Sets-ZFA | `VR.SetsZFA` |
| VR-Apparatus | `VR.Apparatus` |
| Examples | `VRCycle.Examples.E0N` |

### No sorry policy

**No `sorry` or `admit` in any implementation file** (under `VRCycle/Apparatus/`, `VRCycle/Audit/`, etc.). The only permitted `sorry` is in the tutorial skeleton `VRCycle/Examples/E04_ModeBSkeleton.lean`, which is explicitly a template.

---

## Apparatus usage patterns

### PredicateOperationality vs ReferenceOperationality

Use the **identity nature criterion**:

| Identity nature | Class | When to use |
|----------------|-------|-------------|
| `AsPoint` | `PredicateOperationality` | Objects identified by value in a classical type (e.g., real numbers, formal terms). Predicate P : T → Prop selects the operational sub-collection. |
| `AsReference` | `ReferenceOperationality` | Objects identified by position in a membership graph. Pre-set type Q with setoid gives the quotient (e.g., ZFSet, OSetZFA). |

**Test**: does your type have a natural membership relation (`∈`)? If yes → `ReferenceOperationality`. If no → `PredicateOperationality`.

### Mode A vs Mode B

| Mode | Class | When to use |
|------|-------|-------------|
| **Mode A** | `IsModeAOp` | The operation ALWAYS stays within the operational register: `∀ x, P x → P (f x)`. Closure is unconditional. Proof is typically trivial (one-liner). |
| **Mode B** | `IsModeBOp` | The operation produces an operational result ONLY FOR enriched operands: `∀ x, PA x → W x → PB (f x)`. The witness W encodes the enrichment. |

**Rule of thumb**: if you can prove `P (f x)` from `P x` alone → Mode A. If you need an additional witness (domain structure, computability condition, positivity bound) → Mode B.

### InterApparatusMorphism

Use `InterApparatusMorphism` when mapping **between two different setoids** (cross-apparatus maps):
- `f : Q1 → Q2` where `Q1` has setoid `s1` and `Q2` has setoid `s2`
- Condition: `a ≈₁ b → f a ≈₂ f b`
- Lifts to `Quotient s1 → Quotient s2` via `hf.lift` (uses only `[Quot.sound]`)

Do NOT use IAM for same-setoid endomorphisms — use Reference Mode A (`ReferenceOperationality.IsModeAOp`) instead.

**Reference**: VR-Apparatus preprint §V (DOI 10.5281/zenodo.20381417).

---

## How to add new content

### New apparatus instance

1. Define the carrier type `T` (or find an existing mathlib type).
2. Define the operational predicate `P : T → Prop` or setoid.
3. Declare the typeclass instance:
   ```lean
   instance instMyApparatus : PredicateOperationality T myPredicate := ⟨⟩
   ```
4. Document identity nature (AsPoint for predicate-wrapping, AsReference for reference).
5. Add `#print axioms instMyApparatus` to the axiom audit section.
6. Open a PR or extend the appropriate `*Instances.lean` file.

### New Mode A theorem

1. Identify the operation `f : T → T` and predicate `P`.
2. State the theorem: `@PredicateOperationality.IsModeAOp T P f`
3. Prove: `fun x hx => ...` (typically one-liner from an existing library theorem).
4. Audit: `#print axioms myModeA_theorem`.
5. Optionally: use `modeA_liftFn` to lift to the operational subtype.

**Pattern** (from `isComputableReal_neg_isModeA`):
```lean
theorem myOp_isModeA :
    PredicateOperationality.IsModeAOp (P := myPredicate) myOp :=
  fun _ hx => libraryTheorem_preserving hx
```

### New Mode B theorem

1. Identify: `PA` (source predicate), `PB` (target predicate), `W` (witness), `f` (operation).
2. Choose witness level (from weakest to richest):
   - `W = fun _ => True` — no extra condition (trivial witness, like VR-Forms transit).
   - `W = PA` — operand must satisfy the source predicate (degenerate Mode A).
   - `W = HasSeparabilityStructure` — domain structure (Hilbert space analysis).
   - `W = Factorisable PA PB f` — explicit computable function matching `f` at the operand.
3. Prove: `IsModeBOp PA PB W f`
4. Optionally: use `IsModeBOp.lift` to get typed outputs.
5. Optionally: use `Factorisable` + `operand_determines_operational` for the explicit witness approach.

**See**: `VRCycle/Examples/E04_ModeBSkeleton.lean` for the skeleton template.

**See**: `VRCycle/Apparatus/ModeB.lean` (`riesz_extension_isModeBOp`) for a complete instance.

### New operational audit (VR-Audit pattern)

An operational audit applies the apparatus framework to a classical mathematical theorem:

1. **Identify the operands**: which classical objects need operational enrichment? (e.g., a Hilbert space, a functional, a subspace)
2. **Define operational predicates/typeclasses**: wrap each operand type with `PredicateOperationality` or `ReferenceOperationality`.
3. **State the operational version**: the classical theorem, restricted to operational operands, yields operational output.
4. **Prove as Mode B**: the classical proof provides the operation; the operational witnesses come from the typeclass instances.
5. **Prove non-vacuity**: exhibit at least one concrete instance satisfying all typeclasses.

**Pattern** (from VR-Audit-1, Hahn-Banach):
```
Classical: ∃ bounded extension f̃ of f.
Operational: [OperationalHilbertSpace E] → [operational f] → operational f̃
Proof structure: Mode B with W = [HasSeparabilityStructure E].
```

---

## Development workflow

VRCycle was developed using the **Variant A** pattern:

1. **Plan first, code second**: each stage has a written plan submitted for architectural review before any Lean code is written. This prevents scope creep and catches structural errors early.
2. **Reconnaissance before new stages**: read existing files before writing new ones. Check for name collisions, existing definitions, and setoid instance availability.
3. **Axiom audit after each public object**: run `#print axioms` immediately after defining each public object. Don't wait until the end of a file.
4. **Word-first documentation**: write the mathematical content of a doc-comment before writing the Lean proof. The comment is the specification; the proof implements it.

For contributors: this discipline is recommended but not required. The key invariants are:
- No `sorry` in implementation files.
- Every public object has a documented axiom profile.
- `lake build` must be clean before any commit.

---

## Twelve apparatus findings (reference)

The VR-Apparatus preprint (DOI 10.5281/zenodo.20381417) catalogues twelve structural findings discovered during formalisation. The most important for contributors:

| Finding | Description | Relevance |
|---------|-------------|-----------|
| S3-A | Two parallel tracks (predicate, reference) — no cross-track composition | Don't try to compose predicate Mode A with IAM directly |
| S4-B | Operand-not-operation principle | Operationality of the result is determined by the operand, not the operation |
| S1-A | VR-Forms transit IS Mode B | `translate_implies_realisable` instantiates `IsModeBOp` with trivial witness |
| S2-B | `[Quot.sound]` tier | IAM lift uses only quotient soundness — keep this when possible |
| S5-A | Lens applicability depends on natural structure | Don't force `ReferenceOperationality` on types without natural membership |

Full catalog: `VRCycle/Apparatus.lean` module header (inline) and VR-Apparatus preprint Part VI.

---

## Testing

After any change:

```bash
lake build VRCycle           # Full build (all subsystems)
lake build VRCycle.Apparatus # Apparatus subsystem only
lake build VRCycle.Audit     # Audit subsystem only
```

Expected: `Build completed successfully` with no errors. The one expected warning is `VRCycle/Examples/E04_ModeBSkeleton.lean: declaration uses sorry` (intentional skeleton).

For axiom verification, add `#print axioms` at the end of your file and check the output against the four-tier table above.

---

## Downstream use

To import VRCycle into another Lean project, add to your `lakefile.toml`:

```toml
[[require]]
name = "VRCycle"
scope = "inventor1975"
rev = "v1.7-vr-apparatus-1.0.0"  # pin to a specific tag
```

Then in your Lean file:

```lean
import VRCycle.Apparatus           -- VR-Apparatus (apparatus framework)
import VRCycle.Audit.Computable    -- IsComputableReal predicate
import VRCycle.Audit.HahnBanach    -- Main operational Hahn-Banach theorem
import VRCycle.SetsZFA             -- OSetZFA, AFA theorem
```

See `VRCycle/Examples/` for usage patterns.
