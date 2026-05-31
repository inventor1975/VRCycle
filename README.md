# VRCycle — Lean 4 Formalisation of the VR Cycle

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20324240.svg)](https://doi.org/10.5281/zenodo.20324240)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20352057.svg)](https://doi.org/10.5281/zenodo.20352057)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20354340.svg)](https://doi.org/10.5281/zenodo.20354340)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20355757.svg)](https://doi.org/10.5281/zenodo.20355757)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20363739.svg)](https://doi.org/10.5281/zenodo.20363739)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20364111.svg)](https://doi.org/10.5281/zenodo.20364111)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20368268.svg)](https://doi.org/10.5281/zenodo.20368268)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20369346.svg)](https://doi.org/10.5281/zenodo.20369346)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20380344.svg)](https://doi.org/10.5281/zenodo.20380344)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20381417.svg)](https://doi.org/10.5281/zenodo.20381417)

Formal verification in Lean 4 (v4.29.1) of the **VR Cycle** — a series of works (each with Lean formalisation and companion preprint), formalising arithmetic, numbers, sets, forms, the first VR-Audit application (Hahn-Banach for operational Hilbert spaces), a foundational extension providing non-well-founded sets with AFA proved as a theorem, the methodological apparatus used implicitly throughout, a domain extension demonstrating apparatus generality in algebra, and constructive predicative formal topology with the binary Tychonoff theorem. **Seven published works** (14 Zenodo records, git tags `v1.0-vr` through `v1.7-vr-apparatus-1.0.0`); **eighth work** (Operational Algebra **v1.0.0** — stable release, git tag `v1.12-vr-operational-algebra-v1.0.0`) and **ninth work** (VR-Topology **v1.0.0**, git tag `v1.13-vr-topology-v1.0.0`) in this repository (both pending Zenodo submission); and a **tenth work** (VR-Transit **v1.0.0**, transit conservativity and a bounded witness library, git tag `v1.15-vr-transit-v1.0.0`, code cited by git tag, no Zenodo by curatorial decision). Algebra: 64 public objects, Findings A0–A19, closed Recognition Discipline Loop. Topology: ~85+ public objects, binary Tychonoff, zero `Classical.choice` including Order.Frame bridge.

## Publications

Fourteen Zenodo records (seven works × Lean + preprint). Two further works (Operational Algebra v1.0.0, VR-Topology v1.0.0) are in this repository under the git tags below, pending Zenodo submission. All Lean formalisations are in this repository under the listed git tags.

| # | Work | Zenodo DOI | Git tag |
|---|------|-----------|---------|
| 1 | VR. A Formal System (preprint) | [10.5281/zenodo.20324391](https://doi.org/10.5281/zenodo.20324391) | — |
| 2 | VR. A Formal System (Lean) | [10.5281/zenodo.20324240](https://doi.org/10.5281/zenodo.20324240) | `v1.0-vr` |
| 3 | VR-Numbers v1.0.2 (preprint) | [10.5281/zenodo.20352239](https://doi.org/10.5281/zenodo.20352239) | — |
| 4 | VR-Numbers (Lean) | [10.5281/zenodo.20352057](https://doi.org/10.5281/zenodo.20352057) | `v1.1-vr-numbers` |
| 5 | VR-Sets v1.0.1 (preprint) | [10.5281/zenodo.20354628](https://doi.org/10.5281/zenodo.20354628) | — |
| 6 | VR-Sets (Lean) | [10.5281/zenodo.20354340](https://doi.org/10.5281/zenodo.20354340) | `v1.2-vr-sets` |
| 7 | VR-Forms v1.0.1 (preprint) | [10.5281/zenodo.20355939](https://doi.org/10.5281/zenodo.20355939) | — |
| 8 | VR-Forms (Lean) | [10.5281/zenodo.20355757](https://doi.org/10.5281/zenodo.20355757) | `v1.3-vr-forms` |
| 9 | VR-Audit v1.0.0 (preprint) | [10.5281/zenodo.20364111](https://doi.org/10.5281/zenodo.20364111) | — |
| 10 | VR-Audit (Lean) | [10.5281/zenodo.20363739](https://doi.org/10.5281/zenodo.20363739) | `v1.4-vr-audit-hb-hilbert` |
| 11 | **VR-Sets-ZFA (preprint)** | [**10.5281/zenodo.20369346**](https://doi.org/10.5281/zenodo.20369346) | — |
| 12 | **VR-Sets-ZFA (Lean)** | [**10.5281/zenodo.20368268**](https://doi.org/10.5281/zenodo.20368268) | **`v1.5-vr-sets-zfa`** |
| 13 | **VR-Apparatus v1.0.0 (Lean)** | [**10.5281/zenodo.20380344**](https://doi.org/10.5281/zenodo.20380344) | **`v1.7-vr-apparatus-1.0.0`** |
| 14 | **VR-Apparatus v1.0.0 (preprint)** | [**10.5281/zenodo.20381417**](https://doi.org/10.5281/zenodo.20381417) | — |
| 15 | **VR-Topology v1.0.0 (Lean)** | — *(Zenodo pending)* | **`v1.13-vr-topology-v1.0.0`** |
| 16 | **VR-Transit v1.0.0 (Lean)** | — *(no Zenodo; cited by git tag, curatorial decision)* | **`v1.15-vr-transit-v1.0.0`** |

Preprint PDFs are in [`preprints/`](preprints/).

---

## Getting started

### Audience guidance

| Background | Recommended entry point |
|-----------|------------------------|
| **Mathematician** | Companion preprints on [Zenodo](https://zenodo.org/communities/vr-cycle) — each work has a self-contained PDF. Start with *VR. A Formal System*, then follow the numbered works in the table above. |
| **Philosopher** | *VR. A Formal System* preprint (DOI [10.5281/zenodo.20324391](https://doi.org/10.5281/zenodo.20324391)) for the foundational ontological claims; *VR-Forms* preprint (DOI [10.5281/zenodo.20355939](https://doi.org/10.5281/zenodo.20355939)) for the two-register apparatus. |
| **Lean developer** | `VRCycle/Examples/` (four annotated tutorial files) + [`CONTRIBUTING.md`](CONTRIBUTING.md) for code conventions and apparatus patterns. |

### Build the project

Requires [elan](https://github.com/leanprover/elan):

```bash
git clone https://github.com/inventor1975/VRCycle.git
cd VRCycle
lake build
```

First build downloads the mathlib4 cache (~1 GB). Expected output: `Build completed successfully (3361 jobs).` with one expected warning (E04 skeleton uses `sorry`).

### Tutorial examples (Lean developers)

Four annotated examples in `VRCycle/Examples/`:

| File | What it demonstrates |
|------|---------------------|
| `E01_ComputableReals.lean` | `IsComputableReal` — predicate-wrapping on ℝ; operational subtype; Mode A closure |
| `E02_ModeA.lean` | Mode A recognition and lifting; custom predicate `IsEven`; axiom minimisation |
| `E03_InterMorphism.lean` | `InterApparatusMorphism` — cross-setoid maps; parity quotient; `[Quot.sound]` tier |
| `E04_ModeBSkeleton.lean` | Mode B structure; trivial and non-trivial witnesses; `Factorisable` pattern |

Build a single example:

```bash
lake build VRCycle.Examples.E01_ComputableReals
```

### Use VRCycle as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "VRCycle"
scope = "inventor1975"
rev = "v1.7-vr-apparatus-1.0.0"
```

Then import the subsystem you need:

```lean
import VRCycle.Apparatus           -- apparatus framework (all of Apparatus/)
import VRCycle.Audit.Computable    -- IsComputableReal predicate
import VRCycle.Audit.HahnBanach    -- operational Hahn-Banach theorem
import VRCycle.SetsZFA             -- OSetZFA, AFA as theorem
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for code conventions, axiom profile discipline, and how to add new apparatus instances.

---

## What is formalised

### VR. A Formal System (`VRCycle/VR.lean`)

A complete Lean 4 formalisation of **VR. A Formal System**, Parts I–II. All 51 theorems and definitions depend on no axioms (see [Axiom audit](#axiom-audit) below).

#### Primitives and axioms (§1–§2)

- `VRObj` — inductive type generated by `base` (∅) and `succ` (t)
- `VRBool`, `impl` — boolean layer {F, ⊤} with classical implication
- `A1_1`, `A1_2`, `A1_F_reaches_both`, `A1_T_reaches_only_T` — generativity (A1)
- `A2_FF/FT/TF/TT` — implication truth table (A2)
- `mem`, `subset`, `A3_mem_self`, `A3_subset_succ` — succession axiom (A3)
- `A4_induction`, `A4_exhaustion` — induction axiom (A4)

#### Derived operators and Leibnizian identity (§3–§5)

- `vnot`, `vor`, `vand`, `viff`, `T_def` — derived from → and ∅ (Def. 1)
- `vrEq`, `vrNe`, `Eq_to_vrEq` — Leibnizian equality and distinctness (Def. 2–3)
- `not_mem_self`, `succ_ne_self` — acyclicity of ∈ (§5 lemma)

#### Von Neumann ordinals (§4, §6)

- `O : Nat → VRObj` — naming function O₀, O₁, O₂, …
- `O_one`, `O_two`, `O_three` — concrete values
- `O_mem_lt` — O_k ∈ O_n for all k < n

#### Arithmetic (§7)

- `vadd`, `vmul`, `vpow` — addition, multiplication, exponentiation on VRObj
- `vadd_zero_left`, `vadd_succ_left` — auxiliary lemmas for T1
- `T1_vadd_comm` — commutativity of addition
- `T2_vadd_assoc` — associativity of addition
- `T3_vmul_distrib` — distributivity
- `T4_one_plus_one` — O₁ + O₁ = O₂

#### Peano correspondence (§9–§10)

- `O_zero`, `O_succ` — 0 ↦ O₀, S ↦ t (§9)
- P1, P2 absorbed by Lean's type system (see note in source)
- `P3_succ_ne_zero` — t(O_n) ≠ O₀
- `P4_succ_inj_leibniz` — injectivity of t in vrEq (exact preprint form)
- `P4_succ_inj` — injectivity of t in Lean Eq (used in Theorem 11)
- `P5_induction` — induction principle = A4

#### Equivalence theorem (§11)

- `O_inv : VRObj → Nat` — Gödel encoding (§10)
- `O_left_inv`, `O_right_inv` — bijection
- `O_add`, `O_mul`, `O_pow` — operation-preserving bridge lemmas
- `VR_PA_iso`, `Theorem_11_VR_PA` — structural isomorphism Nat ≃ VRObj

---

### VR-Numbers (`VRCycle/Numbers/`)

A complete Lean 4 formalisation of **VR-Numbers**, Parts II–V. Operational superstructures ℤ, ℚ, ℝ, ℂ over VR natural numbers, each as a quotient type (except ℂ_VR) with a proved isomorphism to the corresponding Lean/Mathlib type.

#### ℤ_VR — integers (`Numbers/Integers.lean`, §II)

- `IntExpr` — raw signed pairs over ℕ_VR
- `intEq` — equivalence relation (a − b = c − d)
- `ℤ_VR` — quotient type `IntExpr / intEq`
- `intAdd`, `intMul`, `intNeg`, `intSub` — lifted operations
- `IntVRIntIso` — isomorphism structure (forward, backward, right_inv, left_inv, preserveZero, preserveOne, preserveAdd, preserveMul, preserveNeg)
- `Theorem_II_6_IntVR_Int : IntVRIntIso` — ℤ_VR ≅ Int

#### ℚ_VR — rationals (`Numbers/Rationals.lean`, §III)

- `NonZeroRatExpr` — formal fractions over ℤ_VR with nonzero denominator
- `ratEq` — equivalence relation (cross-multiplication)
- `ℚ_VR` — quotient type `NonZeroRatExpr / ratEq`
- `ratAdd`, `ratMul`, `ratSub`, `ratDiv` — lifted operations
- `RatVRRatIso` — isomorphism structure (9 fields including preserveDiv)
- `Theorem_III_6_RatVR_Rat : RatVRRatIso` — ℚ_VR ≅ Rat
- `Theorem_III_4_CanonicalForm` — every ℚ_VR element equals `backwardQ (forwardQ q)`

#### ℝ_VR — reals (`Numbers/Reals.lean`, §IV)

- `FundSeqVR` — fundamental (Cauchy) sequences of ℚ_VR
- `cauchyEqVR` — equivalence relation (sequences with limit-zero difference)
- `ℝ_VR` — quotient type `FundSeqVR / cauchyEqVR`
- `realAdd`, `realMul`, `realSub`, `realDiv` — operations (realDiv noncomputable)
- `forwardR : ℝ_VR → ℝ`, `backwardR : ℝ → ℝ_VR` — bijection maps
- `RealVRRealIso` — isomorphism structure (9 fields including preserveDiv)
- `Theorem_IV_7_RealVR_Real : RealVRRealIso` — ℝ_VR ≅ Real

#### ℂ_VR — complex numbers (`Numbers/Complex.lean`, §V)

- `ComplexVR` — direct structure `{ fst snd : ℝ_VR }` (no quotient; §V.5 trivial equivalence)
- Two-dimensionality motivated by the duality of axiom A1 (§V.1–§V.2): the real axis corresponds to `A1_F_reaches_both` (F→F), the imaginary axis to `A1_T_reaches_only_T` (F→⊤). The joining rule `i² = −1` is a separate postulate encoded in `cmul` (§V.3).
- `czero`, `cone`, `embedR` — zero, one, real embedding
- `cadd`, `cmul`, `cconj`, `csub` — operations
- `cabs : ℂ_VR → ℝ_VR` — modulus via `Real.sqrt ∘ Complex.normSq ∘ forwardC` (noncomputable)
- `cdiv : ℂ_VR → ℂ_VR → ℂ_VR` — division via `backwardC ∘ (/ ) ∘ forwardC` (noncomputable)
- `forwardC : ℂ_VR → ℂ`, `backwardC : ℂ → ℂ_VR` — bijection maps
- `ComplexVRComplexIso` — isomorphism structure (9 fields: forward, backward, right_inv, left_inv, preserveZero, preserveOne, preserveAdd, preserveMul, preserveConj)
- `Theorem_V_8_ComplexVR_Complex : ComplexVRComplexIso` — ℂ_VR ≅ ℂ
- `preserveAbs`, `preserveDiv` — standalone preservation theorems

---

### VR-Sets (`VRCycle/Sets/`)

A complete Lean 4 formalisation of **VR-Sets** (DOI 10.5281/zenodo.20303536), Parts II–V,
built on mathlib's `ZFSet = Quotient PSet.setoid`. The formalisation covers
positive theorems (9 ZFC axioms), negative boundary results (ZFA provably absent),
and formulations of open questions — a three-tier result structure new to the VR cycle.

#### Foundation (`Sets/Foundation.lean`, Stages 1–2)

- `OSet := ZFSet` — operational set type; `abbrev` so all mathlib ZFSet operations apply directly
- `osetEmpty : OSet` — the empty set ∅ (Definition 2)
- `notation a " ≡ " b` — operational identity (Definition 4); reduces to Lean `Eq` on OSet
- `Lemma_II_1_Extensionality` — `∀ x, x ∈ a ↔ x ∈ b → a = b` via `ZFSet.ext`
- `Lemma_II_2_UniquenessEmpty` — `∃! a, ∀ x, x ∉ a` via `ZFSet.notMem_empty`
- `operationalDepth : OSet → Ordinal` — von Neumann rank (Definition V.3.5)
- `Lemma_II_3_DepthEmpty` — `rank ∅ = 0`
- `Lemma_II_3_DepthMono` — `b ∈ a → rank b < rank a` (induction instrument)

#### ZF closure theorems (`Sets/ZF.lean`, Stages 3–8)

Each theorem is a wrapper over the corresponding mathlib lemma on ZFSet.

- `osetPair`, `Theorem_III_3_Pairing` — pairing axiom
- `osetUnion`, `Theorem_III_4_Union` — union axiom
- `osetPower`, `Theorem_III_5_Power` — power set axiom
- `omega_OSet`, `Theorem_III_6_Infinity` — infinity axiom
- `osetReplacement`, `Theorem_III_7_Replacement` — replacement as single theorem (not schema)
- `Theorem_III_8_Foundation` — regularity/foundation axiom (added at Stage 9)
- `Theorem_III_9_Choice` — choice axiom via `Classical.choice`

#### Modes (`Sets/Modes.lean`, Stages 9–10)

**Stage 9 — ZFC-mode:**
- `isZFCmode (s : OSet) : Prop := Acc (· ∈ ·) s` — per-element well-foundedness predicate
- `isZFCmode_all` — every OSet element is in ZFC-mode (structural consequence of ZFSet)
- `Theorem_IV_1_ZFCAxioms` — structural collector: all nine ZFC axioms hold on OSet

**Stage 10 — ZFA boundary (total absence):**
- `isZFAmode (_ : PSet) : Prop := True` — ZFA-mode is the maximal universe (conceptual)
- `isZFAmode_all` — every PSet is in ZFA-mode (trivial/definitional)
- `quineAtomSpec : Prop := ∃ p : PSet.{0}, p ∈ p` — Quine atom specification
- `quineAtom_impossible : ¬quineAtomSpec` — **axiom-free proof**: no Quine atom in PSet
- `AFA_Statement` — classical Anti-Foundation Axiom (Aczel 1988), full generality
- `AFA_Refuted : ¬AFA_Statement` — **axiom-free proof**: AFA is false in mathlib's PSet
  (via universal self-loop graph + `PSet.mem_irrefl`)

The Stage 10 objects are the only **axiom-free theorems** in the VR-Sets formalisation — a structural consequence of `PSet` being inductive (not coinductive). The ZFA boundary is type-theoretic, not axiomatic.

#### Conjectures (`Sets/Conjectures.lean`, Stage 11)

Open questions formalised as `def : Prop` — a third Lean status distinct from `theorem` and `axiom`.

- `Conjecture_IV_1_Statement` — ZFC-mode is mutually interpretable with a countable model of ZFC.
  Nine conjuncts (Extensionality, Empty, Foundation, Pairing, Union, Power, Infinity,
  Replacement, Choice) over a countable type `M` embedded in OSet.
  Axioms: `[propext, Quot.sound]` (through OSet reference).
- `Conjecture_IV_2_Statement` — existence of a universe satisfying classical AFA (Aczel 1988).
  Quine atom + Extensionality + full graph-decoration AFA over abstract `(U, mem)`.
  Axioms: `[]` empty (abstract Type/Prop, no mathlib quotient infrastructure).

#### VR numbers bridge (`Sets/VRNumbers.lean`, Stage 12)

- `osetSuccOp (s : OSet) : OSet := insert s s` — von Neumann successor `s ∪ {s}`
- `embedVR : VRObj → OSet.{0}` — `base ↦ ∅`, `succ x ↦ osetSuccOp (embedVR x)`
- `embedVR_zero`, `embedVR_succ` — definitional equations (axiom-free, `rfl`)
- `Theorem_V_1_WellFounded` — all VR numbers in ZFC-mode (via `isZFCmode_all`)
- `embedVR_mem_iff` — `VR.mem x y ↔ embedVR x ∈ embedVR y` (membership preservation)
- `embedVR_injective` — `Function.Injective embedVR`
- `VR_OSet_iso` — isomorphism structure (5 fields: embed, preserve_zero, preserve_succ, preserve_mem, injective)
- `Theorem_V_2 : VR_OSet_iso` — the explicit instance

---

### VR-Forms (`VRCycle/Forms/`)

A partial Lean 4 formalisation of **VR-Forms** (DOI 10.5281/zenodo.20313735), Parts II, IV–V, and VII.
VR-Forms is proof-theoretic: it introduces a two-register system (formal register L₁ / operational register L₀),
formal terms, operational realisability, and the transit pattern. The central result (Theorem III.1:
conservativity of T₁ over T₀) is the **explicit structural boundary** of this Lean cycle — documented in code
at every relevant point. See "Central boundary" below and PLAN.md §"Critical boundary statement".

**18 public objects across 5 files (1545 lines). Classical.choice absent throughout the entire cycle.**

#### Language (`Forms/Language.lean`, Stage 1)

- `Register` — inductive type with two constructors: `.formal` (L₁ / formal register) and `.ontological` (L₀ / operational register); derives `DecidableEq, Repr`
- `FormalTerm` — structure `{ description : String; register : Register }`; derives `DecidableEq, Repr`
- `⌜·⌝` macro (ident form) — `⌜foo⌝ = FormalTerm.mk "foo" .formal`
- `⌜·⌝` macro (str form) — `⌜"foo"⌝ = FormalTerm.mk "foo" .formal`
- Axioms: **`[]` (axiom-free)** — no imports, pure structure

#### Realisability (`Forms/Realisability.lean`, Stage 2 + Stage 4 retroactive extension)

`isRealisable : FormalTerm → Prop` — total predicate; match on `description` over 6 named cases plus catch-all `| _ => False`. Three-category structure:

| Category | Formal terms | Lean status |
|----------|-------------|-------------|
| Provably realisable | `⌜"∅"⌝`, `⌜"omega_OSet"⌝`, `⌜"osetPair"⌝` | Witnessed by VR-Sets objects |
| Open realisability | `⌜"Conjecture_IV_1_Statement"⌝`, `⌜"Conjecture_IV_2_Statement"⌝` | Reduces to open conjecture |
| Provably non-realisable | `⌜"AFA_Statement"⌝` | Proved false via `AFA_Refuted` |

- `isRealisable_empty : isRealisable ⌜"∅"⌝` — ∅ is operationally realisable (witness: `osetEmpty`)
- `isRealisable_omega : isRealisable ⌜"omega_OSet"⌝` — ω is operationally realisable (witness: `omega_OSet`)
- `isRealisable_osetPair : isRealisable ⌜"osetPair"⌝` — formal pairing term is operationally realisable
- Axioms: `[propext, Quot.sound]`

#### Transit pattern (`Forms/Transit.lean`, Stage 3)

- `translate_pi : FormalTerm → Prop` — π translation; maps named formal terms to their defining operational predicates; catch-all `| _ => False`
- `translate_pi_empty`, `translate_pi_omega`, `translate_pi_osetPair` — concrete translations of three operationally realisable terms
- `translate_implies_realisable` — `∀ t, translate_pi t → isRealisable t` (translation implies realisability)
- Large doc-block: the transit pattern as a documented inference pattern (not a theorem); references Theorem III.1 (conservativity) as structural boundary; quotes the preprint verbatim
- Axioms: `[propext, Quot.sound]`

#### Bridge (`Forms/Bridge.lean`, Stage 4)

Bridge theorems connect formal terms in the formal register to concrete VR-Sets Lean objects. This is the junction point between the VR-Sets Lean cycle (Stages 1–13) and VR-Forms.

- `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝` — proved via `AFA_Refuted` (VR-Sets Stage 10); the ZFA boundary of VR-Sets reappears as a realisability theorem in VR-Forms
- `bridge_Conjecture_IV_1 : isRealisable ⌜"Conjecture_IV_1_Statement"⌝ ↔ Conjecture_IV_1_Statement` — iff trivially proved by `⟨id, id⟩`; mathematical content open (VR-Sets Stage 11)
- `bridge_Conjecture_IV_2 : isRealisable ⌜"Conjecture_IV_2_Statement"⌝ ↔ Conjecture_IV_2_Statement` — iff trivially proved by `⟨id, id⟩`; mathematical content open (VR-Sets Stage 11)
- Axioms: `[propext, Quot.sound]`

#### Examples (`Forms/Examples.lean`, Stage 5)

- `not_isRealisable_Russell` — Russell class formal term is not operationally realisable
- `not_isRealisable_Vitali` — Vitali set formal term is not operationally realisable
- `not_isRealisable_classical_R` — classical reals formal term is not operationally realisable
- `not_isRealisable_classical_powerset_N` — classical power set of ℕ is not operationally realisable (formal-register half only; ontological side «℘_VR(ω) is countable» is metatheoretic — documented in comment, not formalised; see VR-Numbers §VIII.6 boundary)
- `mixed_omega_two_register : (∅ : OSet) ∈ omega_OSet ∧ isRealisable ⌜"omega_OSet"⌝` — mixed formula: operational fact + formal-register fact in one statement (Part VII §VII.2)
- `mixed_AFA_boundary : (∀ x : OSet, x ∉ x) ∧ ¬isRealisable ⌜"AFA_Statement"⌝` — **central junction theorem** of the cycle: ZFA boundary in both registers simultaneously; `ZFSet.mem_irrefl` (operational) + `bridge_AFA` (formal)
- Axioms: `[propext, Quot.sound]`

#### Central boundary

**Theorem III.1 (conservativity of T₁ over T₀)** — the core result of VR-Forms — is **not formalised** in this Lean cycle. Full formalisation would require deep-embedding `Formula L₁`, `Derivation T₁`, and proving conservativity by induction over derivations — a proof-theory project beyond the scale of the VR-Forms preprint cycle.

This boundary is structurally different from VR-Sets's five structural boundaries:

| Cycle | Boundary type | Nature |
|-------|--------------|--------|
| VR-Sets | Five boundaries | Gaps in mathlib's set-theoretic infrastructure |
| VR-Forms | One central boundary | Shallow-embedding vs. deep-embedding (proof-theoretic) |

The boundary is documented at every relevant Lean object with explicit comments. The conservativity result is **not an open question** (it has a metalogical proof in the preprint); it is unformalisable *at this depth* in shallow Lean — distinct from the open Conjectures IV.1/IV.2 in VR-Sets, which are mathematically open questions.

---

### VR-Audit: Hahn-Banach for Operational Hilbert Spaces (`VRCycle/Audit/`)

**Lean: [10.5281/zenodo.20363739](https://doi.org/10.5281/zenodo.20363739) — git tag `v1.4-vr-audit-hb-hilbert`**  
**Preprint v1.0.0: [10.5281/zenodo.20364111](https://doi.org/10.5281/zenodo.20364111)**

The fifth and latest work in the VR Cycle. VR-Audit is **structurally different** from
predecessor cycles: it is *applied* rather than foundational — using both mathlib and
predecessor VR cycles as black-box dependencies, contributing computability predicates
and transit theorems on top of existing classical mathematics.

#### Position in the VR Cycle

| # | Cycle | Tag | Nature |
|---|-------|-----|--------|
| 1 | VR. A Formal System | v1.0-vr | Foundational (primitives, arithmetic) |
| 2 | VR-Numbers | v1.1-vr-numbers | Foundational (ℤ, ℚ, ℝ, ℂ over VR-ℕ) |
| 3 | VR-Sets | v1.2-vr-sets | Foundational (ZFC, ZFA boundary) |
| 4 | VR-Forms | v1.3-vr-forms | Foundational (two-register apparatus) |
| 5 | **VR-Audit** | **v1.4-vr-audit-hb-hilbert** | **Applied (first VR-Audit application)** |

#### Core architectural principle: wrapping

VR-Audit does **not** redefine classical mathematics. It **wraps** existing mathlib
types and theorems with computability predicates — the direct embodiment of the
VR-Forms two-register apparatus in Lean:

- **Formal register** = mathlib's full classical types (unrestricted).
- **Operational register** = the sub-collection satisfying computability predicates,
  with explicit constructive witnesses in proof terms.

The **transit pattern**: given operational input (witnesses), apply a classical mathlib
theorem, prove that output also satisfies operationality (witness derived from inputs).

#### Main theorem

```lean
theorem HahnBanachOperational_Hilbert
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [OperationalHilbertSpace E]
    (M : OperationalLocatedSubspace E)
    (f : OperationalNormableFunctional M.toSubmodule) :
    ∃ (x₀ : E),
      (∀ m : ℕ, IsComputableReal
        (inner (OperationalHilbertSpace.denseSeq (E := E) m) x₀))  ∧
      (∀ y ∈ (M.toSubmodule : Set E),
        f.toFun y = inner y x₀)  ∧
      ‖x₀‖ = f.fnNorm
```

For any operational Hilbert space and any operational normable functional on an
operational located subspace, the Riesz representation vector is operationally
accessible. Classical Hahn-Banach follows; the transit via Riesz avoids the
Specker obstruction.

#### File structure (`VRCycle/Audit/`)

| Stage | File | Public objects | Description |
|-------|------|---------------|-------------|
| 1 | `Computable.lean` | 8 | `IsComputableReal`, `IsComputableSequence`, base lemmas |
| 2 | `Hilbert.lean` | 2 | `OperationalHilbertSpace` typeclass; ℝ instance |
| 3 | `Subspace.lean` | 2 | `OperationalLocatedSubspace` structure; ⊤ instance |
| 4 | `Functional.lean` | 3 | `OperationalNormableFunctional` structure; zero instance |
| 5 | `HahnBanach.lean` | 1 | Main theorem `HahnBanachOperational_Hilbert` |
| 6 | `Example.lean` | 1 | `instOperationalHilbertSpaceEuclidean` (ℝⁿ for all n) |

**Total: 17 public objects, ~1427 lines of Lean.**

#### Axiom profile

All 17 public objects:

```
'VR.Audit.IsComputableReal'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableSequence'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_rat'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_zero'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_one'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_neg'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_add'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.IsComputableReal_sub'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.OperationalHilbertSpace'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.instOperationalHilbertSpaceReal'         depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.OperationalLocatedSubspace'              depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.topOperationalLocatedSubspace'           depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.OperationalNormableFunctional'           depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.fn_computable_everywhere'                depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.zeroOperationalNormableFunctional'       depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.HahnBanachOperational_Hilbert'           depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Audit.instOperationalHilbertSpaceEuclidean'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Classical.choice` is **expected and accepted** throughout: mathlib's Hahn-Banach uses
Zorn's lemma (equivalent to `Classical.choice`). The methodological point is not
axiom minimisation but **preservation of operationality**: operational witnesses for
outputs are constructed from input witnesses, even when classical machinery uses
`Classical.choice` between.

#### Key methodological observations

1. **Wrapping principle confirmed**: `IsComputableReal` over mathlib's `Real`, no parallel `OperationalReal` type.
2. **Riesz as transit enabler**: Hilbert + Riesz gives clean transit; general Banach does not (Riesz gives an explicit vector, not a supremum).
3. **Locatedness as operational closedness**: `OperationalLocatedSubspace` replaces classical closedness with computable `infDist`.
4. **Specker boundary avoided by structure**: projection gives an explicit vector x₀, not a bounded monotone limit.
5. **Two-register apparatus in practice**: formal register = mathlib Hilbert spaces (unrestricted); operational register = three-field wrapping typeclass.
6. **Non-vacuity confirmed**: Stage 6 shows `EuclideanSpace ℝ (Fin n)` is an `OperationalHilbertSpace` for every `n : ℕ`, with explicit dense sequence and computable inner products.
7. **`ring` vs `mul_comm` on ℝ inner products**: `@inner ℝ ℝ _ x y = y * x` definitionally (reversed order); `ring` treats `⟪·,·⟫` as opaque; `exact mul_comm _ _` is the correct tactic.

#### Acknowledgement

Developed using **Claude Opus 4.7** (architectural review) and **Claude Sonnet 4.6**
(Lean implementation), Variant A (interactive parent-child architecture), consistent
with predecessor VR Lean cycles.

---

---

### VR-Sets-ZFA (`VRCycle/SetsZFA/`)

**Lean: [10.5281/zenodo.20368268](https://doi.org/10.5281/zenodo.20368268) — git tag `v1.5-vr-sets-zfa`**  
**Preprint v1.0.0: [10.5281/zenodo.20369346](https://doi.org/10.5281/zenodo.20369346)**

The sixth work in the VR Cycle. VR-Sets-ZFA is a **foundational extension** of VR-Sets
that provides operational reference semantics for non-well-founded sets, with Aczel's
Anti-Foundation Axiom (AFA) proved as a theorem, not postulated. This answers
`Conjecture_IV_2_Statement` from VR-Sets `Conjectures.lean` constructively.

#### Position in the VR Cycle

| # | Cycle | Tag | Nature |
|---|-------|-----|--------|
| 1 | VR. A Formal System | v1.0-vr | Foundational (primitives, arithmetic) |
| 2 | VR-Numbers | v1.1-vr-numbers | Foundational (ℤ, ℚ, ℝ, ℂ over VR-ℕ) |
| 3 | VR-Sets | v1.2-vr-sets | Foundational (ZFC, ZFA boundary) |
| 4 | VR-Forms | v1.3-vr-forms | Foundational (two-register apparatus) |
| 5 | VR-Audit | v1.4-vr-audit-hb-hilbert | Applied (first VR-Audit application) |
| **6** | **VR-Sets-ZFA** | **v1.5-vr-sets-zfa** | **Foundational (ZFA extension, AFA as theorem)** |

#### Core architectural principle

VR-Sets is a ZFC model (`OSet = ZFSet = Quotient PSet.setoid`, with `PSet` inductive
and `PSet.mem_wf` following from the inductive structure). VR-Sets proved that AFA is
**refuted** in that model (`AFA_Refuted`, axiom-free). VR-Sets-ZFA builds a parallel
universe:

```
PSet (inductive) --[embedPSet]--> CoPSet (coinductive, via PFunctor.M)
      |                                    |
   ZFSet.mk                           OSetZFA.mk
      ↓                                    ↓
   OSet (ZFC) ---[embedOSet]--------> OSetZFA (ZFA)
```

`CoPSet` is the coinductive parallel of `PSet`, built via `PFunctor.M`. The quotient
`OSetZFA = Quotient CoPSet.cobisim` (cobisimulation as equality) gives the ZFA universe.
AFA emerges as the universal property of `CoPSet.corec` — the final coalgebra property.

#### Main theorem

```lean
theorem AFA_in_OSetZFA (E : V → V → Prop) :
    ∃! f : V → OSetZFA, isDecoration E f
```

For any relation `E : V → V → Prop` (a graph), there exists a unique decoration
`f : V → OSetZFA` assigning to each vertex the set of images of its successors.
This is Aczel's AFA for the ZFA universe `OSetZFA`, proved — not postulated.

#### File structure (`VRCycle/SetsZFA/`)

| Stage | File | Public objects | Lines | Description |
|-------|------|---------------|-------|-------------|
| 1 | `CoPSet.lean` | 13 | 265 | `CoPSet` coinductive type via `PFunctor.M`; `CoPSet.mk`, `.corec`, `.bisim` |
| 2 | `Cobisimulation.lean` | 7 | 265 | `CoPSet.Equiv` (cobisimulation); setoid properties; `bisim_imp_Equiv` |
| 3 | `OSetZFA.lean` | 11 | 209 | `OSetZFA` quotient type; `mk`, `sound`, `exact`, `eq_iff`, lifting infrastructure |
| 4 | `Membership.lean` | 6 | 217 | `∈` on OSetZFA; `mem_mk`, `ext`, `ext_iff`; `CoPSet.mem_congr` |
| 5 | `AFA.lean` | 8 | 291 | `graphCoalg`, `graphCoPSet`, `graphDecoration`; `AFA_in_OSetZFA` (main theorem) |
| 6 | `Embedding.lean` | 8 | 256 | `embedPSet`, `embedOSet`; faithfulness (`injective`); membership preservation |
| 7 | `Examples.lean` | 10 | 311 | `quineAtom`, `cycleDecoration`, `omegaChain`; non-well-foundedness witnesses |
| 8 | `API.lean` | 7 | 295 | `OSetZFA.empty`, `OSetZFA.singleton`; `acc_irrefl`; `@[simp]` additions |

**Total: 70 public objects, 2109 lines of Lean.**

#### Key theorems

```lean
-- AFA (main theorem)
theorem AFA_in_OSetZFA (E : V → V → Prop) :
    ∃! f : V → OSetZFA, isDecoration E f

-- Quine atom: a set equal to its own singleton
theorem quineAtom_self_mem : quineAtom ∈ quineAtom
theorem quineAtom_eq_singleton_self : quineAtom = OSetZFA.singleton quineAtom

-- OSet embeds faithfully into OSetZFA
theorem embedOSet_injective : Function.Injective embedOSet
theorem embedOSet_mem (x a : ZFSet) : embedOSet x ∈ embedOSet a ↔ x ∈ a

-- ZFA membership is not well-founded
theorem OSetZFA_mem_not_wf : ¬ WellFounded (· ∈ · : OSetZFA → OSetZFA → Prop)

-- Quine atom is not a well-founded set
theorem quineAtom_not_in_range_embedOSet : quineAtom ∉ Set.range embedOSet
```

#### Axiom profile

**8 axiom-free objects** (pure structural/corecursive definitions):

```
'VR.SetsZFA.CoPSetFunctor'    does not depend on any axioms
'VR.SetsZFA.CoPSet'           does not depend on any axioms
'VR.SetsZFA.CoPSet.mk'        does not depend on any axioms
'VR.SetsZFA.CoPSet.corec'     does not depend on any axioms
'VR.SetsZFA.graphCoalg'       does not depend on any axioms
'VR.SetsZFA.graphCoPSet'      does not depend on any axioms
'VR.SetsZFA.embedPSet'        does not depend on any axioms
'VR.SetsZFA.acc_irrefl'       does not depend on any axioms
```

**62 objects at standard ceiling** `[propext, Classical.choice, Quot.sound]`:
all remaining public objects. `Classical.choice` enters through `PFunctor.M.bisim`
(the coinductive bisimulation principle) and the `OSetZFA` quotient machinery.
No additional axioms anywhere in the cycle.

#### Key methodological observations

1. **AFA as theorem via final coalgebra**: `CoPSet.corec` is the universal property
   of the final coalgebra. AFA follows: `graphCoPSet E = CoPSet.corec (graphCoalg E)`
   is the unique decoration, and `graphDecoration E = OSetZFA.mk ∘ graphCoPSet E`
   descends to the quotient.

2. **Coinductive constructor and corecursor are axiom-free**: `CoPSet.mk` and
   `CoPSet.corec` depend on no axioms — the coinductive content is constructive.
   Classical choice enters only through the destructor (`CoPSet.dest`) and the
   bisimulation principle.

3. **Bisimulation collapse (two-cycle ≡ self-loop)**: `cycleDecoration true` and
   `cycleDecoration false` (nodes of a two-cycle graph) are cobisimilar, both equal
   to `quineAtom` (self-loop graph decoration). The two-cycle APG and self-loop APG
   produce the same OSetZFA element — AFA's uniqueness theorem in action.

4. **Forward embedding via coinduction, backward via induction**: `embedPSet_congr`
   (`PSet.Equiv → CoPSet.Equiv`) uses a single bisimulation — no induction on PSet.
   `embedPSet_faithful` (`CoPSet.Equiv → PSet.Equiv`) requires structural induction
   on PSet's well-founded structure. A methodological asymmetry between the
   coinductive and inductive directions.

5. **`acc_irrefl` is axiom-free**: Irreflexivity from `Acc r x` is proved by pure
   structural induction on the `Acc` inductive type — no classical choice needed.

6. **Formal answer to Conjecture_IV_2**: VR-Sets posed the question of whether
   a type satisfying AFA can be constructed; VR-Sets-ZFA answers constructively.
   The answer lives in `OSetZFA`, not as a new axiom but as a theorem.

#### Acknowledgement

Developed using **Claude Opus 4.7** (architectural review) and **Claude Sonnet 4.6**
(Lean implementation), Variant A (interactive parent-child architecture), consistent
with predecessor VR Lean cycles.

---

### VR-Apparatus (`VRCycle/Apparatus/`)

**Lean: [10.5281/zenodo.20380344](https://doi.org/10.5281/zenodo.20380344) — git tag `v1.7-vr-apparatus-1.0.0`**  
**Preprint v1.0.0: [10.5281/zenodo.20381417](https://doi.org/10.5281/zenodo.20381417)**

The seventh work in the VR Cycle. VR-Apparatus is a **meta-work**: it makes explicit and machine-verifies the methodological apparatus used implicitly throughout the six predecessor works.

Two apparatus modes, two transit modes, five architectural tiers, twelve methodological findings.

#### Two apparatus modes

- **Predicate-wrapping** (`PredicateOperationality`): objects identified by classical type membership; predicate `P : T → Prop` selects the operational sub-collection. Identity: `AsPoint`. Example: `IsComputableReal` on `ℝ`.
- **Reference semantics** (`ReferenceOperationality`): objects identified by position in a membership graph; pre-set type `Q` with setoid gives the quotient operational type. Identity: `AsReference`. Example: `OSetZFA` via cobisimulation quotient.

#### Two transit modes

- **Mode A** (`IsModeAOp`): operations preserving the operational predicate lift to the operational subtype by `rfl`. Apparatus-structure-independent.
- **Mode B** (`IsModeBOp`): classical operations with `Factorisable` witness yield operational results. Captures operand-not-operation principle. Riesz extension (VR-Audit Hahn-Banach) is the canonical instance.

#### File structure (`VRCycle/Apparatus/`)

| Stage | File | Public objects | Description |
|-------|------|---------------|-------------|
| v0.1.0 | `Identity.lean` | 2 | `IdentityNature` (AsPoint, AsReference) |
| v0.1.0 | `Wrapping.lean` | 2 | `PredicateOperationality` marker class |
| v0.1.0 | `Reference.lean` | 3 | `ReferenceOperationality` (membership + ext fields); instRefOpCoPSet |
| v0.1.0 | `ModeA.lean` | 11 | `IsModeAOp`, `IsModeAOp₂`, `modeA_liftFn`, compose (both modes) |
| v0.1.0 | `ModeB.lean` | 9 | `IsModeBOp`, lift, compose; Riesz instance |
| v0.1.0 | `Instances.lean` | 5 | neg/sub Mode A, `instRefOpPSet`, embedPSet pattern |
| 4 | `Factorisation.lean` | 8 | `Factorisable`, `operand_determines_operational`, `IsModeBOp_of_factorisable` |
| 6 | `Separability.lean` | 3 | `HasSeparabilityStructure`; Hilbert instance; separability→factorisable |
| 2 | `InterMorphism.lean` | 8 | `InterApparatusMorphism`, lift, lift_mk, compose; ZFC→ZFA embedding |
| 3 | `Composition.lean` | 7 | Identity morphisms; unit laws; interop between morphism levels |
| 5 | `Numbers.lean` | 4 | Hybrid lens analysis: ℝ (Cauchy bridge), ℕ (von Neumann IAM) |
| 1 | `FormsIntegration.lean` | 3 | VR-Forms transit as Mode B; three-way identity nature contrast |

**Total: 68 public objects, ~3430 lines of Lean.**

#### Axiom profile (four tiers)

| Tier | Profile | Count | Representative |
|------|---------|-------|---------------|
| 1 | `[]` (axiom-free) | 40 | `IsModeBOp.lift_val`, `Factorisable`, `nat_vonNeumann_isInterApparatus` |
| 2 | `[Quot.sound]` | 7 | `InterApparatusMorphism.lift_mk`, `IsModeAOp_of_interApparatus` |
| 3 | `[propext, Quot.sound]` | 12 | `instRefOpPSet`, `instPredicateOpFormalTerm`, `vr_forms_transit_isModeBOp` |
| 4 | `[propext, Classical.choice, Quot.sound]` | 9 | `riesz_extension_isModeBOp`, `instHasSepStructOfOpHilbert` |

**New tier discovered**: `[Quot.sound]` — 7 objects using only quotient soundness (IAM lift infrastructure). Sub-ceiling between axiom-free and `[propext, Quot.sound]`.

#### Three honest scope limitations

1. No `ReferenceOperationality` for Cauchy sequences — no natural membership relation on `CauSeq ℚ abs`.
2. No `DirectionalMorphism` typeclass — Mode B already captures VR-Forms transit asymmetry.
3. No generic `Register` structure — Lean's typeclass system provides this implicitly.

#### Key methodological findings

**S3-A**: Two parallel tracks (predicate, reference) with no natural cross-track composition.  
**S4-B**: Operand-not-operation — operationality of the result is determined by the operand, not by the operation itself.  
**S5-A**: Lens applicability depends on natural structure — ℝ+Cauchy artificial (no ∈), ℕ+von Neumann natural.  
**S1-A**: VR-Forms transit IS `IsModeBOp translate_pi isRealisable (fun _ => True) id` — no new abstraction needed; Mode B already captures it.

#### Acknowledgement

Developed using **Claude Opus 4.7** (architectural review) and **Claude Sonnet 4.6**
(Lean implementation), Variant A (interactive parent-child architecture), consistent
with predecessor VR Lean cycles.

---

### Operational Algebra (`VRCycle/Algebra/`)

**Git tags**: `v1.8-vr-operational-algebra-v0.1.0` (additive groups), `v1.9-vr-operational-algebra-v0.2.0` (rings), `v1.10-vr-operational-algebra-v0.3.0` (fields + multiplicative groups), `v1.11-vr-operational-algebra-v0.4.0` (modules + zsmul + A15 investigation), `v1.12-vr-operational-algebra-v1.0.0` (stable release)
**Status**: v1.0.0 — stable release. Pending Zenodo paired publication (companion preprint in preparation).
**Preprint**: in preparation. Zenodo submission deferred for paired publication.

The **eighth work** in the VR Cycle. A domain extension demonstrating that the
VR-Apparatus framework (meta-formalised in VR-Apparatus v1.0.0,
DOI 10.5281/zenodo.20380344) extends naturally to **algebraic structures** —
confirming the framework is general methodology, not analysis-specific.

#### Core contributions

**v0.1.0** — `OperationalAddGroup`: an additive group equipped with a VR operational predicate
`IsOperational : G → Prop` and closure axioms (zero, add, neg). The apparatus
framework (`PredicateOperationality`, Mode A, Mode B) is **reused without
modification** for algebraic instances — this reuse is the main result.

**v0.2.0** — `OperationalRing`: extends `Ring R` with the same operational predicate,
adding closure axioms for `1` and `*`. Instances: ℤ and ZMod n (both trivially operational).
Ring Mode A theorems: `mul_isModeAOp`, `npow_isOperational`. Bridge instance:
`OperationalRing.toOperationalAddGroup`. Substantive Mode B audit completed:
the v0.1.0 intentional sorry in `image_isOperationalAddSubgroup_isModeBOp` is **eliminated**.

**v0.3.0** — Completes the algebraic hierarchy: **groups → rings → fields**.
- `OperationalGroup` (multiplicative): revived from v0.1.0 Finding A0 — justified by field unit groups (Finding A12, recognition discipline reversal).
- `OperationalField`: extends `Field K` with `inv_isOperational`. Bridge `→ OperationalRing`.
- ℚ as `OperationalField` — first instance beyond ℤ and ZMod n.
- `OperationalField.toOperationalGroupUnits`: bridge `[OperationalField K] → OperationalGroup Kˣ` — the concrete justification for `OperationalGroup`'s revival. **Recognition discipline loop CLOSED**.
- Mode A theorems for multiplicative groups: `mul_isModeAOp`, `inv_isModeAOp`, `div_isModeAOp`, `npow_isOperational`, `zpow_isOperational` (ℤ-exponentiation — new vs additive side).

**v0.4.0** — Closes three content gaps and extends to **modules**.
- **`zsmul_isOperational`**: additive ℤ-scalar analogue of `zpow_isOperational`. Completes the additive/multiplicative symmetry table: `nsmul`/`npow` (v0.1.0/v0.3.0) and now `zsmul`/`zpow` (v0.4.0/v0.3.0). Finding A18.
- **Finding A16** (A15 structural investigation): systematic isolation confirms `Classical.choice` in `inv_isModeAOp_field` and `toOperationalGroupUnits` is structurally embedded — one source is the apparatus import chain pulling `Mathlib.Data.Real.Basic`; the other is proof-structural (field-inverse reasoning via `Units.val_inv_eq_inv_val`). Neither is removable by file isolation. The programme remains honest: these two objects are the only non-eliminable `Classical.choice` sources in the algebraic hierarchy.
- **`OperationalModule`**: bridge-based typeclass over `[OperationalRing R] [OperationalAddGroup M] [Module R M]`. Adds one axiom: `smul_isOperational`. Introduces **no new predicate** on M — M's predicate is sourced entirely from `[OperationalAddGroup M]`. Instances: ℤ as ℤ-module, ℚ as ℚ-module.
- **`smul_isModeAOp`**: Mode A theorem for scalar action. First **heterogeneous binary operation** in VR Cycle — `smul : R → M → M` requires `IsModeAOp (r • · : M → M)` (unary, for fixed operational `r`), not `IsModeAOp₂`. Finding A19. Fourth confirmation of apparatus generality (Finding A17).

#### Classical.choice — honest framing (updated v0.4.0 / Finding A16)

Prior cycles: `Classical.choice` absent from all 46 algebraic objects (v0.1.0 + v0.2.0).

v0.3.0 introduced two objects with `Classical.choice` in their elaborated proof terms:
- `inv_isModeAOp_field` (`ModeA.lean`)
- `OperationalField.toOperationalGroupUnits` (`Field.lean`)

v0.4.0 Stage 2 (Finding A16) systematically investigated whether isolation could remove them.
**Conclusion: both sources are structurally embedded and not removable**:

- `inv_isModeAOp_field`: root is the apparatus import chain — `VRCycle.Apparatus.ModeA`
  transitively imports `Mathlib.Data.Real.Basic`, injecting instances that affect `Inv K`
  elaboration in `IsModeAOp` types. `IsModeAOp` cannot be used without the apparatus import;
  file separation is impossible. Confirmed: minimal-import test file still shows `Classical.choice`.
- `OperationalField.toOperationalGroupUnits`: root is proof-structural — any valid proof must
  use `Units.val_inv_eq_inv_val` to connect `(u⁻¹ : Kˣ).val` to `(u.val)⁻¹ (K)`; after this
  rewrite, the goal contains field-level `(·)⁻¹`, which carries `Classical.choice`.
  The type alone (sorry-proof) elaborates `[propext, Quot.sound]` — so it is the proof
  necessity, not the type, that requires classical reasoning.

**Programme position**: the cycle is **logically constructive with two structural
`Classical.choice` exceptions** in field-inverse reasoning. These exceptions reflect genuine
mathematical structure (multiplicative inversion in a field requires classical reasoning
about the zero case), not implementation choices or import noise that could be engineered away.
All 62 other public objects remain at or below `[propext, Quot.sound]`.

#### Recognition discipline applications (seven total across v0.1.0–v0.4.0)

**Removals** (five):
- **Finding A0** (v0.1.0 Stage 1): `OperationalGroup` (multiplicative) removed — no v0.1.0 instances.
- **Finding A6** (v0.1.0 Stage 5): `OperationalAddSubgroup` bundled structure removed — the predicate `IsOperationalAddSubgroup H := ∀ x ∈ H, IsOperational x` suffices.
- **Finding A9** (v0.2.0 Stage 2): `OperationalCommRing` removed — diamond conflict; no new content.
- v0.2.0 Stage 5: `one_isOperational_bridge` omitted — alias with no content.
- v0.2.0 Stage 5: `mul_chain_isOperational` omitted — derivable from `mul_isModeAOp`.

**Introduction** (one — **first documented introduction in cycle**):
- **Finding A12** (v0.3.0 Stage 1, confirmed Stage 5): `OperationalGroup` REVIVED — field unit groups (`Kˣ`) provide the natural multiplicative instance that was absent in v0.1.0. The bridge `OperationalField.toOperationalGroupUnits` is the concrete justification. **Bidirectional recognition discipline**: remove preemptive abstractions; introduce when natural justification arrives.

**Architectural correction** (v0.4.0 Stage 5 — Variant A разделение работ):
- PLAN.md error: proposed `IsModeAOp₂ (· • · : R → M → M)` for `smul_isModeAOp`. Incorrect: `IsModeAOp₂` requires `f : T → T → T` (homogeneous single type). Scalar action `R → M → M` is heterogeneous. Sonnet (implementer) caught this during Stage 5 reconnaissance, before any proof attempt. Correct form: `IsModeAOp (r • · : M → M)` for fixed `r`. The apparatus architecture correctly distinguishes internal from external operations (Finding A19).

#### File structure

| Stage | File | Public objects | Description |
|-------|------|---------------|-------------|
| v0.1.0 §1 | `Algebra/AddGroup.lean` | 1 | `OperationalAddGroup` typeclass |
| v0.1.0 §2,4 | `Algebra/Instances.lean` | 8 | ℤ and ZMod n additive group instances + demos |
| v0.1.0 §3 | `Algebra/ModeA.lean` | 5 | Mode A closure; `instPredOpAddGroup` |
| v0.1.0 §5 | `Algebra/Subgroups.lean` | 8 | `IsOperationalAddSubgroup`; ⊥, ⊤, ⊓ |
| v0.1.0→v0.2.0 §6 | `Algebra/ModeBExample.lean` | 9 | Mode B: negation + image subgroup (substantive, sorry eliminated) |
| v0.2.0 §1-2 | `Algebra/Ring.lean` | 2 | `OperationalRing` + bridge `→ OperationalAddGroup` |
| v0.2.0 §3,4 | `Algebra/Instances.lean` | 10 | ℤ and ZMod n ring instances + demos |
| v0.2.0 §5 | `Algebra/ModeA.lean` | 3 | `mul_isModeAOp`; `npow_isOperational`; `instPredOpRing` |
| v0.3.0 §1 | `Algebra/MulGroup.lean` | 1 | `OperationalGroup` typeclass (multiplicative) |
| v0.3.0 §2,5 | `Algebra/Field.lean` | 3 | `OperationalField`; bridge `→ OperationalRing`; bridge `→ OperationalGroup Kˣ` |
| v0.3.0 §3,5 | `Algebra/Instances.lean` | 5 | ℚ field instance + demos; ℚˣ demos (anonymous) |
| v0.3.0 §4 | `Algebra/ModeA.lean` | 8 | MulGroup Mode A (6 objects) + Field Mode A (2 objects) |
| v0.4.0 §3 | `Algebra/Module.lean` | 1 | `OperationalModule` typeclass (bridge-based; no new predicate on M) |
| v0.4.0 §12 | `Algebra/Instances.lean` | 6 | ℤ and ℚ module instances + demos (3 each) |
| v0.4.0 §2,11 | `Algebra/ModeA.lean` | 2 | `zsmul_isOperational` (§2); `smul_isModeAOp` (§11) |

**Total: 64 named public objects (31 v0.1.0 + 15 v0.2.0 + 9 v0.3.0 + 9 v0.4.0).**

#### Axiom hierarchy — algebraic (Finding A5, extended by A10, A14, A15, A16)

| Tier | Profile | Representative objects |
|------|---------|----------------------|
| 0 | `[]` | `OperationalAddGroup`, `OperationalRing`, `OperationalGroup`, `OperationalModule`; all Mode A theorems for add/mul/sub/div/pow/zpow/zsmul/smul; bridge instances (AddGroup, Ring, Module); `image_isOperationalAddSubgroup_isModeBOp` |
| 1 | `[propext]` | ℤ instances (additive + ring + **module**); `neg_isModeAOp`, `MulGroup.inv_isModeAOp`; Mode B lifts; `int_ker/image` theorems |
| 2 | `[propext, Quot.sound]` | ZMod n instances; `OperationalField`; bridges `→ OperationalRing`, `→ OperationalAddGroup`; `instPredOpField` |
| 3 | `[propext, Classical.choice, Quot.sound]` | ℚ instances (Finding A14); ℚ **module** instances (inherit via bridge chain); `inv_isModeAOp_field`, `toOperationalGroupUnits` (**structurally embedded**, Finding A16 — not removable by isolation) |

**Finding A10** (extended through v0.4.0): axiom ceiling = underlying type ceiling, not algebraic depth. Module structure adds no new ceiling: ℤ-module ≡ ℤ-ring ceiling `[propext]`; ℚ-module ≡ ℚ-field ceiling `[propext, Classical.choice, Quot.sound]`.

**Finding A14** (v0.3.0): ℚ concrete instances reach the full analysis ceiling. Source: `Rat.instField` carries classical infrastructure for multiplicative inverses via `GroupWithZero`.

**Finding A16** (v0.4.0): A15 structural confirmation — two `Classical.choice` sources are not removable by isolation. See Classical.choice section above for details.

#### Key findings (A0–A19)

**A3** (v0.1.0, extended through v0.4.0): Apparatus reuse confirmed for five algebraic structures — AddGroup, Ring, Group, Field, **Module**. `PredicateOperationality` instance = `⟨⟩` in first four; Module reuses existing `instPredOpAddGroup` unchanged (Finding A17 — strongest confirmation).

**A4** (v0.1.0, confirmed v0.3.0): `neg_isModeAOp` and `inv_isModeAOp` pull `[propext]`; all binary operations (`add`, `mul`, `sub`, `div`) and scalar action (`smul_isModeAOp`) are `[]`. Unary inversion elaborates through `Neg`/`Inv` infrastructure; binary and external closures do not.

**A10** (v0.2.0, extended through v0.4.0): Axiom ceiling = underlying type ceiling, not algebraic depth. Confirmed for all four structures: AddGroup, Ring, Field, Module.

**A11** (v0.2.0): Algebraic Mode B requires one proof step (constructive witness from `AddSubgroup.mem_map`, no `Classical.choice`).

**A12** (v0.3.0): Recognition discipline reversal — `OperationalGroup` omitted (A0), revived (Stage 1), justified concretely by `OperationalField.toOperationalGroupUnits` (Stage 5). First documented *introduction* in the recognition discipline pattern (previously: removals only).

**A13** (v0.3.0): `OperationalField` does not escalate beyond `Field K`'s axiom profile. Consistent with A10.

**A14** (v0.3.0): ℚ reaches full analysis ceiling via `Rat.instField`'s classical inverse infrastructure.

**A15** (v0.3.0): Import-context ceiling escalation. Certain Mathlib imports change how `Inv K` resolves for generic `[Field K]`, affecting two objects: `inv_isModeAOp_field`, `toOperationalGroupUnits`.

**A16** (v0.4.0 Stage 2): A15 structural confirmation. Systematic isolation confirms `Classical.choice` is not removable from the two affected objects — one source is apparatus import chain (proof-architectural), one is proof-structural (field-inverse necessity). Programme framing updated: two structural exceptions, all others at tier 0–2.

**A17** (v0.4.0 Stages 3–5): Apparatus reuse for Module — fourth and strongest confirmation of A3. `smul_isModeAOp` uses `instPredOpAddGroup` (v0.1.0 instance) unchanged. Bridge-based design (no new predicate on M) means literal reuse, not mere extension.

**A18** (v0.4.0 Stage 1): `zsmul_isOperational` closes v0.3.0 gap. Completes the additive/multiplicative symmetry table for ℕ-scalar and ℤ-scalar pairs. Proof mechanics asymmetry: `zsmul` requires explicit `change + rw [natCast_zsmul]`; `zpow` admits definitional unfolding.

**A19** (v0.4.0 Stage 5): First heterogeneous binary operation in VR Cycle. Scalar action `R → M → M` requires `IsModeAOp (r • · : M → M)` (unary, for fixed operational scalar), not `IsModeAOp₂`. Apparatus architecture correctly distinguishes internal (homogeneous) from external (heterogeneous) algebraic operations.

#### Acknowledgement

Developed using **Claude Opus 4.7** (architectural review) and **Claude Sonnet 4.6**
(Lean implementation), Variant A (interactive parent-child architecture), consistent
with predecessor VR Lean cycles.

---

### VR-Topology (`VRCycle/Topology/`)

**Lean: git tag `v1.13-vr-topology-v1.0.0` — Zenodo submission pending**

The ninth work in the VR Cycle. VR-Topology is a **constructive predicative formalisation of formal topology** in Lean 4, proving the binary Tychonoff theorem for compact formal topologies — with zero `Classical.choice` throughout, including the bridge to mathlib's classical `Order.Frame` infrastructure.

#### Position in the VR Cycle

| # | Cycle | Tag | Nature |
|---|-------|-----|--------|
| 1 | VR. A Formal System | v1.0-vr | Foundational (primitives, arithmetic) |
| 2 | VR-Numbers | v1.1-vr-numbers | Foundational (ℤ, ℚ, ℝ, ℂ over VR-ℕ) |
| 3 | VR-Sets | v1.2-vr-sets | Foundational (ZFC, ZFA boundary) |
| 4 | VR-Forms | v1.3-vr-forms | Foundational (two-register apparatus) |
| 5 | VR-Audit | v1.4-vr-audit-hb-hilbert | Applied (first VR-Audit application) |
| 6 | VR-Sets-ZFA | v1.5-vr-sets-zfa | Foundational (ZFA extension, AFA as theorem) |
| 7 | VR-Apparatus | v1.7-vr-apparatus-1.0.0 | Meta (apparatus formalisation) |
| 8 | Operational Algebra | v1.12-vr-operational-algebra-v1.0.0 | Domain extension (algebraic structures) |
| **9** | **VR-Topology** | **v1.13-vr-topology-v1.0.0** | **Domain extension (formal topology)** |

#### Core architectural principle: formal topology, not frames

VR-Topology uses **formal topology** (Coquand 1992, Sambin–Smith–Valentini 2003) — coverage relations on posets — rather than frames as complete lattices. The distinction is forced by Lean 4's universe hierarchy: a `FreeFrame(generators)` construction requires a `Set (FreeFramePre G) → FreeFramePre G` field, which Lean 4 rejects via its positivity check. This was **T0** — the cycle's founding architectural pivot, caught before any Lean code was committed. Formal topology places the coverage relation `cov : S → Set S → Prop` entirely in `Prop`, with no universe inflation.

#### Main theorem

```lean
def tychonoff_binary
    (T₁ T₂ : FormalTopology)
    [inst₁ : OperationalFormalTopology T₁]
    [inst₂ : OperationalFormalTopology T₂]
    [DecidableEq T₁.S] [DecidableEq T₂.S]
    [DecidableRel T₁.le] [DecidableRel T₂.le]
    (w₁ : CompactWitness T₁ inst₁.basicCov)
    (w₂ : CompactWitness T₂ inst₂.basicCov)
    [DecidablePred (· ∈ w₁.F)] [DecidablePred (· ∈ w₂.F)] :
    CompactWitness (FormalTopology.prod T₁ T₂)
                   (OperationalFormalTopology.instProd T₁ T₂).basicCov
```

Binary Tychonoff for formal topology (Vickers 2006 Theorem 19, constructive version): the binary product of compact formal topologies is compact. Mode B audit object: multi-step constructive proof (~480 active lines across five helper theorems and assembly). Axiom profile: **`[propext, Quot.sound]`**, zero `Classical.choice`.

The decidability hypotheses (T16) are explicit: Lean 4's `List`-based compactness machinery — replacing `Finset`, which inherits `Classical.choice` via `Multiset` (T13) — requires decidable equality, order, and compactness-set membership as explicit typeclass parameters.

#### File structure (`VRCycle/Topology/`)

| Stage | File | Public objects | Description |
|-------|------|---------------|-------------|
| 1 | `FormalTopology.lean` | 14 | `FormalTopology` structure; `CoverGen` inductive; `ofPresentation`; five coverage axioms (`cov_refl`, `cov_trans`, `cov_ref_mono`, `cov_local`, `cov_meet`); four derived theorems |
| 2 | `Operational.lean` | 16 | `IsDescribable` data class (T3); `OpCoverGen` inductive; `OperationalFormalTopology` class; `toCoverGen`/`toOpCov` bridge theorems; `ofPresentation`; Unit and Bool instances |
| 3 | `Continuous.lean` | 10 | `ContinuousMap` structure; `OpContinuous`; identity and composition; Mode A theorems `id_isModeAOp`, `comp_isModeAOp` |
| 4 | `Product.lean` | 11 | `FormalTopology.prod`; `prodLe`, `prodBasicCov`, `opProdBasicCov`; `proj₁`, `proj₂`; all `[]` |
| 5 | `Compact.lean` | 10 | `CompactWitness` (List-based, T13); `listLowerOrder`; `OperationalCompact`; `implies_classical_compact`; Unit and Bool operational compact instances |
| 6+6b | `Tychonoff.lean` | 14+ | `tychonoff_binary` (Mode B audit); five `prodF.*` helper theorems; `prodWitness`; `Unit × Bool` concrete operational compactness instance (T20 R3 concrete-only path) |
| 7 | `Bridge.lean` | 10 | `IsSaturated`, `SatSet`, `saturate`; `instCompleteLattice`; **`instFrame`** (bridge to mathlib `Order.Frame`, constructive) |

**Total: ~85+ public objects, ~2863 lines of Lean.**

#### Axiom profile

**Zero `Classical.choice` across all public objects — including the bridge to mathlib's classical `Order.Frame` infrastructure.** This was an unexpected positive deviation: Stage 7's plan expected frame distributivity to require classical machinery from mathlib's lattice infrastructure. The coverage induction proves it constructively.

| Profile | Count | Representative objects |
|---------|-------|----------------------|
| `[]` axiom-free | ~50 | All of Stages 1 and 4; `CoverGen`, `FormalTopology`, `OpCoverGen`, `OperationalFormalTopology`, `CompactWitness`, `OperationalCompact`, `IsSaturated`, `SatSet`; `ContinuousMap.id`, `ContinuousMap.comp` |
| `[propext]` | ~4 | `cov_meet_iter`, `product_decomposition_lemma`, `prodF_set_invariant`, `IsDescribable.instSingleton` |
| `[propext, Quot.sound]` | ~22 | **`tychonoff_binary`**, **`instFrame`**, `OpContinuous.id/comp`, `prodF_cover_closure`, compact instances |
| `[propext, Classical.choice, Quot.sound]` | **0** | — |

#### Key methodological observations (selected T-findings)

1. **T0 — Frame infeasibility pivot**: free-frame construction fails Lean 4's positivity check (universe inflation). Formal topology is not a fallback — it is the mathematically correct constructive setting. Caught at initial reconnaissance, before any Lean code committed. Founded the cycle's entire architecture.

2. **T6/T13 — Classical.choice avoidance via custom implementations**: `Nat.unpair_pair` (T6) and mathlib's `Finset` (T13) both transitively pull `Classical.choice`. Resolved by custom bit-interleaving pairing (`IsDescribable` namespace) and replacing `CompactWitness.F : Set (Finset T.S)` with `Set (List T.S)` (~268 lines discarded, ~245 rewritten). Lean core's `List` carries no Classical dependency.

3. **T7 — `cov_meet` as product infrastructure**: Coquand's minimal 4-axiom coverage condition is insufficient for the product universal property. Vickers's product construction requires `cov_meet` (Sambin's meet axiom: `a ◁ V₁ → a ◁ V₂ → a ◁ (V₁ ∩ V₂)`). Added as fifth axiom to `FormalTopology`; trivial for `ofPresentation`-built topologies. This was the critical infrastructure for Stage 7 frame distributivity.

4. **T21 — `iSup_pos` bridge for Order.Frame**: Stage 7 frame distributivity requires bridging mathlib's `⨆ b ∈ S, A ⊓ b` elaboration (nested conditional `iSup`) against the explicit `sSup S' := saturate (⋃ U ∈ S', U.1)`. The `iSup_pos` lemma (`(⨆ h : p, f h) = f hp` given `hp : p`) provides the bridge in ~5 lines once identified.

5. **Constructive frame bridge**: `instFrame` is proved constructively at `[propext, Quot.sound]`. Together with `tychonoff_binary` at the same profile, VR-Topology occupies the **multistep constructive** position on the Mode B audit spectrum — the first such work in the VR cycle, and the first with a constructive bridge to mainstream classical mathematical infrastructure.

6. **18 T-findings, all pre-code**: T0–T21 (with T18 skipped, T4/T10 absorbed). 7 of 18 are architect-direction errors caught by implementer paper-sketch before any incorrect Lean code was committed. Full catalog in `T_FINDINGS.md`.

#### Acknowledgement

Developed using **Claude Opus 4.7** in both architectural and implementation roles — architect (PLAN documents, halts, sub-plans) and implementer (Lean code, axiom audit) — under human curator Vitaly Reznik. Both AI roles carried by Opus 4.7 in this work (Variant A workflow). Structural separation of roles — not model diversity — is what sustains recognition discipline.

---

### Brouwer fixed-point theorem (`VRCycle/Brouwer/`) — *mathlib-bound, not part of the VR Cycle*

**Lean: git tag `v1.16-vr-brouwer-v1.0.0`**

A Lean 4 formalisation of **Brouwer's fixed-point theorem via Sperner's lemma** (Kuhn–Freudenthal grid), developed as a candidate contribution to **mathlib** — the VR methodology is shared, but the target is mathlib, not the VR Cycle. It proves Sperner's lemma in every dimension, Brouwer for the standard simplex `stdSimplex ℝ (Fin (n+1))` (all `n`), and for any nonempty compact convex set in `EuclideanSpace ℝ (Fin n)`. `sorry`-free, lint-clean.

Distinctive: the constructive/classical boundary is a **machine-checked differential witness** (`VRCycle/Meta/DependsOn.lean`) — the Sperner combinatorics and the approximate fixed point are certified free of the compactness extraction `IsCompact.tendsto_subseq`, which enters only at the final limit. Exposition in blueprint [Chapter 11](https://inventor1975.github.io/VRCycle/).

*Status: proposed to mathlib (the 1000-theorems entry Q1144897 is currently a Lean 3 external formalisation; this would be the first in Lean 4 / mathlib). Outcome pending community discussion.*

#### Acknowledgement

Developed using **Claude Opus 4.8** in both architectural and implementation roles (Variant A workflow), under human curator Vitaly Reznik. AI assistance is disclosed in the mathlib contribution proposal.

---

## What this formalisation does NOT claim

**Ontological theses.** The preprint makes claims about minimalism, the **absence of any ontology of the empty set** (∅ is not "a thing that is empty", and there is no "nothing inside": it is a nullary operation whose entire characterisation is `∀ x, ¬ (x ∈ ∅)`; objects are terms over the operations, so *there are only operations* — the base constructor is named `base`), and the operational character of objects. These are interpretive layers on top of the formal system. This Lean formalisation verifies formal derivability given a specific translation into Lean types — not the philosophical claims themselves.

**Consistency independence.** The preprint argues that VR is consistent relative to ZF via PA. That chain (VR ≅ PA, PA consistent relative to ZF) is not reproduced here. Reproducing it would require formalising PA and ZF independently, which is outside the scope of this project. The formalisation shows that the VR axioms, as translated, produce no contradictions within Lean's kernel — but this is a weaker statement than an explicit consistency proof.

**Faithfulness of translation.** Lean's type-theoretic translation of VR is one possible translation among several. The choices made here (VRObj as an inductive type, vrEq as ∀ p, p x ↔ p y over Prop, etc.) reflect a principled reading of the preprint. Different translation choices could produce different formalisation results while remaining faithful to the preprint's intent.

---

## What the formalisation revealed

### VR. A Formal System

**Theorem 11 is constructively stronger.** The preprint states VR–PA equivalence as a metatheoretic claim about theorem sets. The Lean formalisation produces an explicit constructive witness: a structure `VR_PA_iso` with nine fields (bijection + five operation-preservation proofs), checked by the kernel. The metatheoretic equivalence follows trivially from this.

**T1–T4 are not needed for Theorem 11.** The bridge lemmas `O_add`, `O_mul`, `O_pow` are proved by direct induction on the right Nat argument. The proofs close without referencing T1–T4, because Nat's and VRObj's recursion schemes are symmetric in the same way. T1–T4 stand as independent results about VR arithmetic — they are not steps toward the equivalence theorem.

**Half of Peano's axioms are absorbed by typing.** P1 («O₀ is an object») and P2 («t(O_n) exists») are not theorems in Lean — they are immediate consequences of type-checking. `O 0 : VRObj` is guaranteed by the definition of `O`; `VRObj.succ : VRObj → VRObj` is a total function by its type signature. This is a structural observation: typed foundations make some first-order existence axioms redundant.

**A4 is a theorem, not an axiom.** In the preprint, induction is axiom A4. In Lean, it is a provable theorem derived from the inductive type declaration `VRObj`. The kernel generates the recursor `VRObj.rec` automatically; `A4_induction` is a thin wrapper. This is the deepest structural difference between the preprint's axiom system and the Lean formalisation.

**Leibnizian equality requires two levels of ↔.** The preprint uses ↔ in two distinct senses: (1) as `viff` on VRBool in §3, and (2) as propositional equivalence in Def. 2 (vrEq). Lean makes this distinction explicit: `vrEq` uses Lean's `Iff` (propositional), not `viff` (computational). This is not a deviation from the preprint — it is a clarification of implicit type stratification.

**Acyclicity of ∈ is provable from structure alone.** `not_mem_self` and `succ_ne_self` are proved without ordinal measures or external well-foundedness principles. The proof uses two private lemmas (`mem_succ_left` as a «lowering» lemma and `mem_asymm` for antisymmetry), both proved by structural induction on VRObj. No `omega`, no Nat arithmetic, no imports.

### VR-Numbers

**The Classical-free boundary corresponds exactly to ℤ → ℚ.** `Theorem_II_6_IntVR_Int` depends only on `[propext, Quot.sound]`; every theorem from ℚ_VR onward requires `Classical.choice` additionally. This boundary is structural: integer arithmetic operates syntactically, while rational arithmetic requires a canonical representative (gcd-reduction of a/b). This is a formal observation about the correspondence between the «depths of operationality» (§VI.4) and the axiom dependencies of the formalisation.

**The quotient structure disappears at ℂ_VR.** ℤ_VR, ℚ_VR, and ℝ_VR are all quotient types requiring well-definedness proofs for every lifted operation. ℂ_VR is a direct structure with two ℝ_VR fields — no equivalence relation, no `Quotient.lift`, no well-definedness obligations. §V.5 of the preprint justifies this: the equivalence on ℂ_VR is trivial (identity). The Lean formalisation makes this simplification structurally explicit: the bijection proofs (`forwardC_right_inv`, `forwardC_left_inv`) are four lines total, compared to hundreds of lines for the Cauchy sequence quotient in ℝ_VR.

**Two-dimensionality of ℂ_VR has ontological grounding but not computational dependency.** Axiom A1 of the VR system has two generating facts (`A1_F_reaches_both`: F→F self-reference; `A1_T_reaches_only_T`: F→⊤ value change). These motivate the two fields of `ComplexVR` (real axis / imaginary axis). However, `A1_F_reaches_both` and `A1_T_reaches_only_T` are not referenced in the definition of `ComplexVR` or its operations — they provide ontological motivation, not computational structure. The algebraic coupling between the axes (`i² = −1`) requires a separate joining postulate encoded in `cmul`.

**Division at ℝ_VR and ℂ_VR is defined via the isomorphism, not axiomatically.** `realDiv` and `cdiv` are both defined as `backward ∘ (/) ∘ forward`, inheriting Lean's junk-value convention for division by zero. This is consistent with the preprint's operational approach: the division operation exists by construction from the isomorphism, not as a primitive.

---

## Axiom audit

Every theorem was checked with Lean's `#print axioms`. The formalisation has a three-tier axiom structure:

### Tier 1 — Axiom-free (VR. A Formal System, Parts I–II)

All 51 theorems in `VRCycle/VR.lean` return:

```
'VR.X' does not depend on any axioms
```

Purely constructive: no `Classical.choice`, no `propext`, no `Quot.sound`. Proofs use only Lean's built-in computation rules and structural induction.

### Tier 2 — `[propext, Quot.sound]` (VR-Numbers, ℤ_VR)

`Theorem_II_6_IntVR_Int` and all ℤ_VR theorems depend on `[propext, Quot.sound]` only. `Classical.choice` is absent. Integer arithmetic (`Int.add`, `Int.mul`) is axiom-free in Lean 4 core; the remaining axioms enter through the quotient construction of `ℤ_VR`.

### Tier 2b — `[propext, Quot.sound]` (VR-Sets, most theorems)

Most VR-Sets theorems (Stages 1–6, 9 partial, 11–12) depend only on `[propext, Quot.sound]`:
the quotient construction of `ZFSet` requires `Quot.sound`; membership and extensionality
require `propext`. No `Classical.choice`.

### Tier 2c — `[]` axiom-free (VR-Sets Stage 10, boundary results)

The ZFA-boundary theorems are **constructively proved** with no axioms:

```
'VR.Sets.isZFAmode_all'        does not depend on any axioms
'VR.Sets.quineAtom_impossible' does not depend on any axioms
'VR.Sets.AFA_Refuted'          does not depend on any axioms
'VR.Sets.Conjecture_IV_2_Statement' does not depend on any axioms
```

These derive from `PSet.mem_irrefl` via `Acc.rec` and `PSet`'s inductive structure — no
quotient axioms needed because the proofs never leave the inductive type.

### Tier 2d — `[propext, Quot.sound]` / `[]` (VR-Forms — entire cycle)

All 18 public objects in VR-Forms depend on at most `[propext, Quot.sound]`.
**`Classical.choice` is absent from the entire VR-Forms cycle** — this was not predicted
(the estimate was «all `[propext, Classical.choice, Quot.sound]` or stricter»).
The Classical-free outcome is the most structurally significant axiom result of VR-Forms Lean.

Language.lean (Stage 1, 2 public objects: `Register`, `FormalTerm`) is **axiom-free `[]`** —
a pure structure with no imports and no quotient infrastructure.

All remaining 16 objects (Stages 2–5) depend on `[propext, Quot.sound]` through
the `OSet = ZFSet = Quotient PSet.setoid` chain inherited from VR-Sets. No theorem
in VR-Forms touches `Classical.choice`: the realisability predicate match reduces by
iota-reduction (concrete scrutinees, no noncomputable reasoning), bridge theorems
use direct application and `⟨id, id⟩`, and the catch-all residual is proved by
`unfold`+`split`+`simp_all [FormalTerm.mk.injEq]` — all decidable.

### Tier 3 — `[propext, Classical.choice, Quot.sound]` (VR-Numbers ℚ_VR+; VR-Sets Stages 7–9)

All theorems from ℚ_VR through ℂ_VR, and VR-Sets Stages 7–9 (Replacement, Choice, Foundation, Theorem IV.1), depend on `Classical.choice`. For VR-Numbers this is a **structural property of Lean 4 core**:

```
-- Lean 4 Core (no mathlib):
#print axioms Rat.add  -- [propext, Classical.choice, Quot.sound]
#print axioms Int.add  -- does not depend on any axioms
```

`Rat.add` and `Rat.mul` must normalise their results via `Nat.gcd`, producing a coprimality proof that depends on `Classical.choice`. This cannot be avoided by replacing individual lemmas: any theorem mentioning `+` or `*` on `ℚ` inherits `Classical.choice` from the target type itself.

**The Classical-free boundary in VR-Numbers formalisation corresponds exactly to the transition from ℤ to ℚ** — from operations performed syntactically (`a + b` on `ℤ`) to operations requiring a canonical representative (gcd-reduction of `a/b` on `ℚ`). This is a formal observation about the correspondence between the "depths of operationality" (§VI.4) and axiom dependencies of the formalisation.

<details>
<summary>Complete #print axioms output — VR. A Formal System (all 51 theorems)</summary>

```
-- §2: A1
'VR.A1_1'                 does not depend on any axioms
'VR.A1_2'                 does not depend on any axioms
'VR.A1_F_reaches_both'    does not depend on any axioms
'VR.A1_T_reaches_only_T'  does not depend on any axioms
-- §2: A2
'VR.A2_FF'                does not depend on any axioms
'VR.A2_FT'                does not depend on any axioms
'VR.A2_TF'                does not depend on any axioms
'VR.A2_TT'                does not depend on any axioms
-- §3: derived operators
'VR.vnot_F'               does not depend on any axioms
'VR.vnot_T'               does not depend on any axioms
'VR.vor_FF'               does not depend on any axioms
'VR.vor_FT'               does not depend on any axioms
'VR.vor_TF'               does not depend on any axioms
'VR.vor_TT'               does not depend on any axioms
'VR.vand_FF'              does not depend on any axioms
'VR.vand_FT'              does not depend on any axioms
'VR.vand_TF'              does not depend on any axioms
'VR.vand_TT'              does not depend on any axioms
'VR.viff_FF'              does not depend on any axioms
'VR.viff_FT'              does not depend on any axioms
'VR.viff_TF'              does not depend on any axioms
'VR.viff_TT'              does not depend on any axioms
-- §4: definitions
'VR.T_def'                does not depend on any axioms
'VR.Eq_to_vrEq'           does not depend on any axioms
-- §2: A3
'VR.A3_mem_self'          does not depend on any axioms
'VR.A3_subset_succ'       does not depend on any axioms
-- §2: A4
'VR.A4_induction'         does not depend on any axioms
'VR.A4_exhaustion'        does not depend on any axioms
-- §5
'VR.not_mem_self'         does not depend on any axioms
'VR.succ_ne_self'         does not depend on any axioms
-- §6: ordinals
'VR.O_one'                does not depend on any axioms
'VR.O_two'                does not depend on any axioms
'VR.O_three'              does not depend on any axioms
'VR.O_mem_lt'             does not depend on any axioms
-- §7: arithmetic
'VR.vadd_zero_left'       does not depend on any axioms
'VR.vadd_succ_left'       does not depend on any axioms
'VR.T1_vadd_comm'         does not depend on any axioms
'VR.T2_vadd_assoc'        does not depend on any axioms
'VR.T3_vmul_distrib'      does not depend on any axioms
'VR.T4_one_plus_one'      does not depend on any axioms
-- §9
'VR.O_zero'               does not depend on any axioms
'VR.O_succ'               does not depend on any axioms
-- §10: P3-P5
'VR.P3_succ_ne_zero'      does not depend on any axioms
'VR.P4_succ_inj_leibniz'  does not depend on any axioms
'VR.P4_succ_inj'          does not depend on any axioms
'VR.P5_induction'         does not depend on any axioms
-- §11
'VR.O_left_inv'           does not depend on any axioms
'VR.O_right_inv'          does not depend on any axioms
'VR.O_add'                does not depend on any axioms
'VR.O_mul'                does not depend on any axioms
'VR.O_pow'                does not depend on any axioms
'VR.Theorem_11_VR_PA'     does not depend on any axioms
```
</details>

<details>
<summary>Complete #print axioms output — VR-Sets</summary>

```
-- Foundation.lean (Stages 1-2)
'VR.Sets.Lemma_II_1_Extensionality'  depends on axioms: [propext, Quot.sound]
'VR.Sets.Lemma_II_2_UniquenessEmpty' depends on axioms: [propext, Quot.sound]
'VR.Sets.Lemma_II_3_DepthEmpty'      depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Sets.Lemma_II_3_DepthMono'       depends on axioms: [propext, Classical.choice, Quot.sound]
-- ZF.lean (Stages 3-8)
'VR.Sets.Theorem_III_3_Pairing'      depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_III_4_Union'        depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_III_5_Power'        depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_III_6_Infinity'     depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_III_7_Replacement'  depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Sets.Theorem_III_8_Foundation'   depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Sets.Theorem_III_9_Choice'       depends on axioms: [propext, Classical.choice, Quot.sound]
-- Modes.lean Stage 9 (ZFC-mode)
'VR.Sets.isZFCmode_all'              depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_IV_1_ZFCAxioms'     depends on axioms: [propext, Classical.choice, Quot.sound]
-- Modes.lean Stage 10 (ZFA boundary) — AXIOM-FREE
'VR.Sets.isZFAmode_all'              does not depend on any axioms
'VR.Sets.quineAtom_impossible'       does not depend on any axioms
'VR.Sets.AFA_Refuted'                does not depend on any axioms
-- Conjectures.lean (Stage 11)
'VR.Sets.Conjecture_IV_1_Statement'  depends on axioms: [propext, Quot.sound]
'VR.Sets.Conjecture_IV_2_Statement'  does not depend on any axioms
-- VRNumbers.lean (Stage 12)
'VR.Sets.Theorem_V_1_WellFounded'    depends on axioms: [propext, Quot.sound]
'VR.Sets.embedVR_mem_iff'            depends on axioms: [propext, Quot.sound]
'VR.Sets.embedVR_injective'          depends on axioms: [propext, Quot.sound]
'VR.Sets.Theorem_V_2'                depends on axioms: [propext, Quot.sound]
```
</details>

<details>
<summary>Complete #print axioms output — VR-Forms (all 18 public objects)</summary>

```
-- Language.lean (Stage 1) — AXIOM-FREE
-- (Register and FormalTerm are structures/inductives with no imports;
--  #print axioms on theorems in Stage 1 returns no axioms.)

-- Realisability.lean (Stage 2)
'VR.Forms.isRealisable'          depends on axioms: [propext, Quot.sound]
'VR.Forms.isRealisable_empty'    depends on axioms: [propext, Quot.sound]
'VR.Forms.isRealisable_omega'    depends on axioms: [propext, Quot.sound]
'VR.Forms.isRealisable_osetPair' depends on axioms: [propext, Quot.sound]

-- Transit.lean (Stage 3)
'VR.Forms.translate_pi'                  depends on axioms: [propext, Quot.sound]
'VR.Forms.translate_pi_empty'            depends on axioms: [propext, Quot.sound]
'VR.Forms.translate_pi_omega'            depends on axioms: [propext, Quot.sound]
'VR.Forms.translate_pi_osetPair'         depends on axioms: [propext, Quot.sound]
'VR.Forms.translate_implies_realisable'  depends on axioms: [propext, Quot.sound]

-- Bridge.lean (Stage 4)
'VR.Forms.bridge_AFA'               depends on axioms: [propext, Quot.sound]
'VR.Forms.bridge_Conjecture_IV_1'   depends on axioms: [propext, Quot.sound]
'VR.Forms.bridge_Conjecture_IV_2'   depends on axioms: [propext, Quot.sound]

-- Examples.lean (Stage 5)
'VR.Forms.not_isRealisable_Russell'                depends on axioms: [propext, Quot.sound]
'VR.Forms.not_isRealisable_Vitali'                 depends on axioms: [propext, Quot.sound]
'VR.Forms.not_isRealisable_classical_R'            depends on axioms: [propext, Quot.sound]
'VR.Forms.not_isRealisable_classical_powerset_N'   depends on axioms: [propext, Quot.sound]
'VR.Forms.mixed_omega_two_register'                depends on axioms: [propext, Quot.sound]
'VR.Forms.mixed_AFA_boundary'                      depends on axioms: [propext, Quot.sound]
```
</details>

<details>
<summary>Complete #print axioms output — VR-Numbers (key theorems)</summary>

```
-- ℤ_VR (Tier 2)
'VR.Numbers.Theorem_II_6_IntVR_Int'      depends on axioms: [propext, Quot.sound]
-- ℚ_VR (Tier 3)
'VR.Numbers.Theorem_III_6_RatVR_Rat'     depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Numbers.Theorem_III_4_CanonicalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
-- ℝ_VR (Tier 3)
'VR.Numbers.Theorem_IV_7_RealVR_Real'    depends on axioms: [propext, Classical.choice, Quot.sound]
-- ℂ_VR (Tier 3)
'VR.Numbers.Theorem_V_8_ComplexVR_Complex' depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Numbers.preserveAbs'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Numbers.preserveDiv'                 depends on axioms: [propext, Classical.choice, Quot.sound]
```
</details>

<details>
<summary>Complete #print axioms output — Operational Algebra (all 64 public objects, v0.1.0–v0.4.0)</summary>

```
-- AddGroup.lean (v0.1.0 Stage 1) — AXIOM-FREE
'VR.Algebra.OperationalAddGroup' does not depend on any axioms

-- Instances.lean §1-2 (v0.1.0 Stage 2)
'VR.Algebra.instOperationalAddGroupInt'         depends on axioms: [propext]
'VR.Algebra.int_isOperational'                  depends on axioms: [propext]
'VR.Algebra.int_add_isOperational'              depends on axioms: [propext]
'VR.Algebra.int_three_plus_five_isOperational'  depends on axioms: [propext]

-- Instances.lean §3-4 (v0.1.0 Stage 4)
'VR.Algebra.instOperationalAddGroupZMod'          depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod_isOperational'                   depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod5_add_isOperational'              depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod5_two_plus_three_isOperational'   depends on axioms: [propext, Quot.sound]

-- ModeA.lean §1-3 (v0.1.0 Stage 3)
'VR.Algebra.instPredOpAddGroup'  does not depend on any axioms
'VR.Algebra.add_isModeAOp'       does not depend on any axioms
'VR.Algebra.sub_isModeAOp'       does not depend on any axioms
'VR.Algebra.nsmul_isOperational' does not depend on any axioms
'VR.Algebra.neg_isModeAOp'       depends on axioms: [propext]

-- ModeA.lean §2 (v0.4.0 Stage 1) — AXIOM-FREE
'VR.Algebra.zsmul_isOperational' does not depend on any axioms

-- Subgroups.lean (v0.1.0 Stage 5)
-- Note: OperationalSubgroup structure was not implemented (Finding A6 — predicate suffices).
-- The 8 objects below are the actual public objects in Subgroups.lean.
'VR.Algebra.IsOperationalAddSubgroup'                  depends on axioms: [propext]
'VR.Algebra.bot_isOperationalAddSubgroup'              depends on axioms: [propext, Quot.sound]
'VR.Algebra.top_isOperationalAddSubgroup'              depends on axioms: [propext]
'VR.Algebra.inf_isOperationalAddSubgroup'              depends on axioms: [propext]
'VR.Algebra.inf_isOperationalAddSubgroup_bilateral'    depends on axioms: [propext]
'VR.Algebra.int_bot_isOperationalAddSubgroup'          depends on axioms: [propext, Quot.sound]
'VR.Algebra.int_top_isOperationalAddSubgroup'          depends on axioms: [propext]
'VR.Algebra.int_inf_top_isOperationalAddSubgroup'      depends on axioms: [propext]

-- ModeBExample.lean §1 (v0.1.0 Stage 6, fully proved)
'VR.Algebra.neg_isModeBOp'        depends on axioms: [propext]
'VR.Algebra.neg_modeb_lift'       depends on axioms: [propext]
'VR.Algebra.neg_modeb_lift_val'   depends on axioms: [propext]

-- ModeBExample.lean §2 (v0.2.0 Stage 6, sorry ELIMINATED)
'VR.Algebra.image_isOperationalAddSubgroup_isModeBOp'
                                  depends on axioms: [propext]   ← was [propext, sorryAx]
'VR.Algebra.operationalImage_lift'     depends on axioms: [propext]
'VR.Algebra.operationalImage_lift_val' depends on axioms: [propext]

-- ModeBExample.lean §3 (v0.1.0 Stage 6, concrete ℤ examples)
'VR.Algebra.int_ker_isOperationalAddSubgroup'         depends on axioms: [propext]
'VR.Algebra.int_image_isOperationalAddSubgroup'       depends on axioms: [propext]
'VR.Algebra.int_to_zmod_ker_isOperationalAddSubgroup' depends on axioms: [propext, Quot.sound]

-- Ring.lean (v0.2.0 Stages 1-2) — AXIOM-FREE
'VR.Algebra.OperationalRing'                       does not depend on any axioms
'VR.Algebra.OperationalRing.toOperationalAddGroup' does not depend on any axioms

-- Instances.lean §5-6 (v0.2.0 Stage 3)
'VR.Algebra.instOperationalRingInt'              depends on axioms: [propext]
'VR.Algebra.int_one_isOperational'               depends on axioms: [propext]
'VR.Algebra.int_mul_isOperational'               depends on axioms: [propext]
'VR.Algebra.int_two_mul_three_isOperational'     depends on axioms: [propext]
'VR.Algebra.int_sum_mul_isOperational'           depends on axioms: [propext]

-- Instances.lean §7-8 (v0.2.0 Stage 4)
'VR.Algebra.instOperationalRingZMod'                depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod5_one_isOperational'                depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod5_mul_isOperational'                depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod5_two_mul_three_isOperational'      depends on axioms: [propext, Quot.sound]
'VR.Algebra.zmod7_sum_mul_isOperational'            depends on axioms: [propext, Quot.sound]

-- ModeA.lean §4-7 (v0.2.0 Stage 5) — AXIOM-FREE
'VR.Algebra.instPredOpRing'      does not depend on any axioms
'VR.Algebra.mul_isModeAOp'       does not depend on any axioms
'VR.Algebra.npow_isOperational'  does not depend on any axioms

-- MulGroup.lean (v0.3.0 Stage 1) — AXIOM-FREE
'VR.Algebra.OperationalGroup' does not depend on any axioms

-- Field.lean (v0.3.0 Stages 2 and 5)
'VR.Algebra.OperationalField'
    depends on axioms: [propext, Quot.sound]
'VR.Algebra.OperationalField.toOperationalRing'
    depends on axioms: [propext, Quot.sound]
'VR.Algebra.OperationalField.toOperationalGroupUnits'
    depends on axioms: [propext, Classical.choice, Quot.sound]   ← Finding A15/A16

-- Instances.lean §9-10 (v0.3.0 Stage 3)
'VR.Algebra.instOperationalFieldRat'
    depends on axioms: [propext, Classical.choice, Quot.sound]   ← Finding A14
'VR.Algebra.rat_half_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Algebra.rat_half_plus_third_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Algebra.rat_product_inv_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Algebra.rat_sub_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]

-- ModeA.lean §8-10 (v0.3.0 Stage 4)
-- Note: VR.Algebra.MulGroup.xxx is the within-namespace form used in file-level #print axioms.
-- Absolute Lean 4 names: VR.Algebra.VR.Algebra.MulGroup.xxx (namespace nesting artifact).
'VR.Algebra.VR.Algebra.MulGroup.instPredOpMulGroup'  does not depend on any axioms
'VR.Algebra.VR.Algebra.MulGroup.mul_isModeAOp'       does not depend on any axioms
'VR.Algebra.VR.Algebra.MulGroup.inv_isModeAOp'       depends on axioms: [propext]
'VR.Algebra.VR.Algebra.MulGroup.div_isModeAOp'       does not depend on any axioms
'VR.Algebra.VR.Algebra.MulGroup.npow_isOperational'  does not depend on any axioms
'VR.Algebra.VR.Algebra.MulGroup.zpow_isOperational'  does not depend on any axioms
'VR.Algebra.instPredOpField'
    depends on axioms: [propext, Quot.sound]
'VR.Algebra.inv_isModeAOp_field'
    depends on axioms: [propext, Classical.choice, Quot.sound]   ← Finding A15/A16

-- Module.lean (v0.4.0 Stage 3) — AXIOM-FREE
'VR.Algebra.OperationalModule' does not depend on any axioms

-- Instances.lean §12 (v0.4.0 Stage 4)
'VR.Algebra.instOperationalModuleIntInt'            depends on axioms: [propext]
'VR.Algebra.int_smul_isOperational'                 depends on axioms: [propext]
'VR.Algebra.int_two_smul_three_isOperational'       depends on axioms: [propext]
'VR.Algebra.instOperationalModuleRatRat'
    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Algebra.rat_smul_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]
'VR.Algebra.rat_half_smul_third_isOperational'
    depends on axioms: [propext, Classical.choice, Quot.sound]

-- ModeA.lean §11 (v0.4.0 Stage 5) — AXIOM-FREE
'VR.Algebra.smul_isModeAOp' does not depend on any axioms
```
</details>

---

## Build instructions

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
git clone <repo-url>
cd VRCycle
lake build
```

The first build downloads mathlib cache (~1 GB). Subsequent builds are fast.

**Expected output:** `Build completed successfully (3361 jobs).` Zero warnings. Zero sorry.

## Toolchain

| Component | Version |
|-----------|---------|
| Lean | 4.29.1 |
| mathlib4 | v4.29.1 |
| Lake | bundled with Lean 4.29.1 |

## Status

### VR. A Formal System

| Stage | Description | Status | Axioms |
|-------|-------------|--------|--------|
| 0 | Project setup | ✓ | — |
| 1 | Primitives and axioms | ✓ | none |
| 2 | Derived operators, Leibnizian identity | ✓ | none |
| 3 | Von Neumann ordinals | ✓ | none |
| 4 | Arithmetic operations | ✓ | none |
| 5 | Peano equivalence (Theorem 11) | ✓ | none |
| 6 | Publication | ✓ | — |

### VR-Numbers

| Stage | Description | Status | Axioms |
|-------|-------------|--------|--------|
| 7 | ℤ_VR: integers as signed pairs over ℕ_VR | ✓ | `[propext, Quot.sound]` |
| 8.1–8.8 | ℤ_VR operations, embedding, isomorphism ℤ_VR ≅ ℤ | ✓ | `[propext, Quot.sound]` |
| 8.9 | ℚ_VR: rationals, isomorphism ℚ_VR ≅ ℚ | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 8.10 | Canonical form (§III.4) | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 9 | ℝ_VR via Cauchy sequences, isomorphism ℝ_VR ≅ ℝ | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 10 | ℂ_VR, isomorphism ℂ_VR ≅ ℂ | ✓ | `[propext, Classical.choice, Quot.sound]` |

### VR-Sets

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1–2 | `Foundation.lean` | OSet type, ∅, ≡; Lemmas 1–3 | ✓ | Lemmas 1–2: `[propext, Quot.sound]`; Lemma 3: `[propext, Classical.choice, Quot.sound]` |
| 3–6 | `ZF.lean` | Pairing, Union, Power, Infinity | ✓ | `[propext, Quot.sound]` |
| 7–8 | `ZF.lean` | Replacement, Choice | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 9 | `Modes.lean` | §III.8 Foundation; ZFC-mode; Theorem IV.1 | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 10 | `Modes.lean` | ZFA boundary: Quine impossible, AFA refuted | ✓ | **`[]` (axiom-free)** |
| 11 | `Conjectures.lean` | Conjectures IV.1, IV.2 (formulations only) | ✓ | IV.1: `[propext, Quot.sound]`; IV.2: `[]` |
| 12 | `VRNumbers.lean` | VR numbers as von Neumann ordinals; Theorem V.2 | ✓ | `[propext, Quot.sound]` |
| 13 | — | Final audit, README, git tag, Zenodo | ✓ | — |

### VR-Forms

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Forms/Language.lean` | Register, FormalTerm, ⌜·⌝ macro | ✓ | **`[]` (axiom-free)** |
| 2 | `Forms/Realisability.lean` | isRealisable predicate; 3 base lemmas; extended Stage 4 | ✓ | `[propext, Quot.sound]` |
| 3 | `Forms/Transit.lean` | translate_pi; translate_implies_realisable; transit pattern (documented boundary) | ✓ | `[propext, Quot.sound]` |
| 4 | `Forms/Bridge.lean` | bridge_AFA; bridge_Conjecture_IV_1/IV_2; retroactive Stage 2 extension | ✓ | `[propext, Quot.sound]` |
| 5 | `Forms/Examples.lean` | 4 non-realisable examples; mixed_omega_two_register; mixed_AFA_boundary | ✓ | `[propext, Quot.sound]` |
| 6 | — | Full audit, README, PLAN.md, git tag v1.3-vr-forms | ✓ | — |

### VR-Audit (Hahn-Banach for Operational Hilbert Spaces)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Audit/Computable.lean` | `IsComputableReal`, `IsComputableSequence`, 6 base lemmas | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 2 | `Audit/Hilbert.lean` | `OperationalHilbertSpace` typeclass; ℝ instance | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 3 | `Audit/Subspace.lean` | `OperationalLocatedSubspace` structure; ⊤ instance | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 4 | `Audit/Functional.lean` | `OperationalNormableFunctional` structure; zero instance | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 5 | `Audit/HahnBanach.lean` | `HahnBanachOperational_Hilbert` (main theorem via Riesz) | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 6 | `Audit/Example.lean` | `instOperationalHilbertSpaceEuclidean` (ℝⁿ for all n) | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 7 | — | Full audit, README, PLAN.md, git tag v1.4-vr-audit-hb-hilbert | ✓ | — |

### VR-Sets-ZFA (Operational Reference Semantics for Non-Well-Founded Sets)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `SetsZFA/CoPSet.lean` | `CoPSet` coinductive type via `PFunctor.M`; `mk`, `corec`, `bisim` | ✓ | `CoPSetFunctor`, `CoPSet`, `CoPSet.mk`, `CoPSet.corec`: **none**; rest: standard ceiling |
| 2 | `SetsZFA/Cobisimulation.lean` | `CoPSet.Equiv` (cobisimulation); setoid; `bisim_imp_Equiv` | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 3 | `SetsZFA/OSetZFA.lean` | `OSetZFA` quotient; `sound`, `exact`, `eq_iff`, lifting | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 4 | `SetsZFA/Membership.lean` | `∈` on OSetZFA; `mem_mk`, `ext`, `ext_iff` | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 5 | `SetsZFA/AFA.lean` | `graphCoalg` (axiom-free), `graphCoPSet`, `AFA_in_OSetZFA` | ✓ | `graphCoalg`, `graphCoPSet`: **none**; rest: standard ceiling |
| 6 | `SetsZFA/Embedding.lean` | `embedPSet` (axiom-free), `embedOSet`, faithfulness, mem-preservation | ✓ | `embedPSet`: **none**; rest: standard ceiling |
| 7 | `SetsZFA/Examples.lean` | `quineAtom`, `cycleDecoration`, `omegaChain`; non-wf witnesses | ✓ | `[propext, Classical.choice, Quot.sound]` |
| 8 | `SetsZFA/API.lean` | `OSetZFA.empty`, `OSetZFA.singleton`, `acc_irrefl` (axiom-free), `@[simp]` | ✓ | `acc_irrefl`: **none**; rest: standard ceiling |
| 9 | — | Full audit, README, PLAN.md, git tag v1.5-vr-sets-zfa, Zenodo | ✓ | — |

### VR-Apparatus (Methodological Apparatus Formalisation)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| v0.1.0 | `Apparatus/Identity.lean` | `IdentityNature` (AsPoint, AsReference) | ✓ | **`[]`** |
| v0.1.0 | `Apparatus/Wrapping.lean` | `PredicateOperationality` marker class | ✓ | **`[]`** |
| v0.1.0 | `Apparatus/Reference.lean` | `ReferenceOperationality`; instRefOpCoPSet | ✓ | instRefOpCoPSet: `[propext, Classical.choice, Quot.sound]` |
| v0.1.0 | `Apparatus/ModeA.lean` | `IsModeAOp`, `IsModeAOp₂`, `modeA_liftFn`, compose | ✓ | instances: `[propext, Classical.choice, Quot.sound]` |
| v0.1.0 | `Apparatus/ModeB.lean` | `IsModeBOp`, lift, compose; Riesz instance | ✓ | core: **`[]`**; Riesz: `[propext, Classical.choice, Quot.sound]` |
| v0.1.0 | `Apparatus/Instances.lean` | neg/sub Mode A, `instRefOpPSet`, embedPSet pattern | ✓ | `instRefOpPSet`: `[propext, Quot.sound]`; rest: ceiling |
| 4 | `Apparatus/Factorisation.lean` | `Factorisable`, operand-not-operation theorem, `IsModeBOp_of_factorisable` | ✓ | core: **`[]`**; Riesz: ceiling |
| 6 | `Apparatus/Separability.lean` | `HasSeparabilityStructure`; Hilbert instance; separability→factorisable | ✓ | core: **`[]`**; Hilbert instance: ceiling |
| 2 | `Apparatus/InterMorphism.lean` | `InterApparatusMorphism`, lift, lift_mk (new `[Quot.sound]` tier), compose | ✓ | lift/lift_mk: `[Quot.sound]`; ZFC→ZFA: ceiling |
| 3 | `Apparatus/Composition.lean` | Identity morphisms; unit laws; interop | ✓ | reference identities: `[Quot.sound]`; rest: **`[]`** |
| 5 | `Apparatus/Numbers.lean` | Hybrid lens: ℝ (Cauchy bridge), ℕ (von Neumann IAM) | ✓ | ℝ: ceiling; ℕ: **`[]`** |
| 1 | `Apparatus/FormsIntegration.lean` | VR-Forms transit as Mode B; three-way identity nature | ✓ | `[propext, Quot.sound]` |
| Polish | `Apparatus.lean` | Comprehensive module doc; four-tier axiom table; twelve findings | ✓ | — |
| Pub | — | Full audit, git tag v1.7-vr-apparatus-1.0.0, Zenodo DOI 10.5281/zenodo.20380344 | ✓ | — |

### Operational Algebra (domain extension to algebraic structures)

**64 public objects** across 9 files. No sorry. No admit. `sorryAx` eliminated in v0.2.0 Stage 6. Logically constructive throughout — `Classical.choice` absent from all logical content; two objects carry it as structurally embedded field-inverse reasoning (Finding A16). Git tags: `v1.8–v1.11` (v0.1.0–v0.4.0); `v1.12-vr-operational-algebra-v1.0.0` (stable release).

#### v0.1.0 — Additive groups (31 objects, tag `v1.8-vr-operational-algebra-v0.1.0`)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Algebra/AddGroup.lean` | `OperationalAddGroup` typeclass; Finding A0 (multiplicative omitted) | ✓ | **`[]`** |
| 2 | `Algebra/Instances.lean` §1–2 | `OperationalAddGroup ℤ`; 3 demos | ✓ | `[propext]` |
| 3 | `Algebra/ModeA.lean` §1–3 | Mode A theorems; `instPredOpAddGroup`; Findings A3, A4 | ✓ | `[]` – `[propext]` |
| 4 | `Algebra/Instances.lean` §3–4 | `OperationalAddGroup (ZMod n)`; 3 demos; Finding A5 | ✓ | `[propext, Quot.sound]` |
| 5 | `Algebra/Subgroups.lean` | `IsOperationalAddSubgroup`; ⊥, ⊤, ⊓; Finding A6 | ✓ | `[propext]` – `[propext, Quot.sound]` |
| 6 | `Algebra/ModeBExample.lean` §1–3 | Mode B: negation (trivial) + image subgroup (substantive); Findings A7, A8 | ✓ | `[propext]` (sorryAx eliminated in v0.2.0) |
| 7 | — | Polish, axiom audit, git tag v1.8-vr-operational-algebra-v0.1.0 | ✓ | — |

#### v0.2.0 — Rings + substantive Mode B audit (15 new objects, tag `v1.9-vr-operational-algebra-v0.2.0`)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Algebra/Ring.lean` | `OperationalRing` typeclass (extends `Ring R`); 5 closure axioms for 0, +, −, 1, * | ✓ | **`[]`** |
| 2 | `Algebra/Ring.lean` | `OperationalCommRing` OMITTED (Finding A9 — recognition discipline); bridge `OperationalRing → OperationalAddGroup` | ✓ | **`[]`** |
| 3 | `Algebra/Instances.lean` §5–6 | `OperationalRing ℤ`; 4 ring demos; Finding A10 first observed | ✓ | `[propext]` |
| 4 | `Algebra/Instances.lean` §7–8 | `OperationalRing (ZMod n)` `[NeZero n]`; 4 ring demos; Finding A10 confirmed | ✓ | `[propext, Quot.sound]` |
| 5 | `Algebra/ModeA.lean` §4–7 | `mul_isModeAOp`, `npow_isOperational`, `instPredOpRing`; recognition discipline (2 omissions) | ✓ | **`[]`** |
| 6 | `Algebra/ModeBExample.lean` §2 | **Substantive Mode B audit** — sorry eliminated; Finding A11 | ✓ | `[propext]` (was `[propext, sorryAx]`) |
| 7 | — | Polish, full axiom audit, module index, README, git tag v1.9-vr-operational-algebra-v0.2.0 | ✓ | — |

#### v0.3.0 — Fields + multiplicative groups + ℚ (9 new objects, tag `v1.10-vr-operational-algebra-v0.3.0`)

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Algebra/MulGroup.lean` | `OperationalGroup` typeclass (multiplicative); Finding A12 anticipated | ✓ | **`[]`** |
| 2 | `Algebra/Field.lean` | `OperationalField` typeclass (extends `Field K`); bridge `→ OperationalRing` | ✓ | `[propext, Quot.sound]` |
| 3 | `Algebra/Instances.lean` §9–10 | `OperationalField ℚ`; `OperationalRing ℚ` (bridge); Finding A14 | ✓ | `[propext, Quot.sound]` |
| 4 | `Algebra/ModeA.lean` §8–10 | mul/inv/div/npow/zpow Mode A for `OperationalGroup`; inv for field; Finding A15 | ✓ | `[]` – `[propext, Quot.sound]`* |
| 5 | `Algebra/Field.lean` | `OperationalField.toOperationalGroupUnits` — Units bridge; Finding A12 CLOSED | ✓ | `[propext, Classical.choice, Quot.sound]`* |
| 6 | — | Polish, full axiom audit, module index, README, git tag v1.10-vr-operational-algebra-v0.3.0 | ✓ | — |

\* Import-context ceiling escalation (Finding A15). Logical ceiling: `[propext, Quot.sound]`.

#### Findings catalog (A0–A15)

| Finding | Summary |
|---------|---------|
| A0 | Multiplicative typeclass omitted — no v0.1.0 instances (recognition discipline) |
| A1 | Lean 4 `extends` resolves mathlib's Ring hierarchy correctly |
| A2 | `toAddGroup := inferInstance` resolves bridge to AddGroup via ring chain |
| A3 | `PredicateOperationality` reused WITHOUT modification — apparatus generic across AddGroup, Ring, Field |
| A4 | `neg_isModeAOp` pulls `[propext]`; multiplication does NOT — Neg elaboration artefact |
| A5 | Logical axiom ceiling hierarchy: `[]` → `[propext]` → `[propext, Quot.sound]`; `Classical.choice` absent from all logical content |
| A6 | `IsOperationalAddSubgroup` as predicate (not typeclass) — correct design, no diamond |
| A7 | Algebraic Mode B structurally similar to analytic Mode B, but simpler witness extraction |
| A8 | Trivial vs substantive Mode B: `True` witness vs operational-morphism condition |
| A9 | `OperationalCommRing` OMITTED — diamond on `toRing` (Form A fails); duplication no content (Form B); `[OperationalRing R] [CommRing R]` suffices |
| A10 | Ring extension does NOT escalate axiom ceiling — ceiling = underlying type, not algebraic depth |
| A11 | Algebraic Mode B = one proof step (`exact hW x (hS x hxS)`); constructive witness from `mem_map`; no Classical.choice |
| A12 | Recognition discipline REVERSAL — `OperationalGroup` (multiplicative) omitted at A0 (no instances); revived at v0.3.0 (anticipated); justified concretely by `toOperationalGroupUnits` (Stage 5). Loop closed. |
| A13 | Apparatus reuse confirmed for Field — third structure (after AddGroup, Ring). Finding A3 generalises to entire algebraic hierarchy. |
| A14 | ℚ axiom ceiling `[propext, Quot.sound]` — identical to ℤ and ZMod n; rational arithmetic same constructive depth as integer arithmetic |
| A15 | Import-context ceiling escalation — `Mathlib.Data.Real.Basic` (via apparatus chain) changes `Inv K` resolution for generic `[Field K]`, injecting `Classical.choice` into two proof terms. Logical ceiling remains `[propext, Quot.sound]`; programme remains logically constructive. |

### VR-Topology (formal topology, binary Tychonoff)

**~85+ public objects** across 7 files. No sorry. No admit. **Zero `Classical.choice` across the entire tower** including bridge to mathlib `Order.Frame`. Git tag: `v1.13-vr-topology-v1.0.0`.

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Topology/FormalTopology.lean` | `FormalTopology`, `CoverGen`, `ofPresentation`; five coverage axioms as theorems; four derived theorems | ✓ | **`[]`** |
| 2 | `Topology/Operational.lean` | `IsDescribable`, `OpCoverGen`, `OperationalFormalTopology`, bridge theorems; Unit/Bool instances | ✓ | `[]`–`[propext, Quot.sound]` |
| 3 | `Topology/Continuous.lean` | `ContinuousMap`, `OpContinuous`; identity, composition; Mode A theorems | ✓ | `[]`–`[propext, Quot.sound]` |
| 4 | `Topology/Product.lean` | Binary product, `prodLe`, `prodBasicCov`, projections | ✓ | **`[]`** |
| 5 | `Topology/Compact.lean` | `CompactWitness` (List-based, T13); `OperationalCompact`; `implies_classical_compact`; Unit/Bool instances | ✓ | `[]`–`[propext, Quot.sound]` |
| 6 | `Topology/Tychonoff.lean` | **`tychonoff_binary`** (Mode B audit; ~480 lines) | ✓ | **`[propext, Quot.sound]`** |
| 6b | `Topology/Tychonoff.lean` | `Unit × Bool` concrete operational compactness instance | ✓ | `[propext, Quot.sound]` |
| 7 | `Topology/Bridge.lean` | **`instFrame`** (bridge to mathlib `Order.Frame`, constructive) | ✓ | **`[propext, Quot.sound]`** |
| Tag | — | Full axiom audit (FINAL_AXIOM_AUDIT.md), T_FINDINGS.md, git tag `v1.13-vr-topology-v1.0.0` | ✓ | — |

### VR-Transit (transit conservativity, bounded witness library)

**Tenth work.** Extends VR-Apparatus from *"transit is well-behaved"* to *transit is conservative over axioms* and *leverage is a bounded library of witnesses*. **Five public objects** across three files (plus one exhibition file with none). No sorry. No admit. Full build: 3366 jobs. Git tag: `v1.15-vr-transit-v1.0.0`. A clarity result, not new power: the apparatus contributes no axiom of its own to any transited object; this work says exactly where each transit's axiom cost lives, and exactly where the witness method stops.

| Stage | File | Description | Status | Axioms |
|-------|------|-------------|--------|--------|
| 1 | `Transit/FiniteWitness.lean` | `HasFiniteGeneratorStructure`; `finiteGen_provides_factorisable` (pointwise); `finiteSpan_provides_factorisable` (aggregating over an explicit `Finset`, choice-free) | ✓ | `[]` / `[]` / **`[propext, Quot.sound]`** |
| 2 | `Transit/Conservativity.lean` | Conservativity (I) exhibited by axiom attribution; four-source cost decomposition; apparatus column empty (no public objects) | ✓ | exhibition |
| 3 | `Transit/Located.lean` | `located_witness_operational`, `located_provides_factorisable` — located structure supplies the witness `f ∘ P_M` (realised Level-B; source: operation) | ✓ | **`[propext, Classical.choice, Quot.sound]`** |
| 4 | — | Reference-track provider examined and dropped (recon-first; no clean instance) — Finding TR-R1 | — | — |
| 5 | `blueprint/src/chapters/10_transit.tex` | Blueprint Chapter 11; `leanblueprint checkdecls` + `web` green | ✓ | — |

VR-Transit contributes **two new providers** — finiteness (finite generators, in pointwise and aggregating tiers) and completeness/projection (located). With the **inherited** density provider (separability, from VR-Apparatus Stage 6), the predicate-track library now spans four.

**Findings** (`T_FINDINGS_TRANSIT.md`):
- **TR-FW1** — finite-transit cost lives in the carrier *encoding*, not the algebra (two removable faces: `Fintype`/`Finset.univ` inflation; `Finset`-as-class-field contamination of the pointwise tier).
- **TR-C1** — the operation source is a spectrum: `[propext]` (algebraic infrastructure) ↔ `[propext, Classical.choice, Quot.sound]` (analytic); neither is apparatus.
- **TR-R1** (headline) — the witness method reaches exactly as far as the obstacle is witnessable; the reference track's non-descent reduces to `Classical.choice`, which cannot be witnessed, so it admits no clean witness method.

#### Acknowledgement

Developed using **Claude Opus 4.8** in both architectural and implementation roles — architect (PLAN, briefs, halts) and implementer (Lean code, axiom audit) — under human curator Vitaly Reznik. Both roles were carried by the same model (Opus 4.8) in this work (Variant A workflow); here the discipline rested on the structural separation of architect and implementer, not on model diversity.
