# Part X. Lean 4 Formalisation of VR-Sets: Methodological Observations

*Draft for VR-Sets v1.0.1. Based on the Lean 4 formalisation
(VRCycle repository, tag v1.2-vr-sets; Zenodo Software DOI: 10.5281/zenodo.20354340).
Companion to the Lean formalisation of VR-Numbers (§VIII, v1.0.2).*

---

## §X.1 Overview

The formalisation of VR-Sets Parts II–V in Lean 4 (mathlib v4.29.1) was
completed in thirteen stages. The base type `OSet := ZFSet` — mathlib's
`Quotient PSet.setoid` — carries all nine ZFC axioms as theorems and
serves as the operational set universe. The formalisation uses the same
Opus–Sonnet review architecture as VR-Numbers (§VIII). The same axiom
ceiling `[propext, Classical.choice, Quot.sound]` is maintained; four
objects achieve the empty axiom profile (no axioms whatsoever), a tighter
result than VR-Numbers, where no object was axiom-free.

The results divide into three categories, each new relative to VR-Numbers:

1. **Proved theorems**: all nine ZFC axioms, Theorem V.1 (well-foundedness),
   Theorem V.2 (VR–OSet isomorphism), Theorem IV.1 (ZFC-mode collector).
2. **Refuted claims**: classical Anti-Foundation Axiom (AFA) and the Quine
   atom specification, both provably false in mathlib's `PSet`.
3. **Open formulations**: Conjectures IV.1 and IV.2, recorded as
   `def : Prop` — a third Lean status distinct from `theorem` and `axiom`.

The sections below record methodological observations arising from the
formalisation, grouped thematically. Each observation is stated concisely;
the underlying Lean evidence (definitions, proofs, `#print axioms` output)
is in the formalisation repository.

---

## §X.2 Bisimulation and the Quotient Base

**Observation A.1 (Bisimulation as definitional equality).**
The preprint defines operational identity (Definition 4) as a bisimulation:
«for every element x of A there exists an element y of B with x ≡ y, and
conversely». In Lean, this is `PSet.Equiv` — the extensional bisimulation
on pre-sets (Mathlib ZFC.PSet). The quotient `ZFSet := Quotient PSet.setoid`
promotes `PSet.Equiv` to Lean's propositional equality `Eq`. Setting
`OSet := ZFSet` (as an `abbrev`) makes `a ≡ b` syntactically identical to
`a = b : OSet`. The bisimulation does not require a separate proof step —
it is *definitionally absorbed* into the quotient construction.

This is more economical than VR-Numbers, where each isomorphism
(`IntVRIntIso`, `RatVRRatIso`, etc.) required explicit `forward`/`backward`
maps with round-trip proofs. Here, the bisimulation is the quotient.

**Observation A.2 (Duplicate elements via quotient).**
The preprint states (§II.2): «the union reveals elements without
repetitions up to ≡». In ZFSet, duplicate suppression does not require
a separate predicate or a decidability hypothesis. The quotient `ZFSet`
identifies extensionally equivalent elements automatically;
`ZFSet.sUnion` (union) and `ZFSet.powerset` (power set) return elements
of `ZFSet`, so membership is already modulo `PSet.Equiv`. No `DecidableEq`
typeclass or analogous instance is needed at the union/power level, in
contrast to settings where set equality is a separate predicate.

---

## §X.3 Structural Boundaries

This section records five places where the Lean formalisation reveals
a structural boundary between the operational universe of VR-Sets and
mathlib's type-theoretic infrastructure. The boundaries are of two types:
*Lean is wider* (the Lean object admits more than the operationally
describable) and *Lean is narrower* (the Lean object pre-commits to a
restriction not present in the preprint's general formulation).

**Observation B.1 (First boundary: Power set).**
Stage 5 formalises `℘(A)` via `ZFSet.powerset`. The preprint §III.5
restricts the power set to *operationally describable* subsets, yielding
a countable result for countable `A`. In Lean, `ZFSet.powerset` contains
*all* subsets — including non-describable ones. For `A = ω`, the resulting
set is uncountable. This is the first structural boundary of the
formalisation: Lean's `℘(ω)` is strictly wider than the preprint's
operational `℘(ω)`. The discrepancy is metatheoretic (the condition
«operationally describable» is not Lean-expressible) and is documented
in the Stage 5 source.

This boundary parallels the `ℝ_VR` inexpressibility in §VIII.6 of
VR-Numbers v1.0.2: both involve a countability restriction that is
meaningful in the preprint's operational universe but metatheoretic
from Lean's perspective.

**Observation B.2 (Second boundary: Replacement).**
`Theorem_III_7_Replacement` wraps mathlib's `ZFSet.replacement`. The
preprint §III.7 restricts replacement to *operationally definable*
functions. `ZFSet.replacement` takes a *Lean function* `F : ZFSet → ZFSet`
— the full class of Lean functions, not just describable ones. The
formalisation records the classical theorem (wider than the preprint),
with the boundary documented in a comment. The axiom dependency is
`Classical.allZFSetDefinable`, reflecting that «all Lean functions are
considered definable» is precisely the non-operational assumption.

**Observation B.3 (Third boundary: Choice).**
`Theorem_III_9_Choice` is proved via `Classical.choice`. The preprint §III.9
argues that AC is a theorem of *countable* VR-Sets: in a countable universe
a choice function can be constructed algorithmically. In Lean, `Classical.choice`
is a single axiom that applies universally — it does not specialise to
countable sets and does not produce an explicit algorithm. The preprint's
argument (countability → constructive choice) is metatheoretic. Lean records
AC as an axiom; it cannot express the countability restriction that would
make it a theorem.

Three boundaries in one direction: power set, replacement, choice — each
place where operational describability is lost in the classical Lean universe.

**Observation B.4 (Fourth boundary: Foundation, opposite direction).**
`Theorem_III_8_Foundation` holds unconditionally on `OSet = ZFSet` because
`ZFSet` is well-founded by construction: `PSet` is an inductive type, so
all elements are accessible. The preprint §IV presents Foundation as
*mode-dependent*: it holds in ZFC-mode but not in ZFA-mode (where cyclic
sets exist). In Lean, there is no ZFA-mode to speak of (see Observation B.5),
so Foundation is a universal theorem — but this is a *pre-commitment*,
not a generalisation. Lean's type theory pre-commits the entire universe
to ZFC-mode; the modal distinction of the preprint surfaces here not as
two parallel universes but as a single universe plus an explicit boundary
marker (`AFA_Refuted`, Stage 10) and a formulation of the opposite mode
as a conjecture (`Conjecture_IV_2_Statement`, Stage 11). The modal
analysis is not foreclosed — it is repositioned. This is a boundary
in the *opposite* direction from B.1–B.3: Lean is *narrower*, not wider.

**Observation B.5 (Fifth boundary: ZFA — total absence, type-theoretic).**
The ZFA-mode of VR-Sets (§IV.5–§IV.7) requires a universe of non-well-founded
sets where the Quine atom A = {A} exists and AFA holds. A systematic search
of all of mathlib4 for terms `AFA`, `AntiFoundation`, `non-well-founded`,
`coinductive` (for sets), `NonWellFounded`, and `Quine` returned **zero results**.
mathlib contains no AFA or coinductive set infrastructure.

More importantly, `PSet` is an *inductive* type in Lean 4:
```lean
inductive PSet : Type (u + 1)
  | mk (α : Type u) (A : α → PSet) : PSet
```
Lean's inductive types have a built-in well-founded recursion principle.
The direct consequence is `PSet.mem_irrefl : ∀ x : PSet, x ∉ x`. The
Quine atom would require `Q ∈ Q`, which contradicts `PSet.mem_irrefl`.
Therefore the Quine atom is *provably impossible* in PSet — not merely
hard to construct.

This yields the strongest result of the formalisation:

```lean
theorem quineAtom_impossible : ¬quineAtomSpec  -- axiom-free proof
theorem AFA_Refuted : ¬AFA_Statement            -- axiom-free proof
```

Both are proved with *no axioms* (`#print axioms` returns `[]`). The
proof of `AFA_Refuted` applies AFA to the universal self-loop graph
(V = Unit, E _ _ = True) and derives `f () ∈ f ()`, contradicting
`PSet.mem_irrefl`. No `propext`, no `Classical.choice`, no `Quot.sound`.

This boundary is categorically stronger than boundaries B.1–B.4:
- At B.1–B.3, Lean's object *exists* (as a classical entity) and is
  merely *wider* than the operational version.
- At B.4, the operational restriction is *absent*, but no inconsistency
  arises.
- At B.5, the ZFA-mode universe *provably does not exist* in mathlib's
  type hierarchy. Adding AFA as an axiom would be inconsistent with
  `PSet.mem_irrefl` already present in mathlib.

This is categorically stronger than the VR-Numbers §VIII.6 boundary at
`ℝ_VR`. There, classical `ℝ` existed in Lean and the computability
restriction was *metatheoretic* — an unexpressed condition on the type.
Here, the ZFA-mode universe has *no representation at all* in mathlib's
type hierarchy, and the impossibility is *constructively provable*
(axiom-free proof). The boundary moves from "metatheoretic" to
"structurally proven" — a stronger form of inexpressibility.

---

## §X.4 Axiom-Minimal Patterns

**Observation C.1 (Four faces of Classical.choice).**
`Classical.choice` enters the VR-Sets formalisation through four distinct
mechanisms — none of which is the direct application of AC to a set-theoretic
family:

| Theorem | Source of Classical.choice |
|---------|---------------------------|
| `Lemma_II_3_DepthMono` (rank) | `Ordinal.iSup` (supremum of ordinal-valued function) |
| `Theorem_III_7_Replacement` | `Classical.allZFSetDefinable` (all Lean functions are «definable») |
| `Theorem_III_8_Foundation` | `WellFounded.has_min` (existence of a minimal element) |
| `Theorem_III_9_Choice` | `Classical.choice` directly (AC on ZFSet families) |

This parallels VR-Numbers, where the boundary into `Classical.choice`
came primarily through a single structural place — mathlib's `Rat.add`
normalisation via `Nat.gcd` (VR-Numbers §VIII.4). In VR-Sets, by
contrast, the boundary is *distributed* across four mechanically distinct
sources, reflecting the broader algebraic surface of set theory compared
to number theory.

**Observation C.2 (Axiom profiles of formulations reflect structural nature).**
The two conjectures of Stage 11 have different axiom profiles:

```
Conjecture_IV_1_Statement : [propext, Quot.sound]
Conjecture_IV_2_Statement : []  (no axioms)
```

`Conjecture_IV_1_Statement` references `OSet.{0} = ZFSet.{0}` — a specific
mathlib quotient type — so it inherits `Quot.sound` from the quotient
construction and `propext` from membership on `ZFSet`. `Conjecture_IV_2_Statement`
is stated over abstract `(U : Type, mem : U → U → Prop)` — no reference to
any specific mathlib type — and is therefore axiom-free.

This is not an incidental technical difference. It reflects what the
conjectures *point to*: Conjecture IV.1 asks about a countable submodel
of a specific mathlib type (OSet); Conjecture IV.2 asks about the existence
of an abstract type with AFA structure — something *outside* the current
mathlib type hierarchy. The axiom profiles witness this structural distinction
at the level of dependency closures.

---

## §X.5 Methodological Convergences

**Observation D.1 (Replacement: schema → single theorem).**
In classical ZF, the Axiom of Replacement is a *schema*: one axiom instance
for each first-order formula φ(x, y) defining a functional relation. In
the preprint §III.7, replacement is stated as a single theorem (over all
operationally definable functions, where definability is built into the
operational semantics). In Lean 4, `ZFSet.replacement` is a single
polymorphic function: the schema is unified into one statement via function
quantification. This is a three-way convergence: classical ZF (schema),
operational VR-Sets (single theorem over describable functions), and Lean
(single theorem over all functions) all agree that replacement is not a
logical schema but a single closure principle — the classical version
merely lacks a mechanism to unify function
quantification.

**Observation D.2 (Three-tier formalisation result).**
VR-Numbers produced only *positive* results: theorems proved, isomorphisms
constructed. VR-Sets produces a structurally richer outcome:

| Category | Objects | Example |
|----------|---------|---------|
| Proved theorems | 16 | `Theorem_IV_1_ZFCAxioms`, `Theorem_V_2` |
| Refuted claims | 2 | `AFA_Refuted`, `quineAtom_impossible` |
| Open formulations | 2 | `Conjecture_IV_1_Statement`, `Conjecture_IV_2_Statement` |

The refuted claims are *structural boundary theorems*: they arise because
mathlib's type hierarchy cannot accommodate ZFA-mode, not because ZFA-mode
is logically inconsistent. The open formulations are the first instances in
the VR Lean cycle of a theorem-like object that the system records but
cannot resolve.

This three-tier structure is a consequence of the modal analysis of Parts IV:
any formalisation of a system that distinguishes modes (ZFC vs. ZFA) must
confront the question of which mode the formalisation framework itself inhabits.
Lean's type theory inhabits ZFC-mode by construction; VR-Sets is designed to
be mode-agnostic. The boundary between these is the primary finding of Stage 10.

---

## §X.6 Conclusion

The Lean 4 formalisation of VR-Sets demonstrates that the operational set
theory of Parts II–V is machine-verifiable, with no axioms beyond the standard
Lean ceiling `[propext, Classical.choice, Quot.sound]`. The formalisation
required no new axioms, no `sorry`, and no changes to mathlib.

The most significant finding — the axiom-free refutation of AFA and the Quine
atom specification (Observation B.5) — was not anticipated in the formalisation
plan. It arises from a structural property of Lean 4's inductive type system
(induction, not coinduction, for `PSet`) and represents the deepest boundary
between the operational VR-Sets universe and classical Lean's type hierarchy.

The Lean formalisation generated seventeen methodological observations
across thirteen stages; the ten presented in §X.2–§X.5 are those most
directly bearing on the relationship between operational and
type-theoretic foundations. The remaining seven (technical details of
axiom inheritance, mathlib API quirks, and intermediate steps) are
documented in the source comments of the formalisation. Together, they
document not only what was proved, but what could not be proved, why, and
what the corresponding structural boundary implies for the relationship
between operational set theory and classical type-theoretic foundations.

---

*Lean 4 formalisation repository: VRCycle, tag v1.2-vr-sets.*
*Zenodo Software DOI: 10.5281/zenodo.20354340.*
*Lean toolchain: v4.29.1 + mathlib v4.29.1.*
