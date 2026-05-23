# **IX.0. Introduction**

The present part documents the Lean 4 formalisation of the two-register apparatus of VR-Forms (Parts II–IV and §VII.2 of the present preprint), carried out after the publication of v1.0.0 and presented as a self-contained companion software publication (Reznik 2026, Lean VR-Forms, Software DOI 10.5281/zenodo.20355757; Git tag v1.3-vr-forms). The formalisation realises the apparatus as a shallow embedding over mathlib and surfaces a single explicit structural boundary at conservativity (Theorem III.1).

Part IX is the fourth such methodological-observations part in the VR cycle, following Part VIII of VR-Numbers v1.0.2 and Part X of VR-Sets v1.0.1. Its function is the same: not to introduce new mathematical content, but to record what the formalisation made visible — observations about the structural relationship between the preprint's apparatus and Lean's proof-theoretic infrastructure.

Ten observations are presented in four thematic clusters. §IX.1 collects two observations on foundation-level properties of the formalisation. §IX.2 collects five observations centred on the central structural boundary of the cycle (conservativity) and its four substructural manifestations. §IX.3 collects two observations on structural patterns in the apparatus. §IX.4 closes with two cross-cycle observations, including the finale on zero Classical.choice usage. §IX.5 summarises the comparison with the boundaries documented in VR-Sets Part X.

Methodologically, Part IX resolves Question 1 of §VIII.1 («Formalisation in Lean/Coq/Agda») of the present preprint for the formalisable core (the two-register apparatus); the central boundary at conservativity is documented but not crossed. The Lean formalisation is also accessible directly: each observation has a corresponding source location in the Lean code documented in comment form.

# **IX.1. Foundation-level properties**

### **Observation 1: foundation file is import-free and axiom-free**

The foundation file `Forms/Language.lean` introduces the syntactic skeleton of the apparatus (the `Register` inductive type, the `FormalTerm` structure, the notation `⌜·⌝`) without importing any mathlib or VR-Sets module. `String` and inductive/structure constructions are part of the Lean 4 prelude. The axiom profile is empty `[]` for both `Register` and `FormalTerm`.

This contrasts with the foundation files of VR-Numbers and VR-Sets Lean. `Numbers/Foundation.lean` imports mathlib's natural number infrastructure; `Sets/Foundation.lean` imports mathlib's `ZFSet` and inherits `[propext, Quot.sound]` for every theorem. The contrast reflects the deliberate architectural choice of shallow embedding in VR-Forms: formal terms are syntactic metadata, not mathematical objects in mathlib's hierarchy.

The methodological consequence is structural. The base layer of VR-Forms is the most axiom-minimal foundation of the four cycles; any axiom dependency in subsequent stages arrives **through** the connection to VR-Sets (which carries `propext` and `Quot.sound` from the ZFSet quotient), not through the formal-term apparatus itself.

### **Observation 2: realisability inherits the Classical-free closure layer of VR-Sets**

The predicate `isRealisable : FormalTerm → Prop` is defined in `Forms/Realisability.lean` via `match` on `FormalTerm`, with cases for the realisable terms `⌜∅⌝`, `⌜omega_OSet⌝`, `⌜osetPair⌝`, plus VR-Sets-refutable `⌜AFA_Statement⌝`, plus the open Conjecture cases (added retroactively in Stage 4), plus a catch-all `False`. All four base realisability lemmas sit at `[propext, Quot.sound]`, with **no Classical.choice**.

The structural reason is direct. The realisable cases (∅, ω, pair) correspond to Theorems III.1–III.3 and Theorem III.6 of VR-Sets, which are Classical-free closure theorems. The realisability layer of VR-Forms is structurally tied to the Classical-free closure layer of VR-Sets — realisability of operationally well-defined terms inherits exactly the axiom dependency of their closure proofs.

Realisable terms tied to *Classical* VR-Sets theorems (replacement, choice, foundation) would inherit `Classical.choice`. No such terms appear in the present formalisation; this is consistent with the preprint's position that the operationally well-defined VR objects (∅, ω, pair) form the cycle's realisable core, while constructions essentially using Classical infrastructure remain formal terms without realisation.

# **IX.2. The central boundary and its substructural manifestations**

The defining feature of VR-Forms Lean is its **single explicit structural boundary** at conservativity. This contrasts with VR-Sets Lean, which surfaced five distinct boundaries between the operational universe and mathlib's set-theoretic infrastructure. The VR-Forms boundary is methodologically different: it sits at the proof-theoretic meta-level (between shallow and deep embedding), not at the mathematical-content level (between operational and classical sets).

§IX.2 documents the central boundary (one observation) and four substructural manifestations encountered in the formalisation (four observations).

### **Observation 3: conservativity (Theorem III.1) is the explicit structural boundary**

Theorem III.1 of the present preprint (§III.2) — the conservativity of T₁ over T₀ in the ontological register — is **not** formalised in the Lean cycle. Instead, it is documented as the explicit structural boundary, with verbatim citation in the doc-comment of `Forms/Transit.lean`.

The reason is architectural. Full formalisation of conservativity would require deep-embedded `Formula L₁`, `Derivation T₀`, `Derivation T₁` types, the translation π as a function on the formula syntax, and an induction proof over derivations. This is a proof-theory project larger than the entire VR-Sets Lean cycle, and would shift the formalisation's role from «Lean library reflecting the preprint» to «Lean library *about* proof theory». The decision is documented in the Lean cycle's `CLAUDE.md` and `PLAN.md`, with three alternatives (full deep embedding, shallow embedding making conservativity trivial, partial formalisation with explicit boundary) discussed before the cycle began.

The methodological position is honest: conservativity is **mathematically proved** in the preprint (§III.2 gives the full inductive proof via the translation π), but **Lean-unformalisable** at the shallow-embedding depth chosen here. This is distinct from open conjectures, which are mathematically open rather than formalisation-limited. The Lean cycle records this distinction by *not* introducing a `def Conjecture_Conservativity : Prop` — such a definition would misrepresent the result as open to Lean attack, when in fact it is proved (just outside the shallow apparatus).

The transit pattern (§IV.2) is documented as an inference template in `Forms/Transit.lean`, not formalised as a Lean theorem. The conservativity justification flows through external reference to the preprint's §III.2 proof.

### **Observation 4: equation-compiler catch-all does not reduce in term mode**

The first substructural manifestation of the boundary is technical. The function `translate_pi : FormalTerm → Prop`, defined via `match` with named cases plus a catch-all `| _ => False`, does **not** reduce `translate_pi x` to `False` in term mode for an arbitrary `x : FormalTerm`. The reduction is blocked by the equation compiler's schematic-variable representation of the catch-all: the term `translate_pi x✝` (where `x✝` is the catch-all's schematic variable) stays unreduced even when the user knows that `x` is not one of the named cases.

The working proof structure (used in `translate_implies_realisable`) is `by_cases` discrimination on the named constructors — which `DecidableEq FormalTerm` makes possible without Classical.choice — followed by `unfold translate_pi; split <;> simp_all [FormalTerm.mk.injEq]` in the residual catch-all branch. The fix costs zero new axioms but requires explicit case structure.

The observation parallels the proof technique in VR-Sets Stage 8, where `Classical.epsilon` had to be applied with `eq_empty_or_nonempty` case-split to make reduction work. Both cases share the same structural fact: Lean's pattern matching requires explicit case discrimination at the boundary between abstract scrutinee and concrete reduction.

### **Observation 5: realisability and π-translation form complementary layers**

The second substructural manifestation: `isRealisable` (existential — «term has operational witness») and `translate_pi` (specific — universal-quantified statement about a named VR-Sets object) form two complementary layers in the Lean apparatus, connected by `translate_implies_realisable : ∀ t, translate_pi t → isRealisable t` via existential introduction.

The preprint §II.7 / §III.2 conflates the two notions (operational realisability and π-translation are presented as aspects of the same apparatus). The Lean formalisation separates them, and only the forward direction (specific → existential) is proved. The converse (existential → specific) is **not** provable from the existential alone: from «there exists some operational witness» one cannot extract «the specific witness `osetEmpty`» without Skolemisation, which is not available from the existential in the shallow embedding. The transit pattern of §IV.2 operates exclusively in the forward direction, which is structurally consistent.

This separation is the formal content of what the preprint calls «the transit pattern operating forward»: from an operational truth about a specific VR-Sets object (the π-translation), the realisability of the corresponding formal term follows.

### **Observation 6: two-level structure of negative cases**

The third substructural manifestation concerns non-realisability. The Lean formalisation distinguishes **two levels** of non-realisable formal terms.

**Level 1 (trivially False).** For «mythological» terms — those without mathematical formulation in VR-Sets — the proof is `id`: `¬isRealisable ⌜"Vitali"⌝ := id`, `¬isRealisable ⌜"Russell_class"⌝ := id`, and so on. The catch-all `| _ => False` redirects all unnamed terms to `False`, and negation is trivial. These four theorems (Russell, Vitali, classical ℝ, classical ℘(ℕ)) are in `Forms/Examples.lean`. The proof carries no VR-Sets mathematical content; non-realisability is by *absence from the realisability list*.

**Level 2 (VR-Sets-refutable).** For `⌜AFA_Statement⌝`, the case is different. The match returns `VR.Sets.AFA_Statement` (a Prop with mathematical formulation in mathlib's PSet inductive structure). The bridge theorem `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝ := AFA_Refuted` (in `Forms/Bridge.lean`) is a direct application of `AFA_Refuted` from VR-Sets Stage 10. Non-realisability carries genuine mathematical content: AFA contradicts the well-foundedness of PSet.

The two-level structure formalises a distinction implicit in the preprint between «paradoxical descriptions without operational correlate» (Russell, Vitali) and «descriptions whose negation has independent mathematical content» (AFA). The latter category is rarer but methodologically more substantial.

### **Observation 7: three-category structure of formal terms**

The fourth substructural manifestation. The bridge module surfaces a triadic classification of formal terms by realisability status:

— **(a) Provably realisable** — Stage 2 lemmas with concrete witnesses (`isRealisable_empty`, `isRealisable_omega`, `isRealisable_osetPair`). The realisable list is closed and explicit; each entry corresponds to a closure theorem of VR-Sets.

— **(b) Open realisability** — Conjecture formal terms (`bridge_Conjecture_IV_1`, `bridge_Conjecture_IV_2`). The bridge `iff` is trivially provable by definitional reduction, but the content (whether the conjecture holds) is mathematically open. Both directions of the `iff` reduce to `id`.

— **(c) Provably non-realisable** — split into the two levels of Observation 6.

The triadic structure parallels VR-Sets Stage 11's three-tier formalisation result (proved theorems, refuted claims, open formulations), but localised at the level of formal terms rather than at the level of mathematical claims. The bridge module thus inherits and refines the VR-Sets tier structure within the formal register of VR-Forms.

# **IX.3. Structural patterns**

### **Observation 8: universe handling across cross-cycle boundaries**

Two distinct universe-management issues surfaced in the formalisation; both arise from the cross-cycle nature of VR-Forms.

**Issue (a)** — Stage 2. In the body of `def isRealisable`, references to `OSet` require the explicit annotation `OSet.{0}`. Without it, Lean cannot infer the universe level when `OSet` is the codomain of a `match`-induced quantification. The issue is namespace-related: inside `namespace VR.Sets`, surrounding context fixes the universe; inside `namespace VR.Forms` with `open VR.Sets`, the universe must be pinned explicitly.

**Issue (b)** — Stage 5. Projecting `.1` from `Theorem_III_6_Infinity` (a two-universe `{u v}` signature inherited from `ZFSet/PSet` interaction) generates universe metavariables outside the defining namespace. The workaround is to use `translate_pi_omega.1` instead, whose match-case pins `OSet.{0}` and makes the projection unambiguously typed.

Both issues point to the same architectural fact: VR-Forms is structurally a *cross-cycle* module, and Lean's universe inference does not propagate cleanly across cycle boundaries without explicit annotation. This is a mathlib/Lean 4 idiosyncrasy, not a logical issue — but it costs care in implementation, and it is the first such cross-namespace technical concern in the VR Lean programme.

### **Observation 9: ZFA boundary manifests simultaneously in both registers**

The Lean finale theorem `mixed_AFA_boundary` (in `Forms/Examples.lean`) captures, in a single Lean Prop, the parallel manifestation of well-foundedness across the two registers of VR-Forms:

```
theorem mixed_AFA_boundary :
    (∀ x : OSet.{0}, x ∉ x) ∧ ¬isRealisable ⌜"AFA_Statement"⌝ :=
  ⟨ZFSet.mem_irrefl, bridge_AFA⟩
```

Ontologically: `∀ x : OSet, x ∉ x` — regularity, via `ZFSet.mem_irrefl`. Formally: `¬isRealisable ⌜"AFA_Statement"⌝` — non-realisability of the AFA formal term, via `bridge_AFA`. Both sides derive from the inductive nature of mathlib's `PSet`, and surface the same structural fact (well-foundedness of mathlib's set-theoretic infrastructure) through different conceptual layers.

This is the most mathematically substantive mixed formula of the VR-Forms cycle and the structural counterpart to VR-Sets's Stage 10 boundary B.5 («ZFA total absence»). What appeared in VR-Sets Part X as the deepest *structural* boundary appears in VR-Forms Lean as a *theorem* with cross-register content — the same architectural fact, now formulated in the apparatus that VR-Forms provides for talking about both registers at once.

# **IX.4. Cross-cycle integration**

### **Observation 10: zero Classical.choice usage across the entire cycle**

The final observation closes the cycle. The original cycle plan (`PLAN.md` of the Lean repository) predicted that the public objects of VR-Forms Lean would sit at `[propext, Classical.choice, Quot.sound]` or stricter — admitting some Classical use. The actual result, verified by `#print axioms` for every public object, is stricter than predicted:

| File | Public objects | Axiom profile |
|---|---:|---|
| Language.lean | 3 | `[]` empty |
| Realisability.lean | 4 | `[propext, Quot.sound]` |
| Transit.lean | 5 | `[propext, Quot.sound]` |
| Bridge.lean | 3 | `[propext, Quot.sound]` |
| Examples.lean | 6 | `[propext, Quot.sound]` |

Eighteen public objects total. Three are axiom-free (Stage 1). Fifteen sit at `[propext, Quot.sound]`. **Zero objects require Classical.choice.**

This contrasts sharply with the predecessor cycles. VR Part I and VR-Numbers Lean each contain several objects depending on Classical infrastructure; VR-Sets Lean has six of twenty-two objects at the full ceiling `[propext, Classical.choice, Quot.sound]`, through four structurally distinct Classical mechanisms (ordinal-valued constructions, definability, foundation, choice).

The structural reason is direct. The realisable cases of VR-Forms correspond to the *Classical-free* closure theorems of VR-Sets (Observations 1 and 2); the non-realisable cases either reduce trivially (Russell, Vitali via `False`) or use `AFA_Refuted` (Classical-free, proved via inductive PSet reasoning). No formalisation step in VR-Forms requires a Classical mechanism, because the formalisable apparatus operates entirely within the operationally well-behaved subset of VR-Sets.

The observation reflects the nature of the present preprint: a *formal language* for the non-operational, not a substantive mathematical theory. The Lean formalisation, when carried out at the chosen depth, lives entirely within Lean's constructive-plus-quotient core.

# **IX.5. Comparison with VR-Sets Part X**

The structure of boundaries in VR-Forms Lean differs methodologically from VR-Sets Lean (documented in Part X §X.3 of VR-Sets v1.0.1).

**VR-Sets** surfaced **five** structural boundaries between the operational universe and mathlib's set-theoretic infrastructure (B.1 powerset cardinality, B.2 replacement schema, B.3 foundation modes, B.4 ZFA modal status, B.5 ZFA total absence). Each boundary is a gap in mathematical content — what the preprint claims about the operational universe versus what mathlib provides in its type-theoretic infrastructure.

**VR-Forms** surfaces **one** structural boundary at conservativity. The boundary is at the proof-theoretic meta-level (between shallow and deep embedding), not at the mathematical-content level. The four observations of §IX.2 are not separate boundaries but substructural manifestations of the single central boundary in different aspects of the formalisation.

The shift in structure — from five mathematical-content boundaries to one proof-theoretic boundary with four manifestations — reflects the shift in subject matter. VR-Sets formalises a set theory; its boundaries are about what mathlib's sets can and cannot do. VR-Forms formalises a *language for talking about sets*; its boundary is about what the shallow embedding can and cannot say about its own metatheory.

Both cycles arrive at axiom-minimal results, but through different routes. VR-Sets achieves axiom-minimality by *navigating* the boundaries (proving theorems despite mathlib's structural mismatches); VR-Forms achieves axiom-minimality by *staying entirely on the shallow side* of its single boundary.

# **IX.6. Summary of Part IX**

Ten observations have been documented:

(1) Foundation file is import-free and axiom-free; the most axiom-minimal foundation of the four VR Lean cycles. (§IX.1)

(2) Realisability inherits the Classical-free closure layer of VR-Sets; no realisable case requires Classical.choice. (§IX.1)

(3) Conservativity (Theorem III.1) is the explicit structural boundary — mathematically proved in the preprint, Lean-unformalisable at shallow depth, documented in `Transit.lean`. (§IX.2)

(4) Equation-compiler catch-all does not reduce in term mode; `by_cases + unfold + split + simp_all` is the zero-axiom fix. (§IX.2)

(5) `isRealisable` (existential) and `translate_pi` (specific) form complementary layers; forward implication is the formal content of the transit pattern. (§IX.2)

(6) Two-level structure of negative cases: trivially False (Vitali, Russell) vs VR-Sets-refutable (AFA via `AFA_Refuted`). (§IX.2)

(7) Three-category structure of formal terms: provably realisable, open realisability, provably non-realisable. (§IX.2)

(8) Universe handling across cross-cycle boundaries — `OSet.{0}` annotation and `translate_pi_omega.1` projection workaround. (§IX.3)

(9) ZFA boundary manifests in both registers simultaneously; `mixed_AFA_boundary` formalises this as a single Lean Prop. (§IX.3)

(10) Zero Classical.choice usage across the entire cycle — the most axiom-minimal of the four VR Lean cycles. (§IX.4)

The full Lean source is at https://github.com/inventor1975/VRCycle (tag v1.3-vr-forms); each observation has a corresponding source location documented in Lean comments.

**Methodological summary.** The formalisation realises in Lean exactly the apparatus that VR-Forms is — a shallow, operationally minimal, axiom-light layer over VR-Sets, with one explicit structural boundary at the place where it would have to become a proof-theory project. The boundary is honest, the apparatus on the formalisable side is complete, and the cycle as a whole is the most axiom-minimal of the four VR Lean formalisations.

**What this resolves.** Question 1 of §VIII.1 («formalisation in Lean/Coq/Agda») is now answered for the formalisable core. Question 2 («precise strength of the translation π») receives a partial answer: in the shallow embedding, π is total and exact for the named realisable cases. Question 3 («composition of transits») is not addressed in the formalisation — the transit pattern is documented but not compositionally analysed. The full conservativity formalisation (Question 1 in its strict sense) remains the structural boundary.

**What follows.** The VR cycle in its current form — four works with four Lean formalisations — closes the planned ontological contour. The next directions, sketched in §VIII.2 of the present preprint, are VR-Audit (the direct application of the present apparatus to classical mathematics), VR-Categories, and VR-Physics. The Lean cycle of VR-Forms, by realising the formalisable core of the apparatus, prepares the technical infrastructure for VR-Audit: the bridge module and the transit pattern are the working tools through which classical theorems can be systematically classified.
