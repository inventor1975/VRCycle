# VR-UNIQUENESS.md

**Purpose**: catalogue of specific facts about VR programme. Compass for
positioning, not publication. Items added, revised, or removed as evidence
accumulates. Each fact testable against reality.

**Author**: Vitaly Reznik.

**Working with**: Claude Opus 4.7 (architect), Claude Sonnet 4.6 (implementer).

**Started**: 26 May 2026.

**Last updated**: 26 May 2026.

---

## How this file is used

- **Demonstrated facts** — verifiable claims. Object counts, axiom profiles,
  formal proofs. If contested, point to evidence.
- **Unique combinations** — features each individually existing elsewhere,
  combined in VR uniquely.
- **Methodological signatures** — patterns specific to VR development.
- **Open positioning** — aspirational claims not yet validated. Marked
  explicitly as such. Internal compass, not external claim.
- **Honest gaps** — what VR lacks. Counterweight to prevent overclaim.

Items can move between categories as evidence shifts. Demonstrated facts can
be demoted to gaps if found wrong. Open positions can promote to demonstrated
if validated. Recognition discipline applies — remove items that fail.

---

## 1. Demonstrated facts

Verifiable, concrete, externally defensible.

### Foundation

- **3 primitives, 4 axioms**: VR formal system has {∅, →, t} as primitives
  and four axioms (A1, A2, A3, A4). Documented in VR (A Formal System)
  preprint, DOI 10.5281/zenodo.20324391.

- **PA-equivalence**: VR arithmetically equivalent to Peano arithmetic.
  Proved formally in VR Lean formalisation (DOI 10.5281/zenodo.20324240).
  Consistency relative to ZF follows.

- **Equality by Leibniz**: equality defined as `x = y := ∀p, p(x) ↔ p(y)`,
  not primitive. Documented in VR formal system.

- **von Neumann ordinals constructed**: O₀ = ∅, O_{n+1} = t(O_n) = O_n ∪ {O_n}.
  Standard construction from VR primitives.

### Set theory

- **VR-Sets foundation**: set theory built on VR primitives, ZFC-equivalent
  via formal embedding. DOI 10.5281/zenodo.20354340 (Lean), 10.5281/zenodo.20354628 (preprint).

- **AFA as theorem**: in VR-Sets-ZFA, Anti-Foundation Axiom derived
  via coinductive M-construction, not postulated. Machine-verified.
  DOI 10.5281/zenodo.20368268 (Lean), 10.5281/zenodo.20369346 (preprint).

- **Quine atom machine-verified**: existence of q = {q} formally proved
  in VR-Sets-ZFA.

- **Membership as reference, not containment**: in VR-Sets, `x ∈ y`
  interpreted as `y references x by name`, not `y contains x as
  ontological component`. Documented in VR-Sets preprint.
  DOI 10.5281/zenodo.20303536.

- **`x ∈ x` operationally meaningful without separate axiom**: with
  reference semantics, set referencing itself is name pointing back
  to itself — operationally legitimate. ZFC forbids via Foundation
  axiom; ZFA postulates via Anti-Foundation axiom; VR dissolves the
  question — reference interpretation makes self-reference natural
  without new axiom. Russell paradox separately dissolved (contradictory
  description, not specifically about self-membership).

### Apparatus

- **Two apparatus modes formalised**: PredicateOperationality and
  ReferenceOperationality as Lean typeclasses. VR-Apparatus v1.0.0,
  DOI 10.5281/zenodo.20380344.

- **Mode A and Mode B distinction**: Mode A = closure under operations,
  Mode B = classical operations yielding operational results via witness.
  Both as Lean predicates.

- **Apparatus reuse confirmed**: Finding A3 from Operational Algebra v0.1.0
  — VR-Apparatus framework applies to algebraic structures without modification.
  Zero-field marker instance mechanism.

- **Three-tier axiom hierarchy demonstrated**: typeclass [], ℤ [propext],
  ZMod [propext, Quot.sound], analysis adds [Classical.choice]. Finding A5.

### Cycle scope

- **14 Zenodo records published**: 7 works × 2 (Lean + preprint).

- **Operational Algebra v0.1.0 on GitHub**: 8th work, 31 public objects,
  tag v1.8-vr-operational-algebra-v0.1.0. Pending Zenodo until v1.0.0.

- **~100+ public Lean objects across cycle**: VR (formal system),
  VR-Numbers, VR-Sets, VR-Forms, VR-Audit, VR-Sets-ZFA, VR-Apparatus,
  Operational Algebra v0.1.0.

- **Eleven-day initial cycle**: VR foundation through VR-Apparatus (7 works,
  14 Zenodo records) developed 15-25 May 2026.

---

## 2. Unique combinations

Each feature exists in some other programme. The **combination** appears
unique to VR.

### Foundation depth + apparatus layer

- **What it is**: VR has both a foundational level (sets derived from
  3 primitives) and an apparatus level (operational tracking on top).

- **Other programmes**:
  - Bishop: constructive content, no foundation contribution.
  - Weihrauch: computability focus, classical foundation.
  - Proof mining: post-hoc analysis, no foundation contribution.
  - HoTT: foundation only, no apparatus tracking.
  - ZFA: non-well-founded sets, no apparatus.
  - Mathlib: extensive content, no operational apparatus layer.

- **VR**: foundation + apparatus combined explicitly, formalised in same
  Lean codebase.

### AFA derived as theorem in operational set framework

- **What it is**: Anti-Foundation Axiom obtained via coinductive M-construction
  within VR-Sets-ZFA, not postulated.

- **Other programmes**: ZFA, SAFA, Boffa's axiom, FAFA — all postulate
  some anti-foundation principle.

- **VR**: derives AFA from operational set construction. Machine-verified.

### Apparatus as Lean typeclasses (layered, not metalanguage)

- **What it is**: apparatus discipline implemented as typeclass hierarchy
  in Lean 4, with instance search corresponding to apparatus lookup.

- **Other programmes**:
  - Bishop: informal practice, not in proof assistant.
  - Weihrauch: some formalisation, not as layered apparatus typeclasses.
  - Proof mining: mostly informal, recent Lean work emerging.
  - Mathlib: classical, no operational apparatus layer.

- **VR**: 68 public Lean objects in VR-Apparatus v1.0.0 demonstrate
  apparatus as typeclasses. Reused without modification in Operational
  Algebra (Finding A3).

### Recognition discipline as catalogued pattern

- **What it is**: documented practice of removing abstractions when
  recognised as unnecessary. Applied three times: Finding F11 (VR-Apparatus,
  generic Register), Finding A0 (Operational Algebra, multiplicative
  OperationalGroup), Finding A6 (Operational Algebra, bundled subgroup
  structure).

- **Other programmes**: similar discipline informal in mathematical practice,
  but not explicitly catalogued as method.

- **VR**: pattern documented across three concrete cases with explicit
  references between them.

### AI-augmented development at this scale

- **What it is**: 8 works (7 preprints + 8 Lean formalisations) developed
  in approximately 12 days with documented Variant A AI workflow.

- **Other programmes**: no other foundational mathematics programme has
  documented this scale and pattern of AI-assisted formalisation
  (as of May 2026).

- **VR**: methodology contribution independent of mathematical content.

### Precise ontological account of 1 (and other natural numbers)

- **What it is**: VR provides explicit ontological definition of 1 as
  `1 = t(∅)` — the unique result of applying the unique successor operation
  to the unique ontological primitive. Necessity, not convention. Each
  natural number `n` is `t^n(∅)` — trace of `n` applications of `t` to `∅`.

- **Other programmes**: ZFC defines 1 = {∅} (von Neumann) by convention;
  alternative encodings (Zermelo: 1 = {{∅}}) equally valid. Peano takes
  successor as primitive without ontological account. Category theory:
  1 = terminal object, structural not ontological. The criticism that
  "mathematics has no account of what 1 is" (cf. physicists' observation,
  e.g. Semikhatov) applies to standard foundations.

- **VR**: 1 is not a thing but a trace of action — first application of
  the unique operation to the unique primitive. Ontologically minimal:
  only `∅` exists; everything else is `doing`. Each natural number has a
  unique unambiguous construction; no arbitrary encoding choice.

- **Philosophical position**: "only ∅ is, everything else is doing" — slogan
  carries through programme. 1 specifically isolated as the simplest case
  where convention vs necessity distinction is visible.

---

## 3. Methodological signatures

Patterns developed and applied consistently across VR cycle.

### Variant A workflow

- Opus as architectural reviewer.
- Sonnet as implementer.
- Author retains methodological authority.
- Plan-before-code discipline per stage.
- Stage reports with axiom audits.
- Findings catalogued, not discovered ad hoc.

### Word-first formulation

Mathematical content formulated in words before Lean encoding. Forces
clarity about what is being built and why. Reduces formalisation as
exercise in symbol manipulation.

### Recognition rather than invention

Abstractions emerge from concrete content, not posited before content
exists. Generic structures removed when no instances arise. Three
catalogued applications (F11, A0, A6).

### Axiom audit as discipline

Every public Lean object receives `#print axioms` audit. Axiom profile
documented per object, ceiling per file. Findings drawn from axiom
asymmetries (A1, A4, A5).

### Honest scope discipline

When difficulty encountered, documented and adjusted rather than forced.
When ambition exceeds achievable, scope reduced explicitly. Visible in
VR-Apparatus Stage 6 (Mode B deferred to skeleton example) and
Operational Algebra Stage 5 (predicate over structure).

---

## 4. Open positioning

Aspirational claims, not yet externally validated. Internal compass.
**Not** external claims until evidence supports.

### "VR is the only universal foundational system currently available"

- **Status**: author's working conviction (compass). Not externally argued.
- **What would validate**: peer engagement with foundational community,
  comparison of VR to HoTT, type theory, set theory on universality
  criteria explicitly defined.
- **What would refute**: identification of feature VR cannot express
  that other foundations can.

### "Apparatus is general methodology applicable across all mathematics"

- **Status**: demonstrated in 2 domains (analysis, algebra). Conjectured
  for others.
- **What would validate**: successful apparatus instances in topology,
  category theory, model theory, logic.
- **What would refute**: domain where apparatus framework requires
  fundamental modification or fails.

### "VR programme efficient for foundational research"

- **Status**: 8 works in ~12 days documented. Speed enabled by AI assistance.
- **What would validate**: another foundational researcher achieving
  comparable rate with apparatus methodology.
- **What would refute**: speed turns out to be AI-specific, not
  apparatus-related.

### "VR-Sets-ZFA improves on standard ZFA"

- **Status**: VR-Sets-ZFA derives AFA, has operational interpretation,
  Lean-formalised. ZFA has 35 years of literature, mature applications.
- **What would validate**: VR-Sets-ZFA used for actual mathematical work
  (process algebra, coalgebra, modal logic) producing results.
- **What would refute**: applications stay confined to ZFA tradition,
  VR-Sets-ZFA remains formalisation exercise.

### "VR operates on operational infinity through DC; actual infinity and full AC are operational acts of description without operational correlates"

- **Status**: philosophical position emerging from VR programme structure.
  Operational infinity (A4 as process principle) is the substrate of
  **everything**, including descriptions of actual infinity. Every
  description is an operational act; the difference lies in what the
  description references. Descriptions of operational objects (∅, t(∅),
  computable sequences) have operational correlates. Descriptions of
  actual infinity (⌜℘(ℕ)⌝, ⌜c⌝, ⌜full AC⌝) are operational acts of
  description without operational correlates.
- **DC vs full AC**: DC (process-based choice) unfolds along A4 —
  description AND correlate both operational. Full AC (simultaneous
  selection from uncountable family) — operational act of description,
  but correlate not operational (requires completed totality that VR
  ontology does not provide).
- **Inheritance**: structurally identical к author's earlier pseudo-infinity
  (פ) framework (ZF + DC, boundary at full AC). Not currently cross-referenced
  in published preprints — integration gap identified.
- **Philosophical content**: expanded position — **everything is
  operational**, including descriptions of non-operational referents.
  The distinction is not between "operational register" and "formal
  register" as different levels of reality; the distinction lies in
  whether a description has an operational correlate. Distinct from
  Bishop (rejects descriptions without correlates), classical (treats
  all descriptions as having referents in full ontology), reverse
  mathematics (measures axiom strength). VR position: all descriptions
  are operational; some descriptions have operational correlates, some
  do not; the distinction matters structurally but does not divide
  ontology into parts.
- **What would validate**: dedicated preprint articulating expanded position
  precisely, with Lean evidence; engagement with constructive math community.
- **What would refute**: shown that VR's operational infinity actually
  presupposes actual infinity in some formulation; or that expansion of
  operational к include descriptions of non-operational referents makes
  the position too broad for defensibility.

### "Cantor's diagonal does not work in VR (no actual infinity); works in ZF (Power Set axiom); does not work in Bishop"

- **Status**: structural observation flowing from operational/actual infinity
  boundary. In ZF, Power Set axiom postulates ℘(ℕ) as completed totality;
  diagonal selects element from completion, proving uncountability. In VR-Sets,
  no Power Set axiom; ℘_VR(ℕ) is countable operational subsets; diagonal
  construction requires effective enumeration of describable subsets, equivalent
  to halting problem, not operational. In Bishop's constructive analysis,
  diagonal as uncountability proof rejected — actual infinity not in ontology.
- **Position alignment**: VR aligns с Bishop on diagonal (both reject as
  uncountability proof). VR distinct from ZF (which has Power Set axiom
  enabling diagonal). AC orthogonal — diagonal works in ZF без C, fails in
  VR regardless of choice axioms.
- **Philosophical content**: actual infinity is the prerequisite, not AC.
  Cantor's diagonal isolates Power Set's contribution к classical mathematics.
  Removing Power Set (operational substrate) breaks diagonal-as-uncountability
  even before choice axioms enter picture.
- **Connection к VR-Forms**: in formal register, ⌜℘(ℕ)⌝ is formal term;
  "⌜℘(ℕ)⌝ is uncountable" admissible formally. Skolem's paradox dissolves
  as register distinction (VR-Forms §V.2 documents this for ℘(ℕ); diagonal
  observation parallel).
- **What would validate**: explicit treatment в dedicated preprint on
  operational/actual infinity boundary, including Cantor's diagonal as
  illustration; comparison с Bishop articulated.
- **What would refute**: shown that operational substrate admits some
  diagonal-like argument proving uncountability of some operational
  collection; or shown Power Set axiom not essential к Cantor's diagonal.

### "Continuum hypothesis dissolves in VR ontology, remains in formal register"

- **Classical status**: CH is independent of ZFC (Gödel 1940 — negation
  undisprovable; Cohen 1963 — CH unprovable via forcing). Independence
  is the resolution within classical framework: choose model with CH
  or without CH.
- **VR ontological position**: CH presupposes actual infinity и multiple
  uncountable cardinals (ℵ₀, c, possibly intermediate). VR ontology has
  no actual infinity, no uncountable continuum (ℝ_VR is countable
  computable reals, |ℝ_VR| = ℵ₀), no Power Set axiom. Question "is there
  cardinal between ℵ₀ and c" not formulable operationally — c as
  uncountable cardinal not in ontology.
- **VR formal register treatment**: ⌜ℝ⌝ (classical), ⌜℘(ℕ)⌝, ⌜c⌝ all
  formal terms. CH formulable formally: "no cardinal between ⌜ℵ₀⌝ and
  ⌜c⌝". This is formal statement without ontological correlate.
  Conservativity (VR-Forms Theorem III.1) ensures CH в formal register
  does not affect ontological register.
- **Distinct framing across foundations**:
  - **ZFC**: CH undecidable, choose model.
  - **Brouwer / Bishop**: CH meaningless — no uncountable in ontology.
  - **VR**: CH **simultaneously** dissolved ontologically AND meaningful
    formally — two-register apparatus makes both readings consistent.
- **Pattern**: same operational/actual infinity boundary as Cantor's
  diagonal (Power Set absence) and AC/DC. CH is third instance of the
  same structural pattern. Three pillars of classical set theory
  (uncountability via diagonal, full AC, CH) all dissolve в VR ontology
  via same mechanism (no actual infinity); all remain formally meaningful
  through two-register apparatus.
- **What VR contributes к CH discussion**: not solution, not rejection —
  reframing. CH ceases to be open question (within VR ontology) and
  becomes formal-register statement (within VR formal apparatus).
  Independence result (Gödel/Cohen) becomes irrelevant — independence
  presupposes formal derivation framework where CH meaningful; VR
  dissolves the precondition.
- **What would validate**: dedicated preprint articulating VR's treatment
  of CH explicitly; engagement с set theorists working on continuum
  questions.
- **What would refute**: shown that VR ontology actually admits CH
  formulation operationally; or shown that classical CH independence
  result has stronger structural consequences VR cannot dismiss.

### "VR belongs to the class of constructively self-exhibiting arithmetics"

- **Class definition**: arithmetics whose consistency is exhibited
  structurally through construction itself, not derived via formal
  Gödel-style internal proof. Members:
  - Brouwer's intuitionistic arithmetic.
  - Heyting arithmetic (formalisation of Brouwer).
  - Bishop's constructive arithmetic.
  - Martin-Löf type theory arithmetic.
  - **VR** (operational instance).
- **Position**: each VR axiom emerges as operational consequence of the
  ontological setup. ∅ is the minimum (existence trivial); t is the unique
  possible operation on ∅; A1 (duality) derives from ∅'s structure;
  A2 (classical implication) is logic primitive; A3 (successor with ∪);
  A4 (induction as operational principle). The chain of justification is
  structural — no axiom is postulated arbitrarily; each is exhibited as
  inevitable given the ontological minimum.
- **Important distinction from Gödel-blocked claim**: this is **not** the
  claim that VR formally derives `Con(VR)` inside itself. Gödel's second
  incompleteness theorem applies к VR via its arithmetical equivalence к
  PA — formal internal derivation of consistency is impossible. The claim
  here is different: consistency is **operationally self-evident through
  structural exhibition**, not formally derivable as theorem. This is
  characteristic of the entire class, not VR specifically.
- **VR's distinct specifics within the class**: more minimal ontology than
  Brouwer (∅ only, not mental constructions generally); operational rather
  than mental; formally encoded in Lean 4 with machine-verified axiom
  dependencies; apparatus framework for tracking operational status.
- **Honest framing**: VR is one instance of constructively self-exhibiting
  arithmetic, in the tradition started by Brouwer. Not "first arithmetic
  to prove itself" (overclaim Gödel refutes); rather "modern instance of
  the class, with distinguishing specifics: minimal ontology, operational
  character, formal Lean encoding, apparatus tracking".
- **What would validate**: dedicated preprint articulating VR's place in
  the class precisely, with explicit comparison to Brouwer, Heyting, Bishop,
  Martin-Löf; engagement with foundations philosophy community.
- **What would refute**: shown that VR's structural justification chain
  hides a hidden assumption requiring external proof; or shown that VR
  does not belong к the class (e.g., some axiom revealed as not
  structurally exhibited but postulated arbitrarily).

### "VR programme belongs to the class of constructively self-exhibiting foundational programmes"

- **Class definition**: comprehensive foundational programmes whose entire
  content — not just arithmetic core — is exhibited structurally through
  construction, with each extension justified operationally rather than
  postulated externally. Members:
  - Brouwer's intuitionism (arithmetic + analysis + continuum theory).
  - Bishop's constructive mathematics (analysis + algebra + topology).
  - Martin-Löf type theory (full foundation: sets, functions, propositions).
  - **VR programme** (arithmetic + numbers + sets + forms + audit + ZFA
    + apparatus + algebra).
- **Programme-level extension beyond arithmetic class**: each VR work
  extends the operational position structurally:
  - **VR-Numbers**: ℤ as records, ℚ as syntax, ℝ as algorithms, ℂ via
    A1 duality. Each extension operational consequence.
  - **VR-Sets**: sets as describable functionalities, ∈ as reference.
    Closure principle derived.
  - **VR-Forms**: two-register apparatus с explicit conservativity
    theorem (Theorem III.1).
  - **VR-Sets-ZFA**: coinductive parallel, AFA derived constructively
    (not postulated).
  - **VR-Apparatus**: tracking discipline formalised as typeclasses.
  - **VR-Algebra**: apparatus applied to algebra, reuse pattern confirmed.
- **VR-Audit qualification**: VR-Audit explicitly **uses** classical
  infrastructure (Zorn's lemma, Classical.choice) to demonstrate apparatus
  on classical content. This is **not** a violation of self-exhibition;
  it is the apparatus's deliberate demonstration of operational tracking
  across the boundary between operational and classical machinery. VR-Audit
  belongs to the programme as the work showing the apparatus's reach into
  classical mathematics, not as content claimed to be operationally
  self-derived from VR's ontological minimum.
- **VR programme distinguishing specifics within the class**:
  - More minimal ontology than Brouwer (∅ only).
  - Operational character rather than mental constructivism.
  - Eight works machine-encoded in Lean 4 with full axiom audits.
  - Apparatus framework formalised abstractly (VR-Apparatus), demonstrated
    on two domains (analysis via VR-Audit, algebra via VR-Algebra).
  - Recognition discipline as methodological signature documented across
    cycle (bidirectional, seven applications in VR-Algebra alone).
- **Honest framing**: VR programme is a modern instance of constructively
  self-exhibiting foundational programmes, in the tradition started by
  Brouwer and continued by Bishop and Martin-Löf. Not first; one of class.
  Distinguishing specifics: ontology minimality, operational character,
  Lean encoding, apparatus methodology, eight-work scope.
- **What would validate**: peer engagement with foundations community
  positioning VR programme within the class; comparative analysis с
  Brouwer/Bishop/Martin-Löf showing precise relations и distinctions.
- **What would refute**: shown that some VR work introduces axioms
  postulated externally rather than structurally exhibited; or that
  VR-Audit's use of classical machinery undermines programme-level
  self-exhibition claim.

### "VR's two-register apparatus provides structural framing for intelligence limits"

- **Connection к Smale 18**: Smale's eighteenth problem asks about limits
  of intelligence (artificial and human). The problem is philosophical
  rather than strictly mathematical. VR programme is not solving it, but
  VR's two-register apparatus (operational + formal) provides clean
  structural language for discussing intelligence limits.
- **VR's structural framing**: any intelligence working on operational
  substrate has structural boundary between:
  - **Operational reasoning**: constructions reachable from ontological
    primitive (∅ in VR case) through finite sequences of operations
    OR through process-based unfolding (operational infinity via A4
    induction principle). This includes the entire operational substrate —
    not limited к finite, но limited к process-based access. Decidable
    per instance, witness-bearing.
  - **Formal reasoning**: syntactic expressions using ontological-completion
    concepts (actual infinity, uncountable cardinals, Power Set as
    completed totality, non-effective existence) without operational
    correlate. Conservativity (VR-Forms Theorem III.1) ensures formal
    use does not affect operational ontology.
- **Boundary is process vs completion, не finite vs infinite**: operational
  infinity (process-based) is on the operational side; actual infinity
  (completion-based) is on the formal side. Intelligence working с
  operational substrate has access к full process-based unfolding —
  но not к completion concepts.
- **Position**: the boundary is **substrate-independent** — same limit
  applies к AI on silicon, human on carbon, or any operational reasoner.
  What is reachable operationally depends on substrate, but the structure
  of the boundary (operational reasoning vs formal language extension) is
  invariant.
- **Examples of boundary in practice**:
  - Halting problem: formally meaningful, operationally undecidable
    uniformly.
  - Cantor's diagonal: formally proves uncountability, operationally
    reduces к halting problem (already covered in earlier item).
  - CH: formally meaningful, operationally dissolved (already covered).
  - Actual infinity / Power Set / AC: formal terms, no operational
    correlate.
- **Connection к classical AI debates**: VR apparatus could reframe
  - Penrose-style arguments (consciousness > computation): question is
    which formal terms have operational correlate vs which are pure syntax.
  - Symbolic vs subsymbolic AI: VR tracks operational content explicitly.
  - Strong AI claims: operational substrate **does** support reasoning;
    formal extension is **language-mediated**, not substrate-extending.
- **Honest framing**: VR provides **structural language** for discussing
  intelligence limits, not **solution** к Smale 18. Philosophical
  contribution, not technical resolution. The two-register apparatus
  enables precise statements that current philosophy-of-mind discussions
  often blur.
- **What would validate**: dedicated preprint or essay applying VR's
  apparatus к philosophy of mind / AI limits; engagement with
  philosophical community working on these questions.
- **What would refute**: shown that some intelligence-limit question
  collapses across operational/formal boundary (i.e., boundary not
  structural for the question); or that VR's two-register distinction
  doesn't transfer к philosophy of mind context cleanly.

---

## Investigated and not applicable

Open mathematical problems explicitly investigated and found **not** к benefit
from VR programme. Documented to prevent re-investigating later.

- **Hilbert 2** (consistency of arithmetic): Gödel-blocked formally; VR
  belongs к self-exhibiting class but does not "solve" the problem in
  Hilbert's original formulation. Already covered in Category 4 item on
  self-exhibiting arithmetics.
- **Hilbert 4** (metrics where lines are geodesics): geometric problem,
  not foundational. VR не contributes.
- **Hilbert 6** (axiomatization of physics): physics problem, outside VR
  current scope. Partially solved 2025 by classical methods.
- **Hilbert 7** (2^√2 transcendence, Gelfond-Schneider): already solved
  classically. VR inherits naturally — no special treatment, classical
  proof transfers.
- **Hilbert 12** (Kronecker theorem extension): class field theory,
  algebraic number theory content-specific.
- **Hilbert 15** (Schubert calculus): algebraic geometry content-specific.
- **Smale 4** (integer zeros of univariate polynomials, tau-conjecture):
  Diophantine / complexity content-specific.
- **Smale 6** (finiteness central configurations celestial mechanics):
  algebraic geometry of solutions к specific equations.
- **Yang-Mills millennium problem**: physics + analysis + QFT, outside
  current VR scope. Mass gap as operational predicate observation noted
  but does not bypass construction difficulty.
- **Collatz conjecture**: Diophantine wall (log₂ 3), foundation reform
  does not bypass.
- **P vs NP**: computational complexity, content-specific, foundation
  reform does not affect computational resources.

**Pattern**: VR contributes specifically к foundation-related questions
(CH, Cantor's diagonal, AC). Most open mathematical problems are
content-specific (Diophantine, algebraic geometry, complexity, physics)
and not addressable through foundation reform. Three items in Category 4
(CH, diagonal, AC) plus the self-exhibiting class membership constitute
the substantive list of foundation-related contributions.

---

## 5. Honest gaps

What VR lacks compared to existing programmes. Counterweight to prevent
overclaim.

### Mathematical content vs Bishop

Bishop's constructive analysis has decades of derived content. VR-Audit
has one substantive audit (Hahn-Banach via Riesz). Programme young.

### Computability classification vs Weihrauch

Weihrauch's computable analysis systematically classifies functions by
computability degree. VR does not systematically classify; it tracks
operational status via apparatus but not in Weihrauch's quantitative way.

### Extraction depth vs proof mining

Proof mining extracts explicit bounds from many classical proofs.
VR has not yet performed comparable extractions; VR-Audit shows
structural transit but not quantitative content extraction.

### Axiom strength measurement vs reverse mathematics

Reverse mathematics measures axiom strength systematically across many
theorems. VR observes axiom asymmetries (F3, A1, A4, A5) but does not
systematically measure strength.

### Library scale vs mathlib

Mathlib has 1M+ lines, comprehensive coverage. VR has thousands of lines,
focused on apparatus and foundation.

### Categorical depth vs HoTT / category theory foundations

HoTT and categorical foundations have deep theoretical development.
VR has not engaged categorical foundations beyond informal acknowledgement.

### Application maturity vs ZFA

ZFA has 35+ years of applications (process algebra, modal logic,
situation theory, philosophy of liar paradox). VR-Sets-ZFA is recent,
no validated applications.

### Community engagement

Single author. No peer review yet. No publication in standard math venues.
No citations. ArXiv submission pending endorsement.

### Philosophical robustness

Operational interpretation provided through VR programme metalanguage,
not enforced by Lean code (Lean treats ℕ classically). Philosophical
position requires peer engagement with philosophy of mathematics
community.

---

## File maintenance

- **Add**: when new fact verified, new combination identified, new gap
  recognised.
- **Move**: open position → demonstrated when validated; demonstrated → gap
  if refuted.
- **Remove**: when fact turns out wrong, when claim untestable, when
  redundant.

This file is not preprint, not pitch, not marketing. It is compass.
Internal navigation tool. External claims drawn from category 1 only.
