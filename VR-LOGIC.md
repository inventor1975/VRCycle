# VR-LOGIC.md

**Purpose.** A logic-led map of the VR programme: what follows by logic (and is
machine-checked, with its axiom cost stated), and what is open — where there is no
certainty yet. Not a catalogue of ambitions, not a pitch, not a uniqueness claim. The
single criterion is **logic**: if something is wrong, it is unacceptable. The starting
point is clean — **no ontology of substance** (being is relocated into doing; see the
Foundation note below) — and the discipline is not to stumble. Where we arrive,
and where those who come after arrive, is the open question; the compass is logic alone.

**Author**: Vitaly Reznik. **Implementation partner**: Claude (Opus 4.x), Variant A.
**Supersedes**: `VR-UNIQUENESS.md` (26 May 2026 — recorded earlier goals and ambitions;
those are set aside). **This file**: facts drawn from the Lean sources and their
`#print axioms` audits, not from narrative.

---

## 0. The two things this file tracks

1. **Established by logic** — claims with a machine-checked proof and a known axiom
   profile. If contested, point to the Lean object and its audit.
2. **Open** — questions where there is genuinely no certainty yet. Marked as such, with
   what would settle them. Honesty here is the counterweight to overclaim.

Recognition discipline applies: an "established" item demoted to "open" or removed if the
code says otherwise; an "open" item promoted only when the code earns it. The code is the
arbiter — narrative (README, blueprint) summarises it but does not override it.

---

## 1. Established by logic (machine-checked)

Axiom tiers used below (mathlib/Lean): `[]` axiom-free · `[Quot.sound]` · `[propext,
Quot.sound]` (the cycle's constructive ceiling) · `[propext, Classical.choice, Quot.sound]`
(full classical ceiling). The tier is a property of the *construction*, stated per object.

**Build status (verified in code).** The root `VRCycle.lean` aggregates all twelve modules —
including Continuum and Brouwer (the Continuum module's own README still says "not in the root
aggregator"; that is stale — it *is* imported and built). The whole cycle is **`sorry`-free**
except (a) one intentional teaching skeleton, `Examples/E04_ModeBSkeleton` (a documented
`sorryAx` warning), and (b) `Topology/_attic/` — historical, **not** imported, not built.

### Foundation — the formal system (`VR.lean`)

- **Two primitives, no axioms of its own, no ontology of substance.** Primitives `{∅, t}`
  — v1.1.1 removed the propositional `→` (and A1, A2, the F/∅ logical register); VR is now
  pure arithmetic on `{∅, t}`, generating no logic of its own. In Lean `VRObj` is the
  inductive type with constructors `base` (∅, a
  **nullary operation** — the 0-ary term-former) and `succ` (t). The source states it
  directly: *"No ontology is ascribed. ∅ is not a thing that is empty… every VR object is a
  TERM over the signature {base, succ, ∈, →} — there are ONLY operations."* The earlier
  labels ("Leibnizian void", "Spencer-Brown mark") are dropped as still ontological.
  **Scope of "no ontology" (the correction).** This is **no *substance* ontology** — no
  object that *is*; being is relocated into doing. It is **not** the claim that VR ascribes
  no ontology *at all*: the operational / set layer carries genuine commitments — global
  `∈` (an Aczel-style member family), potentialist infinity, relational identity — which are
  *tracked* (register + axiom tiers), not denied. The bare slogan "the cycle ascribes no
  ontology" (as it stands in the published *Numbers* v1.1.0 and *Forms* v1.0.2 preprints)
  overshoots and reads, at face value, as a blanket denial that collides with VR-Sets'
  global `∈`; the accurate claim is **being relocated into doing, remaining commitments
  audited**. Cf. the good scoped form already in *VR-Apparatus* (§: "formal register —
  syntactic descriptions *without ontological commitment*"), which correctly localises the
  disclaimer to the formal register alone.
- **What 0 is, and what 1 is.** `0 = ∅ = base` is the nullary operation itself — the act
  taking no operands, the only act available before any succession (not "nothing", not a
  thing). `1 = t(∅) = succ base` is the unique result of the unique operation on that base.
  Each `n = tⁿ(∅)` is the trace of `n` applications. No arbitrary encoding choice (contrast
  von Neumann 1 = {∅} vs Zermelo 1 = {{∅}} as conventions). `O_zero`, `O_one`, all `rfl`.
- **The named principles are theorems, not axioms (A1/A2 gone).** `A3` (succession: `x ∈ t(x)`,
  `x ⊆ t(x)`) is proved from `mem` (`A3_mem_self`, `A3_subset_succ`); `A4` (induction) is the
  recursor of the inductive type (`A4_induction`) — what first-order exposition postulates,
  type formation absorbs. `A1`, `A2` (which governed the removed propositional layer) no longer
  exist. So VR has **no axioms of its own**.
- **VR generates no logic of its own (v1.1.1).** The earlier propositional layer — `VRBool`,
  `{F, →}` functional completeness, `vnot/vor/vand/viff` with `rfl` truth tables — was
  **removed**: a finite truth-function algebra used by no theorem (arithmetic, not logic). The
  logic VR *reasons with* (`∀`, `→`, `↔`, induction, Leibnizian equality) is **metatheoretic**.
  Leibnizian equality `vrEq x y := ∀ p, p x ↔ p y` is defined, not primitive.
- **∈-acyclicity is structural.** `not_mem_self` and `succ_ne_self` proved by structural
  induction on the inductive type — **no measure / no finiteness theorem** needed.
- **VR ≡ PA, as a constructive isomorphism.** `Theorem_11_VR_PA : VR_PA_iso` — an explicit
  `Nat ≃ VRObj` (`O`/`O_inv`) preserving 0, succ, +, ×, ^. The metatheoretic equivalence of
  Part II is realised as a concrete object; consistency of VR relative to ZF follows (via
  PA). Note: T1–T4 (commutativity etc.) are **not** premises of the isomorphism — it rests
  on the shape of the recursions, not the algebraic identities.
- **Axiom cost.** The entire formal system is **axiom-free `[]`** (no `propext`,
  `Classical.choice`, or `Quot.sound`).

### Numbers, sets, methodology, applications (summary; per-object audits in code)

- **VR-Numbers** — ℤ, ℚ, ℝ, ℂ as operational superstructures over VR-ℕ, each proved
  **isomorphic to the corresponding mathlib type** (`Theorem_IV_7 : ℝ_VR ≅ ℝ`, etc.).
  Because the isomorphism reads mathlib's ordered-field substrate, these are Tier-3 by
  necessity (see §1 "construction-relativity of the floor"). **Important**: `ℝ_VR ≅ ℝ` is
  the *full* classical real line (uncountable) — it is **not** the operational `Real` of §1
  Continuum, and not "countable". The two are distinct objects (see Open Questions).
- **VR-Sets** — built on mathlib `ZFSet` (`OSet := ZFSet`). The nine ZFC axioms hold as
  wrappers (Tier-3 through `ZFSet`). `∈` is read as **reference by name**, not containment.
  The ZFA boundary results (`quineAtom_impossible`, `AFA_Refuted`) are the only
  **axiom-free** objects there — a type-theoretic fact (`PSet` is inductive), not an axiom.
- **VR-Sets-ZFA** — **AFA proved as a theorem** (`AFA_in_OSetZFA`) via the final-coalgebra
  property of a coinductive `CoPSet` (mathlib `PFunctor.M`); not postulated. Quine atom
  machine-verified. Mostly `[propext, Classical.choice, Quot.sound]`; `CoPSet.mk`/`.corec`
  axiom-free.
- **VR-Forms** — two registers (operational L₀ / formal L₁) and the transit pattern as a
  shallow embedding. **The central conservativity result (Theorem III.1) is now FORMALISED**
  (2026-06-06, `Forms/Conservativity.lean` + `Forms/ConservativityFOL.lean`): a deep embedding
  via relative interpretation. Propositional floor, then FOL with terms (de Bruijn variables,
  constants, n-ary function symbols) and n-ary operational predicates; classical Hilbert
  `Provable` (K/S/Peirce/MP, ∀-elim, ∀-distribution, generalization); the π-translation, with
  `piTr_subst` (π commutes with substitution — kept trivial by 0-ary formal atoms + closed `tr`,
  avoiding de-Bruijn substitution-composition); and `conservativity`. A concrete VR instance
  (∅, ∈, succ, `⌜∅⌝` ↦ `∀x ¬(x∈∅)`) with `conservativity_empty_concrete` discharging the
  hypothesis end-to-end. All choice-free (`[propext]`, instances `[propext, Quot.sound]`),
  self-contained, lint-clean. **Boundaries (documented, by choice):** `gen` is stated without
  the eigenvariable side-condition (a refinement for matching standard FOL soundness; not needed
  for the syntactic π-transport that conservativity is); the VR instance covers ∅ (richer ω etc.
  marginal). `[propext, Quot.sound]` for the shallow predicates.
  **Extraction asymmetry, machine-checked.** `translate_implies_realisable : ∀ t, translate_pi
  t → isRealisable t` holds — from a specific operational fact (witness in hand) one obtains
  the formal term's realisability (**O→T**: operational ⟶ formal). The **converse fails**:
  from `isRealisable t` (`∃ s, …`) one cannot recover the specific operational object — *no
  Skolemisation across the existential*. So **one can pass from operational to formal, but
  cannot extract the operational from the formal** (**T→O** has no mechanism). This is the
  logical core of register inheritance: an existential asserts a correlate exists but yields
  no witness.
- **VR-Apparatus** — the methodology made explicit as Lean typeclasses: two operationality
  modes (`PredicateOperationality`, `ReferenceOperationality`), two transit modes (Mode A =
  closure by `rfl`; Mode B = classical op + `Factorisable` witness), `InterApparatusMorphism`.
  Reused unchanged in algebra. Four axiom tiers exhibited.
- **VR-Audit** — operational Hahn-Banach for Hilbert spaces via Riesz
  (`HahnBanachOperational_Hilbert`). `Classical.choice` is **expected and accepted** (Zorn);
  the point is preservation of operationality across the classical step, not its avoidance.
- **VR-Algebra** — apparatus across additive groups, rings, fields, modules; both modes
  exercised. Confirms apparatus transfers (Finding A3: zero modification).
- **VR-Topology** — point-free binary Tychonoff (`tychonoff_binary`) reached
  **`[propext, Quot.sound]` — choice-free**, even though classical Tychonoff ⇔ AC; the
  point-free formulation is what makes the choice-free profile attainable.
- **VR-Transit** — transit conservativity exhibited + a bounded-witness library
  (`finiteGen_provides_factorisable` axiom-free; `finiteSpan_provides_factorisable`
  `[propext, Quot.sound]`).
- **VR-Brouwer** — Brouwer's fixed-point theorem via Sperner's lemma:
  `brouwer_stdSimplex_all` (simplex of any dimension), `brouwer_compact_convex` (any
  compact convex K ⊂ ℝⁿ). mathlib-bound (not VR-foundational), with a machine-checked
  differential witness (`Meta/DependsOn`): the constructive layer is free of
  `tendsto_subseq`, the classical layer depends. The cycle's largest module by object count.

### Operational continuum (`Continuum/`, exploratory — not a published work, no DOI)

Built **after Brouwer (Path 1)**, every object kept **below the `Classical.choice` floor**
(over pure ℤ; never through mathlib ℚ/ℝ, which are entirely Tier-3 — Finding CONT-7: even
`(2:ℚ)+3` pulls choice). All objects **`[propext, Quot.sound]`**.

- **The diagonal, with a different character.** `branches_not_enumerable` is an
  **unconditional Cantor diagonal**, choice-free `[propext]`: the branch space (`ℕ → Bool`,
  the *becoming* register) is non-enumerable. The diagonal does **not** "fail" in VR — its
  *meaning* changes. `no_node_surjection`: the countable *operational* register (performed
  nodes `List Bool`) cannot surject onto branches. So the diagonal witnesses **the
  inexhaustibility of becoming by the countable performed** — a cut between *done* and
  *becoming*, not the selection of an element from a completed uncountable totality (as the
  Power-Set diagonal does in ZF). Reinterpreted, not removed. **Consolidated** as the citable
  `operational_cantor` (`Continuum/Cantor.lean`, `[propext, Quot.sound]`, machine-checked):
  *done countable* (`operational_register_countable`, witness `decodeNode`) ∧ *becoming
  non-enumerable* ∧ *done cannot exhaust becoming* — the three registers of the diagonal in one
  statement. **Bridge to ℘(ℕ):** `powerset_diagonal` (`Continuum/Cantor.lean`, `[propext]`,
  choice-free) — the full ℘(ℕ) (characteristic functions `ℕ→Bool`) is non-enumerable AND every
  enumerable (describable) family of subsets misses its own diagonal. So the uncountability of
  ℘(ℕ) requires the **non-describable** diagonal subset — it lives in the completed totality,
  not in the operational (enumerable) layer. The operational ABSENCE of that completed totality
  is essay-level (§3), not asserted in code.
- **Three registers, machine-checked.** operational (performed node `List Bool`, countable) /
  becoming (lawless branch `ℕ → Bool`, non-enumerable) / formal (actual infinity as a label).
  Brouwerian continuity (WC-N) and the fan theorem are carried **only as `Prop`-hypotheses,
  never adopted** — adopting them over classical mathlib is inconsistent (`Continuity` is
  classically FALSE: `not_continuity`). But `Continuity` holds **operationally**, choice-free,
  for finite-information functionals (`continuity_of_nbhd`, Stage C). So the two-register
  thesis is machine-checked on a genuinely Brouwerian principle: FALSE formally, TRUE
  operationally.
- **Choice, read operationally (`Continuum/Choice.lean`).** **DC is operationally available,
  choice-free:** `operational_dependent_choice` (`[propext]`) — a history-dependent rule
  `f : List Bool → Bool` determines a branch `α n = f (α.take n)` by recursion (choice is
  available because there is a *rule*). Bundled with operational continuity as
  `operational_choice_available` (`[propext, Quot.sound]`, choice-free). The picture: **DC**
  (by rule) and **WC-N** (`Continuity` two-register) are operational; **full AC** (selection
  over an uncountable family with no rule) is a formal-register label with no operational
  correlate; **AC+AD→⊥** is a T→T phenomenon (ADDENDUM, §2) that never returns through the
  operational floor. Only the first two are machine objects; full AC and AC+AD are essay
  (cited, not coded).
- **Number spectrum ℤ→ℚ→ℂ→ℝ, below the floor.** `Qop` (operational ℚ): CommRing,
  DecidableEq, full trichotomy, **total** reciprocal — the decidable pole. `GaussQ`
  (operational ℂ): same, total reciprocal. `Real` (operational ℝ): **Bishop reals over ℤ**
  (dyadic asymptotic-Cauchy), full choice-free CommRing, `zero_ne_one`, reciprocal
  **witnessed by apartness** (not total — Markov). `Real ≠` classical ℝ (no trichotomy,
  located-only sup).
- **Construction-relativity of the floor (the real deliverable).** Two rationals, by
  necessity: `ℚ_VR` (Numbers, proved ≅ mathlib ℚ → Tier-3) vs `Qop` (choice-free, makes **no**
  isomorphism claim — choice-freeness forbids it). A single ℚ both choice-free *and* proved
  isomorphic to mathlib ℚ is impossible (the iso is a `ratCast`, which pulls choice). The
  floor is a property of **construction, not of the object** — exhibited concretely, build-time.
- **"Doing, not being", machine-checked (`Meta/DoingNotBeing.lean`).** Operationality is
  **total on being** (`being_total_int`; cycle-wide `Forms.operational_total` — the element
  predicate is constant `True`, discriminates nothing) and **split on doing**: the *same*
  proposition has a choice-free proof (`trans_doing`, omega) and a choice-dependent one
  (`trans_being_via_choice`, `le_trans`). The split is **decidable and universal** —
  `Meta/DependsOn` computes it and gates the build (`#assert_depends_on` etc.). The
  operational boundary lives on the **act**, not the object: "nothing is — all is doing" as
  a checked meta-fact.

---

## 2. The leading principle: operationality (not Bishop's constructivism)

VR is a **free** programme, not a pursuit of pure constructivism. At this stage it pursues
**operationality** — and accommodates classical reasoning rather than rejecting it.

- **Difference from Bishop.** Bishop rejects classical reasoning. VR keeps it — inside the
  **formal register** — and out of the **operational register**, tracking the boundary with
  the apparatus (and, machine-checked, with `Meta/DependsOn`). The classical results stay
  available; they just carry their axiom cost visibly.
- **The three registers** organise this: operational (has an operational correlate),
  becoming (process-based potential), formal (a label for a non-operational referent such as
  actual infinity). Continuity is the cleanest exhibit: false in the formal register, true
  in the operational one — both machine-checked.
- **How the classical "three pillars" read under operationality.** Cantor's diagonal: cuts
  between done and becoming, not inside a completed totality (§1). CH and full AC: live in
  the formal register as labels; whether and how they have operational correlates is an
  **open question**, not a settled "dissolution" (see §3). The earlier framing in
  `VR-UNIQUENESS.md` ("VR dissolves CH / the diagonal does not work / ℝ_VR is countable") is
  **superseded** — partly imprecise (`ℝ_VR ≅ ℝ` is uncountable), partly Bishop-leaning where
  the code took the Brouwer path.

### Invariance of the operational under application of form (a position, not a theorem)

VR's articulated answer on AC / AD / Power Set / CH (from the former ADDENDUM). It is a
**philosophical position** — the ground of conservativity, not a machine-checked result
(conservativity itself is not formalised; §3). Three configurations of application; the thesis
concerns the two with an operational anchor:

- **O→T** (an operational act inscribing a formal term — ⌜℘(ℕ)⌝, ⌜c⌝): the act stays fully
  operational; pointing at a referent with no operational correlate does not diminish the
  operationality of the act.
- **T→O** (a form applied to operational material): "2+2=4" applies to apples, pears, even
  centaurs; the material stays what it was, counting stays an ordinary operational act —
  the material is not damaged by having a form applied to it.
- **T→T** (a form applied to a form): no operational anchor — the only configuration where
  ambiguity, and contradiction, can live; the thesis does not extend here, and need not.

**The invariant**: the operational register survives the application intact — this is *why*
the formal register is conservative over the operational (form has no power to damage the
operational). The invariance preserves the **input**, independent of the **output's** register:
a constructive form returns an exhibitable result; an existential form (AC, Power Set) returns
a formal claim (a promise of an object), not the object — but neither damages the operational
input.

**Legitimate application**: applying a *formally coherent* term to operationally accessible
material is always a legitimate descriptive act (the Russell term is excluded — formally
incoherent, it detonates the register). So "may one apply AC / Power Set?" is mis-posed; the
right question is **what one is entitled to claim**: operational consequences need an
operational correlate (constructive scrutiny applies); formal consequences propagate within the
formal register (conservativity applies). Crossing registers requires explicit construction,
never deductive entailment alone (register inheritance).

**The formal register is a family of description contexts, not one monolithic theory.** AC and
AD are each individually legitimate; their classical incompatibility (AC+AD→⊥) is a **T→T**
phenomenon and never returns through the operational floor — it would require co-asserting two
distinct formal contexts in a single deduction, which the apparatus does not license.
(Operational floor ≈ ZF+DC; AC and AD sit above it as distinct contexts.) CH is a
formal-register claim about the formal-register description ℘(ℕ); it returns operationally only
via explicit construction of a correlate.

A **third position**, neither "AC is true" nor "AC is unacceptable": AC is a legitimate
formal-register act; its consequences inhabit the register of their application; only
operational consequences require constructive scrutiny; the operational is never damaged either
way. A structural reformulation that relocates the dispute — from the axiom to the invariance
plus the register of the consequences. (Caveat: the ADDENDUM reads the real correlate as
"countable computable reals" — a Bishop reading; the code took the Brouwer path. That tension
is the open Bishop/Brouwer question of §3.)

---

## 3. Open — where there is no certainty yet

These are genuine questions, stated to be settled by logic, not asserted.

- **Are formal terms operational?** The deepest open question at this stage. VR pursues
  operationality *even of formal terms* — but whether a description of a non-operational
  referent (⌜℘(ℕ)⌝, ⌜c⌝, ⌜full AC⌝) is itself an operational act with no operational
  correlate, or something else, is **not resolved**. The two-register language is a working
  apparatus, not a decided ontology.
- **Bishop path vs Brouwer path — which is canonical for VR's continuum?** The code took
  Brouwer (Path 1: non-enumerable becoming, diagonal works). A Bishop reading (countable
  computable reals, diagonal as uncountability-proof rejected) is a *different* programme.
  Both are coherent; VR has not committed to one as final. The `Real` (Bishop reals over ℤ)
  and the becoming space (Brouwer) currently coexist — their precise relation is open.
- **CH / diagonal / AC — what is formalised vs what is essay.** §1 establishes: the diagonal
  fully (done countable / becoming non-enumerable / `operational_cantor`; the ℘(ℕ) bridge
  `powerset_diagonal` — full ℘(ℕ) non-enumerable, every enumerable family misses its diagonal),
  `Real` below the floor (done), Continuity two-register (done). **DIAGONAL: formalised core
  complete** (2026-06-06). **Still essay (not done):** that ℘(ℕ) as a completed totality is
  operationally *absent* (a meta-claim — one cannot prove unformulability *inside* the system;
  only exhibit, as we did, that no enumerable family is complete).
  - **CH — resolved as essay (decided 2026-06-06), machine-anchored by `powerset_diagonal`.**
    The machine core is already in hand: the ℵ₀ / non-enumerable gap is `powerset_diagonal`
    (ℕ countable, ℘(ℕ) not). Beyond it CH adds **no new machine content** and gets **no own
    code** (it would be packaging over `powerset_diagonal`). Two reasons it stays essay: (i)
    "no intermediate cardinal" is the *non-existence* of an X with ℵ₀<|X|<c — not an
    operational theorem (classically it is an *independence* result); unformulability is not
    provable inside. (ii) "operational layer is countable" is not even universal here: `Real`
    (Bishop reals, **all** dyadic-Cauchy `ℕ→ℤ`) is **not a countable type** — only *describable*
    reals would be, and they are not isolated as a type. So CH is a formal-register label, read
    philosophically in the essay; the honest machine fact under it is `powerset_diagonal`.
  - **AC — machine core DONE (2026-06-06), `Continuum/Choice.lean`.** **DC is operationally
    available, choice-free:** `operational_dependent_choice` (`[propext]`) — a rule
    `f : List Bool → Bool` determines a branch by recursion. Bundled with operational
    continuity: `operational_choice_available` (`[propext, Quot.sound]`). Plus the Continuity
    two-register (`not_continuity` formal-FALSE / `continuity_of_nbhd` operational-TRUE) = WC-N.
    **Still essay (by design):** full AC (selection over an uncountable family with NO rule) has
    no operational correlate → formal-register label, not a machine object; and AC+AD→⊥ is a
    T→T phenomenon (ADDENDUM, §2) — neither is coded. So DC/WC-N are machine; full AC and AC+AD
    are essay. This is the honest split, not an avoidance.
- **Conservativity (VR-Forms Theorem III.1) — NOW FORMALISED (2026-06-06).** Previously the
  central open boundary (argued metalogically, not machine-checked); now a deep embedding proves
  it (see §1 VR-Forms). The two-register apparatus no longer rests on an unverified result.
  Remaining refinements (documented, not gaps in the result): `gen` without the eigenvariable
  side-condition (would match standard-FOL soundness; not needed for the syntactic π-transport),
  and a richer VR instance (ω). These are polish, not the theorem.
- **Extracting the operational from the formal (T→O) — no mechanism yet.** O→T works
  (operational material yields a formal term, witness in hand; `translate_implies_realisable`).
  The reverse — given a formal term, produce its operational correlate — has **no general
  mechanism**: the specific case is machine-checked *impossible* by extraction (no Skolemisation
  across the existential; the converse of `translate_implies_realisable` fails), and the general
  case is exactly the unformalised conservativity. Whether some formal terms admit a
  constructive T→O extraction (and which) is open; at present T→O is only ever achieved by
  building the operational object independently, never by reading it off the formal term.
- **VR-Sets open conjectures.** `Conjecture_IV_1` (ZFC-mode mutually interpretable with a
  countable ZFC model) is open mathematics, formalised as `Prop`, not proved.
- **Operational ℝ — what is missing.** A `Real`-level inverse wrapper, an analytic
  nontriviality (a genuine limit), completeness / located-sup. Constructive caveats persist
  (no trichotomy). `Real` is Bishop's reals machine-checked choice-free — not the classical
  line.
- **Does operationality reach beyond two domains?** The apparatus is demonstrated in analysis
  and algebra (and transferred to topology). "General across all mathematics" is conjecture,
  not fact.

---

## 4. Honest gaps (maturity and reach — stated as facts)

- **Single author; no peer review; no arXiv endorsement; no citations.** The corpus is
  machine-checked but not community-checked. This is the largest gap and it is not
  mathematical.
- **Content scale.** Thousands of lines focused on foundation + apparatus; not Bishop's
  decades of derived analysis, nor Weihrauch's quantitative computability classification, nor
  mathlib's breadth.
- **Philosophical robustness.** The operational reading is carried in metalanguage; Lean
  treats ℕ/ℝ classically. The position needs engagement with the philosophy-of-mathematics
  community to be stress-tested.
- **The dependency witness is meta-trusted.** `Meta/DependsOn` certifies axiom dependence at
  build time but is not itself kernel-verified — the same trust tier as `#print axioms`.

---

## File maintenance

Established → Open if the code stops supporting it. Open → Established only when a Lean
object with a clean audit earns it. Remove anything that turns out wrong. The criterion is
logic; the arbiter is the code.
