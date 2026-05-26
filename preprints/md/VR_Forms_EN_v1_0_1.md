VR-Forms
An Operational Two-Register Apparatus over VR-Sets

Vitaly Reznik
ORCID: 0009-0002-4103-6387

2026
Version 1.0.1


## Abstract

VR-Forms is the fourth work in the cycle developing the VR programme (Reznik 2026, preprints VR. A
Formal System, VR-Numbers, VR-Sets). It introduces a two-register apparatus on top of VR-Sets: an
ontological register (operational sets of VR-Sets, with closure principle and reference-based ∈ ) and a
formal register (syntactic descriptions without ontological commitment). The formal register provides a
universal language for everything that is not in the operational ontology — classical uncountable
objects, paradoxical classes, mythological and theological terms, philosophical categories. The two
registers are connected by a conservativity theorem (Theorem III.1): the formal register is a
conservative extension of the operational, generating no new ontological commitments and proving
nothing in the ontological register that VR-Sets could not already prove. The transit rule allows formal
reasoning over uncountable intermediaries, with results automatically translating into the operational
register when the conclusion is itself ontological. The apparatus closes the ontological contour of the VR
cycle: VR can now speak about everything, with only ∅ in its ontology. Classical paradoxes (Russell,
Vitali, Skolem) and classical uncountable objects (ℝ, ℘(ℕ), proper classes) receive a clear status —
formal terms without operational correlate. The same status, by uniform application of the principle of
forms, extends to mythological, theological, and literary descriptions, demonstrating the universality of
the formal register beyond mathematics.
Changes in version 1.0.1. A new Part IX has been added: "Lean 4 Formalisation of VR-Forms:
Methodological Observations." This part documents the Lean 4 formalisation of the formalisable core of
the apparatus — Parts II–IV (formal language, realisability, transit) plus mixed formulas of §VII.2
(Reznik 2026, Lean VR-Forms, Software DOI 10.5281/zenodo.20355757; Git tag v1.3-vr-forms). The
formalisation is a shallow embedding over mathlib with one explicit structural boundary at
conservativity (Theorem III.1), which would require deep-embedded Formula and Derivation types
beyond the scope of this cycle. Ten methodological observations are reported in four thematic clusters:
foundation-level properties (§IX.1, two observations), the central boundary at conservativity and its four
substructural manifestations (§IX.2, five observations), structural patterns in the apparatus (§IX.3, two
observations), and cross-cycle integration (§IX.4, two observations including the finale on zero
Classical.choice usage). The Lean formalisation contains 18 public objects across 5 files; three are axiom-
free (Stage 1), fifteen sit at [propext, Quot.sound], and none requires Classical.choice — making it the
most axiom-minimal of the four VR Lean cycles, a stricter result than the original cycle plan predicted.
§I.8 (Structure of the work) is updated to nine parts; the references and acknowledgement are extended
to reflect the parent-child review architecture used in the Lean formalisation, identical to that used in
VR-Sets v1.0.1. No mathematical content of Parts I–VIII has been revised; the changes are additive (Part
IX is new) and editorial.
Companion publications. Preprint VR-Sets v1.0.1 (DOI 10.5281/zenodo.20354628) similarly documents
the Lean 4 formalisation of its mathematical core in Part X. The full VR cycle in its v1.0.1 form consists of
four preprints (VR, VR-Numbers, VR-Sets, VR-Forms) and four Lean formalisations, all available on
Zenodo with cross-references.

**Keywords:** operational ontology, two-register logic, formal terms, conservative extension, transit

pattern, Russell paradox, Skolem paradox, Vitali set, AFA, non-well-founded sets, nominalism, universal
formal language, Lean 4, formal verification, mathlib, axiom audit, shallow embedding.

## Part I. Foundations

I.1. Place in the cycle
VR-Forms is the fourth work in the cycle developing the VR programme:
VR. A Formal System (Reznik, 2026; Zenodo DOI 10.5281/zenodo.20212092) — a minimal
axiomatisation of arithmetic on three primitives {∅, →, t} and four axioms; equivalent to Peano
arithmetic.
VR-Numbers (Reznik, 2026; Zenodo DOI 10.5281/zenodo.20272743) — operational extensions over the
natural numbers of VR: ℤ , ℚ , ℝ , ℂ as operational procedures, without introducing pairs as objects.
VR-Sets (Reznik, 2026; Zenodo DOI 10.5281/zenodo.20303536) — an operational theory of sets: a set is a
describable functionality, ∈ is reference rather than containment. Russell's paradox dissolves
ontologically. Countability of the universe as a consequence of the operational ontology.
VR-Forms is the present work. It introduces a second register — formal terms, descriptions without
ontological force. These terms are formulas, and nothing more. They serve as a language in which VR
can speak about everything that is not in its ontology: about classical uncountable objects, paradoxical
classes, figures of myth and literature — about all descriptions that cannot be reduced to operational
action.
Substantive connection with the preceding works: VR-Sets opened the boundary of operational
ontology. VR-Forms describes how to speak about what lies beyond this boundary, without crossing it
and without blurring it.

I.2. The initial position
The slogan of the whole cycle: «only ∅ is, all else is doing». Applied to arithmetic, it gave VR; to numbers,
VR-Numbers; to sets, VR-Sets. In all three works the slogan operated at the ontological level: the sole
thing that is is ∅; everything else is operational action upon ∅.
VR-Forms adds a third type. Between what is (∅) and what acts (operational functionalities), there is
introduced what is said. Not as a new ontological entity — that would violate minimalism. Rather as a
separate syntactic register, carrying no ontological commitments.
The full formulation of the position:
«Only ∅ is. Everything else either acts or is said. Action is operational and relates to ∅; speech is formal
and refers to nothing by necessity.»
That is VR-Forms in a single sentence.

I.3. Two registers
We introduce two registers of reasoning. They differ not in subject matter and not in language, but in
their relation to ontology.
The ontological register
This is the register of VR-Sets. The following principles hold:
— ontologically, only ∅ is;
— all other terms are operational functionalities, described by a finite procedure;
— the closure principle: every describable operational functionality is a set;
— contradictory descriptions do not specify functionalities and therefore do not specify sets.
In this register terms have reference: they refer to operational entities that are (in a derivative sense —
as action upon ∅).

The formal register
This is the new register introduced by the present work. The following principles hold:
— terms are formulas;
— a formula specifies a formal term, and that is all it specifies;
— no formula is required to have reference;
— a formal term is a formal term and does not presuppose any other entity behind it.
In this register terms are speech. They refer to nothing by necessity. They are form — and only form.

Passage between registers
The same term may be considered in both registers. The description «the set of all functions ℕ → ℕ» in
the ontological register requires verification: is it operational? Answer: no, the general set of all
functions is not computable; hence in the ontological register it does not specify a set. The same
description in the formal register is a formal term; no verification is required.
Passage between the registers is not an ontological operation. It is a passage between two ways of
considering one and the same syntax. In one case we ask «is there a corresponding entity?»; in the
other, we do not ask.

I.4. What a formal term is
A formal term is the syntactic record of a description. No more.
A formal term should not be thought of as a «potential set», or a «classical set to which VR has no
access», or a «shadow object». All such readings are reifications of a formula, attempts to ascribe
reference to it. In VR-Forms this attempt is rejected as a matter of principle.
A formal term is form without content. Description without being. A record that describes — but the
described does not exist, because in the formal register the question of existence is not posed.
This is not agnosticism. We do not say «perhaps it is, perhaps it is not». We say that the very question of
existence is irrelevant in the formal register. To ask about the being of a formula is a category mistake. If
we do wish to ask about being, we pass to the ontological register. There we obtain an answer: either
«the corresponding operational functionality is» (and then the formal term corresponds to a VR-Sets
set), or «not» (and then the formal term remains in the formal register and has no ontological
correlate).

I.5. Examples of formal terms
Examples are divided into three groups, demonstrating the universality of the formal register.

Group 1. Mathematical formal terms
Classical ℘(ℕ) — the description «the set of all subsets of ℕ». In the ontological register of VR-Sets this
is not a set in the full classical sense: VR contains a countable number of describable subsets of ℕ. In the
formal register «℘(ℕ)» is a formal term. The statement «the classical cardinality of ℘(ℕ) is 2^ℵ₀»
belongs to the formal register and has no ontological force.
Classical ℝ — the description «the set of all real numbers». In the ontological register ℝ_VR is the
countable set of computable reals. In the formal register «classical ℝ» is a formal term distinct from
ℝ_VR.
Russell's class — the description {x : x ∉ x}. In the ontological register it is contradictory and does not
specify a set (VR-Sets §II.3). In the formal register R = {x : x ∉ x} is a formal term. Russell's theorem
now takes the form: R is a formal term having no ontological correlate in VR-Sets.
The Vitali set — the description «a set of representatives of equivalence classes on ℝ under the relation
x − y ∈ ℚ ». Requires choice over an uncountable family. Not operational. In the formal register a formal
term.

Group 2. Paradoxical formal terms
The liar — the description «a statement equivalent to its own negation». In VR-Sets §VII.2 it was shown
that in the ontological register it has no truth value. In the formal register the liar is a formal term;
paradoxicality is a property of form, not an ontological failure.
The set of all sets — the description «an object whose elements are all sets». In the ontological register
contradictory. In the formal register a formal term.

Group 3. Non-mathematical formal terms
The apparatus of the formal register is not confined to mathematics.
A dragon — the description «a fire-breathing lizard-like creature of large size with wings». This is a
formula, a description. In the ontological register of VR-Sets — no operational functionality over ∅. In
the formal register — a formal term.
God in monotheistic understanding — the description «the unique omnipotent eternal creator of the
world». A formula. A formal term.
Unicorn. Phoenix. Centaur. Minotaur. Leviathan. All mythological beings are formal terms.
Soul. Idea in the Platonic sense. Universal. Essence. All classical philosophical terms are formal
terms.
This last point has a fundamental significance. The formal register of VR-Forms covers speech
without exception. Everything that is spoken of but is not operational is a formal term.
This is not reductionism. We do not say that dragons do not exist, or that God does not exist, or that
universals do not exist. We say only: in the VR-ontology they are not; in the formal register one can
speak of them as formal terms. The question of their existence outside the VR-ontology is not a
mathematical question and not a question of the present work.

I.6. What VR-Forms does with speech
The introduction of the formal register changes the status of classical contested questions.
The question of the reality of the uncountable. In the VR-ontology the uncountable is not — the
operational universe is countable (VR-Sets §VI.1). Classical mathematics freely uses the uncountable.
VR-Forms gives a precise formulation: classical ℝ is a formal term. Statements of classical mathematics
about ℝ are statements of the formal register. The dispute about the «reality» of the uncountable is a
dispute about whether the corresponding formal term has an ontological correlate beyond VR.
Mathematics does not answer this question; it shows only that in the VR-ontology there is none.
The question of paradoxes. Russell, the liar, Berry — all of them show: the corresponding formal
terms have no ontological correlate in VR. This is the content of paradoxicality: the paradoxical
description remains in the formal register. No damage to the VR ontology is done.
The question of the reality of non-mathematical entities. Dragons, gods, unicorns. In the VR-
ontology they are not. In the formal register one can speak of them. Whether they exist in some other
ontology is not a question of VR-Forms. The work only provides a formal language permitting talk of
them without ontological commitment.
VR-Forms does not deny the existence of anything. It distinguishes what is operational in its own
ontology from what is merely said and may (in another ontology) exist otherwise. About the first —
ontological speech. About the second — formal speech.

I.7. Connection with the philosophical tradition
The position of VR-Forms has precedents in the history of philosophy.
Medieval nominalism (Ockham, Buridan). Universals are names, not entities. Only concrete
individuals exist. VR-Forms inherits this position: formal terms are names; only the operational is real.
The difference: for Ockham reality is ascribed to material individuals; in VR — only to ∅ and actions
upon it. A more strict nominalism.
Mathematical constructivism (Brouwer, Bishop). Only that which is constructed exists. VR-Forms
agrees with this in the ontological register. The difference: VR-Forms adds the formal register, in which
one may speak of the non-constructive without claiming its existence. Classical constructivism refuses
talk of the non-constructive; VR-Forms permits the talk but deprives it of ontological force.
Formalism (Hilbert). Mathematics is manipulation of formulas without reference. VR-Forms inherits
formalism in the formal register. The difference: VR-Forms does not reduce all mathematics to the
formal register. Part of mathematics has operational ontology — this is VR-Sets. Formalism deprives all
mathematics of reference; VR-Forms — only its uncountable part.
Fictionalism (Field, Balaguer). Mathematical objects are useful fictions, not existing in the proper
sense. VR-Forms agrees with this regarding uncountable and paradoxical objects. The difference: VR-
Forms provides a formal apparatus for working with fictions, not only a philosophical position.
Late Wittgenstein. «Whereof one cannot speak, thereof one must be silent» — but be silent in a
metaphysical sense, not a linguistic one. One may speak, while being aware that the speech is not a
description of reality. VR-Forms continues this line: the formal register is speech aware of its
referentlessness.
VR-Forms does not introduce anything unprecedented. It conducts a known philosophical position
through the formal apparatus of VR. What is new in it is the combination of ontological minimality (∅
as the sole primitive) with formal openness (any description is a formal term).

I.8. Structure of the work
The work consists of nine parts.

## Part I. Foundations. Place in the cycle, initial position, two registers, formal term, examples (including

non-mathematical), connection with the philosophical tradition.

## Part II. The formal language. Precise definition of a formal term. Syntax of the formal register. Rules

of formation of formal terms. Difference between a formal term and an operational set.

## Part III. The principle of forms and consistency. The principle parallel to the closure principle of

VR-Sets: every description specifies a formal term. Consistency of the extension.

## Part IV. Transits. When work in the formal register yields results of the ontological register. The

transit rule. The notion of witness. Safe and problematic transits.

## Part V. Forms of mathematics. Application to mathematical formal terms: ℝ, ℘(ℕ), Vitali,

paradoxical classes. What is translated into the VR-ontology, what remains in the formal register.

## Part VI. Forms of speech. Application to non-mathematical formal terms: dragons, gods, philosophical

categories. Universality of the formal register.

## Part VII. Two-register logic. Logical properties of the extended system. Preservation of classical logic

in both registers. Difference in rules of inference.

## Part VIII. Open questions. Connection with proof theory. Preparation for VR-Audit. Possible

applications of the formal register in other areas.

## Part IX. Lean 4 formalisation of VR-Forms: methodological observations. Added in version 1.0.1.

Documents the Lean 4 formalisation of the two-register apparatus (Reznik 2026, Lean VR-Forms,
Software DOI 10.5281/zenodo.20355757; Git tag v1.3-vr-forms), reporting ten methodological
observations from the formalisation grouped into four thematic clusters: foundation-level properties
(Part IX §IX.1, two observations on import-freedom and inheritance from VR-Sets Classical-free closure
layer); the central structural boundary at conservativity and four substructural observations (Part IX
§IX.2, five observations); structural patterns in the apparatus (Part IX §IX.3, two observations); cross-
cycle integration (Part IX §IX.4, two observations including the finale on zero Classical.choice usage).
The formalisation is the most axiom-minimal of the four VR Lean cycles.

I.9. A note on tone
The work touches both the foundations of mathematics and speech in general. It is mathematical in
apparatus and philosophical in scope. The tone is sustained in the manner of the previous works of the
cycle: precision of definitions, sparsity of rhetoric, transparency of motivation.
The appearance of «dragons» and «gods» as examples of formal terms is not an artistic device or
provocation. It is a direct consequence of the position: the formal register is universal. If it really covers
speech without exception, it must be demonstrated on speech without exception.

## Part II. The Formal Language

II.0. Introduction
Part I set out the general position: the formal register as speech without ontological commitments. The
present part translates this position into formal apparatus.
Contents of Part II: precise definition of a formal term; syntax of the formal register; rules of formation
of formal terms; the relation of a formal term to an operational set of VR-Sets.
Part II is technically minimal. Its task is to fix the apparatus on which Parts III–VII will build
substantive results. No new ontological moves are made here; everything rests on Part I.

II.1. Alphabet and terms
The formal language of VR-Forms is built over the same alphabet as VR-Sets, extended by a register-
separator.

Alphabet
The alphabet of the formal language contains:
— the symbol ∅;
— the functional symbol t (successor);
— logical connectives →, ¬, ∧, ∨, ↔;
— quantifiers ∀, ∃;
— the membership relation ∈ ;
— the operational identity relation ≡ (from VR-Sets);
— variables x, y, z, …;
— brackets {, }, (, );
— the register-separator symbol ⌜·⌝ (see below).
The alphabet remains finite, so that countability of the syntax is preserved (VR-Sets §VI.1).

Terms and formulas
Terms and formulas are defined inductively in the standard way:
— ∅ is a term;
— if τ is a term, then t(τ) is a term;
— variables are terms;
— a description of the form {x : φ(x)}, where φ is a formula with one free variable x, is a term;
— other formulas are built from atomic x ∈ y, x ≡ y by connectives and quantifiers.
So far this is exactly the language of VR-Sets. The difference with VR-Forms arises in the rules of use of
terms, not in their syntax.

II.2. Register-separator
The same term may figure in the ontological or in the formal register. To make the distinction explicit in
writing, a syntactic separator is introduced.

Definition II.1 (register-separator)
For any term τ, the notation ⌜τ⌝ means: the term τ is considered in the formal register. The notation τ
without brackets means: the term is considered in the ontological register.
⌜·⌝ is not a function or operation. It is a sign of the mode of consideration. It indicates in which of the
two registers a given term is read.

Examples
— ∅ is the empty set in the ontological register. By Lemma 2 of VR-Sets it is the unique operational
object with empty functionality.
— ⌜∅⌝ is a formal term, the description «of the empty». In the formal register this is simply a formula;
no ontological commitments. (In practice for ∅ the ontological and formal registers coincide, since the
description directly corresponds to an operational object; the separator is here redundant but
admissible.)
— ⌜{x : x ∉ x}⌝ is the Russell formal term. Admissible in the formal register. The corresponding
ontological term {x : x ∉ x} does not specify a set (VR-Sets §II.3).
— ⌜ℝ⌝ is the formal term «classical set of reals». Admissible in the formal register.
— ℝ_VR is the notation for the operational set of computable reals of VR-Sets. In the ontological
register. Not the same as ⌜ℝ⌝.

A note on practice of notation
In the work, the separator ⌜·⌝ is used explicitly where the register is otherwise ambiguous. In contexts
where the register is clear from the text (for instance, «classical ℝ» — formal register; «ℝ_VR» —
ontological), the separator is omitted.

II.3. Definition of a formal term
We now give the central definition of the present work.

Definition II.2 (formal term)
A formal term is any correctly built syntactic record of a description, considered in the formal register.
Formally: a formal term is a pair (τ, F), where τ is a syntactically correct term of the language of VR-
Forms, and F is the register-marker indicating «formal». The notation ⌜τ⌝ denotes this pair.
Commentary
(1) A formal term is a pair: syntax plus indication of mode. The same τ specifies different entities
depending on the register: an operational set (in the ontological) or a formal term (in the formal).
(2) «Correctly built syntactic record» means: the term is built according to the rules of §II.1. No other
conditions — operationality, consistency, constructivity — are imposed. A formal term may be
contradictory, non-operational, refer to uncountable collections, describe the impossible. All this is
permitted.
(3) In the formal register there is no distinction between «existing» and «non-existing» formal terms.
All formal terms are formal terms. The differences in their content (countable, paradoxical, non-
mathematical) are properties of the description, not properties of being.

II.4. The principle of forms
Corresponding to the closure principle of VR-Sets (every describable operational functionality is a set),
there is in VR-Forms a parallel principle pertaining to the formal register.

The principle of forms
Every syntactically correct record of a description specifies a formal term.
No restrictions: operationality is not required, consistency is not required, describability in any special
sense is not required. It suffices that the record is syntactically correct by §II.1.

Comparison with the closure principle
The closure principle of VR-Sets applies in the ontological register and requires operational
describability. Contradictory descriptions (Russell) do not specify sets. This is a conditional principle:
given operationality — there is a set.
The principle of forms applies in the formal register and requires nothing other than syntactic
correctness. This is an unconditional principle: every description is a formal term.
Parallel and difference: both principles generate objects of their registers; but in the ontological register
the objects «are» (as actions upon ∅), and in the formal — «are formulas». The difference is not in the
statement of the principles, but in the ontological load of the objects they generate.

II.5. Relations and operations on formal terms
Formal terms are formulas. Yet one may work with formulas: formulate statements, derive
consequences, compare. This work is work in the formal register.

Membership
The notation ⌜x ∈ τ⌝ means: the formal statement «x belongs to the formal term τ». The truth value of
this statement is determined by the inference rules of the formal register, not by the ontology of VR-
Sets.
Example: let τ = ⌜{x : φ(x)}⌝. Then ⌜y ∈ τ⌝ is true in the formal register if and only if φ(y) is true (in
the formal register). This is the standard scheme of comprehension for formal terms.
Comprehension in the formal register is not restricted by an axiom of separation. Unlike ZF, where
comprehension applies only to elements of already existing sets, in the formal register any description
{x : φ(x)} directly specifies a formal term. This is what makes the Russell formal term a legitimate
object of the formal register.

Equality and identity
In the formal register the equality of two formal terms ⌜τ₁⌝ = ⌜τ₂⌝ is a statement about their
descriptions. Two formal terms are equal if they are given by one and the same formula (up to
renaming of bound variables) or if the equivalence is provable in the formal register.
This differs from ≡ of VR-Sets — the operational identity requiring coincidence of functionalities. In the
formal register there are no functionalities; there are formulas.

Logical operations
Connectives and quantifiers apply to formulas of the formal register in the usual way. Classical logic is
preserved. No special inference rules for formal terms are introduced.
This is an important technical feature: the formal register is not a new logic; it is the same logical
apparatus applied to a new type of objects (formal terms instead of operational sets).

II.6. Difference between a formal term and an operational set
Let us gather in one place a systematic comparison.

What is shared
— The same syntax: both formal terms and operational sets are written by formulas of one language.
— The same logic: classical, with the usual rules.
— The same starting primitive: ∅ is the base object of both registers.

What differs
Register. An operational set is in the ontological. A formal term is in the formal.
Ontological load. An operational set is (as action upon ∅). A formal term is a formula.
Condition of existence. An operational set requires operational describability (closure principle). A
formal term requires only syntactic correctness (principle of forms).
Paradoxes. Contradictory descriptions do not specify operational sets. Contradictory descriptions
specify formal terms without restriction.
Universe. All operational sets form the countable universe of VR-Sets. All formal terms form a
countable syntactic universe (since formulas are finite sequences over a finite alphabet).
Identity. Operational identity ≡ is the coinductive coincidence of functionalities. Formal identity = is
syntactic or formal-register-provable coincidence of descriptions.

Connection
To every operational set A there corresponds exactly one formal term ⌜A⌝ — the description of A itself,
considered in the formal register. Conversely: not every formal term has an operational correlate. Those
that do form a distinguished subfamily of formal terms — let us call it the operationally realisable
formal terms.
This subfamily is countable (by countability of operational sets). The set of all formal terms is likewise
countable (by finiteness of the alphabet). Both registers thus remain within the countable ontology of
VR.

II.7. Operationally realisable formal terms
We introduce this notion precisely — it will be needed in Part IV for the definition of transit.

Definition II.3
A formal term ⌜τ⌝ is called operationally realisable if in the ontological register there exists an
operational set A such that the description τ corresponds to the functionality A.
Equivalently: ⌜τ⌝ is operationally realisable if τ (without the formal-register marker) is an admissible
description in VR-Sets satisfying the closure principle.

Examples of realisable formal terms
⌜∅⌝, ⌜{∅}⌝, ⌜ω⌝, ⌜℘_VR(ω)⌝, ⌜ℝ_VR⌝ — all of these are realisable. Each corresponds to an operational
set of VR-Sets.
Any description of a computable functionality is an operationally realisable formal term.

Examples of non-realisable formal terms
⌜{x : x ∉ x}⌝ — the Russell term. Not realisable (the description is contradictory).
⌜ℝ⌝ (classical) — not realisable (uncountable, not operationally describable).
⌜the Vitali set⌝ — not realisable (requires choice over an uncountable family).
⌜dragon⌝ — not realisable (no operational action corresponds to the description).

Remark
The distinction «realisable / non-realisable» is a property of the formal term as a pair (description,
register). It only tells whether the formal term has an ontological correlate. The formal term itself does
not become «better» or «worse» from the presence or absence of realisation; in the formal register all
terms are equal.
The distinction matters only when we wish to translate results of the formal register into the
ontological — this is the subject of Part IV.

II.8. Connection with proof theory
The two-register system of VR-Forms structurally resembles several constructions known in logic.
Two-sorted logic. A standard extension of first-order logic in which variables are divided into sorts.
VR-Forms is formally a two-sorted system, with sorts «operational set» and «formal term». However,
the sorts in VR-Forms are not symmetric: the formal sort includes the operational (every operational
set has a formal correlate).
Conservative extensions. An extension of a theory is called conservative if no new statements about
old objects are provable in it. Part III will show: VR-Forms is conservative over VR-Sets in the
ontological register. The formal register does not allow new statements about operational sets to be
proved; it only provides a language for talking about the non-operational.
Realisability (Kleene, Kreisel). A notion linking constructive mathematics to classical: a formula is
considered «realisable» if it has a constructive witness. The notion of operational realisability in §II.7 is
an analogue of realisability specialised to the VR-ontology.
Internal set theory (Nelson). An extension of ZFC separating standard and nonstandard objects.
Structurally similar, but the motivation is opposite: IST introduces the nonstandard as a tool for proofs
about the standard. VR-Forms introduces the formal as a way to speak about the non-existent without
claiming proofs.
A detailed comparison with these systems — Part VII.

II.9. Summary of Part II
Established:
(1) Alphabet and syntax of VR-Forms coincide with VR-Sets, with the addition of the separator ⌜·⌝ for
indicating the register (§II.1, §II.2).
(2) A formal term is a pair (syntactic record, formal register); notation ⌜τ⌝ (Definition II.2, §II.3).
(3) The principle of forms: every syntactically correct record is a formal term. Unconditional, in contrast
with the conditional closure principle (§II.4).
(4) Logic and operations are classical, applied to formal terms in the usual way (§II.5).
(5) Systematic comparison of formal term and operational set (§II.6).
(6) The notion of operationally realisable formal term (Definition II.3, §II.7).
(7) Connections with two-sorted logic, conservative extensions, realisability, IST (§II.8).
What follows. Part III proves consistency of the extension: VR-Forms is conservative over VR-Sets in
the ontological register. This theorem secures the safety of work in the formal register — no new
ontological commitments are generated.

## Part III. The Principle of Forms and Consistency

III.0. Introduction
Part II provided the apparatus: the formal language, register-separator, definition of a formal term,
principle of forms. The present part proves a key property of this apparatus — its safety.
Safety means: adding the formal register to VR-Sets does not generate new contradictions and does not
allow anything new to be proved in the ontological register that could not be proved in VR-Sets without
the formal register. In other words, VR-Forms is a conservative extension of VR-Sets.
This secures the freedom of work in the formal register. One may introduce paradoxical terms, terms for
uncountable collections, terms for mythological beings — and be confident that the ontological register
suffers no harm. The boundary between the registers holds formally.
Contents of Part III: formal statement of conservativity (§III.1); main theorem (§III.2); consequences
(§III.3); comparison with the consistency of VR-Sets relative to ZF (§III.4); summary (§III.5).

III.1. Statement
Before proving, let us precisely formulate what is being proved.

Languages and theories
Let us denote:
— L₀ — the language of VR-Sets: alphabet and terms without the marker ⌜·⌝.
— L₁ — the language of VR-Forms: alphabet of L₀ plus the marker ⌜·⌝, and with it the possibility of
forming a formal term ⌜τ⌝ from any syntactically correct τ.
— T₀ — the theory of VR-Sets: the closure principle and operational definitions (set, ∅, ≡, ZFC/ZFA
modes).
— T₁ — the theory of VR-Forms: everything that is in T₀, plus the principle of forms (§II.4) and the
rules of work with formal terms (§II.5).
Formulas of L₀ are called ontological: they speak only about operational sets. Formulas of L₁ may
contain formal terms.

Definition III.1 (conservativity)
A theory T₁ is conservative over T₀ if for every ontological formula φ ∈ L₀:
T₁ ⊢ φ ⟺ T₀ ⊢ φ.
That is: everything VR-Forms proves about operational sets, VR-Sets could already have proved without
the help of the formal register. The formal register adds no new ontological force.
What is to be proved
The main theorem of Part III: T₁ is conservative over T₀.
In particular, it follows that if T₀ is consistent, so is T₁.

III.2. Conservativity theorem
Theorem III.1 (conservativity of VR-Forms over VR-Sets)
For every ontological formula φ of the language L₀:
T₁ ⊢ φ ⟺ T₀ ⊢ φ.

Proof
Direction (⟸ ) is trivial: every proof in T₀ is also a proof in T₁ (T₁ contains all axioms and rules of T₀ ).
Substantive direction (⟹). Let T₁ ⊢ φ, where φ ∈ L₀. We show that T₀ ⊢ φ.
Idea of the proof: every occurrence of a formal term ⌜τ⌝ in the proof can be eliminated by replacement
with an equivalent ontological formula. More precisely, formal terms are syntactic objects; their use in
the proof reduces to manipulations with formulas without ontological load. If the final formula φ is
ontological, all intermediate formal terms can be «crossed out» by appropriate substitution.
Step 1: translation. Define a mapping π from formulas of L₁ to formulas of L₀ :
— For a formula ψ ∈ L₀: π(ψ) = ψ.
— For an atomic formula ⌜x ∈ τ⌝, where τ is the description {y : ψ(y)}: π(⌜x ∈ τ⌝) = ψ(x)
(comprehension, see §II.5).
— For an atomic formula ⌜τ₁⌝ = ⌜τ₂⌝, where τ₁ = {y : ψ₁(y)}, τ₂ = {y : ψ₂(y)}: π(⌜τ₁⌝ = ⌜τ₂⌝) = ∀y (ψ₁(y)
↔ ψ₂(y)).
— Connectives and quantifiers — π by induction: π(¬α) = ¬π(α), π(α ∧ β) = π(α) ∧ π(β), π(∀x α) =
∀x π(α), and similarly.
The translation π reduces every formula of L₁ to a formula of L₀: formal terms are replaced by their
defining predicates, and the whole formula becomes a statement about properties of objects.
Step 2: preservation of ontological formulas. If φ ∈ L₀, then π(φ) = φ. That is, on ontological
formulas π is the identity.
Step 3: compatibility of π with the inference rules of T₁. All inference rules of T₁ — rules of
classical logic plus axioms of T₀ plus the principle of forms. We show that π translates every inference
rule of T₁ into an admissible step in T₀.
(a) Rules of classical logic (modus ponens, generalisation, and so on) are compatible with π, since π
preserves connectives and quantifiers by definition.
(b) Axioms of T₀ remain themselves under π — they are already in L₀.
(c) The principle of forms. In T₁ the principle of forms states: every description specifies a formal
term. Substantively this means that for any description {y : ψ(y)} we can form the formal term ⌜{y :
ψ(y)}⌝ and work with it by the rules of §II.5. Under π this step is translated into work directly with the
predicate ψ — that is, into a usual application of the comprehension scheme in L₀, which in T₀
generates nothing new (since the comprehension scheme in T₀ is restricted by the closure principle, see
below).
Here is the subtlety. In T₀ comprehension applies to operational descriptions; in T₁ comprehension
applies to arbitrary (formal). But π translates the formal term ⌜{y : ψ(y)}⌝ back into the predicate ψ.
All statements about the formal term become statements about the predicate. And statements about
predicates in T₀ are standard first-order statements and do not require operational describability of the
predicate.
That is: the formal register serves to say «there is something described by ψ», but π converts this
«something» back into simply «property ψ». No new object appears; only a property is there, and one
speaks about it in the language of T₀.
Step 4: consequence. If T₁ ⊢ φ, there is a derivation D in T₁ ending in φ. Apply π to each formula of D.
We obtain a sequence of formulas of L₀ (by Step 1) in which:
— the first formula π(axiom of T₁) is either an axiom of T₀ (if the original axiom was in T₀) or an
admissible application of comprehension (if the original axiom was an instance of the principle of
forms).
— every subsequent step π(application of rule) is an admissible step in T₀ (by Step 3).
— the last formula π(φ) = φ (by Step 2).
We obtain a derivation of φ in T₀. Hence T₀ ⊢ φ.
∎

Remark on the method
The method used is a standard technique for conservativity proofs via interpretation. The formal
register receives an interpretation in the ontological: every formal term is a «figure of speech» about a
property. Under such an interpretation, everything provable with the use of figures of speech is also
provable without them — if the final statement is not itself a figure of speech.
This method is analogous to the interpretation of classes in NBG via formulas of ZFC, or the
interpretation of abstractions in λ-calculus via β-reduction. The content is the same: a syntactic
extension that does not carry new commitments.

III.3. Consequences
Corollary III.1 (consistency)
If T₀ is consistent, then T₁ is consistent.
Proof. Let T₁ be inconsistent: T₁ ⊢ ⊥. Since ⊥ ∈ L₀, by Theorem III.1 T₀ ⊢ ⊥. Contradiction. ∎
Since the consistency of T₀ is established in VR-Sets (through the arithmetical equivalence with PA and
the consistency of VR-Sets relative to ZF), it follows:

Corollary III.2
VR-Forms is consistent relative to ZF.

Corollary III.3 (safety of paradoxical formal terms)
The introduction into the formal register of the Russell term ⌜{x : x ∉ x}⌝, the liar, the set of all sets, and
other paradoxical descriptions does not generate contradictions in T₁.
Justification. All these terms are syntactically correct descriptions. By the principle of forms they are
formal terms. By Theorem III.1 any ontological statement derivable in T₁ with their use is derivable also
without them. In particular, the contradiction ⊥ ∈ L₀ is not derivable in T₁ if not derivable in T₀.
Paradoxicality here becomes a property of the description, not a source of contradiction. The Russell
term ⌜R⌝ is a formal term satisfying the formula ⌜R⌝ ∈ ⌜R⌝ ↔ ⌜R⌝ ∉ ⌜R⌝. This is a formal statement
about a formal term; it shows that ⌜R⌝ has no ontological correlate (if it had, the contradiction would
also be in T₀). And nothing more follows from this.

Corollary III.4 (safety of non-mathematical formal terms)
The introduction into the formal register of ⌜dragon⌝, ⌜god⌝, ⌜soul⌝ and similar descriptions does not
generate contradictions in T₁.
Justification. Similar to Corollary III.3. These terms are syntactically correct descriptions; legitimate in
the formal register by the principle of forms; their operational correlate is absent; no ontological
consequences follow from their presence in the formal register.

III.4. Comparison with the consistency of VR-Sets
The chain of consistency in the VR cycle now looks like this:
VR ↔ PA ↪ ZF (established in VR. A Formal System, Part II)
VR-Sets ↪ ZF (established in VR-Sets, through modelling of the operational universe in classical ZF)
VR-Forms ↪ VR-Sets ↪ ZF (established in the present Part III, as conservative extension)
Each link of the chain: consistency of the preceding follows from consistency of the next. If ZF is
consistent, all four systems of the VR cycle are consistent.
Remark on strength. Conservativity of VR-Forms over VR-Sets — this is equal strength in the
ontological register, but extended language. VR-Forms can speak of more (including the uncountable,
paradoxical, mythological), but proves in the ontological register exactly as much as VR-Sets. This is the
essence of conservative extension: extending the language without extending the theoretical strength
for the original fragment of the language.
Analogy: NBG (Bernays–Gödel) is a conservative extension of ZFC, adding classes as objects. About sets,
NBG proves the same as ZFC; but NBG has a more convenient language for speaking about classes. VR-
Forms plays the same role relative to VR-Sets: extension of language for talking about the non-
operational, without changing ontological strength for the operational.

III.5. Summary of Part III
Established:
(1) Distinction of languages and theories of VR-Sets (L₀, T₀) and VR-Forms (L₁, T₁) (§III.1).
(2) Definition of conservativity (Definition III.1, §III.1).
(3) Conservativity theorem: T₁ is conservative over T₀ (Theorem III.1, §III.2). Proof via interpreting
mapping π, translating formal terms into their defining predicates.
(4) Consistency of VR-Forms relative to ZF (Corollary III.2, §III.3).
(5) Safety of paradoxical and non-mathematical formal terms (Corollaries III.3, III.4, §III.3).
(6) Place of VR-Forms in the chain of consistency of the VR cycle (§III.4).
What follows. Part IV is devoted to transits — rules by which work in the formal register may yield
results in the ontological register. The conservativity theorem guarantees the safety of transits; Part IV
provides their positive content: when and how the formal register is able to help operational proofs.

## Part IV. Transits

IV.0. Introduction
Part III established the conservativity of VR-Forms over VR-Sets. This is a negative result: the formal
register does not generate new ontological statements. Part IV provides the positive content: the
formal register helps in reasoning about operational sets, even without adding new theorems.
The help consists in the following. Many classical proofs use uncountable intermediaries: classical ℝ, σ-
algebras, Lebesgue measure, the axiom of choice for uncountable families. These intermediaries are not
themselves operational. But if a proof using them ends in an ontological statement, then — by
conservativity — this statement is provable also without the intermediaries. Part IV formulates the
transit: a rule by which a formal proof of an ontological statement is recognised as a proof in VR-Sets.
Contents: notion of transit (§IV.1); transit rule and its justification (§IV.2); notion of witness (§IV.3);
safe and problematic transits (§IV.4); examples (§IV.5); summary (§IV.6).

IV.1. The notion of transit
A transit is the passage from the formal register to the ontological. More precisely: the use of formal
terms as intermediate means in a proof whose result is an ontological statement.

Definition IV.1 (transit)
A transit is a derivation in T₁ in which:
(a) the final formula φ is ontological (φ ∈ L₀);
(b) in intermediate steps of the derivation formal terms are used (a nonzero number of steps contains
the marker ⌜·⌝).
A transit, then, is a derivation that passes through the formal register on the way to an ontological
result.

What conservativity promises
By Theorem III.1, if such a derivation exists in T₁, there also exists a derivation of φ in T₀ (without
formal terms). That is, every transit can be rewritten as an ontological proof.
However, the rewriting may require substantial work. In practice, a formal derivation can be shorter
and clearer than the equivalent ontological one. A transit is a way of using the formal register to ease
the work, knowing in advance that the result is ontological.

IV.2. The transit rule
Let us formalise how exactly to use a transit.
Transit rule
If a derivation D ending in an ontological formula φ is constructed in T₁, then φ is accepted as proved in
T₀.
Justification. By Theorem III.1. The existence of a derivation in T₁ of an ontological formula is
equivalent to the existence of a derivation in T₀.
The transit rule, then, is not a new inference rule. It is a methodological permission: one may work in
the formal register, and the result automatically belongs to the ontological, provided it is itself
ontological.

What transit does not do
A transit does not turn formal terms into ontological objects. The Russell term ⌜R⌝, used in a transit,
does not become a set. It remains a formal term used as an intermediate syntactic element. Only the
final formula, if it is ontological, passes into the ontological register.
A transit does not allow anything to be proved in T₀ that could not be proved without the transit. It is
only a convenient way to conduct a proof. No new strength is provided by the transit.
A transit does not «justify» formal terms. That a certain formal term is used in a transit does not mean it
is operationally realisable (see §II.7). Many formal terms figure in transits while remaining non-
realisable. Realisability is a separate question; transit is a syntactic procedure.

IV.3. Witness
Connected with transit is the notion of witness — an operational object whose existence is proved by
the transit.

Definition IV.2 (witness)
Let a formula φ have the form ∃x ψ(x), where ψ is ontological. A witness of φ is an operational set A
such that ψ(A) is true in T₀.
A transit may prove ∃x ψ(x) — that is, the existence of a witness — without exhibiting a specific A. This
is the typical situation of non-constructive proofs in classical mathematics.

Extraction of a witness
If a transit yields ∃x ψ(x), then by conservativity there is a derivation of ∃x ψ(x) in T₀. However, this
derivation may not be constructive: it establishes existence without exhibiting x.
The existence of a witness extraction is a separate question. For constructive proofs existence entails
construction; for classical it does not necessarily. VR-Forms inherits this distinction: transit yields an
ontological statement but does not always yield an operational construction.

Remark
This is the place where the boundary between two possible roles of VR-Forms is visible.
Weak role (proof of existence): transit is used to establish that an operational object with a given
property exists. The object itself may remain unspecified.
Strong role (construction): transit is used as a heuristic — formal reasoning suggests how to build an
operational object. The construction is then verified in the ontological register.
Both roles are admissible. In practice the strong role is preferable, since it yields an explicit operational
object, not leaving it «known only formally».

IV.4. Safe and problematic transits
All transits are safe in the sense of consistency (Part III). However, from a practical viewpoint direct
and problematic transits can be distinguished.

Direct transits
A transit is called direct if in it formal terms are used as convenient abbreviations for ontological
objects. That is, all intermediate formal terms are operationally realisable (§II.7), and the use of the
formal register is mere syntactic convenience.
Direct transits trivially rewrite into ontological proofs. Their use is a stylistic decision.

Problematic transits
A transit is called problematic if it essentially uses non-realisable formal terms. That is, intermediate
steps refer to ⌜ℝ⌝, ⌜℘(ℝ)⌝, ⌜the Vitali set⌝, to choice functions over uncountable families, and so on.
Here one must be more careful. Conservativity guarantees that the result of a problematic transit is
translatable into the ontological register — but the rewriting may be cumbersome, and sometimes
require substantial operational work.

A principal observation
Problematic transits are places where classical mathematics essentially leans on uncountability. If the
result of a transit is ontological (for example, a statement about a concrete computable function), then
by conservativity it is provable also without uncountable intermediaries. This is the programme of
VR-Audit — analysis of classical theorems with the aim of extracting the ontological remainder.
Within Part IV: established only that the rewriting is possible. How to conduct it in concrete cases —
the subject of Parts V onward, and in full — the programme of VR-Audit.

IV.5. Examples
Example 1: proof of the countability of the set of algebraic numbers
Classical proof: the set of polynomials with rational coefficients is countable (as a countable union of
countable sets); each polynomial has finitely many roots; therefore there are countably many algebraic
numbers.
This proof is already ontological: all its steps concern operational sets (ℚ, polynomials with rational
coefficients, roots). No transit is needed. The result belongs to T₀.

Example 2: proof of Bessel's inequality
Bessel's inequality in Hilbert space: for any orthonormal family {eₙ} and any x in the space, Σ|⟨x, eₙ⟩|² ≤
‖x‖².
The classical proof uses the formulation «Hilbert space», which in the full classical form is uncountable.
However, the inequality itself is a statement about operational objects, if x and {eₙ} are computable.
Transit: using ⌜Hilbert space⌝ as a formal term in intermediate steps, we obtain an ontological result —
the inequality for concrete computable x and {eₙ}.
By conservativity this means that Bessel's inequality for computable data is provable in VR-Sets directly.
The transit here is convenience, not necessity.

Example 3: a proof essentially using the uncountable
The Hahn–Banach theorem in its general classical formulation: every bounded linear functional given
on a subspace extends to the whole space with preservation of norm.
The classical proof uses Zorn's lemma, which depends on AC for uncountable families. The formal term
⌜functional on the whole ℝ-space⌝ is essentially non-realisable.
Transit: if the result of the theorem is a statement about a computable extension of a computable
functional, then by conservativity the result is provable in VR-Sets. But the rewriting here is non-trivial:
an explicit operational construction of the extension is needed, which in the general case requires
additional work. This is an example of a problematic transit, requiring operational labour to extract
the ontological content.

Example 4: spectral theorem for the harmonic oscillator
The harmonic oscillator has discrete spectrum E_n = ω(n + 1/2). The classical formulation of the
spectral theorem uses ⌜projection-valued measure⌝ — a formal term requiring an uncountable σ-
algebra.
But for the harmonic oscillator this formal apparatus is superfluous: the discrete spectrum and
eigenfunctions (Hermite polynomials multiplied by a Gaussian) are operational. The transit here yields
an ontological statement — for example, computability of matrix elements of the energy operator —
without essential dependence on uncountable structure.
This is an example where the formal register is replaced by a direct operational construction. The
transit here is a methodological permission to use the classical proof, but more valuable content is
provided by the direct operational derivation, which we build directly in T₀.

IV.6. Summary of Part IV
Established:
(1) Transit as a derivation in T₁ passing through formal terms and ending in an ontological formula
(Definition IV.1, §IV.1).
(2) Transit rule: every transit yields a proof in T₀ (§IV.2). Justification — Theorem III.1.
(3) The notion of witness and the distinction of the weak (existence) and the strong (construction) roles
of transit (§IV.3).
(4) Distinction of direct and problematic transits (§IV.4); problematic — places where classical
mathematics essentially leans on the uncountable.
(5) Examples: algebraic numbers (no transit), Bessel's inequality (direct transit), Hahn–Banach
(problematic), harmonic oscillator (direct operational replacement) (§IV.5).
Methodological role of Part IV. Part IV closes the technical apparatus of VR-Forms. Onward we pass
to substantive application of the apparatus to classical mathematical (Part V) and non-mathematical
(Part VI) formal terms.
Connection with VR-Audit. Part IV outlines a programme: for each classical theorem φ, determine
whether its proof is a direct transit (i.e. φ is provable in VR-Sets without essential loss), a problematic
transit (requires operational labour to extract content), or not a transit at all (φ is non-ontological,
remains in the formal register). Systematic conduct of such an analysis is the content of the future work
VR-Audit; VR-Forms provides for it the apparatus.

## Part V. Forms of Mathematics

V.0. Introduction
Parts II–IV gave the apparatus of VR-Forms. Part V applies it to classical mathematics. The aim is to
demonstrate how uncountable, paradoxical and non-operational mathematical objects find their place
in the formal register, and how this changes their status.
Method of exposition: for each characteristic class of formal terms we give (1) the classical description,
(2) status in the VR-Sets ontological register, (3) status in the formal register of VR-Forms, (4)
methodological consequences.
Contents of Part V: classical ℝ as formal term (§V.1); classical ℘(ℕ) (§V.2); the Vitali set and AC for
uncountable families (§V.3); the Russell term and paradoxical classes (§V.4); proper classes (NBG) and
their status (§V.5); summary (§V.6).

V.1. Classical ℝ
Classical description
Classical ℝ — the set of all real numbers, defined in one of equivalent ways: as the complete ordered
field, as the set of Dedekind cuts of ℚ, as the set of equivalence classes of fundamental sequences in ℚ.
Cardinality 2^ℵ₀ — uncountable.

Status in VR-Sets
In VR-Sets there is ℝ_VR — the operational set of computable reals, isomorphic to the field of
computable reals (VR-Numbers §V.4). ℝ_VR is countable: each computable real is given by an
algorithm, algorithms are countable.
The full classical ℝ is ontologically absent in VR-Sets. Not as «forbidden», but as a description signifying
nothing: «the set of all reals» in the operational ontology does not specify a functionality (there is no
procedure that would enumerate all reals).

Status in VR-Forms
⌜ℝ⌝ is a formal term. Admissible in the formal register by the principle of forms. Not operationally
realisable.
In the formal register one can formulate statements about ⌜ℝ⌝: «the cardinality of ⌜ℝ⌝ is 2^ℵ₀», «⌜ℝ⌝ is
complete as a metric space», «⌜ℝ⌝ is ordered». All these statements belong to the formal register. They
do not generate ontological objects and have no ontological force.

Methodological consequences
Statements of the form «property P holds for all reals» in the formal register speak of ⌜ℝ⌝. To translate
such a statement into the ontological register, one must show that for all elements of ℝ_VR (i.e. for all
computable reals) the property P holds. This is passage via transit (§IV.2).
If P holds for all ℝ_VR — we obtain an ontological statement. If P holds for the classical ⌜ℝ⌝ but is not
derivable for ℝ_VR without essential dependence on uncountability — this is the case of a problematic
transit (§IV.4).
In practical mathematics most statements about ℝ relate to properties derivable from computability
(completeness, ordering, field, metric). These statements transit directly. Statements essentially using
uncountability (Liouville's theorem on transcendental numbers, the existence of measurable non-
recursive sets) require separate analysis.

V.2. Classical ℘(ℕ)
Classical description
℘(ℕ) — the set of all subsets of ℕ. By Cantor's theorem it has cardinality 2^ℵ₀, uncountable.

Status in VR-Sets
℘_VR(ℕ) — the operational set of describable subsets of ℕ (VR-Sets §III.5). Countable. Contains all
computable subsets of ℕ.
The statement «℘_VR(ℕ) is countable» is true in the ontological register. Cantor's diagonal argument in
the operational ontology does not work for the same reasons as in Computable Analysis: there is no
effective enumeration of all describable subsets (this is equivalent to the halting problem), so the
diagonal construction is not operational.

Status in VR-Forms
⌜℘(ℕ)⌝ is a formal term. In the formal register the statement «⌜℘(ℕ)⌝ has cardinality 2^ℵ₀» is
admissible. The statement «⌜℘(ℕ)⌝ is uncountable» is also admissible. Both belong to the formal
register.
Here the difference of the two registers becomes visible. In the ontological: ℘_VR(ℕ) is countable. In the
formal: ⌜℘(ℕ)⌝ is uncountable. No contradiction — these are statements about different objects.
℘_VR(ℕ) is an operational set; ⌜℘(ℕ)⌝ is a formal term; they are not identical.

Skolem's paradox in VR-Forms
In the classical context Skolem's paradox is the observation that ZFC has a countable model in which
«℘(ℕ) is uncountable» is true (Löwenheim–Skolem). This is regarded as ontologically disconcerting:
«how can ℘(ℕ) be countable from outside but uncountable from inside?»
In VR-Forms Skolem's paradox is removed explicitly. The «inside/outside» distinction becomes a
distinction of registers. ℘_VR(ℕ) is countable ontologically («outside», in the full picture). ⌜℘(ℕ)⌝ is
uncountable formally («inside», as a statement about a formal term). These are two different objects,
each with its true status in its own register.
V.3. The Vitali set and AC for uncountable families
Classical description
The Vitali set — a choice of one representative from each equivalence class on ℝ under the relation x − y
∈ ℚ . The existence requires AC for an uncountable family (the number of equivalence classes is
uncountable). Not Lebesgue measurable.

Status in VR-Sets
The Vitali set is ontologically absent in VR-Sets. The description «choose one from each class» is not
operational: there is no procedure that would, on the request «give the next class», yield a definite
representative (classes are uncountable). AC in VR-Sets is a theorem about countable families (VR-Sets
§III.9 and §VI.4), not applicable to uncountable.
The Banach–Tarski paradox is absent in VR-Sets by construction, since it uses precisely Vitali-like
uncountable choices (VR-Sets §VI.5).

Status in VR-Forms
⌜V⌝ is the formal term for the Vitali set. In the formal register the statement «⌜V⌝ exists» is admissible
(by the principle of forms every description specifies a formal term). The statement «⌜V⌝ is non-
measurable» — formal.
⌜Banach–Tarski⌝ — a formal theorem about a paradoxical decomposition of ⌜the ball⌝ into a finite
number of parts and assembly of two ⌜balls⌝. In the formal register admissible as a formal theorem. In
the ontological register no analogue.

Methodological consequences
If in some context Vitali is used (for example, to construct a non-measurable set), this can be described
in the formal register, but the operational correlate is absent. All applications essentially requiring Vitali
remain in the formal register.
On the other hand, many classical results formally using AC for uncountable families can be rewritten
without it — this is the programme of Reverse Mathematics. VR-Forms provides for this programme a
natural frame: check whether the use of uncountable AC is essential (i.e. the transit is problematic in
the sense of §IV.4) or eliminable (direct transit).

V.4. The Russell term and paradoxical classes
Classical description
Russell's class R = {x : x ∉ x}. In naive set theory — source of the paradox: R ∈ R ↔ R ∉ R. In ZF
dissolved by the axiom of separation: one can form only {x ∈ A : x ∉ x} for an already existing A, and
this does not generate R as a whole.
Status in VR-Sets
R is not an operational set (VR-Sets §II.3). The description «a functionality that yields x if and only if x
does not yield itself» contains a contradiction on the query «R ∈ R?». The closure principle does not
apply to contradictory descriptions.

Status in VR-Forms
⌜R⌝ is a legitimate formal term. The principle of forms does not forbid contradictory descriptions
(§II.4): syntactic correctness suffices.
In the formal register the statement ⌜R⌝ ∈ ⌜R⌝ ↔ ⌜R⌝ ∉ ⌜R⌝ is admissible. This is a formal statement
about a formal term, derivable directly from the definition of ⌜R⌝.
This generates no contradiction in T₁. Proof: if from ⌜R⌝ ∈ ⌜R⌝ ↔ ⌜R⌝ ∉ ⌜R⌝ one could derive ⊥ ∈ L₀
(an ontological contradiction), then by conservativity ⊥ would be derivable also in T₀, which is not the
case.

A new reading of Russell
In the classical setting Russell's paradox is an indication of the necessity to restrict the formation of sets.
In VR-Forms Russell's paradox has a different meaning: it shows that the description ⌜R⌝ has no
operational correlate. This is not a defect of the description, but a property of it: some formal terms
are operationally non-realisable.
Paradoxicality is a property of form, not an ontological failure. The liar, Berry, Grelling, Burali-Forti —
all classical paradoxes in VR-Forms become statements about properties of formal terms, saying that the
corresponding descriptions have no ontological correlate.

Remark on the freedom of the formal register
The admissibility of contradictory formal terms might seem alarming — but it does not break classical
logic in the formal register. Logical operations apply to formulas as usual, and from a local contradiction
(such as ⌜R⌝ ∈ ⌜R⌝ ↔ ⌜R⌝ ∉ ⌜R⌝) no global contradiction follows.
The point is that the contradiction ⌜R⌝ ∈ ⌜R⌝ ↔ ⌜R⌝ ∉ ⌜R⌝ is not a statement «is and is not at once»; it is
a statement «the formal term ⌜R⌝ has such a property». The property characterises ⌜R⌝, separating it
from operational sets. No universal logical catastrophe follows from it.

V.5. Proper classes
Classical description
In NBG (Bernays–Gödel) and MK (Morse–Kelley) extensions of ZFC, proper classes are introduced —
collections too «large» to be sets. The class of all sets V, ordinals Ord, cardinals Card — proper classes.
They are not elements of any set.
Status in VR-Sets
In VR-Sets proper classes are absent in the classical form, since the whole universe is countable (VR-Sets
§VI.1) and the «too large» in the classical sense does not arise. However, there is an analogue:
describable families of functionalities that are not themselves functionalities. For instance, «the
family of all computable functions ℕ → ℕ» is a describable family but not an operational set (no
procedure for their effective enumeration; this reduces to the halting problem).

Status in VR-Forms
⌜V⌝ (the class of all sets) is a formal term. Admissible in the formal register. ⌜Ord⌝, ⌜Card⌝ — also
formal terms.
The formal register plays here the same role as classes in NBG: it allows one to speak about large
collections without introducing them into the ontology. Difference: in NBG classes are second-sort
objects; in VR-Forms formal terms are formulas, not objects.

The hierarchy of t-applications
In VR-Sets §VII.3 the hierarchy of applications of the successor t was discussed as an operational
analogue of Tarski's hierarchy of metalanguages. In VR-Forms this hierarchy receives an additional
reading.
Each t^n(ω) is an operational set. Their union, «the entire hierarchy t^n», is a describable family that is
not an operational set (it is an unbounded process). In the formal register it is a formal term ⌜⋃_n
t^n(ω)⌝ — an operational analogue of a proper class. This is an illustration: in VR-Forms the «too
large» does not disappear; it passes into the formal register, remaining workable as a figure of speech.

V.6. Summary of Part V
Established:
(1) Classical ℝ is a formal term ⌜ℝ⌝, not identical with the operational ℝ_VR (§V.1).
(2) Classical ℘(ℕ) is a formal term ⌜℘(ℕ)⌝, not identical with the operational ℘_VR(ℕ); Skolem's
paradox is removed as a difference of registers (§V.2).
(3) The Vitali set and the Banach–Tarski paradox are formal terms; in the ontological register they are
absent (§V.3).
(4) The Russell class is a legitimate formal term with a contradictory characteristic; paradoxicality is
reinterpreted as a property of form indicating operational non-realisability (§V.4).
(5) Proper classes of NBG correspond to formal terms of VR-Forms; the hierarchy of t-applications
provides the operational analogue of a proper class (§V.5).
General conclusion. The formal register of VR-Forms covers the whole classical set theory —
uncountable collections, paradoxical classes, large classes of NBG — without placing any burden on the
ontology beyond the countable operational universe. Classical mathematics becomes speech about
formal terms, operationally realisable only in part; the programme of VR-Audit consists in a systematic
classification of what in this speech has an ontological correlate and what does not.
What follows. Part VI extends the formal apparatus to non-mathematical descriptions — dragons,
gods, philosophical categories — demonstrating the universality of the formal register. This is a natural
completion of applications: the formal language of VR-Forms works with speech without exception, not
only mathematical.

## Part VI. Forms of Speech

VI.0. Introduction
Part V applied the formal apparatus to classical mathematics: classical ℝ, ℘(ℕ), Vitali, Russell's class,
proper classes — all received the status of formal terms. Part VI extends the application beyond
mathematics: to mythological beings, theological concepts, literary figures, philosophical categories.
This is not a rhetorical move and not an artistic extension. It is a test of the universality of the formal
register. If the formal register really covers speech without exception, it must work uniformly with
mathematical and non-mathematical descriptions. Part VI demonstrates exactly this.
Contents: universality of the formal register (§VI.1); mythological terms (§VI.2); theological terms
(§VI.3); philosophical categories as formal terms (§VI.4); literary figures (§VI.5); status of non-
mathematical terms and its philosophical significance (§VI.6); summary (§VI.7).

VI.1. Universality of the formal register
The principle of forms (§II.4) states: every syntactically correct record of a description specifies a formal
term. No restrictions on the content of the description are imposed. The description may be
mathematical, may be non-mathematical, may refer to the existing, the non-existing, the imagined, the
paradoxical. The principle of forms applies to all uniformly.
This means: the formal register of VR-Forms is a universal language of descriptions. Everything for
which a correct syntactic description can be formed has a place in it as a formal term.

Remark on syntactic correctness
«Syntactic correctness» in VR-Forms is a formal notion, set by the rules of §II.1. A description is correct
if it is built by these rules. This means the syntax of VR-Forms is a fixed formal language; descriptions in
natural language («a fire-breathing dragon», «an omnipotent god») are not directly expressed in it.
However, every meaningful natural-language description can be translated into the formal — if a
definite predicate is assigned to it. «Dragon» becomes a formal term ⌜{x : x is a fire-breathing lizard-like
creature with wings}⌝, where «is a fire-breathing lizard-like creature with wings» is a predicate
expressed in the language of VR-Forms (via a chosen system of feature designations). Similarly with
«god», «soul», «unicorn».
Thus the non-mathematical terms in VR-Forms are not literary figures as such, but their
formalisations through predicates. The choice of formalisation depends on context; different contexts
may give different «dragons» (Chinese, European, mythological, literary), and each formalisation is its
own formal term.
VI.2. Mythological terms
Dragon
⌜dragon⌝ is a formal term. Formalisation: ⌜{x : fire_breathing(x) ∧ lizard_like(x) ∧ winged(x)}⌝, where
the predicates «fire_breathing», «lizard_like», «winged» are elements of the chosen feature system.
In the ontological register of VR-Sets: the corresponding operational set is absent. The description «a
functionality enumerating all fire-breathing lizard-like winged creatures» is not a procedure over ∅; no
operational action realises it.
In the formal register: ⌜dragon⌝ is a formal term. One can speak of it, formulate statements: «⌜dragon⌝
breathes fire» (true in the formal register by definition of ⌜dragon⌝), «⌜dragon⌝ exists» — a statement
of the formal register, having no ontological force.

Unicorn, phoenix, centaur, minotaur
Analogously. Each is a formal term with its own formalisation:
⌜unicorn⌝ = ⌜{x : horse_like(x) ∧ single_horned(x)}⌝
⌜phoenix⌝ = ⌜{x : bird_like(x) ∧ reborn_from_ashes(x)}⌝
⌜centaur⌝ = ⌜{x : has_human_upper_body(x) ∧ has_horse_lower_body(x)}⌝
All formal terms. None operationally realisable. For each, one can formulate correct statements in the
formal register that follow from the definition.

Remark on biological consistency
Some mythological terms are formally contradictory in a strong sense — that is, their definitions rely
on properties biologically incompatible. For example, ⌜centaur⌝ with two cardiovascular systems, or
⌜dragon⌝ with an endogenous fire organ without thermal damage.
This does not make the formal term inadmissible in VR-Forms. The principle of forms does not require
biological or physical consistency. Syntactic correctness suffices.
This is an analogue of the mathematical case in which contradictory formal terms are admissible
(Russell's class). In the formal register contradictoriness is a property of the description, not a
prohibition.

VI.3. Theological terms
God in monotheistic understanding
⌜god⌝ = ⌜{x : unique(x) ∧ omnipotent(x) ∧ eternal(x) ∧ creator_of_world(x)}⌝ — a formal term. The
formalisation is the standard theological definition translated into predicate form.
In the ontological register of VR-Sets: the corresponding operational set is absent. No procedure over ∅
realises «the unique omnipotent eternal creator». Not as a «prohibition» but as a description signifying
nothing in the operational ontology: operationally not reproducible.
In the formal register: ⌜god⌝ is a formal term. One can speak of it, prove statements following from the
definition: ⌜god⌝ is unique (by definition), ⌜god⌝ created ⌜the world⌝ (if ⌜the world⌝ is a separate
formal term), and so on.

Classical theological paradoxes
The paradox of the stone (can an omnipotent god create a stone he cannot lift?) in VR-Forms is treated
as a statement of the formal register about the properties of ⌜god⌝, in particular about the consistency of
the predicate «omnipotent». If the formalisation of omnipotence is contradictory (as in this paradox),
then ⌜god⌝ in the given formalisation contains a contradictory characteristic — analogously to the
Russell term. This is a property of the description, not an ontological failure.
This reinterpretation is consistent with the general position of VR-Forms: paradoxicality of theological
concepts is a property of the chosen formalisation. Other formalisations (omnipotence as «can do all
that is logically possible») generate no such contradiction; and these other formalisations are their own
formal terms.

God in polytheistic and other systems
⌜Zeus⌝, ⌜Odin⌝, ⌜Brahma⌝, ⌜Allah⌝ — each a formal term with its own formalisation. Each description
specifies its own formal term. Statements about them belong to the formal register.
VR-Forms neither asserts nor denies the ontological reality of these entities. It only states: in the VR-
ontology they are not (for the same reasons as unicorns: no operational action over ∅). In the formal
register they are admissible as formal terms. About their existence outside the VR-ontology the present
work does not speak.

VI.4. Philosophical categories
Classical philosophical categories — universals, essence, accident, form, matter, soul, mind — are
formal terms in VR-Forms by the same principle: each description, regardless of its philosophical
tradition, satisfies syntactic correctness and so specifies a formal term.

Universals
«Universal» in the classical philosophical tradition — a common nature shared by many individuals.
⌜universal⌝ is a formal term. Each concrete instance (⌜redness⌝, ⌜humanity⌝, ⌜triangularity⌝) is its own
formal term with its own formalisation.
The medieval dispute of realists and nominalists is a dispute about whether universals have ontological
correlates. In terms of VR-Forms: whether formal terms like ⌜redness⌝ have an operational realisation.
The position of VR-Forms is closer to nominalism: in its ontology (∅ + the operational) universals as
self-standing objects are absent. They are admissible as formal terms — that is, as names, not entities.
This is a precise formulation of medieval nominalism in the modern formal apparatus.
Aristotelian and scholastic categories
⌜essence⌝, ⌜accident⌝, ⌜form⌝, ⌜matter⌝ — all formal terms, with formalisations depending on the
chosen scholastic system (Aristotle, Aquinas, Suárez each give different formalisations). VR-Forms does
not adjudicate classical metaphysical disputes; it states only that these categories are formal terms,
work with them belongs to the formal register, and their operational realisability in VR-Sets is absent.

Soul, spirit, mind
⌜soul⌝, ⌜spirit⌝, ⌜mind⌝ — formal terms. Whether ⌜mind⌝ can be reduced to the operational (for
instance, to a procedure over a physically realised neural network) is a separate question — about the
existence of an operational realisation of the corresponding formal term. VR-Forms does not answer it;
it provides a language for formulating it.

VI.5. Literary figures
Literary characters and worlds form a particularly rich domain of formal terms.

Characters and worlds
Literary characters (⌜Hamlet⌝, ⌜Sherlock Holmes⌝, ⌜Anna Karenina⌝) are formal terms. Each carries an
extensive formalisation, set by the corresponding literary work.
Literary worlds (⌜Middle-earth⌝, ⌜Hogwarts⌝, ⌜Narnia⌝) are also formal terms, often containing their
own formal terms (⌜elf⌝, ⌜hobbit⌝, ⌜Harry's wand⌝) — nested structures of formal terms.

Truth in literature
The statement «Sherlock Holmes lived on Baker Street» — true in what sense? In VR-Forms this is a
formal-register statement about the formal term ⌜Sherlock Holmes⌝. Truth is determined by the chosen
formalisation (the text of the work as a source of predicates).
«Sherlock Holmes exists» in VR-Forms: in the formal register admissible (⌜Sherlock Holmes⌝ is a formal
term, in this sense «exists»); in the ontological register the operational correlate is absent.
This two-register treatment corresponds to the intuitive distinction «exists in the work» vs «exists in
reality», but gives it a formal form.

VI.6. Status of non-mathematical terms: philosophical significance
Let us list what has been shown in Part VI, and what conclusions follow.

(1) The formal register is universal
Demonstrated: the formal apparatus of VR-Forms works with mathematical (Part V) and non-
mathematical (the present part) descriptions uniformly. The principle of forms and the transit rule
have no restriction by subject matter.
This asserts the universal character of the two-register structure: the division into operational and
formal applies to speech in general, not specifically to mathematics.

(2) Ontological status of non-mathematical terms
In the VR-ontology non-mathematical formal terms (dragons, gods, unicorns) have no operational
correlate. This is not an ontological denial. It is a statement: in the VR-ontology (∅ + the operational)
they do not exist. Whether they exist in another ontology (theological, literary, psychological) is a
separate question, not pertaining to VR-Forms.
The distinction «not in the VR-ontology» and «not at all» is principial. VR-Forms does not claim
exclusivity for its ontology. It only clearly fixes it, and relative to it classifies formal terms.

(3) Connection with nominalism
VR-Forms gives a precise formal form to the classical nominalist position: universals and general
entities are names (formal terms), only the concrete (the operational) is real. Difference from classical
nominalism: VR-Forms replaces «the concrete» with «the operational» (what in VR has an operational
correlate).
This is a consistent extension of nominalism from objects to operations: real are not «concrete objects»
(which in modern physics is already questionable) but operational actions upon the fundamental ∅.
Names — everything else, including «humanity», «redness», «Socrates as a man» in the universal sense.

(4) Substantive role of the formal register in non-mathematical speech
What practical significance does the formal register have for non-mathematical descriptions?
Above all, methodological. Statements about ⌜dragon⌝, ⌜god⌝, ⌜soul⌝ can be formulated and discussed
formally, without claiming their ontological reality. This removes a classical difficulty: «is there sense in
talking about the non-existent?» — answered by: the formal register provides meaningful speech
without ontological commitments.
This is relevant to theology (one may build theological systems as formal structures without making
ontological claims), literary studies (literary worlds as formal structures), philosophy (categories as
formal terms), mythology (mythological systems as formal systems).
VR-Forms does not take away from these areas their content. It provides them with an apparatus for
talking about them, clearly separating the internal logic of the system from the question of its
ontological reality.

VI.7. Summary of Part VI
Established:
(1) The formal register of VR-Forms is universal: it covers mathematical and non-mathematical
descriptions uniformly (§VI.1).
(2) Mythological terms (dragons, unicorns, phoenixes) are formal terms, not operationally realisable in
VR (§VI.2).
(3) Theological terms (god, divine entities) are formal terms; classical theological paradoxes are treated
as properties of the formalisation (§VI.3).
(4) Philosophical categories (universals, essence, soul) are formal terms; VR-Forms provides a formal
form for classical nominalism (§VI.4).
(5) Literary figures and worlds are formal terms; «truth in the work» receives a precise formal reading
(§VI.5).
(6) Philosophical significance of the universality of the formal register: ontological clarity relative to the
VR-ontology, without a claim of exclusivity; methodological usefulness for theology, literary studies,
philosophy (§VI.6).
Substantive summary. VR-Forms is not only a formal apparatus for mathematical foundations. It is a
universal language of speech about the non-operational. Dragons and classical ℝ have in it the
same status: formal terms, legitimate in the formal register, having no operational correlate in the VR-
ontology. This is the position that in Part I was stated verbally; the present part demonstrates it in
operation.
What follows. Part VII is devoted to the logic of the two-register system — what inference rules act in
each register, how they interact, whether classical logic is preserved. This is a technical closure of the
system.

## Part VII. Two-Register Logic

VII.0. Introduction
The apparatus of VR-Forms was built in Parts II–IV; applications were given in Parts V–VI. The present
part fixes the logical properties of the two-register system: which rules of inference act, how the two
registers interact, whether classical logic is preserved, what peculiarities arise on the boundary.
Part VII is the technical closure of the system. No new ontological commitments are accepted here. The
aim is to collect in one place the logical properties scattered through the preceding parts and to make
their consequences visible.
Contents: classical logic in both registers (§VII.1); mixed formulas and rules of work with them (§VII.2);
quantifiers in the formal register (§VII.3); the law of the excluded middle and its status (§VII.4);
connection with two-sorted logic and other formal systems (§VII.5); summary (§VII.6).

VII.1. Classical logic in both registers
The principled decision, fixed in Part II §II.5 and justified by Theorem III.1: VR-Forms uses classical
first-order logic in both registers.

What this means
In the ontological register the usual rules of classical logic act: modus ponens, generalisation, axiom
schemes of classical predicate calculus. This is inherited from VR-Sets — there too classical logic (VR-
Sets §I.3).
In the formal register — the same rules. The formal register is not a new logic. It is the same logical
apparatus applied to a new type of objects (formal terms).

Why classical, not intuitionistic
A common solution in the foundations of mathematics for systems with operational ontology is to pass
to intuitionistic logic (Brouwer, Bishop). VR-Sets has already declined this move: classical logic is
preserved (see VR-Sets §VIII.3, comparison with constructivism).
The reason in VR-Sets: operational definiteness is already built into the closure principle. Every
operational functionality gives a definite answer to every query; «a third» in the ontology is absent. So
the law of excluded middle holds not as a logical axiom but as a property of the ontology.
In VR-Forms the situation is different: in the formal register there may be contradictory descriptions
(Russell's class, the liar paradox). Here classical logic holds for another reason — because formal terms
are formulas, and working with them is working with formulas; standard logic applies to formulas as
usual. Contradictions in formal terms do not generate global contradictions, since the formal register is
conservative over the ontological (Part III).
Remark on another possibility
VR-Forms could be considered with intuitionistic or paraconsistent logic in the formal register. That
would lead to a different system. The present work chooses classical logic for simplicity and for
compatibility with classical mathematics during transits (Part IV). Alternative variants remain open
directions.

VII.2. Mixed formulas
Formulas of VR-Forms may simultaneously contain ontological terms and formal ones. For instance:
«every element of A satisfies ψ», where A is an operational set and ψ is a predicate referring to a formal
term. Or: «⌜τ⌝ has an element in A», where ⌜τ⌝ is formal and A is operational.

Rules for working with mixed formulas
Mixed formulas are admissible in L₁ by the principle of forms and the usual syntactic rules. Logical
operations apply to them standardly.
In conducting a derivation, a mixed formula may be transformed either into a purely ontological one (if
all formal terms are eliminable — for example, are operationally realisable), or remain mixed. There is
no requirement to «squeeze out» formal terms — they may remain in the derivation as intermediate
elements.

Translation π on mixed formulas
The mapping π from §III.2 applies to mixed formulas naturally: ontological terms remain unchanged,
formal terms are translated into their defining predicates.
In particular, the formula ⌜x ∈ τ⌝ ∧ x ∈ A, where τ = {y : ψ(y)} and A is operational, translates into ψ(x)
∧ x ∈ A. We obtain a purely ontological formula. This is the mechanism of conservativity (§III.2).

Substantive significance
Mixed formulas are the principal working tool in the practice of VR-Forms. They allow one to formulate
statements of the form «the operational object A satisfies the property described formally». This is the
typical situation of transits: the formal register provides a convenient language for the property, the
operational provides a concrete object.
Example: «℘_VR(ω) is a subfamily of ⌜℘(ω)⌝» — a mixed formula stating that the operational set of
describable subsets of ω is a part of the formal term «classical ℘(ω)». The statement is admissible in the
formal register; in the ontological register it is equivalent to «every element of ℘_VR(ω) satisfies the
predicate ‘is a subset of ω’», which is trivially true.

VII.3. Quantifiers in the formal register
Quantifiers ∀ and ∃ applied to formal terms require a separate comment — they have specific content.
Quantifier ∃ over formal terms
The notation ∃⌜τ⌝ φ(⌜τ⌝) means: «there exists a formal term ⌜τ⌝ such that φ». Since formal terms are
syntactic records, this is equivalent to: «there exists a syntactically correct record of a description τ for
which the formula φ(⌜τ⌝) is true».
The set of all formal terms is countable (by the finiteness of the alphabet and the inductive definition of
terms). Hence ∃-quantification over formal terms is, in essence, quantification over a countable set of
syntactic objects. This does not generate uncountable collections, does not require choice over
uncountable families, does not violate the countability of the universe of VR-Sets.

Quantifier ∀ over formal terms
The notation ∀⌜τ⌝ φ(⌜τ⌝) means: «for every formal term ⌜τ⌝, φ holds». Analogously: quantification
over a countable set of syntactic objects.
Remark: in this quantification participate all formal terms — including non-realisable, contradictory,
mythological. A statement ∀⌜τ⌝ φ(⌜τ⌝) is a statement about all descriptions without exception. This is a
strong statement, and in practice rarely encountered; more often the bounded quantification ∀⌜τ⌝
(P(⌜τ⌝) → φ(⌜τ⌝)) is used for some predicate P distinguishing a class of formal terms.

Substantive sense
Quantifiers over formal terms make possible statements of the form «every description of a property has
such-and-such structure», «there exists a formal term with such-and-such characteristic». These are
meta-level statements — about the syntactic language itself.
Their applicability is limited by the fact that they speak about syntax, not about objects. The statement
«there exists a formal term ⌜dragon⌝» is true trivially (dragon is described); the statement «there exists
a dragon» in the ontological sense is a formula of the ontological register, and its truth is determined by
the presence of an operational realisation (of which there is none).

VII.4. The law of the excluded middle
Status of LEM in the ontological register
In the ontological register of VR-Sets the law of the excluded middle (φ ∨ ¬φ) holds — an inheritance
from the classical logic of VR-Sets. Substantively: every operational functionality gives a definite answer;
there is no «middle».

Status of LEM in the formal register
In the formal register LEM also holds — since the logic is classical. However, its substantive significance
requires caution.
The statement «⌜dragon⌝ exists ∨ ¬(⌜dragon⌝ exists)» is true in the formal register by LEM. But
«exists» here is formal (i.e. «the formal term ⌜dragon⌝ is»), not ontological. So the statement is trivial:
the formal term ⌜dragon⌝, of course, is (we have recorded it); hence the disjunction is true, since its first
part is true.
When someone says «a dragon exists or does not exist» in the ontological sense — this is in another
register. In the ontological register the formula «∃x dragon(x)» translates into a statement about the
existence of an operational realisation of a dragon; its truth value is determined by the operational
ontology (and in this case is false — no operational realisation).

Remark
The distinction of registers in the application of LEM removes many classical philosophical difficulties.
«Does god exist?» in the formal register — yes, ⌜god⌝ is a formal term. In the ontological — no, no
operational realisation in the VR-ontology. This is not a contradiction but a difference of semantic
registers of the question.
VR-Forms does not claim that one of the answers is «more correct» than the other. It asserts that they
answer different questions, and explicit distinction of registers helps not to confuse them.

VII.5. Connection with other formal systems
Let us collect the explicit comparisons of VR-Forms with systems known in logic.

Two-sorted logic
A standard extension of first-order logic in which variables are divided into sorts. VR-Forms is formally
a two-sorted system (ontological sort, formal sort). Peculiarity: the formal sort includes the ontological
(every operational set has a formal correlate), but not vice versa. This is an asymmetric embedding.

NBG (Bernays–Gödel)
An extension of ZFC with classes as second-sort objects. VR-Forms is structurally analogous: formal
terms play the role of classes in NBG (large collections that are not operational sets). Difference: classes
of NBG are objects (although of the second sort); formal terms of VR-Forms are formulas. This gives VR-
Forms greater clarity regarding ontological status (the formal register makes no claim of ontology).

Internal Set Theory (Nelson)
An extension of ZFC separating standard and nonstandard objects. Structural similarity with VR-Forms:
two registers, passage between them. Difference in motivation: IST introduces the nonstandard as a tool
for proofs about the standard; VR-Forms introduces the formal as a way to speak about the non-existent
without ontology.
Furthermore: IST ontologically extends ZFC (nonstandard objects «are» in some sense); VR-Forms does
not ontologically extend VR-Sets (formal terms are formulas, not objects). This is a principial distinction
in the spirit of the position.

Constructive and intuitionistic logic
Constructivism (Brouwer, Bishop) and intuitionism (Heyting) reject LEM and non-reflexive proofs of
existence. VR-Forms preserves classical logic. The difference is principled: constructivism refuses
language for the non-constructive; VR-Forms permits the language but deprives it of ontological force.
One could say: VR-Forms gives classical logic in the formal register with operational ontology in the
ontological. This removes the tension between «classical mathematics works» and «not all classical
objects are real»: they work as formulas; real are those that are operationally realisable.

Realisability (Kleene, Kreisel)
Realisability connects classical and constructive mathematics: a formula is classically provable and
constructively realisable if it has a constructive witness. The notion of operational realisability
(Definition II.3) is an analogue of realisability in VR-Forms. The difference: realisability classically
answers «can the proof be constructivised?»; operational realisability in VR-Forms answers «does the
formal term have an operational correlate?»

Free logic (Lambert, Bencivenga)
Free logic admits terms not having reference (terms denoting the non-existent). VR-Forms is formally
similar to free logic: formal terms are terms without reference. Difference: free logic is a single theory
with a single register; VR-Forms has two registers, with strictly formalised passage between them.

VII.6. Summary of Part VII
Established:
(1) Classical first-order logic acts in both registers of VR-Forms (§VII.1).
(2) Rules for working with mixed formulas; the translation π applies to them naturally (§VII.2).
(3) Quantifiers over formal terms are quantifiers over a countable set of syntactic objects; do not
generate uncountability (§VII.3).
(4) The law of the excluded middle holds in both registers; careful distinction of registers removes many
classical difficulties with LEM for non-operational objects (§VII.4).
(5) Connections of VR-Forms with two-sorted logic, NBG, IST, constructivism, realisability, free logic
(§VII.5).
Methodological summary. VR-Forms is logically closed. Its inference rules are clear, the relations
between registers are formalised, connections with known systems are established. The system makes
no hidden logical assumptions beyond classical first-order logic and the principles of VR-Sets.
What follows. Part VIII — the concluding part — records open questions, indicates the programme of
VR-Audit as a natural continuation, and gives the general summary of the VR cycle.

## Part VIII. Open Questions and the Place of VR-Forms in

the Cycle
VIII.0. Introduction
The concluding part of the preprint sums up VR-Forms and records open directions. The structure
parallels Part IX of VR-Sets: technical questions, substantive extensions, philosophical open directions,
general conclusion.
Part VIII closes the work. All formal results are gathered in Parts II–IV; applications in Parts V–VI;
logical properties in Part VII. Here — the fixing of what remains open and of what is planned as the
next work of the cycle (VR-Audit).

VIII.1. Technical open questions
Question 1: formalisation in Lean/Coq/Agda
Machine formalisation of VR-Forms is a natural technical step. The two-register structure fits well with
dependent types: the ontological register — usual types with values, the formal register — syntactic
objects with an interpreting mapping. Lean 4 appears most suitable: its mathematical library (mathlib)
already contains tools for working with conservative extensions, translations, two-sorted logic.
Concrete formalisation tasks: (a) formal verification of Theorem III.1 on conservativity; (b)
formalisation of the transit rule (§IV.2); (c) machine verification of examples (§IV.5, Parts V–VI).

Question 2: precise strength of the translation π
The mapping π from §III.2 translates formal terms into defining predicates. On simple formal terms of
the form ⌜{x : φ(x)}⌝ the translation is trivial. For more complex constructions (quantification over
formal terms, iteration of formal terms, recursive definitions via formal terms) the translation requires
more careful definition.
Open question: what is the precise range of formal constructions for which π gives an invertible
translation? Are there formal terms for which π gives an ambiguous result? These questions matter for
a strict variant of formalisation in Lean.

Question 3: composition of transits
If there is a transit D₁ yielding the ontological statement φ, and a transit D₂ using φ as a lemma on the
way to a statement ψ — is there a single transit for ψ, or is a composition of separate transits needed?
This is a question of practical work with VR-Forms: how naturally do chains of lemmas organise into
one large transit, and do problems with conservativity arise under composition?
It is expected that the composition of transits is safe (by transitivity of conservativity), but a strict proof
and a survey of practical cases remain open.
Question 4: alternative logics of the formal register
In §VII.1 the choice was made in favour of classical logic in the formal register. Open question: what
properties of VR-Forms are preserved, and which change, under replacement of classical logic with:
(a) intuitionistic logic — substantively: the formal register becomes constructive; paradoxical formal
terms receive a different status;
(b) paraconsistent logic — substantively: contradictions in formal terms may be treated explicitly,
without threat of overall contradiction;
(c) modal logic — substantively: formal terms may differ in «mode»
(necessary/possible/counterfactual).
Each of these alternatives is a separate work.

VIII.2. Substantive extensions
Extension 1: VR-Audit
The direct and principal continuation of VR-Forms is the programme of VR-Audit. Content: systematic
analysis of classical mathematical theorems with the aim of determining which of them transit directly
into VR-Sets, which require operational labour to extract content (problematic transits), and which are
essentially non-ontological.
VR-Forms provides the apparatus for VR-Audit. VR-Audit uses this apparatus on concrete theorems. List
of first candidates:
— the spectral theorem in its various formulations (discrete and continuous spectrum);
— the Hahn–Banach theorem in general form;
— Baire's category theorem;
— Tikhonov's compactness theorem;
— the Radon–Nikodym theorem on measures;
— theorems from quantum mechanics (Stone, von Neumann, Naimark).
Each such theorem can be analysed: is the uncountable used essentially, or only as convenience?

Extension 2: connection with reverse mathematics
The programme of Reverse Mathematics (Friedman, Simpson) classifies classical theorems by the
strength of axioms needed for their proof. The hierarchy of subsystems of second-order arithmetic
(RCA₀, WKL₀, ACA₀, ATR₀, Π¹₁-CA₀) gives a precise measure of the «uncountable strength» of each
theorem.
VR-Forms and VR-Audit can connect with this programme through the translation π. Each system of
the Reverse Mathematics hierarchy corresponds to a definite class of formal terms in VR-Forms;
theorems provable in RCA₀ transit directly into VR-Sets; theorems requiring stronger subsystems yield
problematic transits, and the character of problematicity depends on the subsystem.
Establishing the precise correspondence is a separate task, uniting VR-Forms with the already
substantial Reverse Mathematics literature.

Extension 3: connection with topoi and category theory
Categorical set theory (Lawvere ETCS, Macnamara SDG, elementary topoi) gives an alternative view of
foundations through universal properties. VR-Sets is close to them in spirit (see VR-Sets §IX.2). VR-
Forms adds the possibility of speaking about non-operational categorical constructions as formal terms:
⌜topos of all functors⌝, ⌜absolutely complete category⌝, etc.
Open direction: construction of VR-categorical apparatus, where operational categories (countable, with
countable structure) are operational, and larger ones are formal.

Extension 4: homotopy type theory (HoTT)
In HoTT equality is not a relation but a type (path). VR-Forms can be reinterpreted in the HoTT spirit: ≡
as a path in the type of operational sets, formal terms as higher types with a special interpreting
translation. This is technically complex but substantively close.

Extension 5: operational foundations of physics
In VR-Sets §IX.3 the question of the applicability of operational ontology to quantum mechanics was
raised. VR-Forms provides a more complete apparatus for this direction.
Hypothesis: quantum mechanics of operational systems (with discrete spectrum of the Hamiltonian) is
fully formulated in VR-Sets; quantum mechanics of continuous systems requires the formal register for
its uncountable constructions (classical Hilbert space, spectral measure, projection-valued measure). At
the same time the physically observable results — measurable quantities — should transit back into the
operational.
Verification of this hypothesis on concrete physical examples is a task leading to a possible future work
VR-Physics.

VIII.3. Philosophical open questions
Question 1: status of the formal term
In Part I §I.4 it was fixed: a formal term is simply a formula, without ontological status. This position is
consistent but philosophically rigid. Open question: can an intermediate status of formal terms be found
— for example, «existing in the sense of use», «existing as linguistic objects», «existing in Popper's third
world»?
The present work declined such intermediate positions for the sake of clarity. The alternatives remain
open for investigation.
Question 2: place of VR-Forms among the foundations
VR-Forms positions itself as a minimalist operational ontology with formal extension. Close positions:
Feferman's predicativism (FOM community), Bishop's countable constructivism, Bridgman's
operationalism. VR-Forms differs from each, but the precise place on this map requires a separate
philosophical study.

Question 3: the next work of the cycle
VR-Forms is the fourth work of the cycle. Open candidates for the fifth:
(a) VR-Audit — systematic analysis of classical mathematics through the lens of VR-Forms;
(b) VR-Categories — categorical reformulation of VR-Sets and VR-Forms;
(c) VR-Physics — operational reformulation of the foundations of physics;
(d) VR-Logic — detailed elaboration of the A1-duality into a self-standing operational logic.
The natural choice is VR-Audit, as a direct application of the VR-Forms apparatus. VR-Categories and
VR-Physics presuppose more extended programmes. VR-Logic is a parallel branch developed
independently.

VIII.4. Conclusion
Completion of the VR cycle
The VR cycle in its current form — four works:
(1) VR. A Formal System — arithmetic on minimal ontology.
(2) VR-Numbers — numerical extensions over minimal ontology.
(3) VR-Sets — set theory; for the first time reveals the boundary of operational ontology (countability
of the universe).
(4) VR-Forms — a formal language for speech about what lies beyond the boundary. Closes the
ontological contour: now VR can speak about everything, having in its ontology only ∅ and the
operational.
The slogan of the cycle, carried through the four works:
«Only ∅ is. Everything else either acts or is said. Action is operational and relates to ∅; speech is formal
and refers to nothing by necessity.»

What the cycle demonstrates
The VR cycle in its completed form demonstrates: ontological minimalism is possible and
workable. On the sole primitive ∅ are built arithmetic, numerical extensions, set theory; for the
description of the non-operational a formal register is introduced, not violating the minimalism. No
additional ontological commitments are accepted; nothing of classical mathematics or speech in general
is left without a place.
This is a philosophical position carried through a formal apparatus. It does not claim exclusivity:
classical ZFC, constructivism, formalism, categorical set theory — all remain legitimate alternatives. But
the VR cycle shows that minimal operational ontology is a substantive and consistent option, capable
of serving as a foundation for mathematics and as a language for speech in general.

What the cycle does not do
The cycle does not prove the ontological reality of ∅ — this is an ontological position, not a theorem. The
cycle does not deny ontologies other than VR — it only clearly fixes its own and works relative to it. The
cycle does not claim instrumental superiority over classical foundations — the programme of VR-Audit
is precisely what is intended to systematically check in which cases VR provides something beyond the
known.
The mature role of VR is not as an alternative to classical foundations, but as a transparent and
minimalist point of view, relative to which classical foundations receive a clear classification (through
VR-Audit). This is methodological value, not mathematical revolution.

## Part IX. Lean 4 Formalisation of VR-Forms:

Methodological Observations
IX.0. Introduction
The present part documents the Lean 4 formalisation of the two-register apparatus of VR-Forms (Parts
II–IV and §VII.2 of the present preprint), carried out after the publication of v1.0.0 and presented as a
self-contained companion software publication (Reznik 2026, Lean VR-Forms, Software DOI
10.5281/zenodo.20355757; Git tag v1.3-vr-forms). The formalisation realises the apparatus as a shallow
embedding over mathlib and surfaces a single explicit structural boundary at conservativity (Theorem
III.1).
Part IX is the fourth such methodological-observations part in the VR cycle, following Part VIII of VR-
Numbers v1.0.2 and Part X of VR-Sets v1.0.1. Its function is the same: not to introduce new mathematical
content, but to record what the formalisation made visible — observations about the structural
relationship between the preprint's apparatus and Lean's proof-theoretic infrastructure.
Ten observations are presented in four thematic clusters. §IX.1 collects two observations on foundation-
level properties of the formalisation. §IX.2 collects five observations centred on the central structural
boundary of the cycle (conservativity) and its four substructural manifestations. §IX.3 collects two
observations on structural patterns in the apparatus. §IX.4 closes with two cross-cycle observations,
including the finale on zero Classical.choice usage. §IX.5 summarises the comparison with the
boundaries documented in VR-Sets Part X.
Methodologically, Part IX resolves Question 1 of §VIII.1 («Formalisation in Lean/Coq/Agda») of the
present preprint for the formalisable core (the two-register apparatus); the central boundary at
conservativity is documented but not crossed. The Lean formalisation is also accessible directly: each
observation has a corresponding source location in the Lean code documented in comment form.

IX.1. Foundation-level properties
Observation 1: foundation file is import-free and axiom-free
The foundation file `Forms/Language.lean` introduces the syntactic skeleton of the apparatus (the
`Register` inductive type, the `FormalTerm` structure, the notation `⌜·⌝`) without importing any mathlib
or VR-Sets module. `String` and inductive/structure constructions are part of the Lean 4 prelude. The
axiom profile is empty `[]` for both `Register` and `FormalTerm`.
This contrasts with the foundation files of VR-Numbers and VR-Sets Lean. `Numbers/Foundation.lean`
imports mathlib's natural number infrastructure; `Sets/Foundation.lean` imports mathlib's `ZFSet` and
inherits `[propext, Quot.sound]` for every theorem. The contrast reflects the deliberate architectural
choice of shallow embedding in VR-Forms: formal terms are syntactic metadata, not mathematical
objects in mathlib's hierarchy.
The methodological consequence is structural. The base layer of VR-Forms is the most axiom-minimal
foundation of the four cycles; any axiom dependency in subsequent stages arrives through the
connection to VR-Sets (which carries `propext` and `Quot.sound` from the ZFSet quotient), not through
the formal-term apparatus itself.

Observation 2: realisability inherits the Classical-free closure layer of VR-Sets
The predicate `isRealisable : FormalTerm → Prop` is defined in `Forms/Realisability.lean` via `match` on
`FormalTerm`, with cases for the realisable terms `⌜∅⌝`, `⌜omega_OSet⌝`, `⌜osetPair⌝`, plus VR-Sets-
refutable `⌜AFA_Statement⌝`, plus the open Conjecture cases (added retroactively in Stage 4), plus a
catch-all `False`. All four base realisability lemmas sit at `[propext, Quot.sound]`, with no
Classical.choice.
The structural reason is direct. The realisable cases (∅, ω, pair) correspond to Theorems III.1–III.3 and
Theorem III.6 of VR-Sets, which are Classical-free closure theorems. The realisability layer of VR-Forms
is structurally tied to the Classical-free closure layer of VR-Sets — realisability of operationally well-
defined terms inherits exactly the axiom dependency of their closure proofs.
Realisable terms tied to Classical VR-Sets theorems (replacement, choice, foundation) would inherit
`Classical.choice`. No such terms appear in the present formalisation; this is consistent with the
preprint's position that the operationally well-defined VR objects (∅, ω, pair) form the cycle's realisable
core, while constructions essentially using Classical infrastructure remain formal terms without
realisation.

IX.2. The central boundary and its substructural manifestations
The defining feature of VR-Forms Lean is its single explicit structural boundary at conservativity.
This contrasts with VR-Sets Lean, which surfaced five distinct boundaries between the operational
universe and mathlib's set-theoretic infrastructure. The VR-Forms boundary is methodologically
different: it sits at the proof-theoretic meta-level (between shallow and deep embedding), not at the
mathematical-content level (between operational and classical sets).
§IX.2 documents the central boundary (one observation) and four substructural manifestations
encountered in the formalisation (four observations).

Observation 3: conservativity (Theorem III.1) is the explicit structural boundary
Theorem III.1 of the present preprint (§III.2) — the conservativity of T₁ over T₀ in the ontological
register — is not formalised in the Lean cycle. Instead, it is documented as the explicit structural
boundary, with verbatim citation in the doc-comment of `Forms/Transit.lean`.
The reason is architectural. Full formalisation of conservativity would require deep-embedded `Formula
L₁`, `Derivation T₀`, `Derivation T₁` types, the translation π as a function on the formula syntax, and an
induction proof over derivations. This is a proof-theory project larger than the entire VR-Sets Lean cycle,
and would shift the formalisation's role from «Lean library reflecting the preprint» to «Lean library
about proof theory». The decision is documented in the Lean cycle's `CLAUDE.md` and `PLAN.md`, with
three alternatives (full deep embedding, shallow embedding making conservativity trivial, partial
formalisation with explicit boundary) discussed before the cycle began.
The methodological position is honest: conservativity is mathematically proved in the preprint (§III.2
gives the full inductive proof via the translation π), but Lean-unformalisable at the shallow-
embedding depth chosen here. This is distinct from open conjectures, which are mathematically open
rather than formalisation-limited. The Lean cycle records this distinction by not introducing a `def
Conjecture_Conservativity : Prop` — such a definition would misrepresent the result as open to Lean
attack, when in fact it is proved (just outside the shallow apparatus).
The transit pattern (§IV.2) is documented as an inference template in `Forms/Transit.lean`, not
formalised as a Lean theorem. The conservativity justification flows through external reference to the
preprint's §III.2 proof.

Observation 4: equation-compiler catch-all does not reduce in term mode
The first substructural manifestation of the boundary is technical. The function `translate_pi :
FormalTerm → Prop`, defined via `match` with named cases plus a catch-all `| _ => False`, does not reduce
`translate_pi x` to `False` in term mode for an arbitrary `x : FormalTerm`. The reduction is blocked by the
✝
equation compiler's schematic-variable representation of the catch-all: the term `translate_pi x `
✝
(where `x ` is the catch-all's schematic variable) stays unreduced even when the user knows that `x` is
not one of the named cases.
The working proof structure (used in `translate_implies_realisable`) is `by_cases` discrimination on the
named constructors — which `DecidableEq FormalTerm` makes possible without Classical.choice —
followed by `unfold translate_pi; split <;> simp_all [FormalTerm.mk.injEq]` in the residual catch-all
branch. The fix costs zero new axioms but requires explicit case structure.
The observation parallels the proof technique in VR-Sets Stage 8, where `Classical.epsilon` had to be
applied with `eq_empty_or_nonempty` case-split to make reduction work. Both cases share the same
structural fact: Lean's pattern matching requires explicit case discrimination at the boundary between
abstract scrutinee and concrete reduction.

Observation 5: realisability and π-translation form complementary layers
The second substructural manifestation: `isRealisable` (existential — «term has operational witness»)
and `translate_pi` (specific — universal-quantified statement about a named VR-Sets object) form two
complementary layers in the Lean apparatus, connected by `translate_implies_realisable : ∀ t,
translate_pi t → isRealisable t` via existential introduction.
The preprint §II.7 / §III.2 conflates the two notions (operational realisability and π-translation are
presented as aspects of the same apparatus). The Lean formalisation separates them, and only the
forward direction (specific → existential) is proved. The converse (existential → specific) is not provable
from the existential alone: from «there exists some operational witness» one cannot extract «the specific
witness `osetEmpty`» without Skolemisation, which is not available from the existential in the shallow
embedding. The transit pattern of §IV.2 operates exclusively in the forward direction, which is
structurally consistent.
This separation is the formal content of what the preprint calls «the transit pattern operating forward»:
from an operational truth about a specific VR-Sets object (the π-translation), the realisability of the
corresponding formal term follows.

Observation 6: two-level structure of negative cases
The third substructural manifestation concerns non-realisability. The Lean formalisation distinguishes
two levels of non-realisable formal terms.
Level 1 (trivially False). For «mythological» terms — those without mathematical formulation in VR-
Sets — the proof is `id`: `¬isRealisable ⌜"Vitali"⌝ := id`, `¬isRealisable ⌜"Russell_class"⌝ := id`, and so on.
The catch-all `| _ => False` redirects all unnamed terms to `False`, and negation is trivial. These four
theorems (Russell, Vitali, classical ℝ, classical ℘(ℕ)) are in `Forms/Examples.lean`. The proof carries no
VR-Sets mathematical content; non-realisability is by absence from the realisability list.
Level 2 (VR-Sets-refutable). For `⌜AFA_Statement⌝`, the case is different. The match returns
`VR.Sets.AFA_Statement` (a Prop with mathematical formulation in mathlib's PSet inductive structure).
The bridge theorem `bridge_AFA : ¬isRealisable ⌜"AFA_Statement"⌝ := AFA_Refuted` (in
`Forms/Bridge.lean`) is a direct application of `AFA_Refuted` from VR-Sets Stage 10. Non-realisability
carries genuine mathematical content: AFA contradicts the well-foundedness of PSet.
The two-level structure formalises a distinction implicit in the preprint between «paradoxical
descriptions without operational correlate» (Russell, Vitali) and «descriptions whose negation has
independent mathematical content» (AFA). The latter category is rarer but methodologically more
substantial.

Observation 7: three-category structure of formal terms
The fourth substructural manifestation. The bridge module surfaces a triadic classification of formal
terms by realisability status:
— (a) Provably realisable — Stage 2 lemmas with concrete witnesses (`isRealisable_empty`,
`isRealisable_omega`, `isRealisable_osetPair`). The realisable list is closed and explicit; each entry
corresponds to a closure theorem of VR-Sets.
— (b) Open realisability — Conjecture formal terms (`bridge_Conjecture_IV_1`,
`bridge_Conjecture_IV_2`). The bridge `iff` is trivially provable by definitional reduction, but the content
(whether the conjecture holds) is mathematically open. Both directions of the `iff` reduce to `id`.
— (c) Provably non-realisable — split into the two levels of Observation 6.
The triadic structure parallels VR-Sets Stage 11's three-tier formalisation result (proved theorems,
refuted claims, open formulations), but localised at the level of formal terms rather than at the level of
mathematical claims. The bridge module thus inherits and refines the VR-Sets tier structure within the
formal register of VR-Forms.
IX.3. Structural patterns
Observation 8: universe handling across cross-cycle boundaries
Two distinct universe-management issues surfaced in the formalisation; both arise from the cross-cycle
nature of VR-Forms.
Issue (a) — Stage 2. In the body of `def isRealisable`, references to `OSet` require the explicit annotation
`OSet.{0}`. Without it, Lean cannot infer the universe level when `OSet` is the codomain of a `match`-
induced quantification. The issue is namespace-related: inside `namespace VR.Sets`, surrounding context
fixes the universe; inside `namespace VR.Forms` with `open VR.Sets`, the universe must be pinned
explicitly.
Issue (b) — Stage 5. Projecting `.1` from `Theorem_III_6_Infinity` (a two-universe `{u v}` signature
inherited from `ZFSet/PSet` interaction) generates universe metavariables outside the defining
namespace. The workaround is to use `translate_pi_omega.1` instead, whose match-case pins `OSet.{0}`
and makes the projection unambiguously typed.
Both issues point to the same architectural fact: VR-Forms is structurally a cross-cycle module, and
Lean's universe inference does not propagate cleanly across cycle boundaries without explicit
annotation. This is a mathlib/Lean 4 idiosyncrasy, not a logical issue — but it costs care in
implementation, and it is the first such cross-namespace technical concern in the VR Lean programme.

Observation 9: ZFA boundary manifests simultaneously in both registers
The Lean finale theorem `mixed_AFA_boundary` (in `Forms/Examples.lean`) captures, in a single Lean
Prop, the parallel manifestation of well-foundedness across the two registers of VR-Forms:
theorem mixed_AFA_boundary :

(∀ x : OSet.{0}, x ∉ x) ∧ ¬isRealisable ⌜"AFA_Statement"⌝ :=

⟨ZFSet.mem_irrefl, bridge_AFA⟩

Ontologically: `∀ x : OSet, x ∉ x` — regularity, via `ZFSet.mem_irrefl`. Formally: `¬isRealisable
⌜"AFA_Statement"⌝` — non-realisability of the AFA formal term, via `bridge_AFA`. Both sides derive from
the inductive nature of mathlib's `PSet`, and surface the same structural fact (well-foundedness of
mathlib's set-theoretic infrastructure) through different conceptual layers.
This is the most mathematically substantive mixed formula of the VR-Forms cycle and the structural
counterpart to VR-Sets's Stage 10 boundary B.5 («ZFA total absence»). What appeared in VR-Sets Part X
as the deepest structural boundary appears in VR-Forms Lean as a theorem with cross-register content
— the same architectural fact, now formulated in the apparatus that VR-Forms provides for talking
about both registers at once.
IX.4. Cross-cycle integration
Observation 10: zero Classical.choice usage across the entire cycle
The final observation closes the cycle. The original cycle plan (`PLAN.md` of the Lean repository)
predicted that the public objects of VR-Forms Lean would sit at `[propext, Classical.choice, Quot.sound]`
or stricter — admitting some Classical use. The actual result, verified by `#print axioms` for every public
object, is stricter than predicted:
| File | Public objects | Axiom profile |

| Language.lean | 3 | `[]` empty |

| Realisability.lean | 4 | `[propext, Quot.sound]` |

| Transit.lean | 5 | `[propext, Quot.sound]` |

| Bridge.lean | 3 | `[propext, Quot.sound]` |

| Examples.lean | 6 | `[propext, Quot.sound]` |

Eighteen public objects total. Three are axiom-free (Stage 1). Fifteen sit at `[propext, Quot.sound]`. Zero
objects require Classical.choice.
This contrasts sharply with the predecessor cycles. VR Part I and VR-Numbers Lean each contain
several objects depending on Classical infrastructure; VR-Sets Lean has six of twenty-two objects at the
full ceiling `[propext, Classical.choice, Quot.sound]`, through four structurally distinct Classical
mechanisms (ordinal-valued constructions, definability, foundation, choice).
The structural reason is direct. The realisable cases of VR-Forms correspond to the Classical-free closure
theorems of VR-Sets (Observations 1 and 2); the non-realisable cases either reduce trivially (Russell,
Vitali via `False`) or use `AFA_Refuted` (Classical-free, proved via inductive PSet reasoning). No
formalisation step in VR-Forms requires a Classical mechanism, because the formalisable apparatus
operates entirely within the operationally well-behaved subset of VR-Sets.
The observation reflects the nature of the present preprint: a formal language for the non-operational,
not a substantive mathematical theory. The Lean formalisation, when carried out at the chosen depth,
lives entirely within Lean's constructive-plus-quotient core.

IX.5. Comparison with VR-Sets Part X
The structure of boundaries in VR-Forms Lean differs methodologically from VR-Sets Lean (documented
in Part X §X.3 of VR-Sets v1.0.1).
VR-Sets surfaced five structural boundaries between the operational universe and mathlib's set-
theoretic infrastructure (B.1 powerset cardinality, B.2 replacement schema, B.3 foundation modes, B.4
ZFA modal status, B.5 ZFA total absence). Each boundary is a gap in mathematical content — what the
preprint claims about the operational universe versus what mathlib provides in its type-theoretic
infrastructure.
VR-Forms surfaces one structural boundary at conservativity. The boundary is at the proof-theoretic
meta-level (between shallow and deep embedding), not at the mathematical-content level. The four
observations of §IX.2 are not separate boundaries but substructural manifestations of the single central
boundary in different aspects of the formalisation.
The shift in structure — from five mathematical-content boundaries to one proof-theoretic boundary
with four manifestations — reflects the shift in subject matter. VR-Sets formalises a set theory; its
boundaries are about what mathlib's sets can and cannot do. VR-Forms formalises a language for
talking about sets; its boundary is about what the shallow embedding can and cannot say about its own
metatheory.
Both cycles arrive at axiom-minimal results, but through different routes. VR-Sets achieves axiom-
minimality by navigating the boundaries (proving theorems despite mathlib's structural mismatches);
VR-Forms achieves axiom-minimality by staying entirely on the shallow side of its single boundary.

IX.6. Summary of Part IX
Ten observations have been documented:
(1) Foundation file is import-free and axiom-free; the most axiom-minimal foundation of the four VR
Lean cycles. (§IX.1)
(2) Realisability inherits the Classical-free closure layer of VR-Sets; no realisable case requires
Classical.choice. (§IX.1)
(3) Conservativity (Theorem III.1) is the explicit structural boundary — mathematically proved in the
preprint, Lean-unformalisable at shallow depth, documented in `Transit.lean`. (§IX.2)
(4) Equation-compiler catch-all does not reduce in term mode; `by_cases + unfold + split + simp_all` is
the zero-axiom fix. (§IX.2)
(5) `isRealisable` (existential) and `translate_pi` (specific) form complementary layers; forward
implication is the formal content of the transit pattern. (§IX.2)
(6) Two-level structure of negative cases: trivially False (Vitali, Russell) vs VR-Sets-refutable (AFA via
`AFA_Refuted`). (§IX.2)
(7) Three-category structure of formal terms: provably realisable, open realisability, provably non-
realisable. (§IX.2)
(8) Universe handling across cross-cycle boundaries — `OSet.{0}` annotation and `translate_pi_omega.1`
projection workaround. (§IX.3)
(9) ZFA boundary manifests in both registers simultaneously; `mixed_AFA_boundary` formalises this as
a single Lean Prop. (§IX.3)
(10) Zero Classical.choice usage across the entire cycle — the most axiom-minimal of the four VR Lean
cycles. (§IX.4)
The full Lean source is at https://github.com/inventor1975/VRCycle (tag v1.3-vr-forms); each
observation has a corresponding source location documented in Lean comments.
Methodological summary. The formalisation realises in Lean exactly the apparatus that VR-Forms is
— a shallow, operationally minimal, axiom-light layer over VR-Sets, with one explicit structural
boundary at the place where it would have to become a proof-theory project. The boundary is honest,
the apparatus on the formalisable side is complete, and the cycle as a whole is the most axiom-minimal
of the four VR Lean formalisations.
What this resolves. Question 1 of §VIII.1 («formalisation in Lean/Coq/Agda») is now answered for the
formalisable core. Question 2 («precise strength of the translation π») receives a partial answer: in the
shallow embedding, π is total and exact for the named realisable cases. Question 3 («composition of
transits») is not addressed in the formalisation — the transit pattern is documented but not
compositionally analysed. The full conservativity formalisation (Question 1 in its strict sense) remains
the structural boundary.
What follows. The VR cycle in its current form — four works with four Lean formalisations — closes
the planned ontological contour. The next directions, sketched in §VIII.2 of the present preprint, are VR-
Audit (the direct application of the present apparatus to classical mathematics), VR-Categories, and VR-
Physics. The Lean cycle of VR-Forms, by realising the formalisable core of the apparatus, prepares the
technical infrastructure for VR-Audit: the bridge module and the transit pattern are the working tools
through which classical theorems can be systematically classified.

## References

Aczel, P. (1988). Non-Well-Founded Sets. CSLI Lecture Notes, No. 14. Stanford.
Bencivenga, E. (2002). Free logics. In D. Gabbay & F. Guenthner (Eds.), Handbook of Philosophical Logic,
Vol. 5 (pp. 147–196). Springer.
Benacerraf, P. (1965). What numbers could not be. The Philosophical Review, 74(1), 47–73.
Bernays, P. (1937). A system of axiomatic set theory. Journal of Symbolic Logic, 2(1), 65–77.
Bishop, E. (1967). Foundations of Constructive Analysis. McGraw-Hill.
Bridges, D., & Richman, F. (1987). Varieties of Constructive Mathematics. Cambridge University Press.
Brouwer, L. E. J. (1907). Over de Grondslagen der Wiskunde. Doctoral dissertation, University of
Amsterdam.
Feferman, S. (1964). Systems of predicative analysis. The Journal of Symbolic Logic, 29(1), 1–30.
Field, H. (1980). Science Without Numbers. Princeton University Press.
Gödel, K. (1944). Russell's mathematical logic. In P. A. Schilpp (Ed.), The Philosophy of Bertrand Russell.
Northwestern University.
Heyting, A. (1956). Intuitionism: An Introduction. North-Holland.
Hilbert, D. (1926). Über das Unendliche. Mathematische Annalen, 95(1), 161–190.
Kleene, S. C. (1945). On the interpretation of intuitionistic number theory. Journal of Symbolic Logic,
10(4), 109–124.
Lambert, K. (1991). Philosophical Applications of Free Logic. Oxford University Press.
Lawvere, F. W. (1964). An elementary theory of the category of sets. Proceedings of the National
Academy of Sciences, 52(6), 1506–1511.
Löwenheim, L. (1915). Über Möglichkeiten im Relativkalkül. Mathematische Annalen, 76(4), 447–470.
Mendelson, E. (2015). Introduction to Mathematical Logic (6th ed.). Chapman and Hall/CRC.
Nelson, E. (1977). Internal set theory: A new approach to nonstandard analysis. Bulletin of the American
Mathematical Society, 83(6), 1165–1198.
Ockham, William of. (c. 1323). Summa Logicae.
Popper, K. (1972). Objective Knowledge: An Evolutionary Approach. Oxford University Press.
Quine, W. V. O. (1951). Two dogmas of empiricism. The Philosophical Review, 60(1), 20–43.
Reznik, V. (2026). VR. A Formal System: A Minimalist Axiomatization of Arithmetic Grounded in
Leibnizian Void. Zenodo. DOI: 10.5281/zenodo.20212092
Reznik, V. (2026). VR-Numbers: Operational Extensions over the Natural Numbers of VR. Zenodo. DOI:
10.5281/zenodo.20272743
Reznik, V. (2026). VR-Sets: An Operational Theory of Sets Grounded in Leibnizian Void. Zenodo. DOI:
10.5281/zenodo.20303536
Reznik, V. (2026). VR-Forms: A Lean 4 Formalisation of the Two-Register Apparatus (Software, Git tag
v1.3-vr-forms). Zenodo. DOI: 10.5281/zenodo.20355757
Robinson, A. (1966). Non-standard Analysis. North-Holland.
Russell, B. (1903). The Principles of Mathematics. Cambridge University Press.
Shapiro, S. (1997). Philosophy of Mathematics: Structure and Ontology. Oxford University Press.
Simpson, S. G. (2009). Subsystems of Second Order Arithmetic (2nd ed.). Cambridge University Press.
Skolem, T. (1923). Einige Bemerkungen zur axiomatischen Begründung der Mengenlehre.
Matematikerkongressen i Helsingfors, 217–232.
Tarski, A. (1933). Pojęcie prawdy w językach nauk dedukcyjnych. Prace Towarzystwa Naukowego
Warszawskiego, No. 34.
Univalent Foundations Program. (2013). Homotopy Type Theory: Univalent Foundations of Mathematics.
Institute for Advanced Study.
Weihrauch, K. (2000). Computable Analysis: An Introduction. Springer-Verlag.
Whitehead, A. N. (1929). Process and Reality. Macmillan.
Wittgenstein, L. (1953). Philosophical Investigations. Macmillan.
Zermelo, E. (1908). Untersuchungen über die Grundlagen der Mengenlehre. Mathematische Annalen,
65(2), 261–281.

Acknowledgement of AI assistance
The formal exposition of this preprint (Parts I–VIII) was prepared with the assistance of Claude
(Anthropic, model Opus 4.7) for drafting, English translation, language polishing, and consistency
checking, in the same configuration as the earlier works of the VR cycle.
The Lean 4 formalisation documented in Part IX (Reznik 2026, Lean VR-Forms, Software DOI
10.5281/zenodo.20355757) was carried out using a parent-child review architecture: Claude Opus 4.7,
holding the present preprint, acted as architectural reviewer and made all stage-level design decisions;
Claude Sonnet 4.6, running in Claude Code, wrote the Lean code, ran lake build, and reported #print
axioms for every public object. Each of the six stages followed the protocol of plan-before-code with tested
prototype, acceptance criteria, and axiom audit. The same architecture was used in the preceding Lean
cycles of VR-Sets and VR-Numbers.
Part IX itself was drafted by Claude Opus 4.7 from the methodological observations accumulated through
the Lean cycle, with verbatim references to the corresponding source locations in the Lean code.
All mathematical content, definitions, theorems, ontological positions, and architectural decisions are
due to the author.
