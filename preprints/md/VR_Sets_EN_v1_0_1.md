VR-Sets
An Operational Set Theory Unifying ZFC and ZFA through Reference
Semantics

Vitaly Reznik
ORCID: 0009-0002-4103-6387

2026
Version 1.0.1


## Abstract

Building on VR (Reznik, 2026, DOI: 10.5281/zenodo.20212092) and VR-Numbers (Reznik,
2026, DOI: 10.5281/zenodo.20272743), we develop VR-Sets — an operational theory of sets
that unifies ZFC and ZFA through reference semantics. A set is not a container with
contents, but an operational functionality: a procedure that, upon a query, either reveals
a specific element or reveals nothing. The membership relation x ∈ y is read as reference
(the functionality y uses x in its description), not as physical containment. The sole
ontological primitive remains ∅, the empty functionality; everything else arises as
operational action upon ∅. The closure principle — every operationally describable
functionality is a set — replaces the existence axioms of classical ZF and dissolves
Russell's paradox ontologically: paradoxical descriptions simply do not specify
functionalities. All eight ZF axioms together with AC are derived as closure theorems of
the operational universe (or follow from the definitions). The theory distinguishes two
structural modes: the ZFC-mode (well-founded functionalities) and the ZFA-mode
(admitting self-reference and cycles); both are legitimate, and the choice between them is
an explicit ontological decision. The Quine atom A = {A} and other non-well-founded sets
are first-class objects of the ZFA-mode. Three principal divergences from classical ZF
emerge: ℘(ω) is countable; the replacement schema collapses to a single theorem;
foundation is mode-dependent. The VR numbers (von Neumann ordinals) of VR fall
automatically into the ZFC-mode, and the entire arithmetic of VR and VR-Numbers is
inherited without re-proof via the operational isomorphism. The whole operational
universe is countable, which dissolves Cantor's diagonal argument operationally (the
diagonal procedure does not specify a describable functionality), makes AC a theorem
rather than an axiom, and excludes the Banach–Tarski paradox by construction. Tarski's
theorem on the undefinability of truth is reformulated through the hierarchy of
applications of the successor operator t. Part X (added in version 1.0.1) documents the
Lean 4 formalisation of Parts II–V (Reznik 2026, Lean VR-Sets, DOI:
10.5281/zenodo.20354340), reporting ten methodological observations from the
formalisation, centring on five structural boundaries between the operational universe
and mathlib's type-theoretic infrastructure — the deepest of which is the constructive
(axiom-free) absence of the ZFA-mode in mathlib's `PSet`.

**Keywords:** foundations of mathematics, operational set theory, ZFC, ZFA, Anti-

Foundation Axiom, Quine atom, bisimulation, von Neumann ordinals, countable
universe, ontological minimalism, closure principle, reference semantics, Lean 4, formal
verification, mathlib, axiom audit, structural boundaries.

## Part I. Foundations

I.1. Place in the cycle of works
VR-Sets is an operational theory of sets, the third work in a cycle developing the VR
programme:
VR. A Formal System (Reznik, 2026; Zenodo DOI 10.5281/zenodo.20212092) — a formal
axiomatisation of arithmetic on three primitives {∅, →, t} and four axioms. It is
equivalent to Peano arithmetic and consistent relative to ZF. The basic ontological
inventory: the sole primitive ∅, implication →, and the unary successor operator t.
VR-Numbers (Reznik, 2026; Zenodo DOI 10.5281/zenodo.20272743) — operational
extensions over the natural numbers of VR. The integers ℤ, rationals ℚ, reals ℝ, and
complex numbers ℂ are constructed without introducing ordered pairs as objects. In
place of "a pair of numbers" — operational procedures with order built into the
description itself. Substantively: ℝVR is isomorphic to the field of computable reals (a
countable subfield of the classical ℝ); the two-axis structure of ℂ is structurally motivated
by the duality of axiom A1 (the two implications F → F and F → ⊤).
VR-Sets — the present work. An operational theory of sets that unifies ZFC and ZFA
through reference semantics. It resolves the three open questions left in Part VII.3 of VR-
Numbers: an operational reformulation of the ZF axioms, the relation to Tarski's
theorem on the undefinability of truth, and the status of the axiom of choice.
The common methodological line of the three works is ontological minimalism: a sole
primitive ∅, with everything else as operational actions. The slogan, formulated in VR-
Numbers Part VI.5: "only ∅ is, all else is doing." In VR-Sets this principle is applied to
sets: a set is its own operationality, not a separate entity standing behind it.

I.2. The central idea
In classical ZF, a set is a container. The relation x ∈ y is read as "x is located inside y."
Paradoxes of self-reference (Russell) and paradoxes of choice (Banach–Tarski) arise from
tensions in this container metaphor: a container of "all containers that do not contain
themselves" contradicts itself; a container holding "all" elements of a continuum turns
out to be a source of non-measurable decompositions.
In VR-Sets, a set is a functionality. A set does not "contain" elements; a set is the
procedure that, when asked "what are your elements?", either reveals a definite element
or reveals nothing. The elements are themselves sets (themselves functionalities). The
sole initial entity is ∅, the empty functionality, which reveals nothing.
The membership relation x ∈ y is read as reference: x was used in constructing the
functionality y. Not as physical containment. This dissolves the paradox of self-reference
at the ontological level: x ∈ x does not mean "x is physically inside itself" but rather "the
functionality x, in one of its responses, returns x." This is a definite response, not a
structural cycle.
Two ontological modes correspond to two choices regarding self-reference. The ZFC-
mode forbids functionalities from referring to themselves in their responses; the ZFA-
mode permits this. In both modes a set is operationality; the difference lies in which
operationalities are admitted. Part IV of the preprint formalises this distinction.
Summary of the central idea. A set is not a vessel with contents, but a description of
behaviour: "here is what I will reveal when asked." Everything else is consequence of
this change of metaphor.

I.3. Ontological position
We fix here the ontological commitments inherited in VR-Sets from VR and VR-Numbers.

Position 1: ∅ is the sole primitive
In the ontology of VR-Sets there is only one primary object — ∅, the empty
operationality. All other objects are constructions over ∅, realised through operational
functionalities. No atoms (in the sense of urelements in ZFA), no individuals, no ordered
pairs as independent objects. Anything that is "something else" is an action, not a
separate entity.

Position 2: all is sets
The elements of sets are themselves sets. This is consistent with Position 1: if elements
could be some "atoms" distinct from sets, we would have a second primitive kind of
object, violating minimalism. In VR-Sets, the only thing that can be revealed upon
querying a membership functionality is another set (another functionality, or the same
∅).

Position 3: operationality is derived, not ontological
Ontological status in VR-Sets belongs only to ∅. Operationality is a derived entity: it is, in
the sense that it is given by its description, but it is not ontologically primary — it exists
as an action upon ∅, not as a self-standing kind of being alongside ∅.
This distinction is principled. To say "we have two kinds of objects — ∅ and
operationality" would be ontologically inaccurate: this would place operationality on the
same level of primacy as ∅, violating minimalism. The precise formulation: ∅ alone is
ontologically primary; operationality is present as a way of acting — action directed
upon ∅ and upon the results of prior actions — and has no ontological status
independent of this directedness.
A clarifying analogy. In arithmetic, the number 1 is ontologically primary; "add 1" is not
an object but an action. One may speak of "the addition function" as a mathematical
object — but this is already derivative from primary arithmetic, not a separate kind of
number. So too in VR-Sets: ∅ is primary; operationality is action; "functionality as object"
is derivative speech, not a separate ontological kind.
No atoms, individuals, labels, urelements, or ordered pairs as objects belong to the
ontology of VR-Sets. The name of a set is the set itself (is operationality itself); not a
separate syntactic pointer with ontological status. The slogan "only ∅ is, all else is doing"
in application to this position means literally: only ∅ is; everything else acts, and action
is not being.

Position 4: operational infinity in place of actual infinity
Infinity in VR-Sets is the unbounded applicability of an operation, not a "completed
totality." The set ω is infinite not because it holds all natural numbers as a finished
object, but because its functionality is not exhausted at any finite number of queries. The
distinction is methodological: classical ZF postulates the existence of an actually infinite
set; VR-Sets discovers operational infinity as a consequence of the closure principle (see
Part III).

Position 5: operational set in place of set-as-container
A set in VR-Sets is an operational entity given by its membership functionality. A set is its
functionality, not separate from it. This is the core definition, given formally in Part II.
Here we fix it as an ontological position: "set = operationality" is not a renaming, but a
replacement of the underlying metaphor.

The slogan
The slogan of the position, inherited from VR-Numbers Part VI.5 and applied to sets:
"Only ∅ is — all else is doing."
Applied to VR-Sets: a set is its operationality, not separate from it; ∅ is the sole
ontologically primary object; all other sets are actions, not entities.

I.4. Reference vs. containment: the key distinction
The central distinction on which the resolution of self-reference paradoxes in VR-Sets
rests is the distinction between membership as reference and membership as
containment. We examine it through simple examples.

The container picture (classical ZF)
In classical ZF the set {a, b, c} is a "container" physically holding the elements a, b, c. The
self-referential set A = {A} on this picture requires that A contain itself as an element —
which generates the intuitive paradox: "how can a container be inside itself?" Russell's
paradox is a sharpening of this difficulty.
Classical ZF resolves the paradox syntactically (axiom of separation: one cannot form a
set from elements with an arbitrary property, only from elements of an already existing
set with a property); type theory resolves it by stratification (a set and its element must
lie at different levels). Both solutions preserve the container metaphor while imposing
restrictions on it.

The reference picture (VR-Sets)
In VR-Sets a set is not a container. A set is a procedure that answers queries. x ∈ y
means: "the functionality y, in one of its responses, reveals x." This is reference: y uses x
in its description.
The self-referential set A = {A} on this picture: A is a functionality that, upon a query,
reveals A. There is no "physical embedding of itself within itself": there is a procedure
that returns a definite response. That this response happens to be A is no more
paradoxical than a recursive function calling itself within its own definition. The
structure is familiar to a programmer:
function A() { return A; }
— there is no contradiction here. A is a function whose only response is itself. This is an
operationally defined description.

Where the difference lies
The distinction between the two pictures is not mathematical (the mathematics of the
same sets remains the same) but semantic. The container picture reads x ∈ y as a claim
about spatial structure; the reference picture reads it as a claim about computational
behaviour. If this were merely a renaming, the distinction would be empty. But it is
substantive:
(a) Russell's paradox in the container picture requires syntactic restrictions (axiom of
separation). In the reference picture it is dissolved ontologically: the description R =
"reveal x if and only if x ∉x" demands a contradictory response to the query "R ∈R?"
and therefore does not specify a describable functionality. R is not "forbidden" — it does
not exist as a functionality.
(b) Self-membership in the container picture is a pathology, requiring a separate axiom
(anti-foundation) to be admitted. In the reference picture it is a natural possibility,
restricted only by the structural condition of well-foundedness (Part IV). Whether to
admit it or forbid it is an ontological choice, not a mathematical necessity.
(c) Extensionality in the container picture is a separate axiom (sets with the same
elements are equal). In the reference picture it is a tautology of the identity definition:
sets with the same responses to queries are the same functionality (see Definition 4 of
Part II).

An analogy from programming
The distinction between reference and containment is routine in programming. Given a
structure
node = { value: 1, next: node }
— this is a cyclic linked list. There is no "infinite embedding" in memory; there is a
pointer node.next referring to node. The structure is well-defined, not pathological, not
paradoxical. The programmer distinguishes "node holds next as a field" (a reference)
from "node physically contains a copy of itself" (which would be an infinite matryoshka).
VR-Sets makes the same distinction for sets: A ∈ A is a pointer from the functionality A to
itself, not an infinite matryoshka.
This analogy is substantive, not decorative. Modern approaches to non-well-founded sets
(Aczel 1988, Barwise–Moss 1996) explicitly exploit graph representations in which cycles
are admissible data structures. VR-Sets does the same on the ontological level.

I.5. Countability of the operational universe
A fundamental consequence of the operational ontology: the entire universe of sets in
VR-Sets is countable. This is a sharp divergence from classical ZF, where the universe V is
a proper class of uncountable cardinality.

The argument
Every set in VR-Sets is given by a description of its functionality. A description is a finite
syntactic structure (even when the functionality reveals countably many elements — as
with ω — the description itself is finite: "the n-th query yields On"). The set of finite
descriptions over a finite alphabet is countable: this is a basic fact of the theory of formal
languages (a countable union of finite sets is countable).
Therefore the operationally describable functionalities are countable in number. By the
closure principle (Part II §5), every describable functionality is a set. Hence the sets in
VR-Sets are countable in number.

Comparison with classical ZF
In classical ZF the sets form a proper class of uncountable cardinality, and ℘(ω) alone is
already uncountable (Cantor's theorem). VR-Sets departs radically from this picture:
℘(ω) is countable in VR-Sets (Part III, §III.5), and this is not a defect but a consequence of
the ontological choice.
Detailed discussion of this divergence is given in Part VI. Here we fix it as a fundamental
fact: the operational universe of VR-Sets is countable, and from this follow many
structural features of the theory — the absence of uncountability, the simplification of
the axiom of choice, the absence of the Banach–Tarski paradox.

I.6. Terminological glossary
We fix here the terminology used consistently throughout all parts of the preprint.
Ontological terms
Operational set — a set in VR-Sets, given by its membership functionality.
Operationality — the membership functionality, that which is the set. Used as a
synonym for "functionality" in contexts where the ontological status is at issue.
Functionality membership (or simply functionality) — a procedure responding to
queries "what are your elements?"; either reveals a definite element or reveals nothing.
Operational infinity — unbounded applicability of an operation, contrasted with the
actual infinity of classical ZF.
Operational depth — the least number of unfolding steps after which a functionality
reaches ∅. The depth of ∅ is 0; finite sets have finite depth; ω has non-finite but non-
cyclic depth; cyclic sets (such as the Quine atom) have no well-defined depth.
Operational identity ≡ — coincidence of functionalities: A ≡ B if every element of A
matches an element of B under ≡, and conversely. The analogue of Leibnizian equality
from VR.

A note on the sign ≡
The sign ≡ in VR-Sets denotes operational identity. It is not used in any of the standard
alternative senses that this sign carries in mathematical literature:
• not congruence modulo n (as in number theory);
• not logical equivalence (as between formulas);
• not definitional equality (as in type theory).
Rather, ≡ is the coinductive identity between operational functionalities, defined in Part
II Definition 4. It is structurally equivalent to bisimulation in the AFA literature (Aczel
1988), and readers familiar with that tradition may regard ≡ as bisimulation lifted to the
operational setting. We use ≡ rather than = to signal explicitly that identity of sets in VR-
Sets is defined through coincidence of functionalities, not through any pre-existing
notion of equality.

Syntactic terms
Description of a functionality — a finite syntactic record specifying an operational
procedure. A set is describable if it has a description.
Name of a set — the set itself. The ontology of VR-Sets contains no separate layer of
"names denoting objects": the name and the named coincide.

Mode-related terms
ZFC-mode — the operational universe restricted to well-founded functionalities.
Formally defined in Part IV.
ZFA-mode — the operational universe without the well-foundedness restriction;
admitting self-reference and cycles.
Well-founded — a functionality is well-founded if every sequence of successive
unfoldings of its responses terminates at ∅ in a finite number of steps. Discussed in
detail in Part IV §IV.2.

Meta-principles
The closure principle — every operationally describable functionality is a set. Formal
statement in Part II §3. In ZFC-mode the principle is applied subject to well-foundedness;
in ZFA-mode without restriction.
Operational definiteness — a functionality returns a definite response to every query;
contradictory descriptions (requiring contradictory responses) do not specify
functionalities. This is what dissolves Russell's paradox.

I.7. Structure of the preprint
The preprint consists of ten parts, listed below. The present part is the first.

## Part I. Foundations. Place in the cycle of works; the central idea; ontological position;

the distinction between reference and containment; countability of the operational
universe; terminological glossary; structure of the preprint.

## Part II. The Operational Construction of Sets. Four core definitions (set, ∅, kinds of

sets by operationality, operational identity ≡), three lemmas (extensionality, uniqueness
of ∅, operational depth), the closure principle, the resolution of Russell's paradox,
principal examples.

## Part III. The ZF Axioms as Closure Theorems. All eight ZF axioms together with AC are

closure theorems of the operational universe (or follow from the definitions of Part II).
Divergences from classical ZF: ℘(ω) is countable; the replacement schema becomes a
single theorem; foundation is a mode-dependent property.

## Part IV. The Two Modes: ZFC and ZFA. Formal definition of the ZFC-mode and ZFA-

mode through well-foundedness as a structural property of a functionality. Theorems of
completeness of each mode relative to the corresponding classical theory. Conjecture of
equivalence — via a countable model.

## Part V. The Numbers of VR in VR-Sets. The von Neumann ordinals On and ω as specific

well-founded operational sets. Automatic membership in the ZFC-mode as a theorem.
Arithmetic inherited via isomorphism with VR Part I.

## Part VI. Cardinality, Cantor, Choice. Countability of the operational universe in full

detail. Cantor's diagonal argument in the operational ontology. AC as a theorem on the
countable universe. Absence of the Banach–Tarski paradox by construction.

## Part VII. Truth and Self-Reference. Tarski's theorem on the undefinability of truth in

light of the operational ontology. The duality of axiom A1 and the hierarchy of levels of
truth through applications of t. A cautious formulation: a reformulation, not a resolution.

## Part VIII. Ontological Position. A parallel to VR-Numbers Part VI. "Only ∅ is, all else is

doing" applied to sets, with detailed exposition of all ontological commitments.

## Part IX. Open Questions. Connections with topoi, homotopy type theory (HoTT),

formalisation in Lean, machine verification of equivalence conjectures, extensions
(Morse–Kelley, NBG).

## Part X. Lean 4 Formalisation of VR-Sets: Methodological Observations.

Methodological observations arising from the Lean 4 formalisation of Parts II–V (Reznik
2026, Lean VR-Sets, DOI 10.5281/zenodo.20354340; tag v1.2-vr-sets). Ten observations in
four groups: quotient-base structure (A); five structural boundaries between the
operational universe and mathlib (B), centring on the type-theoretic absence of the ZFA-
mode; axiom-minimal patterns (C); methodological convergences (D). Resolves §IX.1
Question 3 of this preprint for Parts II–V.
Each part can be read with minimal context from preceding ones, but Parts II–IV form
the core of the system, on which the remaining parts rest.

## Part II. The Operational Construction of Sets

II.0. Introduction
This part of the preprint formalises the operational construction of sets. Building on the
ontological position fixed in Part I (∅ as the sole primitive; everything else as
operationality), we introduce four definitions forming the core of the system:
• Definition 1 — what a set is in VR-Sets.
• Definition 2 — what ∅ is.
• Definition 3 — three kinds of sets distinguished by the character of their operationality
(finite, infinite, cyclic).
• Definition 4 — operational identity ≡.
From these four definitions three lemmas are derived (extensionality, uniqueness of ∅,
operational depth); the closure principle is stated — the principal instrument by which
the ZF axioms will be proved as theorems in Part III; and Russell's paradox is dissolved
ontologically. The part closes with a set of characteristic examples.
The presentation is structured so that all of Parts III and IV rest only on this text; nothing
from the later parts is presupposed. This part is the self-contained foundation.

II.1. Core definitions
Four definitions forming the core of the operational ontology of sets. They are fixed in
their final form — changes here would affect all that follows.

Definition 1 (set)
A set in VR-Sets is an operational entity given by its membership functionality: upon a
query, the functionality either reveals an element (which is itself a set, possibly the same
set as the one being queried) or reveals nothing. The order in which elements are
revealed is an artefact of observation and does not enter into the identity of the set. A set
has no internal structure beyond its functionality; it is its functionality.
Commentary. (1) A set in VR-Sets is not a container with contents, but a description of
behaviour: "here is what I will reveal when asked." This replacement of the underlying
metaphor is the core divergence from classical ZF (see Part I §I.4).
(2) "A set is its functionality" is an ontological identity, not an operationalism by
definition. The functionality is not "how the set behaves" (as though something more
fundamental stood behind the behaviour); the functionality is the set. No "carrier of the
functionality" distinct from it is presupposed.
(3) The elements of sets are themselves sets. This is explicitly fixed in the definition ("an
element is itself a set") and accords with Position 2 from §I.3: in VR-Sets there are no
atoms, individuals, or urelements.
(4) Self-reference ("the same set as the one being queried") is explicitly admitted in the
definition. This is an operational possibility; restrictions on self-reference pertain to the
choice of mode (Part IV), not to the definition of a set as such.
(5) The order of revelation is an artefact of observation. This means that if a functionality
reveals elements a, b in one observed order and b, a in another, both observations relate
to the same functionality. The identity of a set is determined by which elements are
revealed, not in what order.

Definition 2 (∅)
∅ is the unique set whose functionality reveals nothing: ∅ is the empty operationality.
Commentary. (1) The definition appeals to "uniqueness," which will be proved as
Lemma 2. Here uniqueness is fixed as part of the meaning of the symbol ∅: when we
write ∅, we mean precisely this set, not one among many possible empty sets.
(2) ∅ is the sole object in the ontology of VR-Sets regarding which ontological primacy is
asserted. All other sets are operationalities; ∅ is empty operationality, and this "empty"
is the terminating point of every construction.

Definition 3 (kinds of sets by operationality)
A set A is:
• finite if its functionality exhausts all elements in a finite number of queries;
• infinite if its functionality is not exhausted at any finite number of queries;
• cyclic if among the revealed elements its functionality returns A itself.
These properties are not mutually exclusive.
Commentary. (1) Finiteness is defined through exhaustion: ∅ and all the von Neumann
ordinals On are finite. Every element of any finite set has finite operational depth
(Lemma 3).
(2) Infinity is defined through non-exhaustion, not through cardinality. Example: ω is
infinite — its functionality reveals O0, O1, O2, … without termination.
(3) Cyclicity is defined through self-return. The Quine atom A = {A} is cyclic. The set B =
{∅, B} is cyclic (its functionality returns B among its other elements). Cyclic sets belong to
the ZFA-mode but not the ZFC-mode.
(4) The properties are not mutually exclusive: a set may be simultaneously infinite and
cyclic (for instance, a describable sequence of sets each containing a reference to the
next and to itself). Such cases are rare in substantive mathematics but are not excluded
by the definition.
Definition 4 (operational identity ≡)
Sets A and B are operationally identical (A ≡ B) if their functionalities coincide: for every
element x of A there exists an element y of B with x ≡ y, and conversely. ∅ ≡ ∅.
Commentary. (1) The definition is coinductive: ≡ is defined through ≡ on elements. The
termination point is ∅: if both sets are empty, ≡ holds trivially (vacuously).
(2) Relation to Leibnizian equality from VR. In VR (Part I, Definition 2) equality is given
↔
classically: x = y   ∀p: p(x) ↔ p(y) — coincidence under all properties. In VR-Sets ≡ is
the direct analogue of Leibniz, lifted to the operational level: in place of "under all
properties" — "under all responses to queries." Substantively, this is the same identity
relation, expressed in the language suited to the ontology.
(3) The distinction between ≡ and ordinary =. In what follows ≡ is used for the
operational identity of sets, and = only in contexts referring to classical objects (ZF
formulas, numerical equalities). This discipline is observed in all parts of the preprint.
The sign ≡ is also distinguished from its various standard senses in mathematical
literature (modular congruence, logical equivalence, definitional equality); see Part I §I.6
for the note on notation.
(4) Bisimulation. In the AFA literature (Aczel 1988) the analogous relation is known as
bisimulation: sets are equivalent if their graphs of membership are isomorphic (allowing
cycles). In VR-Sets ≡ is structurally the same relation, expressed operationally. The direct
connection is discussed in Part IV §IV.8.

II.2. Lemmas
Three consequences embedded in the definitions. They are used as lemmas in the later
parts.

Lemma 1 (extensionality)
If A and B have the same elements (up to ≡), then A ≡ B.
Proof. This is a direct reading of Definition 4: the condition of coincidence of
functionalities in Definition 4 is precisely "for every element x of A there exists y of B
with x ≡ y, and conversely." The statement "sets with the same elements are distinct"
contradicts the definition of identity and is inexpressible in VR-Sets.
∎
Remark. This is not a theorem in the strict sense but a formal restatement of the
definition. In classical ZF extensionality is a separate axiom, because in the classical
approach equality is given independently of membership. In VR-Sets equality (more
precisely, operational identity ≡) is defined through membership, so extensionality is
built into the definition.
Lemma 2 (uniqueness of ∅)
There exists exactly one set with an empty functionality.
Proof. If two functionalities both reveal nothing, the coincidence condition of Definition
4 holds vacuously on both sides: "for every element x of A there exists y of B with x ≡ y"
— the premise is false, the implication is true; and conversely. Therefore A ≡ B.
∎
Remark. Lemma 2 does not assert the existence of ∅ — this is given by Definition 2 as
part of the ontology. The lemma asserts uniqueness: in writing ∅ we refer to a fully
determined object, not to an arbitrary "empty set" among many.

Lemma 3 (operational depth)
Every set has an operational depth — the least number of unfolding steps after which ∅
is reached. The depth of ∅ is 0. Finite sets have finite depth. Infinite and cyclic sets do
not have finite depth (for cyclic sets, unfolding does not terminate at ∅).
Note on the status of the lemma. Lemma 3 is not an existence theorem but a definition
of a property of a functionality. Every set A has its depth: a number (or "infinity" with the
qualification "non-cyclic") — a structural characteristic of A. For finite sets this number is
finite; for ω this number is non-finite but each concrete unfolding terminates (see Part IV
§IV.2); for cyclic sets unfolding does not terminate at all.
Significance of Lemma 3. This lemma provides the instrument of induction on sets in
VR-Sets — the analogue of axiom A4 from VR, lifted to the level of sets. The numbers of
VR (the von Neumann ordinals On) have operational depth exactly n; ω has non-finite
depth but is non-cyclic — this is essential for distinguishing "infinite by enumeration"
from "cyclic."

II.3. The closure principle
The principal instrument of VR-Sets. Through it all the ZF axioms are proved in Part III.

Statement
The closure principle of VR-Sets. If a functionality F is operationally describable — that
is, if there exists an operational procedure that gives a definite response to every query
(either revealing a specific element or revealing nothing) — then there exists a set A such
that A is F.
A description requiring a functionality to give contradictory responses to one and the
same query (as in the definition R = "reveal A if and only if A is not revealed") does not
specify an operationally describable functionality, and does not give rise to a set.
Commentary
(1) The closure principle converts the axioms of set existence (as they appear in ZF) into
closure theorems of the operational universe relative to specific describable
constructions. There is no need to postulate "⋃A exists" — one must show that ⋃A is
operationally describable, and then by the closure principle it is a set. This is a
substantive simplification: in place of a long list of existence axioms, a single general
principle.
(2) The closure principle is neither a definition nor a theorem, but an ontological choice:
which functionalities count as sets. The choice is motivated by the slogan "only ∅ is, all
else is doing": all that exists as describable action exists as a set; no different ontological
status is presupposed for "potential" or "inaccessible" entities.
(3) "Operational describability" is a substantive notion. A description must: (a) be finite (a
syntactic record in a formal language); (b) give a definite response to every query (not
contradictory, not undefined, not undecidable by construction). When these conditions
hold, the description specifies a functionality, and the closure principle applies.
(4) In the two modes of VR-Sets the closure principle is applied differently. In the ZFC-
mode — only to functionalities whose successive unfoldings terminate at ∅. In the ZFA-
mode — to all describable functionalities. Part IV unfolds this distinction.

Resolution of Russell's paradox
Russell's paradox is dissolved at the level of the definition. The description R = "reveal x if
and only if x ∉ x" demands a contradictory response from the functionality to the query
"R ∈ R?":
• If the functionality R reveals R on this query, then by the description (R is to contain
only x with x ∉ x) we have R ∉ R, so R should not reveal R. Contradiction.
• If R does not reveal R, then by the description R should contain R (since R ∉ R). So R
should reveal R. Contradiction.
This is a contradictory description. By the closure principle R is not a set — not because
we forbade it by a separation schema (as in ZF) or by type stratification (as in type
theory), but because such a functionality does not exist operationally. At each concrete
step a functionality either reveals a specific element or does not; no third option exists;
the contradictory definition of R cannot be carried out by any procedure.

Relation to classical approaches
Classical ZF resolves Russell's paradox by the axiom of separation: one cannot form a
set from all x with an arbitrary property, only from x ∈ A with a property. This is a
syntactic restriction imposed on the schema of construction.
Type theory resolves the paradox by stratification: an element and a set must lie at
different levels; "x ∈ x" is a type violation.
VR-Sets resolves the paradox by operational definiteness: paradoxical descriptions
simply do not specify functionalities. The result is the same (no paradox), but the cause is
ontological, not syntactic. This is consistent with the general programme of VR:
ontological clarity is placed ahead of technical devices.

II.4. Principal examples
Specific operational sets illustrating the definitions and lemmas.

Example 1: ∅
The functionality ∅ reveals nothing. Operational depth — 0. Finite (exhausted in 0
queries), not infinite, not cyclic. Unique by Lemma 2.

Example 2: {∅}
The functionality {∅} reveals ∅, and on all subsequent queries reveals nothing.
Operational depth — 1 (one unfolding step suffices to reach ∅). Finite.
In the terminology of VR this is O1 — the first non-zero von Neumann ordinal, obtained
by applying t to ∅: O1 = t(∅) = ∅ ∪ {∅} = {∅}.

Example 3: {∅, {∅}}
The functionality reveals ∅ and {∅}. Operational depth — 2. Finite.
In the terminology of VR this is O2 = t(O1) = O1 ∪ {O1} = {∅, {∅}}.

Example 4: ω
The functionality ω reveals on its n-th query the von Neumann ordinal On: ∅, {∅}, {∅,
{∅}}, …, without termination.
Operational depth — non-finite (unfolding does not reach ∅ at any finite step). Infinite
(the functionality is not exhausted). Non-cyclic: ω does not return itself among the
revealed elements. Each revealed element is a specific On with finite n; the unfolding
chain from any specific On terminates at ∅ in n steps.
This last characteristic — "infinite but non-cyclic" — gives ω the property of well-
foundedness, unfolded in Part IV §IV.2: every successive unfolding of ω terminates at ∅,
even though ω itself has no finite operational depth.

Example 5: the Quine atom A = {A}
The functionality A reveals A on every query. Operational depth is undefined: the
unfolding A ∋ A ∋ A ∋ … does not terminate at ∅. Cyclic by Definition 3. Not well-
founded.
The Quine atom belongs to the ZFA-mode of VR-Sets but not to the ZFC-mode. This is the
first example of an ontologically legitimate but non-well-founded set; detailed discussion
appears in Part IV §IV.7.

Example 6: the set B = {∅, B}
The functionality B reveals ∅ and B. Cyclic (reveals itself among its elements). The
unfolding chain B ∋ ∅ terminates at the first step; the chain B ∋ B ∋ B ∋ … does not
terminate. Since well-foundedness requires termination of every chain, B is not well-
founded.
This example shows that cyclicity need not be trivial (as with the Quine atom): a set may
contain both ordinary elements and a self-reference.

Example 7: a description that does not specify a set
R = "reveal x if and only if x ∉ x" (Russell's definition as considered above). This
description is contradictory — it requires the functionality to give a contradictory
response to the query "R ∈ R?". R is not operationally describable. R is not a set.
This is a critically important example: it shows that not every syntactic record specifies a
set. The closure principle yields "every describable functionality is a set," but describable
is a substantive condition, not empty: contradictory descriptions are excluded.

II.5. Summary and transition to Part III
In this part we have introduced the formal apparatus on which the remainder of the
work rests:
(1) Four definitions: of a set, of ∅, of kinds of sets by operationality, of operational
identity ≡.
(2) Three lemmas: extensionality (≡ is built into Definition 4), uniqueness of ∅,
operational depth.
(3) The closure principle: every operationally describable functionality is a set. This is
the principal instrument of the constructions that follow.
(4) Resolution of Russell's paradox — ontologically, not syntactically: paradoxical
descriptions do not specify functionalities.
(5) Seven characteristic examples covering the principal ontological situations: ∅,
finite ordinals, ω, the Quine atom, a partially cyclic set, a contradictory description.
What follows. Part III applies this apparatus to the axioms of classical ZF. Each ZF axiom
(except extensionality and the existence of ∅, already built into Part II) becomes a
closure theorem of the operational universe — that is, an assertion that a corresponding
describable functionality is a set under the closure principle.
Part IV formally separates the two modes in which the closure principle is applied — the
ZFC-mode (only to well-founded functionalities) and the ZFA-mode (to all describable
ones) — and establishes theorems of completeness for each mode relative to the
corresponding classical theory. The Quine atom and its analogues are legitimate objects
of the ZFA-mode but not of the ZFC-mode.

## Part III. The ZF Axioms as Closure Theorems


### 0. Introduction

This part of the preprint shows that the eight standard ZF axioms (together with the
axiom of choice AC) are, in VR-Sets, not postulates of existence but closure theorems of
the operational universe relative to specific describable constructions. Two of them —
extensionality and the existence of the empty set — have already been proved as
Lemmas 1 and 2 of Part II and are only recalled here. The remaining seven assertions
(pairing, union, power, infinity, replacement, foundation, choice) are derived by a
uniform pattern on the basis of the closure principle fixed in Part II.
Proof pattern. For each axiom:
(1) the classical ZF formulation is given; (2) the operational functionality F corresponding
to the asserted set is specified; (3) the operational describability of F is verified — that the
functionality gives a definite response to every query; (4) by the closure principle it is
concluded that F is a set.
Summary of results of Part III. The eight ZF axioms together with AC receive the
following status in VR-Sets:
| **Axiom** | **Status in VR-Sets** |

| Extensionality | Lemma 1 (consequence of Definition ≡) |

| Empty set | Lemma 2 (consequence of Definition 2) |

| Pairing | Closure theorem (trivially) |

| Union | Closure theorem (with a remark on ≡) |

| Power | Closure theorem; ℘(ω) is countable (divergence) |

| Infinity | Theorem via operational infinity |

| Replacement | A single theorem in place of a schema (simplification) |

| Foundation | Mode-dependent: theorem in ZFC, false in ZFA |

| Choice | Theorem on the countable operational universe |

Terminological reminder. All terms — operational set, membership functionality,
operational depth, operational identity ≡, the closure principle — were introduced in
Part II and the Foundation Notes and are used here without redefinition. The sign ≡
denotes the operational identity of sets; the sign of equality = does not appear in this part
as an independent symbol, except in classical ZF formulations.
Three critical points. Before the detailed proofs we highlight three places where the
results of this part are especially important for what follows:
• ℘(ω) in VR-Sets is countable. The sharpest divergence from classical ZF; it shows up
already here, before the separate chapter on uncountability (Part VI).
• The replacement schema collapses into a single theorem. A structural simplification: the
closure principle covers what in ZF requires an axiom schema.
• Foundation is a mode-dependent property. The distinction between the ZFC-mode and
the ZFA-mode is defined precisely through the satisfaction or non-satisfaction of
foundation. In Part IV this becomes a technical definition.

III.1. Extensionality
Classical ZF formulation
∀A ∀B ( ∀x (x ∈ A   ↔ x ∈ B) → A = B )
Status in VR-Sets
Assertion (Lemma 1 of Part II). If sets A and B have the same elements (up to
operational identity ≡), then A ≡ B.
Remark. This is not a closure theorem: extensionality is built into the very definition of
operational identity (Definition 4). The condition "for every element x ∈ A there exists y
∈ B such that x ≡ y, and conversely" is precisely the condition of coincidence of
functionalities, i.e. ≡ by definition. The statement "sets with the same elements are
distinct" contradicts the definition of identity and is inexpressible in VR-Sets.
Relation to ZF. In ZF extensionality is a separate axiom because in the classical
approach equality is given independently of membership. In VR-Sets equality (more
precisely, operational identity) is defined through membership, and hence extensionality
is a tautology of the definition. This is the first (and gentlest) of the places where the
apparatus of VR-Sets proves more compact: a single decision at the level of definitions
removes the need for a separate axiom.

III.2. Empty set
Classical ZF formulation
∃A ∀x (x ∉ A)

Status in VR-Sets
Assertion (Lemma 2 of Part II). There exists exactly one set with an empty
functionality; it is denoted ∅ and is given as a primitive by Definition 2.
Remark. The existence of ∅ is not a closure theorem but a primary primitive of the
ontology: ∅ is the sole entity for which ontological primacy is asserted ("only ∅ is").
Uniqueness was proved in Lemma 2: if two functionalities both reveal nothing, the
condition of coincidence of functionalities in Definition 4 holds vacuously on both sides.
Relation to ZF. In ZF the existence of the empty set is postulated by a separate axiom
and justified by the separation schema. In VR-Sets ∅ is the sole ontological primitive, and
there is no need to postulate it: ∅ is given by the construction of the system. The
existence of the empty set in VR-Sets is neither a theorem nor an axiom but an
ontological decision underlying the entire foundation.

III.3. Pairing
Classical ZF formulation
∀a ∀b ∃A ∀x (x ∈ A   ↔ x ≡ a ∨ x ≡ b)
Theorem (pairing)
For any sets a and b there exists a set, denoted {a, b}, whose functionality reveals exactly
a and b (when a ≡ b — a single element).

Proof
Functionality. Define F{a,b} as follows: on the first query the functionality reveals a; on
the second — reveals b; on all subsequent queries reveals nothing. If a ≡ b, the second
step amounts to a repeated presentation of the same element, and by extensionality
(Lemma 1) the functionality reveals a single element.
Describability. On every concrete query the response is defined: 1st query → a; 2nd
query → b; n-th query for n ≥ 3 → exhaustion. No indeterminacy or contradictory
responses arise.
Conclusion. By the closure principle, F{a,b} is a set. It is denoted {a, b}.
∎

Remark: ordered pairs
The ordered pair ⟨a, b⟩ is not introduced as an object of VR-Sets. This is consistent with
the position of VR-Numbers, where pairs are excluded from the ontology: "only ∅ is, all
else is doing" means that new entities are not produced by "binding" already-existing
ones, only by describable functionalities.
If in the sequel (for instance, in relations and functions) order should be required, it is
realised not by introducing pair-objects but through the order of revelation of elements
within a functionality. Order becomes an internal property of the description of a
functionality, not a separate structure. Technically this means that a function f : A → B in
VR-Sets is an operational set whose functionality, on the query "what does f yield at a?",
returns the corresponding element of B, without the mediation of a set of pairs ⟨a, f(a)⟩.
III.4. Union
Classical ZF formulation
∀A ∃B ∀x (x ∈ B   ↔ ∃C (C ∈ A ∧ x ∈ C))
Theorem (union)
For any set A there exists a set, denoted ⋃A, whose functionality reveals exactly all
elements of elements of A (without repetitions up to ≡).

Proof
Functionality. Define F⋃A as a nested procedure: for each element C revealed by the
functionality A, reveal in turn all elements x revealed by the functionality C; elements
already previously revealed (up to ≡) are skipped.
Describability. The functionality A is describable (A is the given set); for each revealed C
the functionality C is describable (C is a set, an element of A); the composition of
describable functionalities is a describable procedure. On every concrete query ⋃A gives
a definite response: either a new element, or exhaustion (when all elements of all C ∈ A
have already been revealed).
Conclusion. By the closure principle, F⋃A is a set. It is denoted ⋃A.
∎

Subtlety: decidability of ≡ when skipping repetitions
The formulation of the functionality used the condition "skipping repetitions up to ≡." In
general, operational identity ≡ is not algorithmically decidable: for arbitrary infinite sets
A and B the question "A ≡ B?" reduces to a coinductive check of coincidence of
functionalities and in the worst case fails to terminate in a finite number of steps.
This does not render the functionality ⋃A impossible: its operational description is
correct — at each step the decision "yield an element or skip" depends on the true
answer to the question "does it coincide with one of those already yielded?" However,
realising this functionality by an effective algorithm is not always possible. This
distinction is consistent with the general position of VR-Sets: the theory is operational but
not necessarily effective throughout. Decidability of ≡ is a separate question for separate
classes of sets (for finite sets with finite operational depth ≡ is decidable; for VR numbers
≡is decidable by construction; in general — not).
An alternative formulation without appeal to ≡: F⋃A reveals all elements of all C ∈ A
with possible repetitions, and extensionality (Lemma 1) guarantees that the resulting set
coincides with the set without repetitions. In this form describability does not depend on
the decidability of ≡, and the proof becomes more rigorous. In the sequel we take this as
the canonical formulation.
III.5. Power
Classical ZF formulation
∀A ∃B ∀x (x ∈ B   ↔ x ⊆ A)
Theorem (power)
For any set A there exists a set, denoted ℘(A), whose functionality reveals exactly all
subsets of A — that is, all operationally describable functionalities whose revealed
elements belong to A.

Proof
Functionality. Define F℘(A) as a procedure revealing in turn all subsets of A.
Case of finite A. Let A have operational depth n. There are 2n subsets; each is given by a
functionality "reveal such-and-such elements of A, the others not at all," which is trivially
describable. The enumeration of 2n subsets is finite and describable.
Case of infinite A (for instance A = ω). A subset of ω is any operationally describable
functionality revealing some elements of ω. The set of such describable functionalities is
countable: each functionality is given by a finite description (an algorithm of finite
length) over a finite alphabet, and the set of finite strings over a finite alphabet is
countable. The enumeration of these functionalities is describable (for instance, by
increasing length of description and lexicographically within a single length).
Describability. In both cases, on every concrete query F℘(A) gives a definite response:
the n-th subset of A by the enumeration, or exhaustion (for finite A).
Conclusion. By the closure principle, F℘(A) is a set. It is denoted ℘(A).
∎

Important consequence: ℘(ω) in VR-Sets is countable
From the proof it follows that ℘(ω) in VR-Sets is a countable set. This is a sharp
divergence from classical ZF, where ℘(ω) is uncountable by Cantor’s diagonal argument.
The divergence calls for a direct comment.
A clarification on the status of ℘(ω). The proof above establishes ℘(ω) as a set by the
closure principle: the description “the operationality revealing in turn all describable
subsets of A” specifies a functionality, and by closure this functionality is a set. This is
“existence as an object.” It is a separate question whether the same enumeration is
realisable as an effective operational procedure — whether there exists an algorithm
that, on the n-th query, returns a correct description of the n-th subset. The answer is no:
such an algorithm would have to decide, for an arbitrary description, whether it specifies
a correct functionality, which is equivalent to the halting problem. ℘(ω) is therefore
countable as an object but not enumerable as a procedure. This distinction — countable
from without vs. enumerable from within — is developed in detail in Part VI §VI.2 and
§VI.3, where it is shown to be precisely what removes Cantor’s diagonal in the
operational ontology.
Where Cantor’s diagonal fails to apply. The classical diagonal argument constructs,
from an enumeration of subsets S0, S1, S2, …, a set D = {n : n ∉ Sn} differing from every
Sn. For this argument the enumeration of the Sn must be complete, and the definition of
D must specify an operational functionality.
In VR-Sets a complete enumeration of all describable subsets of ω is operationally
unattainable — it is equivalent to solving the halting problem: to enumerate all
algorithms correctly specifying a subset of ω one would have to separate terminating
functionalities from non-terminating ones, which is undecidable. Accordingly, the
diagonal D, defined with respect to "all describable subsets," does not specify a
describable functionality — it rests on an operational procedure which does not exist. By
the closure principle D is not a set.
The diagonal is thus removed not by forbidding it as a proof, but by the fact that its
premise (a complete enumeration of describable subsets) is operationally unrealisable.
Connection with computable analysis. An analogous situation is well known for
computable real numbers: the set of computable reals is countable "from without" (from
the standpoint of classical mathematics) but not enumerable "from within" — there is no
algorithm enumerating all computable reals. ℘(ω) in VR-Sets stands in the same position:
countable as an object, not enumerable as a functionality.
A detailed discussion of the consequences appears in Part VI. Here let us fix: the power
set exists as a closure theorem, but ℘(ω) in VR-Sets and ℘(ω) in classical ZF are not
one and the same object. The difference is most visible precisely at this axiom.

III.6. Infinity
Classical ZF formulation
∃A ( ∅ ∈ A ∧ ∀x (x ∈ A → x ∪ {x} ∈ A) )

Theorem (infinity)
There exists a set, denoted ω, whose functionality reveals in turn ∅, t(∅), t(t(∅)), …
without exhaustion and without cycling.

Proof
Functionality. Define Fω: on the n-th query (for n ≥ 0) the functionality reveals the n-th
von Neumann ordinal On, where O0 = ∅ and On+1 = t(On) (definitions from Part I of VR).
Describability. Each step of revelation is defined: the operator t (successor) is total on
the objects of VR (axiom A3); by induction (axiom A4) the functionality is defined for
every n. On every concrete query Fω gives a definite response — a specific object On. The
functionality does not terminate (is not exhausted at any finite step) and is non-cyclic
(t(x) ≠ x in VR — Theorem 5 of Part I).
Conclusion. By the closure principle, Fω is a set. It is denoted ω.
∎

Remark: operational infinity
This statement lifts to the set level the principle of operational infinity from VR-Numbers
(Part VI.3). In classical ZF the axiom of infinity postulates the existence of a completed
totality of all natural numbers; finite means cannot derive its existence, so it is required
as an axiom.
In VR-Sets no "completed totality" is asserted. ω is an unboundedly applicable
operation enumerating On, and by the closure principle an unboundedly applicable
describable operation is already a set. The divergence with classical ZF at this point is
methodological: where ZF postulates, VR-Sets discovers a consequence of the operational
ontology.
ω has non-finite operational depth (unfolding to ∅ does not terminate in any finite
number of steps), but is non-cyclic: the sequence O0, O1, O2, … is non-repeating. This
distinction "infinite by enumeration" vs. "cyclic" first becomes operative at ω.

III.7. Replacement
Classical ZF formulation (axiom schema)
For every formula φ(x, y) specifying a functional relation (∀x ∃!y φ(x, y)) and for every
set A there exists a set B = { y : ∃x ∈ A, φ(x, y) }.
In ZF this is an axiom schema — one axiom for each formula φ of the language of ZF.

Theorem (replacement)
For any set A and any operationally describable procedure F defined on the elements of
A, there exists a set, denoted image(F, A), whose functionality reveals exactly F(x) for
every x ∈ A.

Proof
Functionality. Define Fimage: for each element x revealed by the functionality A, reveal
F(x).
Describability. The functionality A is describable. The procedure F is describable by
assumption (this is part of the hypotheses of the theorem). The composition of
describable functionalities is a describable functionality. On every query Fimage gives a
definite response: for the next revealed x ∈ A the result is a specific object F(x), or
exhaustion if A is exhausted.
Conclusion. By the closure principle, Fimage is a set. It is denoted image(F, A).
∎

Structural simplification: schema → single theorem
In classical ZF replacement is a schema: one axiom for each formula φ. This is bound up
with the fact that in ZF a "relation" is a syntactic object (a formula of the language), and
for each formula a separate existence assertion is required.
In VR-Sets an "operationally describable procedure F" is a single ontological notion
encompassing all ways of specifying functional relations (including all formulas of the
language of ZF translated into operational descriptions). Therefore a single closure
theorem with respect to describable transformations replaces the entire schema.
This is a pattern typical of VR-Sets: what in ZF is dispersed over an infinite series of
syntactic cases is, in VR-Sets, gathered into a single substantive assertion resting on the
ontology (the closure principle), not on syntax.
Comparison with Fraenkel's replacement. Replacement was added to ZF by Fraenkel
and Skolem in order to construct sets such as { ω, ω+1, ω+2, … }, unreachable by
Zermelo's means. In VR-Sets such sets are obtained directly through the closure
principle: the procedure "apply t k times to ω" is describable, and so the image of this
procedure on ω is a set. No additional postulates are needed.

III.8. Foundation (Regularity)
Classical ZF formulation
∀A ( A ≠ ∅ → ∃x ∈ A (x ∩ A = ∅) )

Equivalent formulation
There exist no infinitely descending chains of membership: there is no sequence x0 ∋ x1
∋ x2 ∋ … without termination.

Status in VR-Sets: mode-dependent
This is the first ZF axiom whose status in VR-Sets depends on the choice of mode (ZFC-
mode vs. ZFA-mode). Unlike the preceding axioms — closure theorems holding
unconditionally — foundation turns out to be a characterising property of one of the two
modes.

Assertion 1 (foundation in the ZFC-mode)
In the ZFC-mode of VR-Sets, foundation holds: there exist no infinitely descending chains
of membership.
Proof
In the ZFC-mode, self-references of a label to its own functionality are syntactically
forbidden. We show by induction on operational depth (Lemma 3 of Part II) that every
set in the ZFC-mode has finite depth or "infinite-but-foundationally-grounded-by-ω-
enumeration" depth.
Base. ∅ has depth 0. There is no membership chain from ∅ (∅ contains no elements).
Step. Suppose the assertion holds for all sets of depth < n. Let A have depth n. Any chain
A ∋ x1 ∋ x2 ∋ … begins with x1 ∈ A; the depth of x1 is strictly less than n (by the
definition of operational depth); by the inductive hypothesis the chain from x1
terminates at ∅. Hence the original chain terminates.
Case of ω-depth. For sets such as ω whose depth "runs to infinity" (and is non-cyclic), a
chain from ω has the form ω ∋ On ∋ On−1 ∋ … ∋ O0 = ∅. Any specific choice of an
element x1 ∈ ω is a specific On with finite n, and the subsequent chain terminates at ∅.
An infinitely descending chain from ω does not arise.
∎

Assertion 2 (failure of foundation in the ZFA-mode)
In the ZFA-mode foundation does not hold. There exist sets giving infinitely descending
chains of membership.

Example
In the ZFA-mode the description of a set A is admissible through a label A := the
functionality revealing one element — A itself. Formally: the functionality "on a query
reveal the set denoted by the same label as the current one." The chain A ∋ A ∋ A ∋ …
does not terminate. This set is known as a Quine atom in Aczel (1988).
Here it is important: A does not contain itself in the sense of physical containment.
According to the ontology of VR-Sets (Foundation Notes §2), membership is a reference,
not a container. A ∈ A means that the functionality A returns A on a query — a specific
definite response, not a structural self-embedding. There is no paradox; there is only a
failure of foundation.

Conclusion
Foundation is not a universal theorem of VR-Sets but a characterising property of the
ZFC-mode. The two modes differ precisely on this:
• ZFC-mode — foundation holds (the theorem above); self-references are syntactically
forbidden; the operational depth of every set is defined.
• ZFA-mode — foundation fails; self-references are admitted; the operational depth of
certain sets is undefined (cyclic functionalities).
In Part IV this will give a technical definition of the distinction between the two modes:
ZFC-mode = ZFA-mode + foundation (when the restriction on self-references of labels is
properly formulated). Conjecture: the ZFC-mode is equivalent to classical ZFC, the ZFA-
mode to Aczel (AFA).

III.9. Choice
Classical ZF formulation (AC)
For every set of pairwise disjoint non-empty sets there exists a set containing exactly one
element from each.

Status in VR-Sets: theorem on the countable universe
The position on AC is fixed in the Foundation Notes (§6.3) and is unfolded here into a
proof. Briefly:
• DC (dependent choice) is built into the operational ontology: every operation is
carried out concretely, and a sequence of operations is built step by step. DC is not an
axiom but a property of operationality itself.
• Full AC is a theorem on the countable operational universe (for countable sets, AC
reduces to DC).
• The Banach–Tarski paradox is not reproduced — not because AC is "operationally
interpreted" but because there is no uncountable classical ℝ in VR-Sets. Disputed
applications of AC take place outside the operational universe.

Theorem (countable choice)
For every countable family {Ai}i ∈ ω of pairwise disjoint non-empty sets there exists a
set, denoted choice({Ai}), containing exactly one element from each Ai.

Proof
Functionality. Define Fchoice: on the i-th query the functionality reveals the first
element of Ai — that is, the element revealed by the functionality Ai on its first query.
Describability. The countable family is an operational set whose functionality reveals
A0, A1, A2, … Each Ai is an operational set with a non-empty functionality, so its first
query gives a definite element. The composition of these describable procedures specifies
a describable functionality Fchoice: for every i ∈ ω a specific response is defined.
Conclusion. By the closure principle, Fchoice is a set.
∎
On full AC and the countability of the universe
The theorem just proved suffices for the entire operational universe of VR-Sets: the
whole universe is countable (Foundation Notes §6.2), and so any family of non-empty
pairwise disjoint sets in VR-Sets is countable. There are no uncountable families in VR-
Sets. Accordingly, AC in full form is equivalent to countable AC, which is a theorem.
A detailed discussion appears in Part VI. Here let us fix: AC is a theorem, not an axiom.
The Banach–Tarski paradox is absent not because AC is weakened, but because the
objects on which it is built (uncountable subsets of ℝ, non-Lebesgue-measurable sets) do
not exist in the operational ontology.

Subtlety: the operationality of "first element"
The formulation "reveal the first element of Ai" requires that the functionality Ai have a
fixed "first" query. By Definition 1 of Part II the order of revelation of elements is an
artefact of observation and does not enter into the identity of a set. However, for each
concrete presentation of the functionality Ai its first query yields a definite element. If
there are several presentations and the order of revelation differs, choice may return
different elements — but these are different functionalities choice, not an inconsistent
definition.
Formally: with a fixed order of revelation of each Ai, the function choice is uniquely
defined. The operational theorem says that such a functionality is a set. It does not
presuppose that there is a uniquely correct choice (which depends on the order of
presentation); only that any consistent choice specifies a set. This is precisely the content
of classical AC: existence of a choice function, not its uniqueness. The operational
reformulation preserves this classical content exactly.

Conclusion
Part III shows that the ZF axioms in VR-Sets are not postulates but theorems. Of the nine
assertions considered:
• Two (extensionality, empty set) are built into the definitions and lemmas of Part II and
do not require a separate proof.
• Six (pairing, union, power, infinity, replacement, choice) are closure theorems of the
operational universe with respect to specific describable functionalities. The closure
principle gives them a uniform proof.
• One (foundation) is a mode-dependent property distinguishing the ZFC-mode from the
ZFA-mode.
Substantive divergences from classical ZF brought out in this part:
(1) ℘(ω) in VR-Sets is countable. Cantor's diagonal argument in the operational ontology
produces no new subset, because its premise (a complete enumeration of describable
functionalities) is operationally unrealisable — it is equivalent to solving the halting
problem.
(2) The replacement schema reduces to a single theorem. The closure principle with
respect to describable transformations covers the entire series of cases that, in ZF,
require a separate axiom for each formula.
(3) Foundation is not a universal property but a distinguishing one. The ZFC-mode and the
ZFA-mode in VR-Sets are two ontologically legitimate configurations; the distinction
between them is a syntactic restriction on self-references of labels, technically
manifesting as the satisfaction or non-satisfaction of foundation.
(4) AC is a theorem, not an axiom. On the countable operational universe AC reduces to
DC, which is built into operationality. The Banach–Tarski paradox is not reproduced, not
because of a weakening of AC but because of the absence of the classical ℝ objects on
which it is built.
What follows. Part IV uses foundation as the technical definition of the distinction
between the ZFC-mode and the ZFA-mode, formulates this distinction syntactically, and
discusses the conjecture of equivalence with classical ZFC and with Aczel. Part V specifies
the role of VR numbers in VR-Sets: On are specific operational sets with finite depth,
landing in the ZFC-mode as a theorem. Part VI develops the countability of the
operational universe and discusses Cantor's diagonal, AC, and the absence of
uncountability paradoxes in detail.

## Part IV. The Two Modes: ZFC and ZFA

IV.1. The fork: two modes as two levels of application of the closure
principle
In Part III the closure principle was applied to describable operational functionalities
without restriction: every describable functionality is a set. In §III.8 it emerged that one
of the ZF axioms — foundation — does not hold on all such functionalities. The Quine
atom A = {A} showed that the description "functionality revealing itself" is operationally
describable but gives rise to a set with an infinitely descending chain of membership.
This is the ontological fork of VR-Sets. The closure principle in full strength gives a
universe in which all ZF axioms hold except foundation. The closure principle,
restricted by the condition that successive unfoldings terminate at ∅, gives a universe in
which all ZFC axioms hold, including foundation. These two universes are the two modes
of VR-Sets:
• ZFC-mode: the closure principle is applied only to functionalities whose successive
unfoldings terminate at ∅.
• ZFA-mode: the closure principle is applied to all describable functionalities, without
additional restriction.
In this part the modes are given a precise definition; it is proved that all ZFC axioms hold
in the ZFC-mode (an assembly of the results of Part III); and the conjecture is discussed
that the ZFC-mode is equivalent to classical ZFC and the ZFA-mode to the theory of Aczel
(AFA, 1988). The corresponding converse directions — that every set of classical ZFC has
an operational representation in the ZFC-mode of VR-Sets, and analogously for AFA —
remain open; for each of them §IV.5 and §IV.6 analyse what is required for a proof.

Remark: the modes are not temporal
In the ontology of VR-Sets only ∅ is ontologically primary; operationality is derived (not
a self-standing kind of being, but action upon ∅ and upon the results of prior actions; see
Part I §I.3 in detail). Considered as a description, however, operationality is an integral
object, not a process in time. When a functionality is given by its description, it is that
description fully — there is no "moment of construction," no "already-built" or "being-
built-just-now" in the ontology. Queries to a functionality are a way of addressing it, not
moments of its being.
The distinction between the ZFC-mode and the ZFA-mode is therefore not temporal ("did
the set manage to be built before reference was made to it?") but structural — a
property of the functionality itself, considered as an integral object. The property is
whether successive unfoldings of its responses terminate at ∅ in a finite number of
steps.
This distinguishes the formulation of VR-Sets from the standard set-theoretic approach,
where the well-foundedness condition is often described through an "iterative
conception of the set" — the image of stepwise construction. In VR-Sets there are no steps
and no construction; there is a structural property of a functionality.

IV.2. Unfolding, termination, operational depth
Before the formal definition of the modes we sharpen the technical apparatus inherited
from Part II.

Unfolding of a functionality
Definition IV.1 (successive unfolding). Let A be an operational set. A successive
unfolding of the functionality A is any sequence of sets
A = x₀ ∋ x₁ ∋ x₂ ∋ x₃ ∋ …
where xk+1 is one of the elements revealed by the functionality xk. The unfolding
terminates at ∅ if there exists n such that xn ≡ ∅. The unfolding does not terminate if no
such n exists.

The property of termination
Definition IV.2 (well-founded functionality). A functionality A is well-founded if every
successive unfolding starting with A terminates at ∅ in a finite number of steps.
An equivalent formulation: there is no infinite sequence x0 ∋ x1 ∋ x2 ∋ … starting with
A. This is precisely the classical well-foundedness of the membership relation, lifted to an
individual functionality.

Relation to operational depth
Lemma 3 of Part II defined the operational depth of a set as the least number of unfolding
steps after which ∅ is reached. Cyclic sets (such as the Quine atom) have no finite depth
because unfolding does not terminate.
Assertion IV.1. A functionality A is well-founded if and only if every set reachable from
A by a finite chain of membership has a defined operational depth (finite, or ω-depth
without cycling).
This is not a theorem in the strict sense but a development of definitions: well-
foundedness is precisely the absence of cycles and the absence of infinite descending
chains. For us it is important to fix that well-foundedness is a structural property of a
functionality, verified on its description, not acquired at a moment of construction.

Examples
• ∅ is well-founded trivially (no elements, no unfoldings).
• Every VR number (On) is well-founded: its depth is n, and the single unfolding chain
terminates at ∅ in n steps.
• ω is well-founded: any unfolding starting with ω yields on the first step some On with
finite n, and then terminates in n steps. Despite the "infinity" of ω itself, each concrete
unfolding is finite.
• The Quine atom A = {A} is not well-founded: the unfolding A ∋ A ∋ A ∋ … does not
terminate.
• The set B = {∅, B} (containing ∅ and itself) is not well-founded: the chain B ∋ B ∋ B ∋
… does not terminate, even though the chain B ∋ ∅ does terminate.
The last example shows that well-foundedness is a property of all unfoldings, not of the
existence of at least one terminating chain. This is in accord with the classical definition.

IV.3. Formal definitions of the ZFC-mode and the ZFA-mode
Having the notion of well-foundedness as a structural property of a functionality, we
define the modes.

Definition IV.3 (ZFC-mode)
The ZFC-mode of VR-Sets is the operational universe in which the closure principle is
applied only to well-founded operational functionalities. Formally: a set exists in the ZFC-
mode if and only if (a) it is operationally describable and (b) it is well-founded.

Definition IV.4 (ZFA-mode)
The ZFA-mode of VR-Sets is the operational universe in which the closure principle is
applied to all describable operational functionalities, without the well-foundedness
restriction. Formally: a set exists in the ZFA-mode if and only if it is operationally
describable.

Relation between the modes
Assertion IV.2. Every set of the ZFC-mode is a set of the ZFA-mode: ZFC-mode ⊆ ZFA-
mode as operational universes. The inclusion is strict: the Quine atom A = {A} belongs to
the ZFA-mode but not to the ZFC-mode.
The proof is trivial: the ZFC-mode is defined as the ZFA-mode with the additional
condition of well-foundedness, so ZFC ⊆ ZFA. Strictness of the inclusion is witnessed by
the Quine atom — it is describable (the functionality "reveal yourself" gives a definite
response to every query) and not well-founded (the chain A ∋ A ∋ … does not
terminate).
∎
Remark: the modes are not paradoxical
The Quine atom in the ZFA-mode is not paradoxical. Russell's paradox (Part II §5.2) is
dissolved by the closure principle: the description R = "reveal x if and only if x ∉ x"
requires a contradictory response to the query "R ∈ R?" and so does not specify a
describable functionality. The Quine atom carries no such contradiction: "the
functionality A reveals A" is a definite description, specifying a definite response to every
query. That A contains itself as an element does not contradict the ontology of VR-Sets,
because membership in VR-Sets is reference, not physical containment (Foundation
Notes §2). A ∈ A is "the functionality A in one of its responses returns A," which is
operationally defined.
The distinction between the ZFC-mode and the ZFA-mode is therefore not a distinction
between "non-contradictory" and "paradoxical." Both modes are non-contradictory. The
distinction lies in which operationalities are admitted.

IV.4. Theorem: all ZFC axioms hold in the ZFC-mode
This section assembles the results of Part III as they apply to the ZFC-mode and
establishes a direct inclusion: the ZFC-mode of VR-Sets is a model of classical set theory
ZFC.

Theorem IV.1 (completeness of ZFC in the ZFC-mode)
In the ZFC-mode of VR-Sets all ZFC axioms hold: extensionality, empty set, pairing, union,
power, infinity, replacement, foundation, choice.

Proof
We show that for every ZFC axiom the corresponding closure theorem of Part III remains
in force under restriction to well-founded sets — that is, that the constructions of Part III
do not lead outside the ZFC-mode.
Extensionality (§III.1). Lemma 1 of Part II is formulated through ≡ and applies to any
sets, in particular to well-founded ones. The well-foundedness condition does not affect
the condition of coincidence of functionalities.
Empty set (§III.2). ∅ is well-founded trivially (no elements means no unfoldings). ∅
belongs to the ZFC-mode.
Pairing (§III.3). Let a and b be well-founded. The functionality {a, b} reveals a and b.
Any unfolding starting with {a, b} yields on the first step a or b — a well-founded set —
and then the chain terminates by assumption. Hence {a, b} is well-founded. The ZFC-
mode is closed under pairing.
Union (§III.4). Let A be well-founded. ⋃A reveals elements of elements of A. Any
unfolding of ⋃A yields on the first step some x ∈ C for C ∈ A; the depth of x is strictly less
than the depth of A (two steps down membership); by the well-foundedness of A the
chain terminates. The ZFC-mode is closed under union.
Power (§III.5). Let A be well-founded. ℘(A) reveals all subsets of A — operationally
describable functionalities revealing subsets of the elements of A. Each subset of A is
well-founded (its elements are elements of A, well-founded by assumption; an unfolding
one step down lands on a well-founded element of A). ℘(A) is itself well-founded: its
unfolding on the first step yields a well-founded subset of A. The ZFC-mode is closed
under the power operation.
Infinity (§III.6). ω is well-founded: this was shown in §IV.2 (any unfolding of ω on the
first step yields On with finite n, and the chain terminates in n steps). ω belongs to the
ZFC-mode.
Replacement (§III.7). Let A be well-founded and F a describable procedure mapping
well-founded sets to well-founded sets. Then image(F, A) consists of well-founded sets;
the chain of unfolding image(F, A) on the first step yields F(x) — well-founded — and
terminates by assumption. The ZFC-mode is closed under describable transformations
preserving well-foundedness.
Foundation (§III.8). This is the defining property of the ZFC-mode: every set of the ZFC-
mode is well-founded by Definition IV.3. Foundation holds automatically.
Choice (§III.9). Let {Ai}i ∈ ω be a countable family of non-empty well-founded sets. The
choice functionality reveals the first element of each Ai. The elements are well-founded
(elements of well-founded sets are well-founded). The chain of unfolding choice on the
first step yields a well-founded element — and terminates. The ZFC-mode is closed under
countable choice, which on a countable operational universe yields full AC.
∎

Corollary
Corollary IV.1. The ZFC-mode of VR-Sets is a model of the theory ZFC: every theorem of
ZFC expressed in the language of operational sets holds in the ZFC-mode.
This is a direct consequence of Theorem IV.1 and of the fact that ZFC is precisely the
theory derivable from these axioms. Substantively: the whole of standard mathematics
formalisable in ZFC is accessible in the ZFC-mode of VR-Sets.
From this, however, it does not follow that the ZFC-mode is equivalent to ZFC.
Equivalence requires the converse direction: that every model of ZFC is realised in the
ZFC-mode of VR-Sets. This is an open question, treated in §IV.5.
IV.5. Conjecture: the ZFC-mode is equivalent to classical ZFC
The direct direction has been established: the ZFC-mode is a model of ZFC. The converse
direction — that every model of ZFC is realised in the ZFC-mode of VR-Sets — is
formulated as a conjecture, and we examine what is required for its proof.

Statement
Conjecture IV.1. The ZFC-mode of VR-Sets and classical ZFC are mutually interpretable:
there exist operational interpretations of the standard model of ZFC in the ZFC-mode and
conversely, agreeing on the membership relation.

What is already proved
The direct direction ZFC-mode → ZFC follows from Theorem IV.1: every statement
provable in ZFC holds in the ZFC-mode, since all axioms hold. Accordingly, any
operational construction correct in the ZFC-mode has an analogue in ZFC.

What is required for the converse direction
The converse direction ZFC → ZFC-mode requires that for every set of classical ZFC there
exist an operationally describable representation in the ZFC-mode. This is stronger than
"a model exists": classical ZFC proves the existence of sets for which an operational
description is not obvious.
Principal obstacle: the uncountability of ℘(ω) in classical ZFC. In classical ZFC, ℘(ω)
is uncountable (Cantor's theorem). In the ZFC-mode of VR-Sets, ℘(ω), as shown in §III.5, is
countable: there are countably many operationally describable subsets of ω. This means
that the classical ℘(ω) is not realised in the ZFC-mode as a single object.
Possible responses to this obstacle:
(a) Conjecture in a weakened form. To assert mutual interpretability not with respect to
full classical ZFC but with respect to the constructive part of ZFC — the fragment yielding
only operationally describable sets. This formulation is correct and provable, but less
ambitious: it asserts the correspondence only for "constructive" mathematics.
(b) Conjecture via submodels. The ZFC-mode is interpreted as a countable transitive
model of ZFC (or, more precisely, a fragment of one). By the Löwenheim–Skolem
theorem such a model exists. The correspondence then is not between the ZFC-mode and
the "real" classical ZFC, but between the ZFC-mode and one of the countable models of
ZFC. This is consistent with the conjecture in the form "there is a countable model of ZFC
realised in the ZFC-mode," and this direction appears the most promising for a rigorous
proof.
(c) Conjecture as a declaration of difference. To acknowledge that the ZFC-mode of VR-Sets
and full classical ZFC are not equivalent — they diverge precisely on those objects that
classical ZFC proves to exist but which VR-Sets cannot specify operationally (such as
uncountable subsets of ω). In this formulation the conjecture becomes a theorem on
divergence, and the work in §IV.5 becomes its formal fixation.
Our working position is (b): the ZFC-mode of VR-Sets corresponds to a countable model
of classical ZFC. This position is technically realistic (countable models of ZFC are well
studied), preserves the substantive connection with ZFC, and is consistent with the
countability of the operational universe fixed in the Foundation Notes. A detailed proof
of such a correspondence is a separate technical undertaking, beyond the scope of this
preprint.

Methodological remark
The fact that the ZFC-mode of VR-Sets is not the "whole" of classical ZFC but a countable
model of it is, in the VR system, not a defect but an expected consequence of the
operational ontology. "Only ∅ is, all else is doing" means that the ontology of VR is
restricted to what can be specified operationally; operationally specifiable objects are
finitely or countably many. The uncountable objects of classical ZFC are an artefact of the
non-operational ontology of classical mathematics, which admits the existence of objects
without their operational description.
VR-Sets therefore does not claim to reproduce the full classical universe of sets. It claims
to be an ontologically coherent alternative in which all objects are operational and which
nonetheless contains enough for the whole of constructive and countable mathematics.

IV.6. The ZFA-mode and Aczel
A parallel picture is built for the ZFA-mode. Aczel (1988) proposed the theory AFA (Anti-
Foundation Axiom) — an extension of ZF in which foundation is replaced by anti-
foundation: every directed graph is realised as the membership graph of a unique set.
This permits the existence of cyclic sets such as the Quine atom.

Theorem IV.2 (completeness of ZFA in the ZFA-mode)
In the ZFA-mode of VR-Sets all ZFC axioms hold except foundation, and also the anti-
foundation axiom AFA.

Proof
The axioms of extensionality, empty set, pairing, union, power, infinity, replacement,
and choice are closure theorems of Part III. The proofs do not use well-foundedness and
carry over to the ZFA-mode directly.
Foundation in the ZFA-mode does not hold: the Quine atom A = {A} belongs to the ZFA-
mode (a describable functionality) and violates foundation. This is in accord with the
removal of the corresponding condition in Definition IV.4.
AFA in the ZFA-mode. Aczel's anti-foundation axiom asserts: for every directed graph G
there exists a unique function assigning to each vertex a set so that the membership
relation between these sets agrees with the edge relation of the graph. In the operational
formulation: for every describable graph G (a graph whose vertices and edges can be
operationally enumerated) there exists an operationally describable collection of
functionalities realising the graph.
The describability of such a collection is a standard construction: every vertex v of the
graph G specifies a functionality fv which on a query reveals fw for every edge v → w.
This is an operationally describable description (for describable G). By the closure
principle in the ZFA-mode (without the well-foundedness condition) this is a collection of
sets. Uniqueness up to bisimulation is a consequence of extensionality (Lemma 1 of Part
II).
∎

Remark: operational AFA vs. classical AFA
Classical AFA (Aczel 1988) ranges over every directed graph, including uncountable
graphs without a finite description. The theorem above establishes AFA in the
operational ontology only for describable graphs — those whose vertices and edges admit
a finite operational description. Call this operational AFA. This restriction is the exact
parallel of the situation with classical ZFC and the ZFC-mode in §IV.5: the operational
universe is countable, so its anti-foundation principle ranges only over countable
describable graphs. For every classical undescribable graph there is no corresponding
object in VR-Sets, just as there is no uncountable ℘(ω). The symmetry between the two
modes is therefore: in the ZFC-mode the operational universe is a countable analogue of
classical ZFC; in the ZFA-mode it is a countable analogue of classical ZFC− + AFA.
Conjecture IV.2 below asserts mutual interpretability via a countable model in this same
sense.

Conjecture IV.2 (equivalence with AFA)
Conjecture. The ZFA-mode of VR-Sets and the theory ZFC− + AFA are mutually
interpretable (in the sense analogous to Conjecture IV.1: presumably via a countable
model).
Obstacles and approaches parallel those of §IV.5. The direct direction ZFA-mode → AFA
follows from Theorem IV.2. The converse direction faces the same difficulties with
uncountability; the working solution is a correspondence with a countable model of AFA.

IV.7. The Quine atom and cyclic sets: examples in the ZFA-mode
To make concrete how the ZFA-mode works in practice, we examine several examples of
non-well-founded sets and verify that they are ontologically legitimate in VR-Sets.

Example IV.1: the Quine atom
Description: the functionality A reveals A on every query. Formally: A = {A}.
Operationality: on a query the functionality gives a response — A. This is a definite
response; the functionality is operationally describable. By the closure principle (in the
ZFA-mode) A is a set.
Well-foundedness: the chain A ∋ A ∋ A ∋ … does not terminate. A does not belong to
the ZFC-mode.
Uniqueness: by extensionality there is exactly one set with this functionality. By AFA,
every graph consisting of a single vertex with a self-loop is realised in a unique way —
this is A.

Example IV.2: a pair of mutually referring sets
Description: sets B and C such that B = {C} and C = {B}.
Operationality: the functionality B on a query reveals C. The functionality C on a query
reveals B. Both descriptions are definite.
Unfolding chain: B ∋ C ∋ B ∋ C ∋ … does not terminate. Neither B nor C belongs to the
ZFC-mode.
Distinguishability: B and C are different sets (B contains C, C contains B; the
functionalities do not coincide), but they are bisimilar: their membership graphs are
isomorphic (a two-vertex cycle). In AFA, bisimilar sets are equal; in the ZFA-mode of VR-
Sets, extensionality through ≡ gives the same result if ≡ is interpreted as bisimulation.
This is consistent with the standard AFA literature.

Example IV.3: a set partially well-founded
Description: D = {∅, D}. The functionality reveals ∅ and D itself.
Operationality: on the 1st query D reveals ∅; on the 2nd — D; on the 3rd, exhaustion (or
D again, depending on the formulation). The description is definite.
Well-foundedness: the chain D ∋ ∅ terminates at the first step. The chain D ∋ D ∋ D ∋
… does not terminate. Since not every chain terminates, D is not well-founded by
Definition IV.2. D belongs to the ZFA-mode but not to the ZFC-mode.
This example shows that well-foundedness demands the termination of all chains, not
the existence of at least one terminating chain. This is the standard formulation, here
verified on concrete operational descriptions.

Example IV.4: an infinitely descending series
Description: a set E0 such that E0 = {E1}, E1 = {E2}, E2 = {E3}, …, and this sequence does
not terminate.
The description of E0 operationally requires the definition of all En — a countable series
of functionalities. This is operationally describable provided there is a uniform
description of the series (for instance, an indexed description of En by n).
Unfolding chain: E0 ∋ E1 ∋ E2 ∋ … does not terminate. E0 is not well-founded; it
belongs to the ZFA-mode but not to the ZFC-mode.
The example shows that non-well-foundedness is not necessarily connected with self-
reference: one can construct a descending series without a cycle. The ZFA-mode
encompasses both kinds of such sets.

Remark: the ZFA-mode as an ontological option
All these sets are legitimate objects of the ZFA-mode. They carry no paradox (the closure
principle has been checked on each description); they create no contradiction with the
other axioms (Part III and Theorem IV.2 were proved without the well-foundedness
condition).
The question of which mathematical applications such sets have is beyond the scope of
this preprint. In the standard literature, AFA is applied to the semantics of circular
phenomena: processes, recursive data structures, situational semantics (Barwise–Moss
1996), the theory of matchings with cyclic references. For VR-Sets it is important to fix:
these applications are ontologically legitimate, and the passage from the ZFC-mode to
the ZFA-mode is not a departure from rigour but an explicit ontological choice.

IV.8. Relation to standard approaches
We briefly fix how the VR-Sets formulation of the two modes relates to standard
approaches in set theory.

Aczel (1988)
Aczel introduced AFA as an anti-axiom: "every pointed graph has a unique realisation as
a set." In VR-Sets this axiom is a theorem of the ZFA-mode (see §IV.6). The difference lies
in the manner of formulation: in Aczel it is a postulate of existence; in VR-Sets a
consequence of the closure principle applied to describable graphs.
Bisimulation in Aczel is the equivalence relation on sets identifying sets with isomorphic
membership graphs. In VR-Sets, the operational identity ≡ (Definition 4 of Part II) is
structurally the same: coincidence of functionalities by elements, recursively up to ≡.
This gives a direct correspondence: ≡ in VR-Sets = bisimulation in Aczel.

Barwise–Moss (1996)
Barwise and Moss in "Vicious Circles" developed in detail the applications of AFA to
situational semantics and the theory of non-correspondence (non-well-founded sets for
modelling self-reference in natural language). VR-Sets is compatible with these
applications: the ZFA-mode gives the same mathematical universe as standard AFA, up to
Conjecture IV.2.
The iterative conception of the set
The standard picture of ZFC rests on the iterative conception: sets are built in stages of
ordinals (V0 = ∅, Vα+1 = ℘(Vα), with union at limit steps). This picture is temporal: a set
exists from the stage at which it first appears.
In VR-Sets there is no such temporality (§IV.1). The ZFC-mode is not "built up in stages"
but is defined by a structural property — well-foundedness. This is not a different theory;
it is a different manner of describing the same (or, in view of §IV.5, the operationally
accessible part of the) universe. The iterative conception and the operational one are two
different methodological optics on a single mathematical structure.

Topoi and categorical set theory
In categorical set theory (Lawvere, ETCS, ETCC) the accent is shifted from "membership"
to "functions." VR-Sets is closer to this tradition than to classical ZF: the membership
functionality is a category of arrows "reveal an element," and ≡ is an isomorphism in
this category. The connection of VR-Sets with topoi is a separate substantive programme,
indicated in Part IX as an open question.

Conclusion
In Part IV the fork between the ZFC-mode and the ZFA-mode has been formalised as two
levels of application of the closure principle. The principal results:
(1) Definitions IV.3 and IV.4 formulate the modes through a structural property of a
functionality (well-foundedness — termination of all successive unfoldings at ∅),
without introducing a temporal order of construction and without a separate layer of
labels.
(2) Theorem IV.1 establishes that the ZFC-mode is a model of classical ZFC: all nine
axioms hold.
(3) Theorem IV.2 establishes an analogous result for the ZFA-mode: all ZFC axioms hold
except foundation, and AFA holds.
(4) Conjectures IV.1 and IV.2 formulate equivalence with the classical theories, with an
analysis of what is required for the converse directions (the working solution:
correspondence via a countable model).
(5) Examples IV.1–IV.4 make concrete the ZFA-mode by means of the Quine atom, cycles,
partially well-founded sets, and infinitely descending series.
Methodological summing-up. The two modes are not two different "kinds" of sets and
not two competing foundations, but two ontological options of a single system. The
closure principle and the definitions of Part II operate in the same way in both modes.
The difference is the explicit choice of which operationalities to admit: only the well-
founded ones (standard mathematics) or all the describable ones (mathematics with self-
references and cycles).
This choice is made once and explicitly, not in each particular construction. After the
mode is chosen, all work proceeds uniformly within it.
What follows. Part V specifies the role of VR numbers in VR-Sets: the von Neumann
ordinals On and ω itself are specific examples of well-founded sets, landing in the ZFC-
mode as a theorem. Arithmetic is inherited via direct isomorphism with VR Part I (no
separate proofs are required). Part V is a short part fixing the correspondence and
establishing that the numbers of VR in VR-Sets are precisely the numbers of classical
arithmetic, presented operationally.

## Part V. VR Numbers in VR-Sets

V.0. Introduction
This part of the preprint establishes the correspondence between the VR numbers — the
von Neumann ordinals On, obtained in the VR system (Reznik, 2026) — and the
operational sets of VR-Sets. The aim is modest: to show that the VR numbers are specific
operational sets; that they fall automatically into the ZFC-mode as a theorem (not as a
restriction); and that the arithmetic developed in VR (Part I §7) is inherited in VR-Sets via
direct isomorphism, without the need for re-proof.
The part is short by design. The substantive work on the axiomatisation of arithmetic has
already been done in VR; the present part only specifies how this arithmetic looks in the
new ontology. No new arithmetic theorems are proved here.
Status reminder. Throughout this part the phrase “belongs to the ZFC-mode” is used in
the strict technical sense established in Part IV: a set is well-founded and operationally
describable. This is Theorem IV.1 territory and does not depend on Conjecture IV.1
(mutual interpretability of the ZFC-mode with a countable model of classical ZFC), which
remains open. Accordingly, when this part says that VR numbers and the apparatus of
VR-Numbers are inherited in VR-Sets without re-proof, the inheritance is from VR and
from VR-Numbers themselves — via the operational isomorphism established below —
not from classical ZFC.

V.1. VR numbers as operational sets
In VR (Part I, Definitions 4–5) the von Neumann ordinals are defined recursively:
O₀ := ∅,    O_{n+1} := t(O_n) = O_n ∪ {O_n}.
Substantively:
O0 = ∅,
O1 = {∅},
O2 = {∅, {∅}},
O3 = {∅, {∅}, {∅, {∅}}},
…
In VR-Sets each of these expressions is interpreted as the description of an operational
functionality. Formally:

Definition V.1 (VR numbers in VR-Sets)
The operational set On is the functionality whose description is as follows: "reveal in
turn O0, O1, …, On−1; on subsequent queries reveal nothing." Recursive base: O0 ≡ ∅
(the empty operationality, revealing nothing).
Commentary. This is precisely what the formula On+1 = On ∪ {On} says: the elements of
On+1 are all elements of On (that is, O0, …, On−1) plus On itself. In the operational
formulation this means that the functionality On+1 reveals O0, …, On−1, On — n+1
elements in all.
The operational depth of On equals n (Lemma 3 of Part II): the unfolding On → On−1 →
On−2 → … → O0 = ∅ terminates in exactly n steps.

V.2. ω as an operational set
The set of natural numbers ω in VR-Sets is the functionality already introduced in Part II
with the description:

Definition V.2 (ω)
ω is the operational set whose functionality, on the n-th query, reveals On. The
functionality does not terminate at any finite step (it is infinite by Definition 3 of Part II)
and is non-cyclic (ω is not among the revealed elements).
The existence of ω was proved in Part III §III.6 as a closure theorem: ω is operationally
describable (on every query the response is defined — a specific On), and by the closure
principle such a functionality is a set.
This accords with the axiom of infinity in its operational reformulation: ω in VR-Sets is
not a "completed totality of all naturals" but an unboundedly applicable operation of
enumerating On. The substantive divergence with classical ZF at this point is
methodological, not mathematical: mathematically ω in VR-Sets is isomorphic to ω in
classical ZF (see §V.4).

V.3. VR numbers in the ZFC-mode: theorem
The principal technical result of this part is that VR numbers fall automatically into the
ZFC-mode of VR-Sets. This is not a restriction imposed on the construction, but a theorem
about a structural property of the numbers.

Theorem V.1
Every VR number — On for arbitrary n ≥ 0, as well as ω itself — is a well-founded
operational set. Accordingly, all VR numbers belong to the ZFC-mode of VR-Sets.

Proof
Part 1: every On is well-founded. Induction on n.
Base (n = 0). O0 = ∅ is well-founded trivially: ∅ has no elements, no unfoldings, and the
termination requirement holds vacuously.
Step (n → n+1). Suppose O0, O1, …, On are all well-founded. We show that On+1 is well-
founded. Any successive unfolding starting with On+1 yields on the first step one of the
elements of On+1, that is, one of O0, …, On. By the inductive hypothesis each of these is
well-founded — and hence the chain of unfolding from that element terminates at ∅ in a
finite number of steps. Consequently every unfolding of On+1 terminates. On+1 is well-
founded.
By induction (axiom A4 from VR, lifted to the level of sets through Lemma 3 of Part II) all
On are well-founded.
Part 2: ω is well-founded. Any successive unfolding starting with ω yields on the first
step some element of ω — namely a specific On with finite n. By Part 1, On is well-
founded; the unfolding chain from On terminates at ∅ in n steps. Consequently the chain
of unfolding of ω terminates in n+1 steps. ω is well-founded.
Conclusion. By Definition IV.3 (Part IV), a set belongs to the ZFC-mode if it is
operationally describable and well-founded. All On and ω are describable (Part III §III.6
for ω; for On — by the construction of Definition V.1) and well-founded (Parts 1 and 2 of
this proof). All VR numbers belong to the ZFC-mode.
∎

Remark: correspondence with VR Part II.5
In VR (Part II §5) it was proved: t(x) ≠ x for every object of the system, and the chains of
membership in the objects of VR are finite. These facts are reformulations of well-
foundedness in the language of VR. Theorem V.1 is the same content, expressed in the
language of VR-Sets:
↔
• t(x) ≠ x in VR   On+1 is not cyclic on itself in VR-Sets (the unfolding of On+1 yields
elements of strictly smaller depth, not On+1 itself).
• Chains of membership in VR are finite   ↔ successive unfoldings in VR-Sets terminate at
∅.
No new proof was carried out; Theorem V.1 is a transcription of what has already been
proved into the new language. This is consistent with the general methodological
position: VR-Sets does not re-prove arithmetic, it interprets it.

V.4. Isomorphism with the natural numbers of VR
The VR numbers in VR-Sets are precisely the VR numbers of the original VR system,
presented operationally. We fix this formally.

Theorem V.2 (isomorphism)
The mapping φ: ℕVR → ℕVR-Sets, sending each VR number On of the original system to
the corresponding operational functionality On in VR-Sets, is an isomorphism of
structures:
(a) bijectivity: to each VR number there corresponds exactly one operational functionality
in VR-Sets, and conversely;
(b) preservation of succession: φ(t(On)) ≡ t(φ(On)) in VR-Sets;
(c) preservation of membership: Om ∈ On in VR ∈
φ(Om) ∈ φ(On) in VR-Sets;
(d) preservation of arithmetic operations: addition, multiplication, and exponentiation
defined in VR Part I §7 agree with the corresponding operations on operational
functionalities in VR-Sets.

Proof
(a) Bijectivity by construction: φ is defined recursively through On in both systems; the
recursion determines the correspondence uniquely.
(b) Preservation of succession. In VR succession is given by axiom A3: t(x) = x ∪ {x}. In
VR-Sets, succession from On is the operational functionality revealing O0, …, On−1, On
(that is, everything that On reveals, plus On itself). This corresponds precisely to the
union of the set of elements of On and {On} — that is, t(On) = On ∪ {On} in VR.
(c) Preservation of membership. In VR, x ∈ y means that x is one of the objects
mentioned in the construction of y by A3. In VR-Sets, x ∈ y means that the functionality y
reveals x as one of its elements. By the construction of Definition V.1 these two relations
coincide.
(d) Preservation of arithmetic operations. Addition, multiplication, and exponentiation in
VR are defined recursively through t (Definitions 7–9 of Part I of VR). These definitions
carry over into VR-Sets literally: they operate through succession and the base O0, and
both constructions are coordinated between the systems by clauses (a), (b). All arithmetic
theorems T1–T4 of VR Part I §7 (commutativity, associativity, distributivity, O1 + O1 = O2)
are inherited in VR-Sets without re-proof.
∎

Corollary V.1
The entire arithmetic developed in VR Part I — a Peano-equivalent theory of natural
numbers with all standard operations and theorems — is available in VR-Sets through
the isomorphism φ without the need for additional work.
Methodological commentary. This result is the consequence of a deliberate
methodological decision: VR-Sets does not replace VR but interprets it. The axiomatic
work justifying arithmetic was carried out in VR once; in VR-Sets, arithmetic appears as
an already-prepared structure, presented operationally. This is consistent with the
general logic of the cycle of works: VR provides the minimal axiomatic; VR-Numbers
extends it to ℤ, ℚ, ℝ, ℂ; VR-Sets places all of this in an ontological context. No part of the
cycle duplicates the work of another.
V.5. Extension to VR-Numbers
We briefly fix that not only the natural numbers, but the whole superstructure of VR-
Numbers (ℤ, ℚ, ℝ, ℂ) is inherited in VR-Sets through the same mechanism.

General principle
In VR-Numbers (Reznik, 2026) the numerical extensions are built as follows:
• ℕ — the von Neumann ordinals On (ontologically — the sole level with sets proper as
objects);
• ℤ, ℚ — operational syntax over ℕ (not pair-objects, but operational procedures with
order built into the description);
• ℝ — algorithms computing real approximations (a countable subfield of the classical ℝ,
isomorphic to the field of computable reals);
• ℂ — a two-axis structure motivated by the duality of axiom A1 (the two implications F →
F and F → ⊤), with algebraic gluing through i² = ⊖1.
All these extensions are ontologically minimal: none of them introduces new
ontological primitives beyond ∅. Integers, rationals, reals, complex numbers are
operational procedures of varying complexity over natural numbers, which are
themselves operational sets.

Transition into VR-Sets
Since all extensions of VR-Numbers ontologically reduce to operational procedures over
natural numbers, and since natural numbers are represented in VR-Sets through the
isomorphism φ (Theorem V.2), the whole apparatus of VR-Numbers transfers into VR-
Sets automatically:
• ℤ, ℚ in VR-Sets are operational sets whose descriptions use elements of ℕVR-Sets as
basic building material. All operational procedures of VR-Numbers (addition of integers
via signed descriptions, rationals as numerator/denominator pairs given operationally,
and so on) are applicable directly.
• ℝVR-Sets is a countable subset of the ZFC-mode containing operational sets
representing computable algorithms. Each such set is well-founded (the elements of
algorithms — rational approximations — are well-founded; the description of an
algorithm is finite, not cycled on itself).
• ℂVR-Sets is the two-axis structure over ℝVR-Sets, preserving the algebraic relation i² =
⊖1.
No new theorems are proved here. The aim of this section is to fix that the transition VR-
Numbers → VR-Sets is as seamless as the transition VR → VR-Sets. A detailed operational
description of each extension is given in VR-Numbers; here we only assert
transferability.
V.6. Under the standard coding, VR numbers do not use the ZFA-mode
One structural fact deserves explicit mention: under the standard von Neumann coding
of numbers used in this preprint, the VR numbers fall entirely within the ZFC-mode. The
ZFA-mode — self-references, cycles, non-well-founded sets — is neither needed nor used
for arithmetic in this coding. Alternative non-von-Neumann codings (including
coinductive constructions in the ZFA-mode) are possible in principle and are noted as an
open direction in Part IX, Extension 4; this assertion concerns only the standard coding.

Assertion V.1
No VR number — neither natural (On or ω), nor integer, nor rational, nor real, nor
complex — is, under the standard coding used in this preprint, a cyclic or non-well-
founded set.
Justification. For natural numbers and ω this is Theorem V.1. For ℤ, ℚ, ℝ, ℂ: the
operational procedures defining these numbers in VR-Numbers operate through finite
syntactic records over already-constructed natural numbers; none of these records
refers to itself; consequently the describable functionalities are well-founded.
Methodological significance. This is consistent with the general programme of VR:
classical mathematics — arithmetic, analysis, algebra — lives entirely in the ZFC-mode of
VR-Sets. The ZFA-mode (the theory of non-correspondence, circular structures,
situational semantics) is a separate area of application that does not intersect with
numbers. The distinction between modes in VR-Sets is therefore not "different
mathematics" but "different applications of a single ontology": classical mathematics of
numbers uses the ZFC-mode as a theorem about a structural property of its objects;
mathematics of self-referential structures uses the ZFA-mode as an explicit ontological
choice.

V.7. Summary and transition to Part VI
This part has established the following:
(1) VR numbers are specific operational sets of VR-Sets. Each On is a functionality
with operational depth n; ω is a functionality with non-finite but non-cyclic depth
(Definitions V.1 and V.2).
(2) VR numbers automatically belong to the ZFC-mode (Theorem V.1). This is not a
restriction but a theorem about a structural property — the analogue of what in VR Part
II.5 was expressed as t(x) ≠ x and the finiteness of chains of membership.
(3) Isomorphism with VR (Theorem V.2): the VR numbers in VR-Sets are precisely the VR
numbers of the original system, presented operationally. The whole arithmetic
developed in VR is inherited without re-proof (Corollary V.1).
(4) VR-Numbers transfers analogously: ℤ, ℚ, ℝ, ℂ are operational procedures over
natural numbers, all well-founded, all in the ZFC-mode (§V.5).
(5) Numbers do not use the ZFA-mode: the whole classical mathematics of numbers
lives in the ZFC-mode (§V.6).
What follows. Part VI unfolds the central divergence of VR-Sets with classical ZFC — the
countability of the operational universe. Already in the present part it is visible that VR
numbers live on a countable structure: ℕVR-Sets is countable, ℝVR-Sets is countable
(isomorphic to the field of computable reals). Part VI establishes the countability of the
entire operational universe in full detail, analyses Cantor's diagonal argument in the
operational ontology, proves AC as a theorem on the countable universe, and fixes the
absence of the Banach–Tarski paradox by construction.

## Part VI. Cardinality, Cantor, Choice

VI.0. Introduction
This part of the preprint is devoted to the most visible divergence of VR-Sets from
classical ZFC: the entire operational universe of VR-Sets is countable. In classical ZF,
already ℘(ω) is uncountable by Cantor's diagonal argument, and the universe V is a
proper class of uncountable cardinality. In VR-Sets, ℘(ω) is countable (Part III §III.5), and
this countability extends to the entire universe.
The divergence is not mathematical (the mathematics of countable and uncountable
collections is identical in both systems under suitable formulation) but ontological:
classical ZF admits the existence of objects without an operational description; VR-Sets
admits only describable objects, and describable functionalities are countable in
number.
In this part we:
(1) precisely formulate and prove the theorem on the countability of the operational
universe (§VI.1);
(2) develop the analysis of Cantor's diagonal argument in the operational ontology —
where it fails and why (§VI.2);
(3) discuss the distinction between "countable from without" and "not enumerable from
within" by analogy with computable analysis (§VI.3);
(4) prove AC as a theorem on the countable universe (§VI.4);
(5) fix the absence of the Banach–Tarski paradox in VR-Sets as a consequence of the
absence of non-measurable sets (§VI.5);
(6) discuss the methodological significance of a countable ontology — its relation to
classical mathematics, constructivism, and computable analysis (§VI.6).

VI.1. Countability of the operational universe
Theorem VI.1
The collection of all operational sets of VR-Sets is countable.

Proof
Every operational set in VR-Sets is given by its description — a finite syntactic record of
an operational procedure. Descriptions are written in a formal language: a fixed finite
alphabet of symbols (the primitives ∅, →, t from VR, together with auxiliary symbols —
brackets, commas, symbols for naming and referencing). A description is a finite string
over this alphabet.
The set of all finite strings over a finite alphabet is countable: this is a basic fact of the
theory of formal languages. Indeed, for each length n there are finitely many strings (|Σ|
n, where |Σ| is the size of the alphabet), and a countable union of finite sets is countable.
Every operational set has a description (by the closure principle — Part II §II.3 — sets are
precisely the describable functionalities). Consequently, the mapping "set → its
description" is an injection from the collection of sets into the set of finite strings. The
image of this injection is a subset of a countable set, hence itself countable.
The collection of operational sets of VR-Sets is countable.
∎

Remarks on the theorem
(1) The description is not unique. The same set may be given by different descriptions.
For instance, ∅ may be described as "the empty operationality," as "the set revealing
nothing," as O0, and so on. This means that the mapping "set → description" is many-to-
one, but the injection in the other direction — "description → the set it specifies" — is
well-defined (up to ≡). The collection of sets is the image of a countable collection of
descriptions modulo extensionality ≡, and the image of a countable set is countable.
(2) Descriptions are countable even for infinite sets. ω is infinite in operational depth,
but the description of ω is finite: "the n-th query yields On." ℝVR-Sets contains infinitely
many reals, but each of them is given by a finite algorithm. The finiteness of the
description is not in contradiction with the infinity of what it describes; the description is
a syntactic record of a rule, and a rule can generate infinitely many consequences.
(3) Comparison with classical ZF. In classical ZF, the sentences of the language are also
countably many (Löwenheim–Skolem), but the objects in the standard model are
uncountable — because the classical theory admits the existence of objects not specified
by any sentence. VR-Sets has no such gap between sentences and objects: each object is a
describable functionality, and this relation is constitutive, not a property that objects
may or may not have.

VI.2. Cantor's diagonal argument in the operational ontology
The most famous proof of uncountability is Cantor's diagonal argument for ℘(ω) and for
ℝ. In classical ZF, it constructs from any proposed enumeration of subsets of ω a new
subset distinct from all those enumerated, and concludes that no such enumeration is
complete.
In VR-Sets ℘(ω) is countable (Part III §III.5). This means that the diagonal argument in
the operational ontology does not produce a new set. We analyse precisely where it
ceases to operate.
The classical argument
Suppose we have an enumeration S0, S1, S2, … of all subsets of ω. Define:
D = { n ∈ ω : n ∉ Sₙ }.
The set D differs from each Sn at the element n: D contains n if and only if Sn does not
contain n. Hence D ≠ Sn for every n. D is a new subset of ω not appearing in the
enumeration, contradicting the completeness of the enumeration. Cantor's conclusion:
no complete enumeration exists, ℘(ω) is uncountable.

What the classical argument presupposes
The argument uses two premises:
(a) Completeness of the enumeration: S0, S1, … covers all subsets of ω.
(b) D is a well-defined set: the condition "n ∉ Sn" specifies a subset of ω.
In classical ZF both premises are accepted without reservation. In the operational
ontology each of them requires verification.

Where the argument fails in VR-Sets
The obstacle is in premise (a), and it is deep.
A complete enumeration of describable subsets of ω is operationally unrealisable.
Every subset of ω in VR-Sets is an operationally describable functionality. The collection
of such functionalities is countable (Theorem VI.1). However, enumerating them in an
operationally describable sequence S0, S1, … is a different task. A description of such an
enumeration requires that for every n there exist an operational procedure returning
the n-th subset on the list. This procedure must:
(i) enumerate all finite descriptions over the alphabet of operational procedures — this is
describable;
(ii) verify that each description specifies a correct functionality — that is, terminates
on every query, gives a definite response, is not self-contradictory. This is an
undecidable task: the question of whether an arbitrary description is correct is
equivalent to the halting problem.
Consequently, an operationally describable enumeration of all describable subsets of ω
does not exist. Premise (a) of the diagonal argument is unrealisable in the operational
ontology.

What this implies for D
The definition D = { n ∈ ω : n ∉ Sn } requires access to Sn for each n — that is, it requires
an operational enumeration. If no such enumeration exists, the description of D does not
specify an operational functionality: on the query "is n ∈ D?" the procedure would have
to refer to Sn, which is undefined by the operational enumeration.
By the closure principle (Part II §II.3), a description that does not specify an operationally
describable functionality does not give rise to a set. D is not a set in VR-Sets. The
diagonal argument in the operational ontology is not a proof of uncountability but a
demonstration that the attempt to construct a complete enumeration encounters the
halting problem.

Relation to the classical result
Cantor's classical result remains true: in classical ZF, ℘(ω) is uncountable. VR-Sets does
not refute Cantor — it works on a different ontological basis. The difference may be
formulated thus:
• In classical ZF, the existence of subsets of ω not specified by any description is
admitted. Such subsets "are" in the sense of classical ontology and form an additional
uncountability beyond the describable.
• In VR-Sets, there are no indescribable subsets: a set is a description, full stop. Cantor's
uncountability is an artefact of admitting indescribable objects; in the operational
ontology that admission is not made, and uncountability does not arise.
This is consistent with the known observation of Skolem (the Skolem paradox): every set
theory in a countable language has a countable model, and "uncountability" within such
a model is a relative notion. VR-Sets is not simply a countable model of ZFC (Part IV
§IV.5), but an ontologically coherent alternative in which the countability of the
operational universe is the natural state, not paradoxical.

VI.3. Countable from without vs. not enumerable from within
A subtle distinction important for the understanding of the status of countability in VR-
Sets. It is well known in computability theory and computable analysis; VR-Sets shares
this distinction and relies on it.

Setting
A collection X is called countable from without if it is countable as an object of classical
set theory — that is, there exists a bijection between X and ℕ in classical ZF.
A collection X is called enumerable from within (recursively enumerable) if there exists
an operational procedure that, as its n-th output, returns the n-th element of X.
These two notions do not coincide. There exist countable collections that are not
recursively enumerable. A classical example from computability theory is the set of
indices of terminating programs: it is countable (a subset of ℕ) but not recursively
enumerable (by Rice's theorem).

Application to VR-Sets
The collection of all describable subsets of ω in VR-Sets:
• Countable from without (Theorem VI.1): descriptions are countable, sets are
countable.
• Not enumerable from within: there is no operational procedure that, for every n,
returns the n-th describable subset of ω.
This distinction dissolves the apparent tension: "if ℘(ω) is countable, why cannot one
exhibit an enumeration?" The answer: countability does not imply enumerability. The
set exists as a countable object; but a procedure that would list its elements does not
exist.

Analogy with computable reals
The same situation is well known in computable analysis for the field of computable
reals:
• The field of computable reals is countable (a subfield of the classical ℝ, consisting of
numbers with an operational description).
• However it is not enumerable: the halting problem prevents the separation of
terminating algorithms for computing reals from non-terminating ones.
ℝVR-Sets stands in the same position: a countable subfield of the classical ℝ, isomorphic
to the field of computable reals, not enumerable from within. This is consistent with the
position of VR-Numbers and confirms that VR-Sets and computable analysis work on the
same ontology — the one in which "operational" means "algorithmically specifiable."

Where this is especially important
The distinction "from without vs. from within" dissolves several apparent problems:
(a) Cantor's diagonal requires enumerability from within; countability from without is
insufficient. Since ℘(ω) in VR-Sets is countable from without but not enumerable from
within, the diagonal does not construct D.
(b) Full AC on the entire universe does not reduce to simple "choose one element from
each set of a countable family" — an operational procedure of choice is required, and for
an arbitrary family it may not be describable. See §VI.4 for details.
(c) The Löwenheim–Skolem theorem predicts the existence of countable models of ZFC
from without; in VR-Sets such a model is countable also from within (though not its
entire structure is enumerable from within). This is consistent with Conjecture IV.1.

VI.4. The axiom of choice as a theorem
Part III §III.9 has already established: countable AC is a theorem of VR-Sets, and full AC
on the countable universe is equivalent to the countable one. Here we develop this
result, examine the connection with DC (dependent choice), and fix what distinguishes
the VR-Sets position from the standard treatment of choice in ZFC.
Three levels of choice
In classical set theory three forms of the axiom of choice are distinguished:
• Countable Choice (CC): for a countable family of non-empty sets there exists a choice
function. Equivalent to countable AC, without which many basic facts of analysis cannot
be proved (for instance, that a countable union of countable sets is countable).
• Dependent Choice (DC): for every binary relation R on a non-empty set A such that for
every x ∈ A there exists y with xRy, there exists a sequence x0, x1, x2, … with xn R xn+1
for all n. Stronger than CC.
• Full AC: for an arbitrary family of non-empty sets there exists a choice function.
Stronger than DC; the source of the Banach–Tarski paradox.

Status of each level in VR-Sets
DC is built into the operational ontology. Every operational procedure consists of
specific steps: at each step the procedure makes a definite choice, and subsequent steps
depend on those already made. This is precisely the structure of DC. In the operational
ontology, DC is not an axiom but a property of operational action itself: it is impossible to
conceive of an operational procedure that does not make dependent choices.
Technically: for a binary relation R given by a describable procedure, a sequence x0, x1,
x2, … is constructed operationally — choosing at each step the first element satisfying R
with the preceding one. "First" here refers to the order of enumeration given by the
description of R. This sequence is itself operationally describable and, by the closure
principle, is a set.
Countable AC is a theorem (§III.9). The proof in §III.9 showed: for a countable family of
non-empty sets, the choice function is operationally describable (on the i-th query, reveal
the first element of Ai). By the closure principle, this is a set.
Full AC is a theorem on the countable universe. Since the entire universe of VR-Sets is
countable (Theorem VI.1), every "family of non-empty sets" is a countable family. Hence
full AC reduces to countable AC, which is a theorem.

Theorem VI.2 (AC in VR-Sets)
In VR-Sets the axiom of choice in its full form is a theorem: for every family of non-empty
sets there exists an operational choice function.
Proof. The collection of sets in VR-Sets is countable (Theorem VI.1). A family of non-
empty sets is an operational set whose functionality reveals the elements of the family.
By countability the whole family has a description of the form A0, A1, A2, … (a countable
enumeration). The choice function: choice(i) = the first element of Ai — is a describable
procedure. By the closure principle, choice is a set.
∎
Subtlety: the operationality of choice
The formulation "the choice function choice" in this proof depends on the order of
presentation of the elements of Ai and Ai+1: "the first element of Ai" is the element
revealed by the functionality Ai on its first query. Different presentations may give
different "first elements," and then choice is a different functionality (formally — several
different sets choice).
There is nothing paradoxical here: the operational theorem says that some choice
function exists, not that it is unique. This is consistent with the classical situation: AC in
ZFC asserts the existence of a choice function, not its uniqueness.

Where VR-Sets differs from ZFC on AC
Substantive difference. In classical ZFC, full AC is an independent axiom. From ZF
without AC one can build models in which AC is false, and these models are
mathematically substantive (for instance, models with the axiom of determinacy AD). In
VR-Sets there is no such gap: AC holds automatically by virtue of the countability of the
universe. To reject AC in VR-Sets would mean to reject countability, and countability is a
consequence of operationality, not a separate postulate.
Methodological difference. In ZFC, AC is often regarded as "suspect" because of its non-
constructive consequences such as Banach–Tarski. In VR-Sets, AC is harmless, because
the objects on which ZFC builds paradoxical consequences (non-measurable subsets of ℝ,
ultrafilters on ℕ) do not exist in the operational ontology. See §VI.5.

VI.5. Absence of the Banach–Tarski paradox
The most famous "pathological" consequence of AC is the Banach–Tarski theorem: the
unit ball in ℝ³ can be partitioned into a finite number of pieces, and from these pieces
two unit balls can be assembled. The proof makes essential use of full AC to construct
non-measurable subsets of the sphere.
In VR-Sets the Banach–Tarski paradox is absent. We fix precisely why — because this is
the most graphic point where the operational ontology departs from the classical one not
only formally but substantively.

Where Banach–Tarski requires AC
The Banach–Tarski proof consists of several steps; the key one uses AC to construct a
non-measurable Vitali subset of the sphere. A Vitali set is a set of representatives of
equivalence classes on the sphere under an appropriate relation. The existence of such a
set requires the selection of one representative from an uncountable family of classes —
which is an application of full AC for uncountable cardinality.
Once the non-measurable set has been constructed, the rest of the proof combines the
free group of rotations of ℝ³ with this set, obtaining a partition of the ball into a finite
number of pieces and a reconstruction of two balls.

Why this does not happen in VR-Sets
Each of the steps relies on classical objects absent in VR-Sets:
(1) Uncountable family of equivalence classes on the sphere. In classical ZFC, the
sphere S² is uncountable (as a subset of ℝ³, classically uncountable), and a factor under a
suitable relation gives an uncountable family. In VR-Sets there is no classically-
uncountable sphere: S²VR-Sets is a countable set of describable points, and any factor
remains countable. No uncountable family of equivalence classes arises.
(2) Non-measurable Vitali set. The Vitali construction requires the selection of one
representative from an uncountable family of classes. In VR-Sets there are no such
families; countable AC gives a choice function without any non-measurability.
(3) Classical ℝ³. The geometric arguments of Banach–Tarski operate on classical ℝ³ — an
uncountable space with the full apparatus of Lebesgue measure and non-measurable
sets. ℝVR-Sets is isomorphic to the field of computable reals and countable; ℝ³VR-Sets is
also countable. On a countable set, measure behaves standardly (countably additive),
and non-measurable subsets do not arise.

Assertion VI.1
The Banach–Tarski paradox is not reproduced in VR-Sets. This follows not from a
weakening of AC (AC in VR-Sets is a theorem) but from the absence of classically-
uncountable objects on which the paradox is built.

Methodological commentary
The Banach–Tarski paradox is often regarded as "evidence of the pathology" of full AC in
classical mathematics. The standard response is that this is the price of working with the
uncountable continuum and its subsets without operational restrictions.
VR-Sets gives a different response: the paradox arises not from AC, but from the attempt
to combine AC with the admission of classically-uncountable objects lacking an
operational description. If the ontology is restricted to operational objects, AC is a
harmless theorem, and there are no paradoxes. The difference is not in the mathematical
apparatus, but in the ontological commitments.
This is consistent with the position of Solovay, Shelah, and others in work on models of
ZF + DC: in such models AD is compatible with DC, there are no non-measurable sets, and
analysis works without paradoxes. VR-Sets is the operational reformulation of this
mathematical line: what is achieved in Solovay's models by restricting the universe (only
definable sets) is, in VR-Sets, the natural state of the ontology.
VI.6. Methodological significance of a countable ontology
Closing the part, we discuss how the countability of the operational universe relates to
classical mathematics and other alternative approaches. This is a methodological section
and contains no new theorems.

What VR-Sets loses
Direct losses in comparison with classical ZFC:
• Uncountable cardinalities: ℵ1, ℵ2, … and the whole theory of uncountable ordinals are
absent in VR-Sets as separate ontological levels. Cardinality in VR-Sets takes only two
values: "finite" and "countable."
• The continuum hypothesis: the question "is the cardinality of ℝ greater than the
cardinality of ℕ?" does not arise in VR-Sets, because both cardinalities are countable.
• Uncountable classical objects: the set of all functions ℕ → ℕ, the set of all subsets of ℝ,
equivalence classes with an uncountable number of representatives — all such objects in
their classical form are absent. Their operational analogues — describable functions,
describable subsets — exist and are countable.

What VR-Sets retains
Direct retentions:
• All of arithmetic and number theory (Part V).
• All of computable mathematics: algorithms, recursive functions, formal languages,
computability theory — all of this works with operational objects by construction.
• Analysis on computable reals: ℝVR-Sets supports integration, differentiation, power
series — everything that does not require the existence of non-measurable sets or
uncountable cardinalities.
• Constructive and reverse mathematics: systems such as RCA0, WKL0, ACA0 — all
formalisable in the countable ontology of VR-Sets.
• Algebra and combinatorics on countable structures: the theory of groups, rings,
fields, graphs — all of this for countable carriers works without modification.

Relation to other approaches
VR-Sets shares its ontological position with several well-known approaches in the
foundations of mathematics:
• Computable analysis (Weihrauch, Pour-El–Richards): mathematics on computable
objects, including computable reals. The operational universe of VR-Sets is isomorphic to
the basic structure of computable analysis.
• Constructivism (Brouwer, Bishop): mathematics on constructively given objects. VR-
Sets is close to this position ontologically, but not necessarily methodologically (for
instance, classical logic in VR-Sets operates without restrictions on the law of excluded
middle).
• Predicativism (Poincaré, Weyl, Feferman): mathematics on predicatively definable
objects. VR-Sets is ontologically still more restrictive (only operationally describable
objects), but substantively close.
• Solovay, ZF + DC + AD: models of ZF with dependent choice and the axiom of
determinacy, without full AC and without non-measurable sets. VR-Sets gives an
operational ontological formulation of this mathematical position.
The differences of VR-Sets from each of these approaches lie in the manner of
formulation. All the listed approaches construct countable or near-countable
mathematics by restricting the classical universe. VR-Sets constructs it by ontological
choice: countability is a consequence of the operational ontology, not a restriction
imposed on the classical one.

Concluding commentary
The countability of the operational universe of VR-Sets is not a defect relative to classical
mathematics but an ontological position consistent with the slogan "only ∅ is, all else is
doing." All objects of VR-Sets are actions, and operationally describable actions are
countable in number. Classical mathematics not fitting this picture (uncountable
cardinalities, non-measurable sets, paradoxes of choice) works on a different ontology —
the one in which the existence of objects without an operational description is admitted.
Which of the two ontologies is "correct" is not a mathematical question. Both ontologies
are internally non-contradictory; both are fruitful. VR-Sets is the explicit fixing of the
operational ontology, with all its consequences. Part VII will discuss how this position
interacts with self-referential statements and Tarski's theorem on the undefinability of
truth.

VI.7. Summary
In this part we have established:
(1) Theorem VI.1: the collection of all operational sets of VR-Sets is countable. Proof —
through an injection into the set of finite descriptions over a finite alphabet.
(2) Cantor's diagonal argument does not operate in VR-Sets (§VI.2): its premise of a
complete enumeration of describable subsets is operationally unrealisable (equivalent to
the halting problem), and so the diagonal D is not a set.
(3) Countable from without ≠ enumerable from within (§VI.3): ℘(ω) in VR-Sets is
countable as an object but not enumerable by procedure. Analogy with computable
reals.
(4) Theorem VI.2 (§VI.4): full AC in VR-Sets is a theorem, a consequence of the
countability of the universe. DC is built into operationality; countable AC was already
proved in Part III §III.9.
(5) Assertion VI.1 (§VI.5): the Banach–Tarski paradox is absent in VR-Sets, not because of
a weakening of AC but because of the absence of classically-uncountable objects on
which the paradox is built.
(6) Relation to other approaches (§VI.6): VR-Sets is ontologically close to computable
analysis, constructivism, predicativism, and models of ZF + DC + AD; it differs in the
manner of formulation — by ontological choice, not by restriction of the classical
universe.
What follows. Part VII treats Tarski's theorem on the undefinability of truth in the light
of the operational ontology and connects it with the duality of axiom A1 from VR. This is
the most philosophically loaded part of the preprint; the formulation is cautious — it
reformulates, it does not resolve.

## Part VII. Truth and Self-Reference

VII.0. Introduction
This part of the preprint considers Tarski's theorem on the undefinability of truth in the
light of the operational ontology of VR-Sets. The aim is not to "resolve" or "circumvent"
Tarski (this would be impossible: his theorem is a formal result, true in any sufficiently
rich formal system) but to examine how the operational ontology reformulates the same
situation and what subtleties this clarifies.
The part has two substantive directions:
(1) Analysis of the liar paradox from the standpoint of the closure principle:
paradoxical self-referential statements do not specify definite operational predicates, in
analogy with Russell's paradox not specifying a set (Part II §II.3).
(2) A hierarchy of levels of truth through t: the idea that applications of the successor
operator t from VR can be interpreted as a passage to a new level of truth at which the
truth of the previous level may be discussed. This accords with Tarski's approach to a
hierarchy of metalanguages.
The formulation is cautious: VR-Sets reformulates the situation, it does not overturn
Tarski's theorem. No claim of resolving classical paradoxes in the sense of "they are now
gone" is being made.

VII.1. Tarski's theorem on the undefinability of truth
A brief reminder of the classical result.

Statement
Tarski's theorem (1933) asserts: for every sufficiently rich formal system T (containing
arithmetic) the predicate "is true in T" is not expressible inside T. More precisely: there is
no formula Tr(x) in the language of T such that for every sentence φ of the language of T:
T⊢
Tr(⌜ φ⌝ )   ↔φ
where ⌜φ⌝ is the encoding (Gödel number) of the sentence φ. If such a predicate were
expressible, one could construct a sentence L asserting "L is false," yielding the classical
liar paradox.

Significance of the result
Tarski showed that truth for the language T must be formulated in a metalanguage — an
extension of T containing expressive means absent in T itself. This gave rise to a
hierarchy of languages: object language, metalanguage, meta-metalanguage, … each with
its own level of truth.
The result is universal: it applies to any formal system capable of encoding its own
syntax. ZF, ZFC, PA, VR — all these systems are subject to Tarski's theorem. VR-Sets too.

VII.2. The liar paradox through the closure principle
Before discussing the hierarchy of truth, we trace how the liar paradox appears in the
operational ontology. This is an exercise parallel to the dissolution of Russell's paradox in
Part II §II.3.

The classical liar paradox
The sentence L = "L is false" generates a contradiction: if L is true, then L is false (by the
content of L); if L is false, then L is true (since this is what it asserts). Neither truth value
is consistent with L itself.

Analogy with Russell's paradox
Russell's paradox in VR-Sets is dissolved by the fact that the description R = "reveal x ⟺
x ∉ x" demands a contradictory response to the query "R ∈ R?" and thus does not specify
an operational functionality. R does not exist as a set — not forbidden, but ontologically
impossible.
The liar paradox has the same structure. The description of the predicate "is true"
applied to L demands a contradictory response: on the query "is L true?" the procedure
must return truth if and only if L is false — that is, when the procedure must return
falsity. Contradictory responses. The description does not specify an operationally
describable truth predicate for L.

Assertion VII.1
The paradoxical self-referential sentence L = "L is false" does not specify an operationally
defined truth value. In the operational ontology L has no truth value — not because L is
"neutral" or "unknowable," but because the description of truth for L is internally
contradictory.

Relation to Tarski
This does not contradict Tarski's theorem. Tarski speaks of the inexpressibility of the
truth predicate for the entire language inside the language itself. Assertion VII.1 speaks of
the inexpressibility of truth for a specific paradoxical sentence — a particular case. VR-
Sets gives an ontological interpretation: the truth predicate does not exist as an
operationally describable functionality, and paradoxical sentences are the clearest
witnesses to this.
For non-paradoxical sentences the truth predicate exists locally: for each specific non-
self-referential φ it is operationally definable whether φ is true in a given model (for
instance, by verification of the formula). What is inexpressible is the single truth
predicate for the entire language — because the attempt to specify it runs into
paradoxical sentences.

VII.3. A hierarchy of levels of truth through the successor operator t
Tarski proposed a resolution of the truth problem through a hierarchy of languages:
language L0, metalanguage L1 (containing a truth predicate for L0), meta-metalanguage
L2 (containing a truth predicate for L1), and so on. Each Ln+1 is an extension of Ln in
which truth for Ln is expressible, but not for Ln+1 itself.
In VR-Sets this hierarchy has a natural operational realisation through the successor
operator t from VR.
A note on what t means here. The operator t is the same operation as in VR axiom A3
and as used in Part V to construct the von Neumann ordinals: t(x) = x ∪ {x}. There is no
second “t”. What differs in §VII.3 is only the domain to which the operator is applied: in
VR and Part V the input is ∅ and its successors On, generating numbers; here the input is
an operational set representing an object language, generating a metalanguage. The
arithmetical and the metalinguistic readings of t are two applications of the same
operation to different starting objects, not two homonymous operators.

The idea
The application of t to a set A produces a new set t(A) = A ∪ {A}, in which A appears as
one of the elements. Substantively: t passes from A to the level at which A may be
discussed as an object. At this new level one may formulate statements about properties
of A which are inexpressible at the level of A itself.
As applied to a language: let Ln be represented by the operational set of words
(sentences) of length ≤ n or complexity ≤ n. Then t(Ln) = Ln ∪ {Ln} is a set containing Ln
as an object. At the level of t(Ln) one may speak about Ln as a whole, in particular
formulate a truth predicate for the sentences of Ln.

Correspondence with Tarski
Tarski: L0 is the object language; L1 is the metalanguage expressing truth for L0; and so
on.
VR-Sets: L0 is an operational set of the object language; t(L0) is the next level containing
L0 as an object; t²(L0) is another level; and so on. The sequence of t-applications is the
operational realisation of the hierarchy of metalanguages.
This is not a proof and not a new theorem. It is the indication of a structural
correspondence: t in VR (succession as the passage to a new object containing the
previous one as an element) corresponds structurally to the passage from a language to a
metalanguage in Tarski (the metalanguage contains the object language as an object of
study).
Where the correspondence is exact
Several places where the parallel operates:
(1) The new level contains the old: t(A) ⊃ A in VR; the metalanguage contains the object
language as a fragment.
(2) At the new level, properties of the old are expressible: t(A) contains A as an
element, so one may formulate predicates of the form "A has property P"; in the
metalanguage, truth for the object language is expressible.
(3) The hierarchy is unbounded: t may be applied any number of times, yielding On
with arbitrarily large n; Tarski's hierarchy of metalanguages is likewise infinite.
(4) Each level has its own truth predicate: at the level tn(L0) truth for L0 is expressible,
but not truth for tn(L0) itself. Parallel with Tarski: each Ln+1 expresses truth for Ln, but
not for itself.

Where the correspondence is inexact
The parallel is structural, not literal. There are essential differences:
• Tarski's hierarchy is a hierarchy of languages including syntax and semantics. The
hierarchy of t is a hierarchy of sets, not carrying any independent semantic load until
interpreted.
• For Tarski, each Ln+1 contains a formal truth predicate Trn for Ln. In VR-Sets the
operation t merely passes to a wrapping set; the formal expression of the truth predicate
is a separate construction that must be built at each level.
• The infinity of the t-hierarchy in VR is operational infinity (Part I §I.3). For Tarski it is
ordinary infinity of ordinals; there are variants with transfinite levels. VR-Sets is
restricted to ω-levels of t (by the countability of the universe — Part VI), which is weaker
than the classical transfinite hierarchy.

Assertion VII.2 (cautious formulation)
The hierarchy of applications of the successor operator t from VR provides an
operational realisation of the idea of Tarski's hierarchy of metalanguages, restricted to ω-
levels. This is not a "resolution" of the problem of the definability of truth but an
ontological interpretation of Tarski's existing resolution within a more minimalist frame.

VII.4. The duality of A1 and self-reference
In the VR system (Part I, axiom A1) the duality of implication is fixed: from F both values
{F, ⊤} are reachable through →; from ⊤ — only ⊤. This asymmetry is the structural
characteristic of two-valued classical logic, expressed through the primacy of F.
In VR-Numbers (Part V) the same duality motivates the two-axis structure of ℂ: the F → F
axis (real) and the F → ⊤ axis (imaginary). In VR-Sets the duality of A1 provides the basis
for one additional observation on self-reference.

Observation
The self-referential sentence L = "L is false" contains a one-sided dependence: the value of
L is determined through the value of L. If one tries to represent L as an operational
procedure, this procedure must first compute L in order to determine L. Circularity.
The duality of A1 gives two directions: F → F (trivial self-identity) and F → ⊤ (passage to
⊤). In the case of the self-referentiality of L, circularity stalls at F → F: the procedure
refers to itself without passing to a new value.
This is not a proof; it is a speculative comment. A substantive connection between the
duality of A1 and the paradoxes of self-reference is an open direction noted in Part IX as
one of the promising questions for further work.

Alpha/Omega/Logos (digression)
In the working notes of the VR cycle (not included in the formal part of the preprints) a
triadic personal apparatus has been explored — Alpha (inner core), Omega (reflexive
observer), Logos (medium of thought). This scheme corresponds structurally to the
logical triad: F (Alpha, the initial state), ⊤ (Omega, the result), → (Logos, the passage).
In the context of Part VII one may note: Tarski's hierarchy of truth is a hierarchy of
Omega: each level of the metalanguage is the reflexive observer of the previous level.
This accords with the fact that the very notion "truth for language L" is already an
observation of language L from without.
This digression is not part of the formal apparatus of VR-Sets and has no theorem status.
It records that the philosophical background of the VR programme naturally accords
with Tarski's approach to self-reference through a hierarchy.

VII.5. Summary and transition to Part VIII
In this part:
(1) Tarski's theorem on the undefinability of truth has been recalled (§VII.1).
(2) It has been established (Assertion VII.1, §VII.2) that paradoxical self-referential
sentences in the operational ontology have no truth value, for the same reason that
Russell's paradox does not specify a set: the description of truth is contradictory.
(3) A parallel has been proposed between Tarski's hierarchy of metalanguages and the
hierarchy of applications of the successor operator t from VR (Assertion VII.2, §VII.3). The
parallel is structural, not literal; bounded to ω-levels by countability.
(4) A speculative comment on the connection of A1-duality and the paradoxes of self-
reference has been fixed (§VII.4); substantive development is an open direction.
The part formulates a cautious position: VR-Sets does not overturn Tarski's theorem and
does not resolve the paradoxes of self-reference; it gives an ontological interpretation of
the existing picture within an operational frame. This is interpretation, not alternative.
What follows. Part VIII gives the final substantive discussion of the ontological position
of VR-Sets. The slogan "only ∅ is, all else is doing," already used repeatedly, is unfolded
into a detailed grounding of the ontological commitments. A parallel to VR-Numbers Part
VI, with the accent on the specifics of a set-theoretic ontology. Briefly, also — the relation
to other positions in the foundations of mathematics (Platonism, formalism,
constructivism).

## Part VIII. Ontological Position

VIII.0. Introduction
This part of the preprint develops in detail the ontological position of VR-Sets. The
substantive commitments accumulated through Parts I–VII are gathered into a single
picture and grounded as a coherent whole. The relation to other well-known positions in
the foundations of mathematics — Platonism, formalism, constructivism, structuralism
— is also discussed.
Part VIII is the parallel of Part VI of the VR-Numbers preprint (Reznik, 2026), where
analogous work was carried out for the ontology of numbers. The emphasis here is
transferred to the specifics of a set-theoretic ontology: what changes when "only ∅ is, all
else is doing" is applied to sets.
The part contains no formal theorems. It is a substantive and philosophical exposition of
the position for which all the remaining work was undertaken.

VIII.1. "Only ∅ is, all else is doing"
The slogan running through all three works of the cycle has three levels of meaning, each
of which operates in the application to VR-Sets:

Level 1: ∅ is the sole primitive
In the ontology of VR-Sets there is only one primary entity — ∅, the empty
operationality. All other "things" are actions. This is an ontological decision, not the
consequence of any theorem. It is motivated by minimalism: the fewer primitives, the
simpler the ontology and the smaller the arbitrary commitments.
The choice of ∅ specifically as the primitive is likewise motivated. ∅ is the only entity
that can be characterised purely negatively (reveals nothing), without requiring a prior
content. Any other primitive object would require some "matter," some initial content
whose origin would have to be explained. ∅ is free of this problem by construction.

Level 2: operationality is derived
Operationality — action upon ∅ and upon the results of prior actions — is not a self-
standing kind of being. An operational set is its functionality, but this functionality is not
a separate ontological entity; it is a way of acting, related to ∅.
This distinction is principled (Part I §I.3). Were operationality a "second kind of entity,"
we would have a dual ontology: ∅ + operationality. A dual ontology is not minimalist —
it has two primitive types that must somehow be related. A derived ontology resolves
this difficulty: operationality "is not" in the proper sense; it "happens" — only its result,
visible as a set, is.
A clarifying metaphor: the number 1 is ontologically primary; "to add 1" is not an object
but an action; "the addition function" as an object is a derivative speech, useful for
mathematics but not a separate kind of number. So too in VR-Sets: ∅ is primary;
operationality is action; "functionality as object" is derivative speech.

Level 3: "doing" as a fundamental modality
The third level is the most philosophical. The slogan asserts not only what is and what is
not, but also in what manner exists everything that is not ∅. The manner is "doing,"
action, process. This is an ontological modality distinct from the classical "being"
(Parmenides) and "becoming" (Heraclitus).
In the classical ontology of sets the modality of being predominates: a set is with all its
properties at the moment of consideration, like a Platonic idea. In VR-Sets the modality of
action predominates: a set acts, it reveals elements when queried, and this activity is not
a property of the set but its essence.
Connection with other philosophical positions: the closest parallel is Whitehead's process
ontology (Whitehead, 1929), where the basic entities are events (actual occasions), not
objects. VR-Sets is not process philosophy in the full sense (Whitehead's events are
temporal; the operationalities of VR-Sets are not), but the methodological kinship is real:
in both, action is prior to object.

VIII.2. The ontological commitments of VR-Sets
We collect into one list all the ontological commitments accumulated in the preprint.
Each is a consciously accepted decision, not a mathematical necessity.

Commitment 1: the sole primitive is ∅
All "objects" of VR-Sets are derived from ∅. No atoms, urelements, individuals, ordered
pairs as objects, classes as ontologically new entities. Only ∅ and operationalities upon
it.
Cost: standard constructions requiring pairs (relations, functions via graphs of pairs) are
reformulated operationally (see Part III §III.3, Part V §V.5). Such reformulations
sometimes lengthen technical proofs; but the ontological gain — the absence of
additional primitives — outweighs this.

Commitment 2: only describable objects
All sets of VR-Sets are operationally describable functionalities. Indescribable objects —
those without a finite description — do not exist in the ontology. This is the principal
divergence from classical ZF, in which the existence of objects without a description is
admitted (for instance, a typical element of an uncountable set).
Cost: the countability of the entire universe (Part VI). Uncountable cardinalities, typical
uncountable constructions, and paradoxical consequences of full AC on uncountable
collections are inaccessible. Standard analysis on ℝ is restricted to computable reals.

Commitment 3: operationality is derived
Operational functionalities are not a self-standing kind of being alongside ∅ but derived
entities — actions upon ∅. Ontological status belongs only to ∅; operationality is in the
sense of describedness, not in the sense of primary ontological givenness.
Cost: attentiveness in formulation is required. To say "there exists a set A" in the full
ontological sense is incorrect: only ∅ exists, while A is a describable action upon ∅. This
reformulation adds philosophical discipline but does not alter mathematical claims.

Commitment 4: membership is reference, not containment
x ∈ y is read as "the functionality y reveals x in one of its responses," that is, as the
reference of y to x. Not as "x is physically located inside y." This dissolves the intuitive
paradoxes of self-reference (Part I §I.4): A ∈ A is not "A is located inside itself" but "the
functionality A returns A in one of its responses."
Cost: a rejection of the container metaphor of a set, to which classical thought is
accustomed. Worth it: the container metaphor is the source of most intuitive difficulties
in the foundations of set theory.

Commitment 5: two modes as an explicit ontological choice
The admission or prohibition of self-references (Quine atoms, cycles) is not a
mathematical necessity but an ontological choice: ZFC-mode or ZFA-mode. Both modes
are legitimate; the choice is made explicitly and depending on the goals of application
(Part IV).
Cost: the illusion of a "uniquely correct" set theory is lost. This is not a cost but a clarity:
different applications require different frames, and explicit acknowledgement of this is a
methodological advantage.

Commitment 6: hierarchy of truth through applications of t
Truth for VR-Sets is not expressible inside VR-Sets in full generality (Tarski's theorem).
The hierarchy of applications of the successor operator t gives levels at each of which
truth for the previous is expressible, but not for the current level (Part VII).
Cost: there is no single "above-all-levels" truth predicate. This is a commitment shared
with all sufficiently rich formal systems by Tarski's theorem; it is not specific to VR-Sets.

VIII.3. Relation to classical positions
We briefly discuss how VR-Sets relates to the principal positions in the philosophy of the
foundations of mathematics.
Platonism
Platonism (Gödel, Quine, the early Goodman) asserts that mathematical objects exist
independently of our knowledge of them; mathematical cognition is discovery, not
construction. Cantorian set theory in its modern form is in large part shaped by Platonist
intuitions: the entire hierarchy V is a "really existing" universe, and our theories describe
it more or less adequately.
VR-Sets is categorically non-Platonist. There are no sets in VR-Sets existing independently
of description. "Only ∅ is" is the ontological minimum, excluding the entire classical
Platonic hierarchy. Mathematical objects not operationally describable are absent in the
ontology of VR-Sets — not because we have "not discovered them," but because there is
no place for them in the ontology.

Formalism
Formalism (Hilbert) asserts that mathematics is the manipulation of formal symbols
without interpretation; the "meaning" of mathematical statements is their derivability in
a formal system. Truth in formalism reduces to provability.
VR-Sets is closer to formalism than to Platonism, but does not reduce to it. Operational
descriptions are not "symbols without meaning" but instructions for functionalities, with
an interpretation through action. The difference: formalism regards mathematics as a
game of symbols; VR-Sets, as an ontology of actions for which symbols are merely a way
of recording. The action is real (as a process), even if expressed through a formal
description.

Constructivism
Constructivism (Brouwer, Heyting, Bishop) asserts that mathematical objects must be
constructively given; existence is construction. In its radical form (intuitionism), the law
of excluded middle is rejected.
VR-Sets is ontologically close to constructivism: all objects must be operationally given (=
constructively built through description). However, VR-Sets does not reject classical logic.
The law of excluded middle may be used in VR-Sets, since operational definiteness is
already built into the closure principle: if a functionality is operationally defined, it gives
a definite response; "the third" is ontologically absent.
The difference: intuitionism rejects classical logic ontologically (there is no objective
truth, only justification); VR-Sets retains classical logic ontologically (objects are defined,
truth is locally definable) but restricts the ontology to describable objects.

Structuralism
Structuralism (Benacerraf, Shapiro, Resnik) asserts that mathematical objects are
positions in structures, and structure matters, not the nature of objects. The natural
number 3 is not "a particular object" but "the third position in any structure of natural
numbers."
VR-Sets is compatible with structuralism and in a sense refines it. Operational sets are
defined through their behaviour (what they reveal upon queries), not through "nature."
Isomorphic functionalities are precisely one and the same set by extensionality ≡. This
accords with the structuralist intuition: structure matters, not matter.
However, VR-Sets is a more ontological position than structuralism: it does not merely
say "matter does not matter" but specifies concretely that only ∅ is ontologically primary
and the rest is action. Structuralism leaves open the question "what then specifically is?";
VR-Sets answers: ∅ is, action happens.

The position of VR-Sets as "operationalism"
A suitable name for the ontological position of VR-Sets is operationalism: mathematical
objects are operational actions upon the minimal ontological primitive ∅. This is:
• not Platonism — the ontology contains no objects independent of description;
• not pure formalism — symbols are interpreted through actions, not left without
meaning;
• compatible with constructivism in ontology but without abandoning classical logic;
• a refinement of structuralism, specifying that "structure" is a pattern of actions upon
∅.
This position does not claim to be "uniquely correct." It is a coherent alternative, with its
own advantages (ontological minimalism, the absence of paradoxes of uncountability)
and limitations (a countable universe, the absence of classical ZFC in its full extent).
A reminder on the status. The discussion in this part has positioned VR-Sets relative to
classical ZFC, classical AFA, and other foundations. The technical relation between the
ZFC-mode and a countable model of classical ZFC (and parallel for the ZFA-mode and
AFA) is the content of Conjectures IV.1 and IV.2 and remains open; this is recorded in
§IX.1 as Questions 1 and 2. The philosophical positioning of VR-Sets as operationalism
does not depend on the resolution of these conjectures: the ontology stands on its own
primitives and commitments, whether or not the technical equivalence with a countable
model of the classical theory is established.

VIII.4. Applicability: for what VR-Sets is suited
Closing the discussion, we fix which mathematical applications are natural for VR-Sets
and which are not.
Naturally suited
• All of computable mathematics: algorithms, recursive functions, formal languages,
complexity theory, programming.
• Constructive mathematics in a broad sense, including reverse mathematics and
predicative analysis.
• Computable analysis: analysis on computable reals and other computable structures.
• Discrete mathematics: graph theory, combinatorics, algebra over countable carriers.
• Logic and model theory for countable structures; formal verification of programs.
• Non-well-founded sets (through the ZFA-mode): modelling of circular phenomena in
semantics, theory of processes, situational semantics of natural language.

Not directly suited
• Standard analysis on the classical uncountable ℝ with the full theory of Lebesgue
measure. The analogue in VR-Sets is analysis on ℝVR-Sets of computable reals, which
covers most practical applications but differs formally.
• The theory of uncountable cardinalities: ℵ1, uncountable ordinals, the continuum
hypothesis. In VR-Sets these notions have no direct analogue.
• Parts of classical functional analysis relying on uncountable bases, Zorn's lemma for
uncountable indices, the existence of ultrafilters. Constructive analogues exist, but not all
classical results carry over.
• Paradoxical consequences of AC: Banach–Tarski and the like. They are absent by
construction (Part VI §VI.5), which is for most purposes an advantage, but if for some
reason they are required, VR-Sets is not suited.

The substantive position
VR-Sets is suited for mathematics in which every object may be exhibited — operationally,
algorithmically, through a description. This is the greater part of substantive
mathematics, including practically everything used in informatics, engineering, physics.
VR-Sets is not suited for mathematics making essential use of non-exhibitable objects —
typical elements of uncountable collections, non-measurable sets, equivalence classes
with an uncountable number of representatives. This second area of mathematics exists
and is fruitful; VR-Sets does not propose an alternative to it.
Accordingly, the choice between VR-Sets and classical ZFC is not mathematical and not
philosophical in the narrow sense, but methodological: what kind of mathematics do we
intend to pursue? For ontologically transparent, operational, computable mathematics,
VR-Sets provides a coherent and minimalist frame. For mathematics requiring classical
uncountability, ZFC or its extensions are needed.
VIII.5. Summary
In this part:
(1) The slogan "only ∅ is, all else is doing" has been unfolded on three levels of meaning:
∅ as the sole primitive, operationality as derivative, "doing" as a fundamental modality
(§VIII.1).
(2) Six ontological commitments of VR-Sets have been fixed, with the cost of each
indicated (§VIII.2).
(3) The position of VR-Sets has been related to Platonism (incompatible), formalism
(close, but not reducible), constructivism (close ontologically but retaining classical
logic), structuralism (compatible, refines). A suitable name for the position is
operationalism (§VIII.3).
(4) The applicability of VR-Sets has been described: naturally suited for all of computable
and constructive mathematics; not directly suited for the classical theory of uncountable
cardinalities (§VIII.4).
Methodological summing-up. VR-Sets is not "better" than classical ZFC and not "worse."
It is a different ontological option, with its own area of applicability and its own
advantages. The principal advantage is ontological transparency: each object is given
explicitly, each existence is grounded through description, and no ontological
assumption beyond operationality is made. The principal cost is the countability of the
universe, excluding part of classical mathematics.
What follows. Part IX, the final part of the preprint, fixes the open questions: technical
(formalisation in Lean, proofs of the equivalence conjectures, machine verification) and
substantive (connections with topoi, homotopy type theory, extensions to Morse–Kelley
and NBG).

## Part IX. Open Questions

IX.0. Introduction
The concluding part of the preprint fixes the open questions of the VR-Sets programme.
They are divided into three groups:
(1) Technical questions — tasks of rigorously proving what has been formulated in the
preprint as conjectures, and tasks of machine formalisation.
(2) Substantive extensions — directions for developing the theory beyond the present
preprint: connections with topoi, HoTT, extensions to MK and NBG, non-von-Neumann
constructions.
(3) Philosophical questions — substantive positions that have not received final
formulation in the preprint.
Each question is formulated as a direction, not as a task with a known method of
solution. Some of these questions may turn out to be technically routine (for instance,
machine formalisation of already-proved theorems); others may require essentially new
work.

IX.1. Technical questions
Question 1: Proof of Conjecture IV.1
Conjecture IV.1 asserts: the ZFC-mode of VR-Sets and classical ZFC are mutually
interpretable (via a countable model of ZFC).
The direct direction was established in Theorem IV.1: the ZFC-mode is a model of ZFC.
The converse direction — interpreting a countable model of ZFC in the ZFC-mode —
requires:
(a) the choice of a suitable countable model of ZFC (by Löwenheim–Skolem such models
exist; a concrete construction convenient for operational interpretation is needed);
(b) the construction of an operational representation of each element of this model as a
describable functionality;
(c) verification that the membership relation in the model is preserved under the passage
to VR-Sets.
This is technical work feasible by standard means of model theory, but not trivial. An
alternative approach — through the theorem on the existence of the minimal model of
ZFC (L); the elements of L are describable by construction, which simplifies the
operational interpretation.
Question 2: Proof of Conjecture IV.2
Conjecture IV.2 is the parallel of IV.1 for the ZFA-mode and the theory ZFC− + AFA (Aczel
1988). Technically similar, with additional difficulty on the AFA side: classical AFA theory
also has an uncountable model, and a correspondence with the ZFA-mode requires work
with a countable AFA-model.
Difficulty: in the AFA literature, countable models are less well studied than countable
models of ZFC. A possible route — through Aczel's theorem on the final coalgebra of the
power-set functor; the final coalgebra in a countable category may yield a countable
AFA-model.

Question 3: Formalisation in Lean / Coq / Agda
Machine formalisation of the preprint in one of the proof assistants is the natural next
task. This would provide:
(a) a formal check of all proofs of Part III and Part IV;
(b) a precise formulation of the definitions of Part II in the language of dependent types;
(c) the possibility of machine verification of Conjectures IV.1 and IV.2 (at least the direct
directions).
Lean 4 appears the most suitable due to its mathematical library (mathlib) and
convenient support for coinductive definitions (for ≡). Alternatively, Coq with its own
library for non-well-founded sets, or Agda with its strong support for sized types.

Question 4: Precise characterisation of describable functionalities
The closure principle rests on the notion of an "operationally describable functionality."
In the preprint this notion is used substantively but does not receive a precise formal
definition. Possible formalisations:
(a) through Turing machines: a describable functionality is one computable by a suitable
machine;
(b) through λ-calculus: a describable functionality is one expressible by a λ-term;
(c) through primitive recursion and general recursion: a describable functionality is one
given by a recursive definition.
These three formalisations are classically equivalent (by the Church–Turing thesis) but
yield different practical approaches to working with VR-Sets. The choice of one or
another formalisation is a separate technical question.

Question 5: Connection of ≡ with bisimulation in rigorous formulation
In Part IV §IV.8 it was asserted that the operational identity ≡ from Definition 4
structurally coincides with Aczel's bisimulation. This assertion requires a rigorous
formulation: which sets/graphs are considered, in which category the correspondence
operates, how this equivalence interacts with the ZFC and ZFA modes.

IX.2. Substantive extensions
Extension 1: Connection with topos theory
Categorical set theory (Lawvere's ETCS and its extensions) considers sets through the
category Set with its universal properties. VR-Sets is closer to this tradition than to
classical ZF: ≡ operates as an isomorphism in the category of operational functionalities.
Open questions:
(a) Is the VR-Sets universe (for the ZFC-mode) a topos? If so, what are its specific
properties (for instance, does it contain a subobject classifier)?
(b) What is the connection between the ZFC-mode and the category of sets in a suitable
topos of computable functions?
(c) Can the ZFA-mode be obtained as a topos with a suitable modification (without the
well-foundedness condition on structural morphisms)?
These questions form a bridge to the powerful categorical apparatus; their development
could significantly extend the expressive power of VR-Sets.

Extension 2: Homotopy type theory (HoTT)
In HoTT, equality is not a relation but a type (path). This is consistent with the
operational ontology: ≡ in VR-Sets is not a static relation but potentially a structure (two
operationalities are equal in a particular way, and there may be many such ways).
Possible directions:
(a) Reformulate VR-Sets in the language of HoTT, where ≡ becomes a path type.
(b) Investigate whether this yields new objects — operational sets with a non-trivial
identity structure.
(c) Connect the hierarchy of t-applications with n-types of HoTT.
This is a substantively close direction, but it would require considerable work in
translating VR-Sets into a type calculus.

Extension 3: Morse–Kelley and NBG
In classical set theory, beyond ZFC, extensions with proper classes are considered: NBG
(von Neumann–Bernays–Gödel) and Morse–Kelley. In these theories, "collections" too
large to be sets are admitted.
In VR-Sets, the entire universe is countable, and so "too large collections" do not arise in
the classical sense. However, operational analogues are possible:
(a) Describable families of functionalities that are not sets through failure of
operational describability. For instance, "all terminating algorithms computing reals" —
this is not a set in VR-Sets, since the corresponding family is not enumerable.
(b) The hierarchy of meta-levels through t: each tn(ω) is a set, but "the entire
hierarchy" is an unbounded process, not a separate object.
A substantive development of the operational analogue of class theory is an open
direction.

Extension 4: Non-von-Neumann codings of numbers
In Part V, VR numbers are represented as von Neumann ordinals On = {O0, …, On−1}.
This is a standard coding but not the only one. Zermelo proposed an alternative: {∅},
{{∅}}, {{{∅}}}, …
In VR-Sets more exotic operational codings of numbers are possible — for instance,
through infinite non-composite functionalities, through coinductive structures in the
ZFA-mode, or through binary representations. Each such coding is a distinct operational
realisation of ℕ; all are isomorphic as algebraic structures but differ in operational
characteristics (operational depth, describability, and so on).
Open question: is there, among these codings, one distinguished in VR-Sets by a
structural property (for instance, minimising operational depth or complexity of
description)?
Consistency with §V.6. Part V §V.6 asserts that, under the standard von Neumann
coding, VR numbers do not use the ZFA-mode. The present extension does not contradict
this: it considers alternative non-von-Neumann codings as an open direction.
Coinductive ZFA-mode codings of numbers, if developed, would be a separate
operational realisation of ℕ alongside the standard one — not a revision of the standard
coding.

IX.3. Philosophical questions
Question 1: The nature of "action"
The slogan "only ∅ is, all else is doing" appeals to the notion of "action" as a fundamental
ontological modality. In Part VIII this was indicated as a parallel to Whitehead's process
ontology, but it was not developed in full.
Open questions:
(a) What does "action" mean in the VR-Sets ontology, given that time does not enter it?
Operational functionalities are integral objects (Part IV §IV.1), not temporal processes.
Then "action" is what?
(b) Can "action" be more ontologically fundamental than "object"? If so, this requires
serious philosophical work not carried out in the preprint.
(c) The relation to other ontologies of action (Heraclitus, Bergson, Whitehead, process
theology) is an open philosophical direction.

Question 2: The status of Conjectures IV.1 and IV.2
Should Conjectures IV.1 and IV.2 turn out to be false — that is, should VR-Sets prove to be
substantively not equivalent to any countable model of ZFC or AFA — this would be a
substantive result. It would mean that the operational ontology yields its own
mathematical structure, irreducible to the classical. Open question: to what then does the
ZFC-mode of VR-Sets correspond, if not to a countable model of ZFC?
This question is not technical but substantive: it bears on the extent to which VR-Sets is
its "own" theory and the extent to which it is a reformulation of the known.

Question 3: Applicability to physics
VR-Numbers (Reznik 2026) discussed possible connections with physics — through ℂ as
the natural algebra of quantum mechanics. VR-Sets potentially deepens this connection:
a countable operational ontology may be a suitable frame for discussing quantum states
as operational descriptions of observables.
Open direction: is the VR-Sets ontology compatible with the structure of Hilbert space
used in quantum mechanics? Hilbert space is classically uncountable; computable
Hilbert space (as in computable analysis) is countable. If physics in reality works only
with computable states, VR-Sets is a natural ontological frame for quantum mechanics.
This is a speculative direction not developed in the preprint; it is mentioned here as one
of the promising areas of application.

Question 4: Relation to the VR programme as a whole
The cycle of works — VR. A Formal System, VR-Numbers, VR-Sets — is built as an
ascending sequence: from arithmetic through numerical extensions to set theory. Open
question: what is the next work in the cycle?
Possible candidates:
(a) VR-Analysis — operational analysis on ℝVR-Sets.
(b) VR-Categories — a categorical reconception of the cycle, with connections to topoi
and HoTT.
(c) VR-Physics — an operational reformulation of the foundations of physics.
(d) VR-Logic — an extension of the basic logic of VR (two-valued classical) to
intuitionistic, modal, or linear operational logics.
The choice of the next work is a substantive question depending on which direction
proves most fruitful.
IX.4. Conclusion
The VR-Sets preprint, consisting of nine parts, has set out an operational theory of sets
based on the single ontological primitive ∅. The principal results:
(1) The ontological foundation (Parts I, II, VIII): a set is an operational functionality;
membership is reference, not containment; operationality is derivative action upon ∅,
not a self-standing kind of being.
(2) The closure principle (Part II §II.3): the operational replacement for the axioms of
existence. Every describable functionality is a set; paradoxical descriptions do not
specify functionalities.
(3) The ZF axioms as theorems (Part III): all nine ZF axioms + AC have been derived
through the closure principle. Three key divergences from classical ZF: ℘(ω) is
countable; the replacement schema becomes a single theorem; foundation is a mode-
dependent property.
(4) The two modes (Part IV): the ZFC-mode (well-founded functionalities) and the ZFA-
mode (all describable). The distinction is structural, not temporal. Conjectures of
equivalence with the classical theories via a countable model.
(5) VR numbers in VR-Sets (Part V): von Neumann ordinals as specific well-founded sets;
arithmetic inherited without re-proof.
(6) Cardinality (Part VI): countability of the entire operational universe; Cantor's
diagonal does not operate; AC is a theorem; absence of Banach–Tarski.
(7) Truth and self-reference (Part VII): a cautious reformulation of Tarski's hierarchy
through the successor operator t. Not a resolution but an operational interpretation.
The position of VR-Sets in the spectrum of foundations of mathematics. VR-Sets is an
operationalist position located between formalism and constructivism, closer to
computable analysis and predicativism than to Platonism. It does not claim to replace
classical ZFC, but provides an alternative ontological frame for mathematics in which
every object may be exhibited operationally.
The principal substantive achievement is the demonstration that ontological
minimalism ("only ∅ is, all else is doing") applied to sets yields a coherent, technically
workable, and philosophically transparent theory, encompassing the greater part of
substantive mathematics and dissolving classical paradoxes (Russell, Banach–Tarski,
partially the Liar) ontologically rather than syntactically.
The open questions gathered in this part indicate directions for further work —
technical (formalisation in Lean, proofs of conjectures, precise characterisation of
describability), substantive (connection with topoi, HoTT, extensions), and philosophical
(the nature of "action," the next work in the VR cycle). Each of these directions is fruitful
as an independent programme.
Closing the preprint, we repeat the slogan of the cycle:
"Only ∅ is — all else is doing."
Applied to sets: ∅ is ontologically primary; everything else is operational action,
describable by finite procedures, unfolding into a countable, transparent, coherent
mathematical universe. This universe is VR-Sets.

## Part X. Lean 4 Formalisation of VR-Sets:

Methodological Observations

§X.1 Overview
The formalisation of VR-Sets Parts II–V in Lean 4 (mathlib v4.29.1) was completed in
thirteen stages. The base type `OSet := ZFSet` — mathlib's `Quotient PSet.setoid` — carries
all nine ZFC axioms as theorems and serves as the operational set universe. The
formalisation uses the same Opus–Sonnet review architecture as VR-Numbers (§VIII).
The same axiom ceiling `[propext, Classical.choice, Quot.sound]` is maintained; four
objects achieve the empty axiom profile (no axioms whatsoever), a tighter result than
VR-Numbers, where no object was axiom-free.
The results divide into three categories, each new relative to VR-Numbers:
1. Proved theorems: all nine ZFC axioms, Theorem V.1 (well-foundedness), Theorem
V.2 (VR–OSet isomorphism), Theorem IV.1 (ZFC-mode collector). 2. Refuted claims:
classical Anti-Foundation Axiom (AFA) and the Quine atom specification, both provably
false in mathlib's `PSet`. 3. Open formulations: Conjectures IV.1 and IV.2, recorded as
`def : Prop` — a third Lean status distinct from `theorem` and `axiom`.
The sections below record methodological observations arising from the formalisation,
grouped thematically. Each observation is stated concisely; the underlying Lean evidence
(definitions, proofs, `#print axioms` output) is in the formalisation repository.

§X.2 Bisimulation and the Quotient Base
Observation A.1 (Bisimulation as definitional equality). The preprint defines
operational identity (Definition 4) as a bisimulation: «for every element x of A there
exists an element y of B with x ≡ y, and conversely». In Lean, this is `PSet.Equiv` — the
extensional bisimulation on pre-sets (Mathlib ZFC.PSet). The quotient `ZFSet := Quotient
PSet.setoid` promotes `PSet.Equiv` to Lean's propositional equality `Eq`. Setting `OSet :=
ZFSet` (as an `abbrev`) makes `a ≡ b` syntactically identical to `a = b : OSet`. The
bisimulation does not require a separate proof step — it is definitionally absorbed into the
quotient construction.
This is more economical than VR-Numbers, where each isomorphism (`IntVRIntIso`,
`RatVRRatIso`, etc.) required explicit `forward`/`backward` maps with round-trip proofs.
Here, the bisimulation is the quotient.
Observation A.2 (Duplicate elements via quotient). The preprint states (§II.2): «the
union reveals elements without repetitions up to ≡». In ZFSet, duplicate suppression
does not require a separate predicate or a decidability hypothesis. The quotient `ZFSet`
identifies extensionally equivalent elements automatically; `ZFSet.sUnion` (union) and
`ZFSet.powerset` (power set) return elements of `ZFSet`, so membership is already
modulo `PSet.Equiv`. No `DecidableEq` typeclass or analogous instance is needed at the
union/power level, in contrast to settings where set equality is a separate predicate.

§X.3 Structural Boundaries
This section records five places where the Lean formalisation reveals a structural
boundary between the operational universe of VR-Sets and mathlib's type-theoretic
infrastructure. The boundaries are of two types: Lean is wider (the Lean object admits
more than the operationally describable) and Lean is narrower (the Lean object pre-
commits to a restriction not present in the preprint's general formulation).
Observation B.1 (First boundary: Power set). Stage 5 formalises `℘(A)` via
`ZFSet.powerset`. The preprint §III.5 restricts the power set to operationally describable
subsets, yielding a countable result for countable `A`. In Lean, `ZFSet.powerset` contains
all subsets — including non-describable ones. For `A = ω`, the resulting set is
uncountable. This is the first structural boundary of the formalisation: Lean's `℘(ω)` is
strictly wider than the preprint's operational `℘(ω)`. The discrepancy is metatheoretic
(the condition «operationally describable» is not Lean-expressible) and is documented in
the Stage 5 source.
This boundary parallels the `ℝ_VR` inexpressibility in §VIII.6 of VR-Numbers v1.0.2: both
involve a countability restriction that is meaningful in the preprint's operational
universe but metatheoretic from Lean's perspective.
Observation B.2 (Second boundary: Replacement). `Theorem_III_7_Replacement`
wraps mathlib's `ZFSet.replacement`. The preprint §III.7 restricts replacement to
operationally definable functions. `ZFSet.replacement` takes a Lean function `F : ZFSet →
ZFSet` — the full class of Lean functions, not just describable ones. The formalisation
records the classical theorem (wider than the preprint), with the boundary documented
in a comment. The axiom dependency is `Classical.allZFSetDefinable`, reflecting that «all
Lean functions are considered definable» is precisely the non-operational assumption.
Observation B.3 (Third boundary: Choice). `Theorem_III_9_Choice` is proved via
`Classical.choice`. The preprint §III.9 argues that AC is a theorem of countable VR-Sets: in
a countable universe a choice function can be constructed algorithmically. In Lean,
`Classical.choice` is a single axiom that applies universally — it does not specialise to
countable sets and does not produce an explicit algorithm. The preprint's argument
(countability → constructive choice) is metatheoretic. Lean records AC as an axiom; it
cannot express the countability restriction that would make it a theorem.
Three boundaries in one direction: power set, replacement, choice — each place where
operational describability is lost in the classical Lean universe.
Observation B.4 (Fourth boundary: Foundation, opposite direction).
`Theorem_III_8_Foundation` holds unconditionally on `OSet = ZFSet` because `ZFSet` is
well-founded by construction: `PSet` is an inductive type, so all elements are accessible.
The preprint §IV presents Foundation as mode-dependent: it holds in ZFC-mode but not in
ZFA-mode (where cyclic sets exist). In Lean, there is no ZFA-mode to speak of (see
Observation B.5), so Foundation is a universal theorem — but this is a pre-commitment,
not a generalisation. Lean's type theory pre-commits the entire universe to ZFC-mode;
the modal distinction of the preprint surfaces here not as two parallel universes but as a
single universe plus an explicit boundary marker (`AFA_Refuted`, Stage 10) and a
formulation of the opposite mode as a conjecture (`Conjecture_IV_2_Statement`, Stage 11).
The modal analysis is not foreclosed — it is repositioned. This is a boundary in the
opposite direction from B.1–B.3: Lean is narrower, not wider.
Observation B.5 (Fifth boundary: ZFA — total absence, type-theoretic). The ZFA-
mode of VR-Sets (§IV.5–§IV.7) requires a universe of non-well-founded sets where the
Quine atom A = {A} exists and AFA holds. A systematic search of all of mathlib4 for terms
`AFA`, `AntiFoundation`, `non-well-founded`, `coinductive` (for sets), `NonWellFounded`,
and `Quine` returned zero results. mathlib contains no AFA or coinductive set
infrastructure.
More importantly, `PSet` is an inductive type in Lean 4:
inductive PSet : Type (u + 1)

| mk (α : Type u) (A : α → PSet) : PSet

Lean's inductive types have a built-in well-founded recursion principle. The direct
consequence is `PSet.mem_irrefl : ∀ x : PSet, x ∉ x`. The Quine atom would require `Q ∈
Q`, which contradicts `PSet.mem_irrefl`. Therefore the Quine atom is provably impossible
in PSet — not merely hard to construct.
This yields the strongest result of the formalisation:
theorem quineAtom_impossible : ¬quineAtomSpec       -- axiom-free proof

theorem AFA_Refuted : ¬AFA_Statement                 -- axiom-free proof

Both are proved with no axioms (`#print axioms` returns `[]`). The proof of `AFA_Refuted`
applies AFA to the universal self-loop graph (V = Unit, E _ _ = True) and derives `f () ∈ f ()`,
contradicting `PSet.mem_irrefl`. No `propext`, no `Classical.choice`, no `Quot.sound`.
This boundary is categorically stronger than boundaries B.1–B.4: - At B.1–B.3, Lean's
object exists (as a classical entity) and is merely wider than the operational version. - At
B.4, the operational restriction is absent, but no inconsistency arises. - At B.5, the ZFA-
mode universe provably does not exist in mathlib's type hierarchy. Adding AFA as an
axiom would be inconsistent with `PSet.mem_irrefl` already present in mathlib.
This is categorically stronger than the VR-Numbers §VIII.6 boundary at `ℝ_VR`. There,
classical `ℝ` existed in Lean and the computability restriction was metatheoretic — an
unexpressed condition on the type. Here, the ZFA-mode universe has no representation
at all in mathlib's type hierarchy, and the impossibility is constructively provable (axiom-
free proof). The boundary moves from "metatheoretic" to "structurally proven" — a
stronger form of inexpressibility.

§X.4 Axiom-Minimal Patterns
Observation C.1 (Four faces of Classical.choice). `Classical.choice` enters the VR-Sets
formalisation through four distinct mechanisms — none of which is the direct
application of AC to a set-theoretic family:
| Theorem | Source of Classical.choice |

| `Lemma_II_3_DepthMono` (rank) | `Ordinal.iSup` (supremum of ordinal-valued function)
|

| `Theorem_III_7_Replacement` | `Classical.allZFSetDefinable` (all Lean functions are
«definable») |

| `Theorem_III_8_Foundation` | `WellFounded.has_min` (existence of a minimal element)
|

| `Theorem_III_9_Choice` | `Classical.choice` directly (AC on ZFSet families) |

This parallels VR-Numbers, where the boundary into `Classical.choice` came primarily
through a single structural place — mathlib's `Rat.add` normalisation via `Nat.gcd` (VR-
Numbers §VIII.4). In VR-Sets, by contrast, the boundary is distributed across four
mechanically distinct sources, reflecting the broader algebraic surface of set theory
compared to number theory.
Observation C.2 (Axiom profiles of formulations reflect structural nature). The two
conjectures of Stage 11 have different axiom profiles:
Conjecture_IV_1_Statement : [propext, Quot.sound]

Conjecture_IV_2_Statement : []    (no axioms)

`Conjecture_IV_1_Statement` references `OSet.{0} = ZFSet.{0}` — a specific mathlib
quotient type — so it inherits `Quot.sound` from the quotient construction and `propext`
from membership on `ZFSet`. `Conjecture_IV_2_Statement` is stated over abstract `(U :
Type, mem : U → U → Prop)` — no reference to any specific mathlib type — and is
therefore axiom-free.
This is not an incidental technical difference. It reflects what the conjectures point to:
Conjecture IV.1 asks about a countable submodel of a specific mathlib type (OSet);
Conjecture IV.2 asks about the existence of an abstract type with AFA structure —
something outside the current mathlib type hierarchy. The axiom profiles witness this
structural distinction at the level of dependency closures.
§X.5 Methodological Convergences
Observation D.1 (Replacement: schema → single theorem). In classical ZF, the Axiom
of Replacement is a schema: one axiom instance for each first-order formula φ(x, y)
defining a functional relation. In the preprint §III.7, replacement is stated as a single
theorem (over all operationally definable functions, where definability is built into the
operational semantics). In Lean 4, `ZFSet.replacement` is a single polymorphic function:
the schema is unified into one statement via function quantification. This is a three-way
convergence: classical ZF (schema), operational VR-Sets (single theorem over describable
functions), and Lean (single theorem over all functions) all agree that replacement is not
a logical schema but a single closure principle — the classical version merely lacks a
mechanism to unify function quantification.
Observation D.2 (Three-tier formalisation result). VR-Numbers produced only
positive results: theorems proved, isomorphisms constructed. VR-Sets produces a
structurally richer outcome:
| Category | Objects | Example |

| Proved theorems | 16 | `Theorem_IV_1_ZFCAxioms`, `Theorem_V_2` |

| Refuted claims | 2 | `AFA_Refuted`, `quineAtom_impossible` |

| Open formulations | 2 | `Conjecture_IV_1_Statement`, `Conjecture_IV_2_Statement` |

The refuted claims are structural boundary theorems: they arise because mathlib's type
hierarchy cannot accommodate ZFA-mode, not because ZFA-mode is logically
inconsistent. The open formulations are the first instances in the VR Lean cycle of a
theorem-like object that the system records but cannot resolve.
This three-tier structure is a consequence of the modal analysis of Parts IV: any
formalisation of a system that distinguishes modes (ZFC vs. ZFA) must confront the
question of which mode the formalisation framework itself inhabits. Lean's type theory
inhabits ZFC-mode by construction; VR-Sets is designed to be mode-agnostic. The
boundary between these is the primary finding of Stage 10.

§X.6 Conclusion
The Lean 4 formalisation of VR-Sets demonstrates that the operational set theory of Parts
II–V is machine-verifiable, with no axioms beyond the standard Lean ceiling `[propext,
Classical.choice, Quot.sound]`. The formalisation required no new axioms, no `sorry`, and
no changes to mathlib.
The most significant finding — the axiom-free refutation of AFA and the Quine atom
specification (Observation B.5) — was not anticipated in the formalisation plan. It arises
from a structural property of Lean 4's inductive type system (induction, not coinduction,
for `PSet`) and represents the deepest boundary between the operational VR-Sets
universe and classical Lean's type hierarchy.
The Lean formalisation generated seventeen methodological observations across
thirteen stages; the ten presented in §X.2–§X.5 are those most directly bearing on the
relationship between operational and type-theoretic foundations. The remaining seven
(technical details of axiom inheritance, mathlib API quirks, and intermediate steps) are
documented in the source comments of the formalisation. Together, they document not
only what was proved, but what could not be proved, why, and what the corresponding
structural boundary implies for the relationship between operational set theory and
classical type-theoretic foundations.

Lean 4 formalisation repository: VRCycle, tag v1.2-vr-sets. Zenodo Software DOI:
10.5281/zenodo.20354340. Lean toolchain: v4.29.1 + mathlib v4.29.1.

## References

Aczel, P. (1988). Non-Well-Founded Sets. CSLI Lecture Notes, No. 14. Stanford: Center for
the Study of Language and Information.
Barwise, J., & Moss, L. (1996). Vicious Circles: On the Mathematics of Non-Wellfounded
Phenomena. CSLI Lecture Notes, No. 60. Stanford: Center for the Study of Language and
Information.
Benacerraf, P. (1965). What numbers could not be. The Philosophical Review, 74(1), 47–73.
Bishop, E. (1967). Foundations of Constructive Analysis. New York: McGraw-Hill.
Brouwer, L. E. J. (1907). Over de Grondslagen der Wiskunde [On the Foundations of
Mathematics]. Doctoral dissertation, University of Amsterdam.
Cantor, G. (1891). Über eine elementare Frage der Mannigfaltigkeitslehre. Jahresbericht
der Deutschen Mathematiker-Vereinigung, 1, 75–78.
Feferman, S. (1964). Systems of predicative analysis. The Journal of Symbolic Logic, 29(1),
1–30.
Gödel, K. (1944). Russell's mathematical logic. In P. A. Schilpp (Ed.), The Philosophy of
Bertrand Russell (pp. 123–153). Evanston: Northwestern University.
Heyting, A. (1956). Intuitionism: An Introduction. Amsterdam: North-Holland.
Hilbert, D. (1926). Über das Unendliche. Mathematische Annalen, 95(1), 161–190.
Lawvere, F. W. (1964). An elementary theory of the category of sets. Proceedings of the
National Academy of Sciences, 52(6), 1506–1511.
Löwenheim, L. (1915). Über Möglichkeiten im Relativkalkül. Mathematische Annalen,
76(4), 447–470.
Martin-Löf, P. (1984). Intuitionistic Type Theory. Naples: Bibliopolis.
Pour-El, M. B., & Richards, J. I. (1989). Computability in Analysis and Physics. Perspectives
in Mathematical Logic. Berlin: Springer-Verlag.
Quine, W. V. O. (1951). Two dogmas of empiricism. The Philosophical Review, 60(1), 20–43.
Resnik, M. D. (1997). Mathematics as a Science of Patterns. Oxford: Oxford University
Press.
Reznik, V. (2026). VR. A Formal System: A Minimalist Axiomatization of Arithmetic
Grounded in Leibnizian Void. Zenodo. DOI: 10.5281/zenodo.20212092
Reznik, V. (2026). VR-Numbers: Operational Extensions over the Natural Numbers of VR.
Zenodo. DOI: 10.5281/zenodo.20272743
Reznik, V. (2026). VR-Sets: A Lean 4 Formalisation of Parts II–V (Software, Git tag v1.2-vr-
sets). Zenodo. DOI: 10.5281/zenodo.20354340
Russell, B. (1903). The Principles of Mathematics. Cambridge: Cambridge University Press.
Shapiro, S. (1997). Philosophy of Mathematics: Structure and Ontology. New York: Oxford
University Press.
Simpson, S. G. (2009). Subsystems of Second Order Arithmetic (2nd ed.). Perspectives in
Logic. Cambridge: Cambridge University Press.
Skolem, T. (1923). Einige Bemerkungen zur axiomatischen Begründung der Mengenlehre.
Matematikerkongressen i Helsingfors, 217–232.
Solovay, R. M. (1970). A model of set-theory in which every set of reals is Lebesgue
measurable. Annals of Mathematics, 92(1), 1–56.
Tarski, A. (1933). Pojęcie prawdy w językach nauk dedukcyjnych [The concept of truth in
the languages of deductive sciences]. Prace Towarzystwa Naukowego Warszawskiego,
Wydział III, No. 34.
Univalent Foundations Program. (2013). Homotopy Type Theory: Univalent Foundations
of Mathematics. Institute for Advanced Study. Available at:
https://homotopytypetheory.org/book/
Weihrauch, K. (2000). Computable Analysis: An Introduction. Texts in Theoretical
Computer Science. Berlin: Springer-Verlag.
Weyl, H. (1918). Das Kontinuum: Kritische Untersuchungen über die Grundlagen der
Analysis. Leipzig: Veit.
Whitehead, A. N. (1929). Process and Reality: An Essay in Cosmology. New York:
Macmillan.
Zermelo, E. (1908). Untersuchungen über die Grundlagen der Mengenlehre.
Mathematische Annalen, 65(2), 261–281.

Acknowledgement of AI assistance
The formal exposition of this preprint was prepared with the assistance of Claude
(Anthropic, model Opus 4.7) for drafting, English translation, language polishing, and
consistency checking. The Lean 4 formalisation underlying Part X was carried out in a
parent-child review architecture, with Claude (Opus 4.7) acting as reviewer and Claude
(Sonnet 4.6, via Claude Code) writing the Lean code; all architectural decisions and
acceptance criteria are due to the author. All mathematical content, definitions, theorems,
and ontological positions are due to the author.
