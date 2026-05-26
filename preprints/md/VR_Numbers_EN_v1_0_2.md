VR-Numbers.
Operational Superstructures of Integers, Rationals, Reals, and Complex Numbers over
the Natural Numbers of VR
Vitaly Reznik
ORCID: 0009-0002-4103-6387
2026
Version 1.0.2


## Abstract

Building on VR (Reznik, 2026, DOI: 10.5281/zenodo.20212092), a formal axiomatization of
arithmetic with three primitives {∅, →, t} and four axioms, we develop VR-Numbers — a
program of operational superstructures yielding ℤ , ℚ , ℝ , and ℂ over VR's natural numbers ℕ . The
construction uses no ordered pairs as ontological objects; each numerical extension is defined as a
formal language of expressions with equivalence relations and operations. The ontological
foundation of the entire system is the single primitive ∅; all numerical objects — including ℕ —
arise as operational constructions of progressively greater depth. The classical actual infinity is
replaced by operational infinity: A4 (induction) is read as an operational principle, not as a
postulate of completed infinite totalities. The two-dimensionality of ℂ is structurally grounded in
the duality present in axiom A1 of VR (the two generating implications F → F and F → ⊤), rather
than postulated through pairs of reals; the algebraic coupling of the two axes requires an additional
joining axiom (i² = ℤ 1). ℚ_VR, ℂ _VR, and ℂ_VR are shown to be isomorphic to the
corresponding standard structures; ℝ _VR is isomorphic to the field of computable real numbers —
a countable subfield of classical ℝ — reflecting the operational character of the construction.
Version 1.0.2 (2026) adds Part VIII collecting methodological observations from the Lean 4
formalisation of Parts II–V (companion publication, Zenodo DOI 10.5281/zenodo.20352057). No
axioms, definitions, or theorems of Parts I–VII are altered.

**Keywords:** foundations of mathematics, operational extensions, operational infinity, integer

construction, rational construction, real numbers, complex numbers, Cauchy sequences, axiomatic
duality, ontology of numbers, computable analysis.


## Part I. Foundation: VR and ℕ

This work builds upon the formal system VR introduced in [Reznik 2026]. We briefly recall its
essentials.

Primitives of VR.
Constant: ∅. Binary operator: → (implication). Unary operator: t (succession).
Axioms.
A1 (Generativity). F → F = ⊤ and F → ⊤ = ⊤, where F is identified with ∅ at the logical level,
and ⊤ := F → F.
A2 (Implication). → is the classical implication on {F, ⊤}.
A3 (Succession). t(x) = x ∪ {x}, so x ∈ t(x) and x ⊂ t(x).
A4 (Induction). The objects O_n = t^n(∅) exhaust all objects generated from ∅ via t.

Natural Numbers.
O₀ = ∅, O₁ = t(∅) = {∅}, O₂ = t(t(∅)) = {∅, {∅}}, …
The natural number n is identified with the expression O_n. Equality is defined via Leibniz's
principle: x = y ⟺ ∀p: p(x) ↔ p(y). VR has been shown to be arithmetically equivalent to Peano
arithmetic, and consistent relative to ZF.

Ontological Status.
In VR, the only ontological primitive is ∅. All other objects of the system — including the natural
numbers themselves — arise as operational results of applying the succession operator t to ∅. The
natural number O_n is not an independent existing thing; it is the result of n applications of t to ∅.
The mathematical content of n is its operational history.
This ontological position is the foundation of the present work. It asserts a minimal ontology —
only ∅ exists — and treats all other numerical constructions as operations of progressively greater
depth performed on this single primitive.


## Part II. Integers ℤ as an Operational Superstructure

We construct integers as formal expressions over ℕ with prescribed equivalence and operations.

II.1. The Formal Language of Subtraction
We extend the language of VR by a binary symbol ⊖. An expression of the form
a ⊖ b, where a, b ∈ ℕ
is a syntactic object intended to denote the operation "subtract b from a". This is not an ordered
pair, but a formal record of an operation.

II.2. Equivalence Relation
Two expressions are declared equivalent when they would yield the same result, using only the
addition operation already defined on ℕ :
a ⊖ b ≈ c ⊖ d ⟺ a + d = b + c.
This relation is reflexive, symmetric, and transitive (direct verification using the commutativity
and associativity of addition in ℕ , established in VR).

II.3. Operations
Addition.
(a ⊖ b) ⊕ (c ⊖ d) := (a + c) ⊖ (b + d).

Multiplication.
(a ⊖ b) ⊗ (c ⊖ d) := (a×c + b×d) ⊖ (a×d + b×c).

Additive Inverse.
⊖(a ⊖ b) := b ⊖ a.

Subtraction.
(a ⊖ b) ⊟ (c ⊖ d) := (a + d) ⊖ (b + c).
Remark. Subtraction is definable through addition and additive inverse: (a ⊖ b) ⊟ (c ⊖ d) = (a ⊖ b)
⊕ ⊖ (c ⊖ d). We list it explicitly for convenience.
All operations are well-defined on equivalence classes.

II.4. Canonical Form
Every expression a ⊖ b can be canonized uniquely:
If a ≥ b, the canonical form is (a − b) ⊖ 0.
If a < b, the canonical form is 0 ⊖ (b − a).

II.5. Embedding ℕ → ℤ_VR
The natural number n ∈ ℕ embeds into ℤ _VR as the class of n ⊖ 0.

II.6. Isomorphism Theorem
Theorem. The set ℤ _VR of equivalence classes of expressions a ⊖ b with operations ⊕, ⊗, ⊟ is a
commutative ring with unit, isomorphic to the standard ring of integers ℤ .
Proof sketch. Define φ: ℤ _VR → ℤ by φ([a ⊖ b]) = a − b. This map is well-defined on classes,
respects operations, and is bijective.


## Part III. Rationals ℚ as an Operational Superstructure

Rational numbers are constructed analogously to integers, but over ℤ _VR.
III.1. The Formal Language of Division
We introduce a binary symbol ⊘. An expression of the form
a ⊘ b, where a, b ∈ ℤ _VR and b ≠ 0_ℤ
is a syntactic object denoting the operation "divide a by b". The restriction b ≠ 0_ ℤ is syntactic and
is effectively decidable via the canonical form in ℤ _VR.

III.2. Equivalence Relation
a ⊘ b ≈_ℚ c ⊘ d ⊗ a ⊗ d ≈ b ⟺
⊗ c,
where ℤ is the multiplication operation in ℤ_VR.

III.3. Operations
Addition.
(a ⊘ b) ⊞ (c ⊘ d) := (a ⊗ d ⊕ b ⊗ c) ⊘ (b ⊗ d).

Multiplication.
(a ⊘ b) ⊠ (c ⊘ d) := (a ⊗ c) ⊘ (b ⊗ d).

Subtraction.
(a ⊘ b) ⊟⊘ (c ⊘ d) := (a ⊗ d ⊟ b ⊗ c) ⊘ (b ⊗ d).

Division.
(a ⊘ b) ⊘⊘ (c ⊘ d) := (a ⊗ d) ⊘ (b ⊗ c), provided c ≠ 0_ℤ.

III.4. Canonical Form
Every fraction a ⊘ b can be brought to canonical form by making the denominator positive and
reducing to lowest terms.

III.5. Embedding ℤ → ℚ_VR
The integer a ∈ ℤ _VR embeds into ℚ _VR as the class of a ⊘ 1_ ℤ , where 1_ ℤ = 1 ⊖ 0 is the
multiplicative identity in ℤ _VR.

III.6. Isomorphism Theorem
Theorem. ℚ _VR with operations ⊞, ⊠, ⊟⊘, ⊘⊘ is a field, isomorphic to the standard field of
rationals ℚ .

## Part IV. Real Numbers ℝ via Cauchy Sequences

Real numbers require a qualitatively different construction: while ℤ and ℚ are syntactic
constructions over finite expressions, ℝ requires infinite processes.

IV.1. Functions as Operational Rules
We extend the language of VR by the notion of function ℕ → ℚ _VR. A function a: ℕ → ℚ _VR is
an operational rule: a finite description (algorithm) producing, for each n ∈ ℕ , a value a(n) ∈
ℚ _VR. Functions are not introduced as sets of ordered pairs; they are operational primitives —
finite specifications of infinite correspondences.
A consequence of this definition is that each function is fully captured by its finite description. The
collection of all such finite descriptions is itself operationally countable: any function in VR-
Numbers can be enumerated through its description. This will have implications for the
relationship between ℝ _VR and the classical ℝ , discussed below.
Operationally, a function ℕ → ℚ _VR is a partial recursive function in the sense of Church–
Turing, or equivalently a Type-2 computable function in the framework of computable analysis
(Weihrauch, 2000). The construction ℝ _VR therefore coincides with the standard development of
computable real numbers via computable Cauchy sequences (Pour-El & Richards, 1989). The
novelty here is not technical but ontological: in VR-Numbers, this is not one approach among
several but the only available approach, dictated by the operational ontology.

IV.2. Fundamental (Cauchy) Sequences
A function a: ℕ → ℚ _VR is fundamental (a Cauchy sequence) if:
∀ε ∈ ℚ_VR, ε > 0, ∃N ∈ ℕ such that ∀m, n ≥ N: |a(m) ⊟⊘ a(n)| < ε.

IV.3. Equivalence of Sequences
a ≈_C b ⟺ ∀ε > 0, ∃N: ∀n ≥ N: |a(n) ⊟⊘ b(n)| < ε.

IV.4. The Construction ℝ_VR
ℝ _VR is defined as the set of equivalence classes of fundamental sequences with respect to ≈_C.

IV.5. Operations
Operations are defined componentwise on representatives:
[a] ⊕_ℝ [b] := [c], where c(n) = a(n) ⊞ b(n);
[a] ⊗_ℝ [b] := [c], where c(n) = a(n) ⊠ b(n);
[a] ⊟_ℝ [b] := [c], where c(n) = a(n) ⊟⊘ b(n);
[a] ⊘_ℝ [b] := [c], where c(n) = a(n) ⊘⊘ b(n).
IV.6. Embedding ℚ → ℝ_VR
Each rational q ∈ ℚ _VR embeds into ℝ _VR as the class of the constant sequence a(n) = q for all
n.

IV.7. Isomorphism Theorem
Theorem. ℝ _VR is a real closed ordered field. It is isomorphic to the field of computable real
numbers — a countable subfield of the classical real line ℝ — and contains all reals that admit a
finite algorithmic description.
Remark. Strictly speaking, ℝ _VR is not isomorphic to the entire classical ℝ . Classical ℝ has
cardinality of the continuum; ℝ _VR, consisting of operational rules each given by a finite
description, is countable. The relationship is therefore: ℝ _VR is isomorphic to the computable
reals, which constitute a countable real closed subfield of classical ℝ . All real numbers
encountered in practice — algebraic numbers, rationals, π, e, and indeed any real definable by a
finite description — are captured by ℝ _VR. Non-computable reals of classical ℝ have no place in
the operational ontology of VR-Numbers, as they correspond to no finite algorithmic description.
This aligns VR-Numbers with the constructive tradition (Bishop, 1967; Martin-Löf, 1984) and
remains consistent with the philosophical position that mathematical objects are operations, not
transcendent entities.

IV.8. Operational Character of ℝ
A real number in VR is, formally, an algorithm — a finite description specifying how to compute
arbitrarily close rational approximations. The square root of 2, for instance, is represented by an
algorithm (such as Newton's method) that, given any precision, produces a rational approximation
within that precision. This view aligns naturally with constructive mathematics.


## Part V. Complex Numbers ℂ via the Duality of A1

The construction of complex numbers introduces the central new conceptual element of this work.
In standard mathematics, ℂ is built as ordered pairs of real numbers (a, b) with a special
multiplication rule, and the two-dimensionality of ℂ is postulated through the choice of pairs. We
propose instead that the two-dimensionality of ℂ is structurally grounded in the logical foundation
of VR — specifically, in the duality present in axiom A1.

V.1. The Duality of A1
Axiom A1 of VR states:
F → F = ⊤,
F → ⊤ = ⊤.
These are two distinct generating facts: F generates both values via implication. The two
implications represent two distinct movements from F:
F → F: a movement returning to F itself (self-reference at the logical level).
F → ⊤: a movement to the opposite value ⊤.
We propose to interpret these two implications as two independent axes of numerical extension.

V.2. The Two Axes
The axis F → F is the real axis: along this axis, the constructions ℕ → ℤ → ℚ → ℝ developed
above unfold.
The axis F → ⊤ is the imaginary axis: along this axis, new operational expressions of the form b·i
live, where i is an operational marker indicating the imaginary axis.
The marker i is not a number nor an object — it is a syntactic indicator of which axis a value
belongs to.

V.3. The Joining Rule
To make ℂ a single algebraic structure rather than two disjoint copies of ℝ , the two axes must be
coupled. This coupling is captured by the rule:
i ⊗ i := ⊖1.
This rule is postulated as an axiom of joining: applying the imaginary marker twice is equivalent to
negation along the real axis. Without this rule, the two axes would remain independent; with it,
they are intertwined into the algebraic structure of ℂ .

V.4. Complex Numbers as Operational Expressions
A complex number is a formal expression
a ⊕ b·i, where a, b ∈ ℝ _VR.
This is not an ordered pair (a, b). It is a syntactic record of two values along two distinct axes.

V.5. Equivalence
a ⊕ b·i ≈ c ⊕ d·i ⟺ a = c (in ℝ_VR) and b = d (in ℝ_VR).

V.6. Operations
Addition.
(a ⊕ b·i) ⊕_ℂ (c ⊕ d·i) := (a ⊕ c) ⊕ (b ⊕ d)·i.

Multiplication (using i ⊗ i = ⊖1).
(a ⊕ b·i) ⊗_ℂ (c ⊕ d·i) := (a⊗c ⊟ b⊗d) ⊕ (a⊗d ⊕ b⊗c)·i.
Conjugation.
conj(a ⊕ b·i) := a ⊕ (⊖b)·i.

Modulus.
|a ⊕ b·i| := √(a⊗a ⊕ b⊗b).

V.7. Embedding ℝ → ℂ_VR
Each real a ∈ ℝ _VR embeds into ℂ _VR as the expression a ⊕ 0·i.

V.8. Isomorphism Theorem
Theorem. ℂ _VR with the operations defined above is a field, isomorphic to the standard field of
complex numbers ℂ (with ℝ replaced by ℝ _VR; the resulting field is isomorphic to the field of
computable complex numbers).

V.9. Discussion: Foundation of Two-Dimensionality
In the standard treatment, the dimensionality of ℂ is a postulate: ℂ is defined as ℝ × ℝ with a
specific multiplication, and there is no deeper justification for why ℂ has exactly two dimensions.
In VR-Numbers, the two-dimensionality of ℂ is structurally grounded in the logical foundation of
the system. Axiom A1 contains exactly two generating implications, F → F and F → ⊤. These two
implications correspond to two distinct axes of numerical construction. The dimensionality of ℂ is
therefore not arbitrary; it reflects the dual generative structure already present in the logical layer of
VR.
Scope of this claim. The duality of A1 provides two distinct generative directions but does not by
itself entail their algebraic coupling. The rule i² = ⊖1 is an additional postulate joining the two axes
into a single field. Thus A1 motivates the two-dimensionality of ℂ ; the field structure on these two
dimensions requires the joining axiom. The conceptual content of the claim is that the two-
dimensionality is not arbitrary — it has a logical origin — not that the entire algebraic structure of
ℂ is derivable from A1 alone.
Position relative to higher-dimensional algebras. The duality of A1 yields exactly two generative
directions at the logical level. The theorems of Frobenius (1878) and Hurwitz (1898) show that
further normed division algebras over ℝ — quaternions ℍ and octonions 𝕆 — require successive
weakening of algebraic properties (commutativity, then associativity). This is consistent with the
position that A1 as a logical primitive does not further subdivide: extensions beyond ℂ require
leaving the purely logical layer and accepting algebraic compromises. Whether such higher-
dimensional algebras admit analogous derivations from deeper logical structure remains an open
question (see Part VII).
This conceptual claim — that the structure of complex numbers is not arbitrary but reflects how
implication operates on falsity — is the principal philosophical contribution of the present work.
The two generating movements from F (one returning to F itself, one moving to ⊤) are precisely
the two axes that, when joined by the rule i² = ⊖1, yield the field of complex numbers.


## Part VI. The Ontological Position of VR-Numbers

VR-Numbers adopts a minimal ontology: the only ontological primitive is the void ∅. All other
objects — natural, integer, rational, real, and complex numbers — are operational constructions of
progressively greater depth performed over ∅.

VI.1. The Single Ontological Primitive
∅ is the unique ontological primitive of the system. It is given as Leibnizian initial datum — that
which is, prior to any operation, division, or distinction. Every other object of VR or VR-Numbers
is the result of operations applied to ∅.
The succession operator t is not itself an object but a rule of operation. The natural numbers O_n =
t^n(∅) are records of successive applications of t. Their content is fully captured by their
operational history: O_3 is "three applications of t to ∅", and this is the totality of what O_3 is.

VI.2. Depths of Operationality
All numerical systems constructed in this work are operational, but they exhibit different depths of
operational character:


```
 System              Operational Character
 ∅                   The single ontological primitive — that which is, prior to all operation
 ℕ                   Direct applications of t to ∅: O_n = t^n(∅)
 ℤ                   Finite syntactic expressions a ⊖ b over ℕ, on the F → F axis
 ℚ                   Finite syntactic expressions a ⊘ b over ℤ , on the F → F axis
 ℝ                   Algorithms producing infinite sequences of rationals, on the F → F axis
 ℂ                   Two-axis syntax over F → F and F → ⊤, joined by i² = ⊖1
```

VI.3. Operational Infinity
The axiom A4 of VR — the principle of induction — is conventionally read as postulating actual
infinity: the completed totality of all natural numbers existing as an object. We reject this reading.
Within the ontological position of VR-Numbers, A4 does not assert the existence of any infinite
object. It formulates an operational principle: any property holding for ∅ and preserved under
application of t holds for every result of iterated application of t. The quantifier "for all n" in A4 is
operational, not ontological — it expresses universal applicability of an operation, not membership
in a completed set.
We call this operational infinity, in contrast to the classical notion of actual infinity. Operational
infinity is mathematically equivalent to actual infinity: every theorem provable using actual
infinity in classical mathematics is provable using operational infinity in VR-Numbers. The two
notions agree on consequences. They differ in ontological status: actual infinity asserts that an
infinite totality exists as an object; operational infinity asserts only that an infinite operation is
available.
This distinction is significant. The chief philosophical objection to actual infinity, raised since
Aristotle and reformulated by intuitionists and constructivists, is the rejection of completed
infinities as objects. Operational infinity bypasses this objection: it does not postulate that the
totality of natural numbers is a thing. It postulates that the procedure of unbounded counting from
∅ is available to us, and that any property preserved by this procedure applies universally. The
resulting mathematics is the same; the ontological commitment is minimal.
Within VR-Numbers, all references to "infinite" objects — the natural numbers ℕ as a domain, the
integers ℤ , the rationals ℚ , the reals ℝ as Cauchy sequences, the complex numbers ℂ — are to be
understood operationally. None of these collections is an object. Each is a domain of applicability
for operations defined over ∅.
Accordingly, the quantifier notations used throughout this work — expressions of the form "a, b ∈
ℕ " or "∀ε ∈ ℚ _VR, ε > 0" — are operational. They mean: "for any concrete expression of the
indicated form". They do not assert the existence of ℕ or ℚ _VR as completed objects. The set-
theoretic notation is retained for convenience and conformity with standard mathematical practice;
the ontological content is operational throughout.
Note on terminology. Throughout this work, set-theoretic vocabulary ("equivalence class", "set",
"field", "subfield") is retained for conformity with standard mathematical practice. Within the
operational ontology of VR-Numbers, every such phrase is to be read operationally: an
"equivalence class" is the operational rule for recognizing equivalence, not a completed object
containing its members; a "field" is the closed system of operations and their results, not a
completed collection of values. The forthcoming work VR-Sets will provide the operational
reconstruction of set-theoretic vocabulary itself. Until then, the standard vocabulary is used with
the operational reading understood.

VI.4. The Gradient of Operationality
The structure of VR-Numbers is a gradient: each successive numerical system corresponds to a
deeper operational construction over ∅.
Natural numbers are the most direct operational result: a single operator t is applied repeatedly to
the primitive ∅.
Integers and rationals introduce a layer of formal syntax: expressions over natural numbers, with
equivalence relations defining when distinct expressions denote the same operational result.
Real numbers add infinite operational depth: each real number is itself a finite description
(algorithm), but the operation it specifies is infinite — producing arbitrarily close rational
approximations.
Complex numbers add a second axis: the duality of A1 generates two independent operational
directions, and ℂ is the syntactic structure on these two axes joined by the multiplication rule.
This gradient reflects the historical development of mathematics. Natural numbers have been
recognized in all cultures since antiquity, while negative, rational, real, and complex numbers were
progressively introduced as the operational needs of mathematics demanded them. The conceptual
difficulty historically accompanying each extension — numeri ficti for negatives, the irrationality
crisis in Greek mathematics, the long dispute over imaginary numbers — reflects, in retrospect, the
increasing operational depth of these constructions.

VI.5. What Does Not Exist as an Object
In VR-Numbers, the following are not introduced as ontological objects:
Ordered pairs. Pairs appear nowhere in the construction as independent objects; pairing is
replaced by syntactic juxtaposition (a ⊖ b, a ⊘ b, a ⊕ b·i).
Negative numbers. The integer −3 is a notation for the operational class {n ⊖ (n+3) : n ∈
ℕ }, not an independent thing.
Fractions. The rational 1/2 is a notation for the class of equivalent division expressions, not
a separate object.
Real numbers. A real number is an equivalence class of Cauchy sequences, which are
themselves operational rules — finite specifications of infinite processes — not sets of
ordered pairs.
Complex numbers. A complex number is a syntactic expression over two operational axes,
not a two-dimensional point in a plane.
This minimalism is the philosophical position of VR-Numbers: only ∅ is. All else is doing.

VI.6. Consistency Relative to ZF
Each construction (ℤ _VR, ℚ _VR, ℂ _VR) is isomorphic to its standard counterpart. The field of
computable real numbers is a definable subfield of ℝ in ZF (Pour-El & Richards, 1989), and
ℝ _VR is isomorphic to it; therefore ℝ _VR has a ZF-model. Combined with the standard ZF-
models for ℤ , ℚ , ℂ and the consistency of VR relative to ZF [Reznik 2026], the full system of VR-
Numbers is consistent relative to ZF.

## Part VII. Open Questions

(1) Formalization in Type Theory.
The constructions of VR-Numbers — particularly the operational view of functions in the
definition of ℝ , and the operational marker i in ℂ — are naturally suited to constructive type
theories such as Martin-Löf's. A formalization in Coq, Agda, or Lean would provide machine
verification and explicit categorical semantics.

(2) Algebraic Closure Beyond ℂ.
By the Fundamental Theorem of Algebra, ℂ is algebraically closed. The theorems of Frobenius
(1878) and Hurwitz (1898) further show that ℂ is the largest finite-dimensional commutative
associative normed division algebra over ℝ — quaternions ℍ and octonions 𝕆 require successive
weakening of algebraic properties. Whether these higher-dimensional algebras admit analogous
derivations from deeper logical structure — and whether such structure could be located in VR-
style logical primitives — remains an open question.

(3) The VR-Sets Program: Operational Set Theory.
A natural extension of the operational ontology is an operational reconstruction of set theory itself,
provisionally named VR-Sets. The central idea is that the membership relation x ∈ y admits an
operational reading as "x was used in the construction of y", distinguishing reference from
physical containment. Under this reading, the expression x ∈ x is not paradoxical: it expresses that
x is a result of an operation referring to its own name, analogous to recursive structures in
programming. This opens a possible unification of well-founded (ZFC-mode) and non-well-
founded (ZFA-mode) set theories as two operational modes of a single system, with bisimulation
(Aczel, 1988) as the natural equivalence criterion in the ZFA-mode. The technical development of
VR-Sets — including the operational reformulation of the ZF axioms, the status of the axiom of
choice in operational vs. non-operational regimes, and the relationship between A1's duality and
Tarski's theorem on the undefinability of truth — is the subject of forthcoming work.

(4) Computational Realization.
Each level of VR-Numbers admits a direct computational realization, making the system suitable
as a foundation for exact-arithmetic computation systems.


## Part VIII. Notes from the Lean 4 Formalisation

The constructions of Parts II–V have been formalised in Lean 4 (Reznik, 2026, DOI
10.5281/zenodo.20352057), building on the prior formalisation of Part I (Reznik, 2026, DOI
10.5281/zenodo.20324240). The formalisation comprises approximately 3,600 lines of Lean code
across four files (Integers.lean, Rationals.lean, Reals.lean, Complex.lean), with no use of sorry or
admit. All axiom dependencies are documented. The formalisation surfaced several observations
that refine or extend the preprint’s account. The present Part collects eight of these, organised into
three groups: hidden lemmas (observations the preprint absorbs into phrases like “direct
verification”), structural boundaries (places where the formalisation makes visible a transition that
the preprint addresses qualitatively), and methodological patterns (recurring tactical choices that
maintain the axiom-minimality of the formalisation). These observations do not alter any axiom,
definition, or theorem of Parts I–VII; they document the relation between the preprint and its Lean
realisation.

VIII.1. Hidden lemma in §II.2: cancellation of addition
Section II.2 establishes reflexivity, symmetry, and transitivity of the equivalence a ⊖ b ≈ c ⊖ d in a
single phrase: “direct verification using the commutativity and associativity of addition in ℕ .” In
the Lean formalisation this phrase splits into three steps of unequal structural cost. Reflexivity
reduces to one application of T1 (commutativity). Symmetry requires two applications of T1 in a
chain. Transitivity, however, requires a separate lemma not stated in T1–T4: the right cancellation
law for addition on VR-naturals: a + c = b + c → a = b. This is not a consequence of T1–T4 by
rewriting; it is proved by induction on c using the injectivity of the successor (the Peano principle
P4 of Part I). The preprint absorbs this cancellation into the phrase “direct verification”; the
formalisation factors it out as an explicit lemma whose proof retraces the inductive structure of ℕ .

VIII.2. Hidden lemma in §II.3: left distributivity of multiplication
Theorem T3 of Part I states right distributivity: a × (b + c) = a×b + a×c. The symmetric left
distributivity (a + b) × c = a×c + b×c is not in T1–T4 and is not derivable by T3 alone, since
commutativity of multiplication is not among T1–T4 either. In informal mathematics the two
forms are interchanged silently. In the Lean formalisation, the proof of well-definedness of
multiplication on integers (§II.3) requires left distributivity explicitly; we prove it by induction on
the right argument using T3 and a combinatorial swap lemma. The observation is twofold: (i) the
preprint’s T1–T4 do not commit to commutativity of multiplication on ℕ , and (ii) the
formalisation makes this restraint visible by requiring an additional lemma at the first place where
it matters.

VIII.3. Hidden lemma in §III.2: multiplicative cancellation as a nonzero
condition
Transitivity of the equivalence a ⊘ b ≈ c ⊘ d (§III.2) relies on the cancellation law xz = yz → x = y
when z ≠ 0 — the integral-domain property of ℤ . The preprint states the transitivity as “direct
verification using multiplication in ℤ _VR.” In Lean this expands into three technical components:
(i) propagation of the nonzero condition through the isomorphism ℤ _VR ≅ ℤ ; (ii) a cancellation
lemma for ℤ itself, which we prove constructively via the absolute value Int.natAbs without
invoking mathlib’s general IntegralDomain infrastructure (which would pull in Classical.choice
unnecessarily); and (iii) a factored polynomial identity, proved by ring, in place of the
linear_combination tactic. The observation: integral-domain cancellation on ℤ is constructive in
itself; the dependence on Classical.choice appears only through the infrastructural generality of
mathlib, not through the cancellation property at this concrete type.
VIII.4. Structural boundary: Classical.choice between ℤ and ℚ
The formalisation of ℤ _VR (Parts II of the preprint) is fully constructive: every theorem depends
only on the standard quotient axiom Quot.sound (and propositional extensionality propext). At
ℚ _VR the situation changes: every theorem mentioning addition or multiplication on rationals
depends on Classical.choice. The reason is structural to Lean 4 Core: the Rat type carries a field
reduced : num.natAbs.Coprime den, so every Rat.add and Rat.mul normalises its result through a
coprimality proof that depends on Classical.choice via Nat.gcd. This dependency is not introduced
by the formalisation; it cannot be removed by lemma substitution or tactic choice. The classical-
versus-constructive boundary in this formalisation therefore falls between ℤ _VR and ℚ _VR. This
is a structural feature of Lean 4 Core’s representation of rationals, not a property of the rationals
themselves: an alternative Rat without normalisation (a plain quotient of pairs) would remain
constructive. The boundary corresponds precisely to the transition from operations performed
syntactically (a + b on ℤ ) to operations requiring a canonical representative (gcd-reduction of a/b
on ℚ ) — the same transition that §VI.4 describes informally as a deepening of operationality.

VIII.5. Structural boundary: the quotient construction becomes vacuous at ℂ
Each of ℤ _VR, ℚ _VR, and ℝ _VR is built by the same three-step pattern: a syntactic record, a
nontrivial equivalence relation, and a quotient. The equivalence collapses syntactically distinct
representatives into one mathematical object (cross-addition, cross-multiplication, Cauchy ε-
convergence). At ℂ _VR the equivalence degenerates: a ⊕b·i ≈ c ⊕d·i iff a = c and b = d (§V.5) —
componentwise equality, which in the formalisation coincides with Lean’s built-in equality on a
two-field structure. The quotient becomes vacuous, and ℂ _VR is the first type in the cycle realised
without Quotient. The methodological cost of the quotient construction, distributed silently across
ℤ , ℚ , ℝ , becomes visible at ℂ by its absence. Substantively: the depth of operationality at ℂ _VR
(§VI.4) is carried not by the equivalence relation but by the two-dimensionality grounded in A1
and the joining rule i² = ⊖1 (§V.3, §V.9).

VIII.6. Structural boundary: inexpressibility of computability on ℝ_VR
Section IV.1 stipulates that functions ℕ → ℚ _VR are operational rules — finite descriptions
producing the values. Section IV.7 then concludes that ℝ _VR is isomorphic to the field of
computable real numbers, a countable subfield of classical ℝ . The Lean type Nat → ℚ _VR,
however, contains every total Lean function of that signature, including those whose existence
requires Classical.choice; this type has the cardinality of the continuum. The formalisation
therefore proves an isomorphism between ℝ _VR and the full classical ℝ , not the computable
subfield. Lean 4 has no type-level predicate distinguishing computable from non-computable
functions; the operational restriction of §IV.1 is metatheoretic relative to Lean. Within the present
cycle (VR-Numbers) the recommended interpretation is: the formalisation reflects faithfully the
construction of ℝ _VR via Cauchy sequences (§IV.1–§IV.6), and additionally proves a structural
isomorphism with classical ℝ ; the restriction to computable reals (§IV.7) is preserved as
metatheoretic commentary. This is a concrete instance where the VR ontology is strictly stronger
than Lean 4 can express in a single type construction. The forthcoming VR-Forms provides a
formal register in which the relation between operational and non-operational objects can be
addressed directly.

VIII.7. Methodological pattern: tactics cleaner than named lemmas
Several lemmas in mathlib carry latent Classical.choice dependencies through algebraic typeclass
infrastructure: mul_zero, zero_mul, mul_right_cancel₀, linarith on integers, and the
linear_combination tactic itself all introduce Classical.choice when used on concrete numeric
types. The same statements can be discharged on those concrete types by tactics that act directly on
the type (ring, omega, manual factored identities) without invoking the general infrastructure, and
remain Classical-free. The pattern recurred at least four times during the formalisation of Parts II
and III. The lesson is counter-intuitive: a tactic appears to be less explicit than a named lemma, but
on concrete numeric types it is often more axiom-minimal, because it bypasses the typeclass
generality where Classical.choice resides. For axiom-minimal formalisation on concrete number
systems, prefer tactics to named algebraic lemmas; the symbolic gain of an explicit lemma may
come at the cost of an additional axiom in the dependency closure.

VIII.8. Methodological pattern: change vs simp for definitional equality
At three independent points in the formalisation of ℝ _VR (Part IV), automatic simplification
(simp) drove the goal into a form syntactically incompatible with the intended rewrite: the strict
order on Rat unfolded through a boolean comparison (Rat.blt) breaking the typeclass for less-than;
abs_neg under simp triggered a ring-normalisation that hid the rewrite target; Real.mk_eq under
simp reshaped the ε-distance into a form using a different CauSeq operator. In each case the
resolution was the same: replace simp-driven unfolding with the change tactic, which restates the
goal in a definitionally equal but syntactically intended form without performing any reduction.
The pattern is related to VIII.7: in both cases, less automation (a weaker tactic) yields a more stable
proof than more automation (simp, named lemma) precisely because it preserves syntactic control
over the goal. For a formalisation aiming at axiom-minimality and proof stability, the lighter tactic
is preferable where it suffices.


## Summary

VR-Numbers extends the formal system VR with operational superstructures yielding ℤ , ℚ , ℝ ,
and ℂ . The work advances three principal theses:
First, a minimal ontology: the single ontological primitive is the void ∅; all other objects,
including the natural numbers, arise as operations of progressively greater depth performed over
∅. No ordered pairs are introduced as ontological objects.
Second, actual infinity is replaced by operational infinity: the axiom of induction A4 is read as an
operational principle expressing universal applicability of an operation, not as a postulate of a
completed infinite totality. The two notions agree on mathematical consequences but differ in
ontological commitment.
Third, the two-dimensionality of ℂ is structurally grounded in the duality of axiom A1: the two
generating implications F → F and F → ⊤ correspond to the real and imaginary axes, respectively.
The algebraic coupling of the two axes through i² = ⊖1 is an additional joining axiom; A1
motivates the two-dimensionality, while the field structure requires the joining rule. This provides
an ontological motivation for a feature standardly postulated through pairs without deeper
justification.
The structures ℤ _VR, ℚ _VR, ℂ _VR are isomorphic to their standard counterparts; ℝ _VR is
isomorphic to the field of computable real numbers (a countable subfield of classical ℝ ), reflecting
the constructive position of the work. The consistency of the system relative to ZF follows from the
consistency of VR established in [Reznik 2026] and from the standard ZF-definability of the
computable real numbers (Pour-El & Richards, 1989). The philosophical position is minimal: only
∅ is — all else is doing.


## References

Aczel, P. (1988). Non-Well-Founded Sets. CSLI Lecture Notes 14. Stanford: Center for the Study
of Language and Information.
Bishop, E. (1967). Foundations of Constructive Analysis. New York: McGraw-Hill.
Boolos, G. S., Burgess, J. P., & Jeffrey, R. C. (2007). Computability and Logic (5th ed.).
Cambridge: Cambridge University Press.
Cauchy, A.-L. (1821). Cours d'analyse de l'École royale polytechnique. Paris: Imprimerie Royale.
Dedekind, R. (1872). Stetigkeit und irrationale Zahlen. Braunschweig: Vieweg.
Frobenius, G. (1878). Über lineare Substitutionen und bilineare Formen. Journal für die reine und
angewandte Mathematik, 84, 1–63.
Hamilton, W. R. (1837). Theory of Conjugate Functions, or Algebraic Couples; with a Preliminary
and Elementary Essay on Algebra as the Science of Pure Time. Transactions of the Royal Irish
Academy, 17, 293–422.
Hurwitz, A. (1898). Ueber die Composition der quadratischen Formen von beliebig vielen
Variablen. Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen, Mathematisch-
Physikalische Klasse, 1898, 309–316.
Martin-Löf, P. (1984). Intuitionistic Type Theory. Naples: Bibliopolis.
Mendelson, E. (2015). Introduction to Mathematical Logic (6th ed.). Boca Raton: Chapman and
Hall/CRC.
von Neumann, J. (1923). Zur Einführung der transfiniten Zahlen. Acta Litterarum ac Scientiarum,
1, 199–208.
Pour-El, M. B., & Richards, J. I. (1989). Computability in Analysis and Physics. Berlin: Springer.
Reznik, V. (2026). VR. A Formal System: A Minimalist Axiomatization of Arithmetic Grounded
in Leibnizian Void. Zenodo. DOI: 10.5281/zenodo.20212092.
Reznik, V. (2026). VR. A Formal System: A Lean 4 Formalisation of Part I. Zenodo (Software).
DOI: 10.5281/zenodo.20324240.
Reznik, V. (2026). VR-Numbers: A Lean 4 Formalisation of Parts II–V. Zenodo (Software). DOI:
10.5281/zenodo.20352057.
Weihrauch, K. (2000). Computable Analysis: An Introduction. Berlin: Springer.
