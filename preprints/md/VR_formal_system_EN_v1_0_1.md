VR. A Formal System.
A Minimalist Axiomatization of Arithmetic Grounded in Leibnizian Void
Vitaly Reznik
2026 — Version 1.0.1


## Abstract

We present a formal axiomatic system VR with three primitives { ∅, →, t} and four axioms. The
von Neumann natural numbers are constructed as the unfolding of the succession operator t from
the initial void ∅. Equality and distinctness are defined via Leibniz's principle and are not
among the primitives. We show that VR is arithmetically equivalent to Peano arithmetic (PA),
from which the consistency of VR relative to ZF set theory follows.

**Keywords:** axiomatic arithmetic, foundations of mathematics, Leibnizian equality, von Neumann

ordinals, Peano arithmetic, consistency.
Version 1.0.1 (2026) adds three editorial notes reflecting the Lean 4 formalisation of Part I,
published as a separate companion work (Reznik, 2026; Zenodo DOI
10.5281/zenodo.20324240). The notes do not alter any axiom, definition, or theorem; they
record points of methodological clarification that became visible only through formalisation.
See the closing Part IV.


## Part I. VR. The Formal System


### 1. Primitives

Constant: ∅.
Binary operator: → (implication).
Unary operator: t (succession).


### 2. Axioms

A1. Generativity.
F → F = ⊤ and F → ⊤ = ⊤, where F is identified with ∅ at the logical level, and ⊤ is defined
as F → F. From F, via →, both values {F, ⊤} are reachable. From ⊤, via →, only ⊤ is
reachable.

A2. Implication.
→ is a function of type {F, ⊤} × {F, ⊤} → {F, ⊤}, given by the classical truth table:
F→F=⊤
F→⊤=⊤
⊤→F=F
⊤→⊤=⊤

A3. Succession.
The operator t is defined on ∅ and on every object generated from it. For every x in the domain
of t:
t(x) = x ∪ {x}, so x ∈ t(x) and x ⊂ t(x).

A4. Induction.
If P is a property of objects of the system, and:
(i) P(O₀) holds,
(ii) for every x: P(x) → P(t(x)),
then P(O_n) holds for all n.
Equivalent formulation: the O_n exhaust all objects generated from ∅ via t.


### 3. Basis

{F, →} is functionally complete for classical two-valued logic over {F, ⊤}.
Derived operators:
¬x := x → F
x ∨ y := (x → y) → y
x ∧ y := ¬(¬x ∨ ¬y)
x ↔ y := (x → y) ∧ (y → x)


### 4. Definitions

Def. 1. ⊤ := F → F.
Def. 2. Leibnizian Equality. x = y := ∀p: p(x) ↔ p(y).1
Def. 3. Distinctness. x ≠ y := ¬(x = y).
Def. 4. The zeroth ordinal: O₀ := ∅.
Def. 5. Recursively: O_{n+1} := t(O_n) = O_n ∪ {O_n}.
Def. 6. The natural number n is identified with the ordinal O_n.

1
Note on the symbol ↔. In §3, ↔ is defined as a derived operator on {F, ⊤} (the truth-functional biconditional of
VR's logical layer). In Def. 2, the formula p(x) ↔ p(y) involves p ranging over properties of objects of the system;
for structural properties such as "contains x as an element" (used in §5, Theorems 3 and 4), p(x) and p(y) are
metatheoretic assertions about the system rather than values in {F, ⊤}. Accordingly, the ↔ in Def. 2 is to be read as
metatheoretic equivalence — distinct from the operator ↔ of §3 — in the same spirit as the schema interpretation
given in §10 for the PA-encoding. The formalization in Lean 4 makes this explicit by quantifying over predicates
valued in Prop.

### 5. Consequence of A3 and Def. 3

t(x) ≠ x for every x in the domain of t.
Proof. The property "contains x as an element" is true for t(x) (since x ∈ t(x) by A3) and false
for x (by the construction of objects via t from ∅). By Def. 3, t(x) ≠ x. ∎


### 6. Construction of von Neumann Numbers

O₀ = ∅
O₁ = t(O₀) = {∅}
O₂ = t(O₁) = {∅, {∅}}
O₃ = t(O₂) = {∅, {∅}, {∅, {∅}}}
...
Each O_n contains all preceding O₀, ..., O_{n−1} as elements.


### 7. Arithmetic

Def. 7. Addition.
a + O₀ := a
a + t(b) := t(a + b)

Def. 8. Multiplication.
a × O₀ := O₀
a × t(b) := (a × b) + a

Def. 9. Exponentiation.
a^{O₀} := t(O₀) = O₁
a^{t(b)} := a^b × a

Theorems (derived by induction via A4).
T1. Commutativity of addition: a + b = b + a.2
T2. Associativity: (a + b) + c = a + (b + c).
T3. Distributivity: a × (b + c) = (a × b) + (a × c).
2
Note on the structural asymmetry of T1. Addition is defined recursively in its second argument (Def. 7): a + O₀ :=
a; a + t(b) := t(a + b). The right-hand neutrality (a + O₀ = a) and right-hand succession (a + t(b) = t(a + b)) are
immediate by definition. The corresponding left-hand statements (O₀ + b = b and t(a) + b = t(a + b)) require
induction on b and constitute distinct lemmas. In informal mathematical exposition both directions are subsumed
under "by definition and symmetry"; in formal verification (Lean 4) the left-hand statements appear as two explicit
auxiliary lemmas without which the proof of T1 does not close. T2 (associativity) and T3 (distributivity), by
contrast, close by direct induction on the rightmost argument without auxiliary lemmas. T1 is therefore structurally
costlier than T2 and T3 — a fact obscured by the symmetric notation a + b = b + a but made explicit by the
asymmetry of Def. 7.
T4. O₁ + O₁ = O₂.


### 8. Structure of the System


```
 Level                   Content
 0. Primitives           ∅, →, t
 1. Axioms               A1, A2, A3, A4
 2. Logic                Classical two-valued (A1–A2)
 3. Equality and         Leibnizian (derived)
```

Distinctness

### 4. Objects              von Neumann ordinals O_n (A3 + A4)


### 5. Arithmetic           +, ×, ^ (A4)


## Part II. Equivalence of VR and Peano Arithmetic

In this part we show that VR is arithmetically equivalent to Peano arithmetic (PA). The
consistency of VR relative to ZF then follows as a direct consequence of the consistency of PA
relative to ZF.


### 9. Direction VR → PA

We show that all five Peano axioms are derivable in VR as theorems.

Peano Axioms (Standard Formulation).
P1. 0 ∈ ℕ.
P2. For every n ∈ ℕ, there exists S(n) ∈ ℕ.
P3. For every n ∈ ℕ: S(n) ≠ 0.
P4. For any n, m ∈ ℕ: if S(n) = S(m), then n = m.
P5. If K ℕ ℕ , 0 ∈ K, and for every n ∈ K: S(n) ∈ K, then K = ℕ .

Translation into the Language of VR.
ℕ ↦ {O_n : n ≥ 0}
0 ↦ O₀
S↦t

Theorem 1 (P1 in VR). O₀ is an object of the system.
Proof. By Def. 4: O₀ := ∅. By the statement of primitives of VR, ∅ is a constant of the system.
Therefore O₀ exists. ∎
Theorem 2 (P2 in VR). For every O_n, t(O_n) exists, and t(O_n) is an object of the
system.
Proof. By A3, the operator t is defined on ∅ and on every object generated from it. We show by
induction (A4) that t is defined on every O_n.
Base case: O₀ = ∅. By A3, t(∅) = ∅ ∪ {∅} exists.
Step: assume t(O_n) is defined. Then O_{n+1} := t(O_n) is an object generated from ∅ via t. By
A3, t is defined on every such object. Hence t(O_{n+1}) is defined.
By A4, t(O_n) is defined for all n, and t(O_n) = O_{n+1} by Def. 5. ∎

Theorem 3 (P3 in VR). For every n: t(O_n) ≠ O₀.
Proof. Consider the property p(x) := "x contains at least one element": p(x) ∃     ∈y: y ∈ x.
We have:
p(∅) = F (the empty set contains no elements),
p(t(O_n)) = ⊤ for every n (since O_n ∈ t(O_n) by A3).
The property p distinguishes t(O_n) and O₀ = ∅. By Def. 3, t(O_n) ≠ O₀. ∎

Theorem 4 (P4 in VR). If t(x) = t(y), then x = y.
Proof. Let t(x) = t(y). By A3: x ∪ {x} = y ∪ {y}.
By Def. 2, for every property q: q(x ∪ {x}) ↔ q(y ∪ {y}).
Take the property q_x(w) := "x ∈ w". We have q_x(x ∪ {x}) = ⊤ (since x ∈ {x} ⊂ x ∪ {x}).
From the equality x ∪ {x} = y ∪ {y} it follows that q_x(y ∪ {y}) = ⊤, that is, x ∈ y ∪ {y}.
By the definition of union: x = y or x ∈ y.
By symmetry, y ∈ x ∪ {x}, hence y = x or y ∈ x.
We show that the cases x ∈ y and y ∈ x are excluded for objects of VR. Chains of membership
in objects generated from ∅ via t are finite and terminate at ∅. Proof by induction via A4:
Base case: O₀ = ∅ has no elements.
Step: O_{n+1} = O_n ∪ {O_n}. Elements of O_{n+1} are either elements of O_n (chains finite
by induction) or O_n itself (the chain O_{n+1} ∋ O_n ∋ ... ∋ ∅ is finite).
Therefore cycles in ∈ are impossible in VR. Hence x ∈ y ∧ y ∈ x is excluded, and x = y. ∎

Theorem 5 (P5 in VR). The Peano induction axiom.
Proof. A4 literally states: if P(O₀) and for every x: P(x) → P(t(x)), then P(O_n) for all n. This is
precisely P5 in our notation. ∎

Corollary.
All Peano axioms (P1–P5) are derivable in VR as theorems. Therefore every theorem of PA that
depends on P1–P5 and classical first-order logic has a corresponding proof in VR.

### 10. Direction PA → VR

We show that every theorem of VR has a corresponding representation in PA via coding.

Method.
Encoding of VR objects as natural numbers of PA via arithmetization of syntax (Gödel
numbering). To each object of VR we assign a natural number:
∅:= 0,
⌜t(x)⌝ := a computable function of ⌜x⌝.
Under a suitable choice of encoding, ⌜O_n⌝ = n. The set-theoretic operations (∪, {·}, ∈) are
encoded as primitive recursive functions on natural numbers. This is standard technique; see
Mendelson, Introduction to Mathematical Logic; Boolos & Jeffrey, Computability and Logic.

Translation of VR Axioms into PA.
A1, A2 (logic): derivable in PA, since PA contains classical first-order logic.
A3 (t(x) = x ∪ {x}): expressible as a primitive recursive relation between ⌜x⌝ and ⌜t(x) ⌝.
A4 (induction): literally the induction axiom of PA.

Translation of Leibnizian Equality.
Equality ⌜x⌝ = ⌜y⌝ of natural numbers in PA corresponds to equality of objects in VR. The
quantifier "for all properties" in Def. 2 is interpreted as a schema over all arithmetical formulas
of PA.


### 11. Equivalence Theorem

From directions 9 and 10 we obtain:
Theorem. VR and PA are arithmetically equivalent: the ℕ-theoretic content of one system
corresponds bijectively to the ℕ-theoretic content of the other.


### 12. Consistency Relative to ZF

Peano arithmetic is consistent relative to ZF: the von Neumann model ℕ ⊆ ZF realizes all PA
axioms as ZF theorems. This is a classical result; see any standard textbook on set theory.
Corollary. VR is consistent relative to ZF.
Proof. VR is arithmetically equivalent to PA (Theorem 11). PA is consistent relative to ZF
(classical result). Therefore any contradiction in VR would entail a contradiction in PA, and
hence in ZF. If ZF is consistent, so is VR. ∎
The chain is established:
VR ↔ PA    ↪ ZF

## Part III. Open Questions

The established consistency of VR relative to ZF makes the system suitable for extensions. The
following remain open:

(1) Extensions of Number Systems.
Construction of integers ℤ, rationals ℚ, and reals ℝ on top of VR. The standard path involves
introducing ordered pairs (after Kuratowski), equivalence classes, Dedekind cuts, or Cauchy
sequences. This requires extending the language of VR with a pair construction.
Status (v1.0.1): Addressed in VR-Numbers (2026, DOI 10.5281/zenodo.20272743), where ℤ, ℚ,
ℝ, ℂ are constructed as operational superstructures over VR's natural numbers without ordered
pairs as ontological objects.

(2) Connection with Type Theory.
Formalization in the style of Martin-Löf, where t is the succ constructor, ∅ is the zero
constructor, and A4 is the Nat eliminator. Leibnizian equality naturally aligns with path equality
in homotopy type theory (HoTT). This would yield a ready categorical semantics: VR as an
initial t-algebra.

(3) Liar Paradox and Tarski's Theorem.
If VR is semantically closed, check the applicability of Tarski's undefinability theorem. A
possible direction is the construction of a level hierarchy via iteration of t (each application of t
creating a new level on which truth of the previous level can be discussed).

(4) Formalization in a Proof Assistant.
Implementation of VR in Coq, Agda, or Lean for machine verification of all derivations and
explicit construction of the VR → PA chain in a formally verifiable form.
Status (v1.0.1): Completed in Lean 4 as a separate companion publication (Reznik, 2026;
Zenodo DOI 10.5281/zenodo.20324240). See Part IV below.


## Part IV. Notes from the Lean 4 Formalisation

Part I of VR has been fully formalised in Lean 4 as a separate companion work (Reznik, 2026;
Zenodo DOI 10.5281/zenodo.20324240). The formalisation verifies every theorem of Part I by
the Lean kernel; no use is made of mathlib's arithmetic; every theorem is axiom-free in the sense
of Lean (does not depend on propext, Classical.choice, or Quot.sound). The complete proof
script and the axiom audit are in the companion repository.
This Part IV records, for the reader of the present preprint, six methodological observations made
visible by that formalisation. Formalisation is, in this work, an instrument of clarification rather
than a separate result. None of the observations invalidates anything in Parts I–III; each marks a
point where the formal layer is more revealing than informal exposition.

### 13. A4 is a theorem, not an axiom

In Part I, A4 (induction) is stated as an axiom. In the Lean formalisation, VR-objects are
introduced as an inductive type with two constructors (void and succ). The induction principle is
then the automatic recursor associated with this type, not a separate postulate. A4 becomes a
derivable theorem.
This is a methodological strengthening: what is postulated at the level of first-order axiomatic
exposition is a consequence of the way the universe of objects is constructed in type theory. The
expressive power gained by moving from first-order to typed logic absorbs A4 into the type
formation rule.


### 14. P1 and P2 are absorbed by typing

In the standard (untyped, first-order) formulation of Peano arithmetic, P1 ("0 ∈ ℕ") and P2 ("for
every n ∈ ℕ, there exists S(n) ∈ ℕ") are existential statements that require proof. Their force in
untyped logic comes from the need to assert membership in a domain.
In typed formalisation, both become type-level statements. P1 is realised by the fact that O 0 is a
well-typed term of the type of VR-objects. P2 is realised by the fact that the successor is a total
function on that type. Neither requires a theorem; both are facts of the syntax.
Of the five Peano axioms, only P3, P4 and P5 retain content as theorems in the typed setting; the
remaining two are dissolved into typing.


### 15. Theorem 11 admits a constructively stronger form

Part II establishes the arithmetical equivalence of VR and PA at the metatheoretical level: the ℕ-
theoretic content of one system corresponds bijectively to that of the other. The proof proceeds
by independently deriving each side's axioms in the other.
In Lean, the equivalence is realised as a structural isomorphism of types: an explicit pair of
functions O : ℕ → VRObj and O_inv : VRObj → ℕ together with proofs that they are mutually
inverse and that they preserve zero, successor, addition, multiplication, and exponentiation. From
this isomorphism the metatheoretical equivalence follows trivially: any theorem about one side
transfers along the bijection.
The Lean formulation is therefore a constructive witness to what Part II asserts as a non-
constructive correspondence between sets of theorems.


### 16. T1–T4 are not needed for the equivalence

Part II's narrative suggests that the equivalence with PA depends on having proved the standard
arithmetical theorems T1–T4 (commutativity, associativity, distributivity, and the concrete
identity O₁ + O₁ = O₂). The Lean formalisation shows that the isomorphism O (m + n) = vadd (O
m) (O n) and its analogues for × and ^ close by direct induction on the right-hand argument,
using only the recursive symmetry between Nat.add/vadd, Nat.mul/vmul, and Nat.pow/vpow.
T1–T4 are consequences of this symmetry on each side separately; they are not premises of the
isomorphism. The arithmetical equivalence rests on the shape of the recursions, not on the
algebraic identities that those recursions entail.

### 17. The symbol ↔ carries two distinct meanings

This is the point recorded in the footnote to Def. 2 and is repeated here for completeness.
In §3, ↔ is defined as a derived operator on {F, ⊤} — a truth-functional biconditional internal
to the logical layer of VR. In Def. 2, the formula p(x) ↔ p(y) involves p ranging over properties
of objects of the system; for the structural properties actually used in §5 and Theorems 3 and 4
("contains x as an element", "x ∈ w"), the assertions p(x) and p(y) are metatheoretic, not values
in {F, ⊤}.
The ↔ in Def. 2 is therefore a metatheoretic equivalence — the same equivalence that §10
invokes when interpreting the universal quantifier as a schema over arithmetical formulas. The
notation conflates two levels that the Lean formalisation distinguishes explicitly (the operator
viff on VRBool versus the proposition-level Iff).


### 18. The acyclicity of ∈ is structurally provable, without measure

The §5 proof that t(x) ≠ x appeals to the fact that "chains of membership in objects generated
from ∅ via t are finite and terminate at ∅". The phrase "finite" suggests that a measure (a
counting of nesting depth) is needed.
The Lean formalisation shows that no such measure is required. Antisymmetry of the
membership relation (x ∈ y → ¬(y ∈ x)) is provable by double structural induction on the VR-
object together with a single "descent" lemma stating that succ a ∈ b implies a ∈ b. Irreflexivity
(¬(x ∈ x)), and hence t(x) ≠ x, follows as a consequence of antisymmetry.
The acyclicity of ∈ in VR is therefore an intrinsic structural property of the inductive
construction, not a corollary of a finiteness theorem. No external arithmetic enters the proof.


## Summary

VR is a formal axiomatization with three primitives {∅, →, t} and four axioms. Equality and
distinctness are derived via Leibniz's principle. The von Neumann natural numbers are
constructed as the unfolding of succession from the initial void; induction guarantees the
completeness of this unfolding. Peano arithmetic is fully derived. Consistency relative to ZF is
established via arithmetical equivalence with PA.
The main content of VR is not the novelty of arithmetical results (it is equivalent to PA), but the
compactness and minimalism of its axiomatization with a transparent motivation for its
primitives: ∅ as Leibnizian initial givenness, → as the minimal logical operator, and t as the
generative operator of counting. All standard properties of the natural numbers are obtained from
these three primitives and four axioms.
The Lean 4 formalisation of Part I, summarised in Part IV, confirms the system without
modifying it, and clarifies several methodological points (the status of A4 as a theorem rather
than an axiom; the absorption of P1, P2 into typing; the constructive strengthening of Theorem
11; the dispensability of T1–T4 for the equivalence; the two readings of ↔ in §3 and Def. 2; the
structural rather than measure-theoretic character of ∈-acyclicity).

## References

Boolos, G. S., Burgess, J. P., & Jeffrey, R. C. (2007). Computability and Logic (5th ed.).
Cambridge University Press.
Mendelson, E. (2015). Introduction to Mathematical Logic (6th ed.). Chapman and Hall/CRC.
Peano, G. (1889). Arithmetices principia, nova methodo exposita.
Reznik, V. (2026). VR. A Formal System: Lean 4 Formalisation of Part I. Zenodo. DOI:
10.5281/zenodo.20324240.
Reznik, V. (2026). VR-Numbers: Operational Superstructures of Integers, Rationals, Reals, and
Complex Numbers over the Natural Numbers of VR. Zenodo. DOI: 10.5281/zenodo.20272743.
von Neumann, J. (1923). Zur Einführung der transfiniten Zahlen. Acta Litterarum ac
Scientiarum, 1, 199–208.
Zermelo, E. (1908). Untersuchungen über die Grundlagen der Mengenlehre. Mathematische
Annalen, 65(2), 261–281.
