-- VR-Sets: ZF Closure Theorems (DOI 10.5281/zenodo.20303536)
-- Part III. The ZF Axioms as Closure Theorems.
--
-- Stages 3–8: Pairing, Union, Power, Infinity, Replacement, Choice.
-- (Foundation/Extensionality/Empty are Stages 1–2 in Foundation.lean.)
-- Source: Part III §III.3–§III.9.

import VRCycle.Sets.Foundation

namespace VR.Sets

-- ============================================================
-- §III.3 — Pairing (Stage 3)
-- ============================================================

/-- The unordered pair set {a, b}.

§III.3, Theorem (pairing) — verbatim:
«For any sets a and b there exists a set, denoted {a, b}, whose
functionality reveals exactly a and b (when a ≡ b — a single element).»

Classical ZF formulation (verbatim from §III.3):
  ∀a ∀b ∃A ∀x (x ∈ A ↔ x ≡ a ∨ x ≡ b)

Implemented as `{a, b} : OSet` via the `Insert ZFSet ZFSet` instance.
Note: `ZFSet.pair` in mathlib is the Kuratowski *ordered* pair `{{a},{a,b}}`;
the preprint's pairing is the *unordered* two-element set, realised here
by the `{·, ·}` notation. -/
def osetPair (a b : OSet) : OSet := {a, b}

/-- §III.3, Theorem (pairing): the membership characterisation of `osetPair`.

For any x, x ∈ {a, b} if and only if x = a or x = b. -/
theorem Theorem_III_3_Pairing (a b : OSet) :
    ∀ x : OSet, x ∈ osetPair a b ↔ x = a ∨ x = b :=
  fun _ => ZFSet.mem_pair

-- ============================================================
-- §III.4 — Union (Stage 4)
-- ============================================================

/-- The union ∪A: the set of all elements of elements of A.

§III.4, Theorem (union) — verbatim:
«For any set A there exists a set, denoted ∪A, whose functionality
reveals exactly all elements of elements of A (without repetitions
up to ≡).»

Classical ZF formulation (verbatim from §III.4):
  ∀A ∃B ∀x (x ∈ B ↔ ∃C (C ∈ A ∧ x ∈ C))

Implemented as `ZFSet.sUnion` (notation `⋃₀`, scoped to `ZFSet`).

Subtlety note (§III.4): The preprint observes that «skipping repetitions
up to ≡» means ≡-decidability is required in principle. In Lean, since
≡ = Eq on ZFSet (Decision 5, CLAUDE.md), equality of ZFSet elements is
decidable propositionally; `ZFSet.mem_sUnion` handles this without extra
hypotheses, using the quotient structure of ZFSet directly. -/
def osetUnion (a : OSet) : OSet := ZFSet.sUnion a

/-- §III.4, Theorem (union): the membership characterisation of `osetUnion`.

For any x, x ∈ ∪A if and only if there exists C ∈ A with x ∈ C. -/
theorem Theorem_III_4_Union (a : OSet) :
    ∀ x : OSet, x ∈ osetUnion a ↔ ∃ c ∈ a, x ∈ c :=
  fun _ => ZFSet.mem_sUnion

-- ============================================================
-- §III.5 — Power set (Stage 5)          [architectural stage]
-- ============================================================

/-- The power set ℘(A): the set of all subsets of A.

## §III.5, Theorem (power) — verbatim
«For any set A there exists a set, denoted ℘(A), whose functionality
reveals exactly all subsets of A — that is, all operationally
describable functionalities whose revealed elements belong to A.»

Classical ZF formulation (verbatim from §III.5):
  ∀A ∃B ∀x (x ∈ B ↔ x ⊆ A)

## ℘(ω) in VR-Sets is countable — first structural boundary

The preprint asserts (§III.5, verbatim):
«**From the proof it follows that ℘(ω) in VR-Sets is a countable set.**
This is a sharp divergence from classical ZF, where ℘(ω) is uncountable
by Cantor's diagonal argument.»

And (§III.5, verbatim):
«**℘(ω) in VR-Sets and ℘(ω) in classical ZF are not one and the same
object.**»

Mechanism (§III.5): each element of ℘(ω) is a describable functionality —
a finite algorithm over a finite alphabet. The set of all such algorithms
is countable. Cantor's diagonal D = {n : n ∉ Sₙ} requires a complete
enumeration of describable subsets, which is equivalent to solving the
halting problem; this enumeration is operationally unattainable. D does
not specify a describable functionality, hence D is not a set in VR-Sets.
The diagonal is removed «not by forbidding it as a proof, but by the fact
that its premise (a complete enumeration of describable subsets) is
operationally unrealisable.»

## What Lean expresses and what it does not

`ZFSet.powerset : ZFSet → ZFSet` produces the **classical** power set —
all subsets of A, including non-describable ones. In particular,
`ZFSet.powerset ZFSet.omega` contains every subset of ω in the classical
sense, and is not countable.

Therefore: the preprint's ℘(ω) (countable, describable subsets) and
`ZFSet.powerset ZFSet.omega` (uncountable, all subsets) are **not the
same object**. The preprint's countability claim is metatheoretic — it
refers to describable subsets within a countable operational universe —
and **cannot be expressed as a Lean theorem about ZFSet**.

The Lean formulation `x ∈ osetPower a ↔ x ⊆ a` uses Lean's `⊆`, which
is the **classical** subset relation, not the preprint's «describable
subset». This is a syntactic manifestation of the same structural
boundary: the Lean theorem is stronger (covers all subsets) than the
preprint's theorem (covers only describable subsets).

## Methodological status — first structural boundary

This is the **first structural boundary** in the VR-Sets Lean
formalisation, parallel to the boundary at ℝ_VR documented in
VR-Numbers §VIII.6 (inexpressibility of computability in Lean 4).

In VR-Numbers, the boundary appeared at Stage 8 (reals): `RealVR` in
Lean equals the classical ℝ (all Cauchy sequences), while the preprint's
ℝ_VR contains only computable reals. In VR-Sets, the analogous boundary
appears earlier, at Stage 5 (power set), because ℘(ω) immediately makes
the countability / describability distinction visible without further
construction.

Both boundaries share the same structure: the Lean/mathlib type is the
classical object; the preprint's object is the restriction to describable
(computable, algorithmic) entities within the same universe. The
restriction is metatheoretic, not formalised in the type.

See Part VI §VI.2 (Cantor's diagonal in the operational universe) and
§VI.3 (countable-from-without vs. enumerable-from-within) of the
VR-Sets preprint for detailed discussion of this boundary. -/
def osetPower (a : OSet) : OSet := ZFSet.powerset a

/-- §III.5, Theorem (power): the membership characterisation of `osetPower`.

For any x, x ∈ ℘(A) if and only if x ⊆ A (classical subset relation).
Note: Lean's `⊆` here is wider than the preprint's «describable subset»;
see the comment on `osetPower` for the structural boundary. -/
theorem Theorem_III_5_Power (a : OSet) :
    ∀ x : OSet, x ∈ osetPower a ↔ x ⊆ a :=
  fun _ => ZFSet.mem_powerset

-- ============================================================
-- §III.6 — Infinity and ω (Stage 6)
-- ============================================================

/-- The operational infinity set ω: the first infinite von Neumann ordinal.

§III.6, Theorem (infinity) — verbatim:
«There exists a set, denoted ω, whose functionality reveals in turn
∅, t(∅), t(t(∅)), … without exhaustion and without cycling.»

Classical ZF formulation (verbatim from §III.6):
  ∃A (∅ ∈ A ∧ ∀x (x ∈ A → x ∪ {x} ∈ A))

Implemented as `ZFSet.omega := ZFSet.mk PSet.omega`, where
`PSet.omega := ⟨ULift ℕ, fun n => PSet.ofNat n.down⟩` — the family
indexed by all natural numbers, with the n-th member being the n-th von
Neumann ordinal Oₙ:

  O₀ = ∅,  O₁ = {∅},  O₂ = {∅, {∅}},  …

In VR-Sets notation: O₀ = ∅ and Oₙ₊₁ = t(Oₙ), where `t` is the VR
succession operator. The set-theoretic successor `insert n n = n ∪ {n}`
corresponds to t(Oₙ) = Oₙ₊₁ (von Neumann ordinal successor).

Remark (§III.6): ω has **non-finite** operational depth (unfolding to ∅
does not terminate in any finite number of steps) but is **non-cyclic**
(the sequence O₀, O₁, O₂, … is non-repeating). This is the first
example where the distinction «infinite by enumeration» vs. «cyclic»
from Definition 3 (Part II) becomes operative. In Lean:
`operationalDepth omega_OSet = Ordinal.omega` (rank of ω = ω). -/
def omega_OSet : OSet := ZFSet.omega

/-- §III.6, Theorem (infinity): ∅ ∈ ω.
The first von Neumann ordinal O₀ = ∅ is a member of ω. -/
theorem Theorem_III_6_Infinity_Zero : (∅ : OSet) ∈ omega_OSet :=
  ZFSet.omega_zero

/-- §III.6, Theorem (infinity): ω is closed under von Neumann successor.
If n ∈ ω, then `insert n n` = n ∪ {n} ∈ ω.
This corresponds to O_{n+1} = t(Oₙ) ∈ ω in VR-Sets terminology. -/
theorem Theorem_III_6_Infinity_Succ (n : OSet) (h : n ∈ omega_OSet) :
    insert n n ∈ omega_OSet :=
  ZFSet.omega_succ h

/-- §III.6, Conjunction: the classical ZF infinity axiom satisfied by ω.
Combines `Theorem_III_6_Infinity_Zero` and `Theorem_III_6_Infinity_Succ`. -/
theorem Theorem_III_6_Infinity :
    (∅ : OSet) ∈ omega_OSet ∧
    ∀ n : OSet, n ∈ omega_OSet → insert n n ∈ omega_OSet :=
  ⟨Theorem_III_6_Infinity_Zero, Theorem_III_6_Infinity_Succ⟩

-- ============================================================
-- §III — Separation (bounded comprehension)
-- ============================================================

/-- The separation set {x ∈ A | p x}: the elements of A satisfying p.

Separation (Aussonderung) is the canonical ZF axiom **schema**: classically
there is one separation axiom for each formula φ of the language,
  ∀A ∃B ∀x (x ∈ B ↔ x ∈ A ∧ φ(x)),
the quantification over formulas being metatheoretic.

In VR-Sets, separation is an instance of the closure principle (§II.3)
restricted to a describable condition bounded by an existing set A. Here it
is realised as a **single theorem parametric in a first-class predicate**
`p : OSet → Prop`: the meta-level quantification over formulas becomes
object-level quantification over predicates, and the entire schema collapses
to one statement.

Unlike Replacement (§III.7), Separation is **bounded** — B ⊆ A — so it needs
no choice/definability machinery. `ZFSet.sep` is **computable** and the
membership characterisation `Theorem_III_Separation` has axiom profile
`[propext, Quot.sound]`, **free of `Classical.choice`**. Classically,
Separation is derivable from Replacement; it is recorded here directly as the
canonical schema-collapse witness for the finite-axiomatization observation
(see Part on axiomatic economy / VR-Sets-ZFA).

Implemented as `ZFSet.sep`. -/
def osetSep (p : OSet → Prop) (a : OSet) : OSet := ZFSet.sep p a

/-- §III, Theorem (separation): the membership characterisation of `osetSep`.

For any x, x ∈ {z ∈ A | p z} if and only if x ∈ A and p x. One theorem
parametric in the predicate `p`, replacing the entire classical separation
schema; axiom profile `[propext, Quot.sound]` (no `Classical.choice`). -/
theorem Theorem_III_Separation (p : OSet → Prop) (a : OSet) :
    ∀ x : OSet, x ∈ osetSep p a ↔ x ∈ a ∧ p x :=
  fun _ => ZFSet.mem_sep

/-- Schema-collapse witness: each instance of the classical separation schema
is recovered as a single application of `Theorem_III_Separation`. Example:
the empty-witnessing subset {x ∈ A | x ≡ ∅}. -/
example (a : OSet) :
    ∀ x : OSet, x ∈ osetSep (fun z => z = ∅) a ↔ x ∈ a ∧ x = ∅ :=
  Theorem_III_Separation _ a

-- ============================================================
-- §III.7 — Replacement (Stage 7)
-- ============================================================

/-- The image of a set A under a function F: the set {F(x) | x ∈ A}.

§III.7, Theorem (replacement) — verbatim:
«For any set A and any operationally describable procedure F defined on
the elements of A, there exists a set, denoted image(F, A), whose
functionality reveals exactly F(x) for every x ∈ A.»

Classical ZF formulation (axiom schema in ZF, single theorem here):
  For every formula φ(x, y) specifying a functional relation (∀x ∃!y φ(x,y))
  and for every set A, there exists B = { y : ∃x ∈ A, φ(x, y) }.

## Schema → single theorem: methodological convergence

In classical ZF, replacement is an **axiom schema** — one axiom for each
formula φ of the language of ZF. The quantification over formulas is
meta-level.

In VR-Sets (§III.7, verbatim): «In VR-Sets an "operationally describable
procedure F" is a single operational notion encompassing all ways of
specifying functional relations (including all formulas of the language
of ZF translated into operational descriptions). Therefore **a single
closure theorem with respect to describable transformations replaces the
entire schema**.»

In Lean/mathlib, the same collapse happens for the same structural reason:
functions `F : ZFSet → ZFSet` are **first-class objects** (Lean lambdas),
and `ZFSet.image F a` is parametric in `F`. The meta-level quantification
over formulas disappears because functions ARE formulas in type theory.
`ZFSet.image` requires `[Definable₁ F]`; for arbitrary Lean functions we
use `Classical.allZFSetDefinable` (Basic.lean), which provides a
`Definable₁` instance for every function at the cost of `Classical.choice`.

This is a **methodological convergence**: VR-Sets and Lean/mathlib arrive
at the same simplification of replacement from different foundational
directions — VR-Sets through «operational describability», Lean through
first-class function types. The result is formally identical: one theorem,
parametric in F.

**Note on axioms**: `Classical.allZFSetDefinable` introduces `Classical.choice`
(via `Quotient.out` for representative selection). This is the second
object in VR-Sets where Classical enters (after Lemma 3 via `Ordinal.iSup`).
Both times, Classical.choice appears due to **non-constructive selection**:
choosing an ordinal sup vs. choosing a set representative. -/
noncomputable def osetReplacement (F : OSet → OSet) (a : OSet) : OSet :=
  @ZFSet.image F (Classical.allZFSetDefinable _) a

/-- §III.7, Theorem (replacement): the membership characterisation.

x ∈ image(F, A) if and only if ∃ y ∈ A, F(y) = x. -/
theorem Theorem_III_7_Replacement (F : OSet → OSet) (a : OSet) :
    ∀ x : OSet, x ∈ osetReplacement F a ↔ ∃ y ∈ a, F y = x :=
  fun x => @ZFSet.mem_image F (Classical.allZFSetDefinable _) a x

-- ============================================================
-- §III.8 — Foundation / Regularity
-- ============================================================

/-- The Foundation axiom (Regularity): every non-empty set has an
∈-minimal element — an element disjoint from the set.

§III.8, Theorem (foundation) — verbatim:
«For any non-empty set A there exists an element x ∈ A such that x
and A share no common element.»

Classical ZF formulation (verbatim from §III.8):
  ∀A (A ≠ ∅ → ∃ x ∈ A, ∀ y ∈ x, y ∉ A)

## Mode-dependence: the fourth structural boundary

In the preprint (§III.8, §IV.5), Foundation is **mode-dependent**:
it holds in ZFC-mode (all set unfoldings terminate at ∅) but **fails**
in ZFA-mode. Example: for the Quine atom A = {A}, the singleton {A}
has only one member A, and A ∩ {A} = {A} ≠ ∅ (A is both a member of A
and a member of {A}), so no disjoint ∈-minimal element exists.

On `OSet := ZFSet`, Foundation holds **unconditionally** — without any
mode guard — because ZFSet = Quotient PSet.setoid and PSet is an
*inductive* Lean type, so membership is globally well-founded. Cyclic
elements do not exist in OSet; the ZFA-mode portion of the preprint's
universe is absent from ZFSet entirely.

This is the **fourth structural boundary** in the VR-Sets formalisation,
running in the **opposite direction** from Stages 5, 7, 8:

| Direction     | Stages    | Pattern                                           |
|---------------|-----------|---------------------------------------------------|
| Lean **wider**    | 5, 7, 8   | Preprint restricts to describable; Lean admits all |
| Lean **narrower** | 9 (§III.8)| Preprint allows ZFA-mode; Lean's ZFSet pre-commits to ZFC-mode |

The two-directional boundary reflects the two-sided gap: Lean cannot
type-level restrict to «describable» (widening), and Lean's ZFSet
pre-commits to well-foundedness (narrowing). The choice `OSet := ZFSet`
simultaneously takes both sides.

## Proof

Via `WellFounded.has_min` on `IsWellFounded.wf : WellFounded (· ∈ ·)`.
The ∈-minimal element of `{z | z ∈ a}` satisfies `∀ y ∈ a, y ∉ x`
(no member of a is in x); contrapositively, `∀ y ∈ x, y ∉ a` (no
member of x is in a), which is the classical Foundation formulation. -/
theorem Theorem_III_8_Foundation (a : OSet) (hne : a ≠ ∅) :
    ∃ x ∈ a, ∀ y ∈ x, y ∉ a := by
  have hwf : WellFounded (· ∈ · : OSet → OSet → Prop) := IsWellFounded.wf
  have hnonempty : (setOf (· ∈ a) : Set OSet).Nonempty := by
    simp only [Set.nonempty_def, Set.mem_setOf_eq]
    rcases ZFSet.eq_empty_or_nonempty a with rfl | ⟨z, hz⟩
    · exact absurd rfl hne
    · exact ⟨z, hz⟩
  obtain ⟨x, hxa, hmin⟩ := hwf.has_min (setOf (· ∈ a)) hnonempty
  simp only [Set.mem_setOf_eq] at hxa hmin
  exact ⟨x, hxa, fun y hyx hya => absurd hyx (hmin y hya)⟩

-- ============================================================
-- §III.9 — Choice (Stage 8)
-- ============================================================

/-- §III.9, Theorem (countable choice) — verbatim:
«For every countable family {Aᵢ}_{i ∈ ω} of pairwise disjoint non-empty
sets there exists a set, denoted choice({Aᵢ}), containing exactly one
element from each Aᵢ.»

Classical ZF formulation (AC — verbatim §III.9):
  For every set of pairwise disjoint non-empty sets there exists a set
  containing exactly one element from each.

## Status in VR-Sets: theorem on the countable universe (§III.9)

The preprint derives AC from DC + countability of the operational universe
(verbatim §III.9):

• «**DC (dependent choice)** is built into the operational universe:
  every operation is carried out concretely, and a sequence of operations
  is built step by step. DC is not an axiom but a property of
  operationality itself.»
• «**Full AC** is a theorem on the countable operational universe (for
  countable sets, AC reduces to DC).»
• «**AC is a theorem, not an axiom.** The Banach–Tarski paradox is absent
  not because AC is weakened, but because the objects on which it is built
  (uncountable subsets of ℝ, non-Lebesgue-measurable sets) do not exist
  in the operational universe.»

## What Lean expresses and what it does not

In Lean, `Classical.choice` is an **axiom** (already in our axiom ceiling
since Stage 1). The theorem below is proved using `Classical.epsilon`, a
direct consequence of `Classical.choice`.

The preprint's argument («countable universe → AC trivial via DC») is
**metatheoretic**: countability of the operational universe is not
expressible in ZFSet as a type-level property. Lean records AC through
`Classical.choice` — for ALL families, not just countable ones — and does
not distinguish "countable" from "arbitrary" at the type level.

This is the **third manifestation** of the structural boundary
(Stages 5, 7, 8):

| Stage | Preprint restriction | Lean/mathlib scope |
|-------|---------------------|---------------------|
| 5 | Describable subsets | All classical subsets |
| 7 | Describable procedures F | All Lean functions |
| 8 | Countable universe, AC from DC | All families via Classical.choice |

In each case, Lean is **classically broader** than the preprint's
operational restriction, and the restriction cannot be expressed as a
type in ZFSet. The boundary is structural: Lean does not have a type of
«operationally describable» entities. -/
theorem Theorem_III_9_Choice (a : OSet) (hne : ∀ x ∈ a, (x : OSet) ≠ ∅) :
    ∃ f : OSet → OSet, ∀ x ∈ a, f x ∈ x := by
  refine ⟨fun x => Classical.epsilon (fun z => z ∈ x), fun x hx => ?_⟩
  apply Classical.epsilon_spec
  rcases ZFSet.eq_empty_or_nonempty x with rfl | ⟨z, hz⟩
  · exact absurd rfl (hne ∅ hx)
  · exact ⟨z, hz⟩

end VR.Sets
