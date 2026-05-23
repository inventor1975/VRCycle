-- VR-Sets: Conjectures (DOI 10.5281/zenodo.20303536)
-- Part IV. Conjectures IV.1 and IV.2.
--
-- Stage 11: Conjecture IV.1 (ZFC-mode mutual interpretability) and
--           Conjecture IV.2 (ZFA-mode mutual interpretability) —
--           formalised as Lean Prop, no proofs.
-- Source: Part IV §IV.5–§IV.6, Part IX §IX.1 Questions 1–2.
--
-- ARCHITECTURAL STATUS (CLAUDE.md Decision 3): Formulations only.
-- These are open questions (§IX.1). Lean records the statement; it cannot
-- resolve either conjecture. No sorry, no admit, no proof attempt.
-- Both are `def : Prop` — a third Lean status distinct from `theorem`
-- and `axiom`. Expected `#print axioms`: [] empty for both.

import VRCycle.Sets.Modes

namespace VR.Sets

-- ============================================================
-- §IV.5, §IX.1 Question 1 — Conjecture IV.1
-- ============================================================

/-- # Conjecture IV.1: ZFC-mode of VR-Sets is mutually interpretable with
a countable model of classical ZFC.

## §IX.1, Question 1 (VR-Sets preprint, verbatim)
«Is the ZFC-mode of VR-Sets (Part IV §IV.2) mutually interpretable with
a classical (non-operational) countable model of ZFC? Specifically: does
there exist a countable set M, closed under all ZFC operations, such that
the ZFC axioms hold when quantified over M?»

## Status: OPEN
This is an open question of the author (§IX.1 Question 1). Lean records
the statement faithfully but cannot resolve it. Neither a proof nor a
disproof is provided or attempted here.

Compare with `AFA_Statement` / `AFA_Refuted` (Stage 10): there, Lean
could prove the negation constructively. Here, no such proof exists;
the conjecture status is genuine openness.

Compare with `Theorem_IV_1_ZFCAxioms` (Stage 9): that theorem proves all
nine ZFC axioms hold on the full OSet. Conjecture IV.1 asks whether a
*countable* submodel (a proper subset of OSet, itself of type M) can be
found that also satisfies all nine axioms internally.

## Lean formulation: internal countable model

Formalised as:

    ∃ (M : Type) [Countable M] (embed : M ↪ OSet),
        all nine ZFC axioms hold relative to (M, embed)

`embed : M ↪ OSet` is an injection (not full isomorphism): it suffices
that M embeds into OSet with ZFC closure properties preserved. «Relative
to (M, embed)» means quantifiers range over M and membership is the
restriction `embed x ∈ embed a` (OSet membership of images).

## Why all nine axioms?

The preprint §IV.2 characterises ZFC-mode by all nine classical ZFC
axioms. `Theorem_IV_1_ZFCAxioms` (Stage 9) assembles all nine for the
full OSet. Conjecture IV.1 mirrors this nine-conjunct structure for a
countable submodel. Omitting any conjunct would understate the conjecture:
mutual interpretability with classical ZFC requires all nine axioms
(not a fragment), since classical ZFC is standardly axiomatised with all
nine. The nine conjuncts below match the ordering of
`Theorem_IV_1_ZFCAxioms` exactly.

## Mutual interpretability: the two directions

«Mutual interpretability» (§IX.1) means:
- (→) A proof in operational VR-Sets translates to classical ZFC.
- (←) A proof in classical ZFC translates to operational VR-Sets.

Direction (←): `Theorem_IV_1_ZFCAxioms` (Stage 9) is already proved —
OSet satisfies all nine ZFC axioms.

Direction (→): requires the countable model M. `Conjecture_IV_1_Statement`
formalises this open direction. Its proof would require constructing a
specific countable model and verifying all nine axioms for it.

## Countability restriction

`[Countable M]` reflects the preprint's claim that the VR-Sets universe
is operationally countable (§II.3, §VI.1): only finitely-describable
operationalities exist. The conjecture's content is that the nine ZFC
axioms are compatible with this restriction — a non-trivial claim since
classical ZFC is typically studied in uncountable models (cf. the
Löwenheim–Skolem theorem, which guarantees *some* countable model but
does not trivially transfer to the operational setting).

## Axiom profile: [] empty
`def : Prop` — type-checks propositional well-formedness only. No lemmas,
tactics, or axioms are invoked. -/
def Conjecture_IV_1_Statement : Prop :=
    ∃ (M : Type) (_ : Countable M) (embed : M ↪ OSet.{0}),
        -- (1) Extensionality: M-elements with the same M-members are equal
        (∀ a b : M, (∀ x : M, embed x ∈ embed a ↔ embed x ∈ embed b) → a = b) ∧
        -- (2) Empty set: some M-element has no M-members
        (∃ e : M, ∀ x : M, embed x ∉ embed e) ∧
        -- (3) Foundation / Regularity: every non-empty M-set has an M-minimal
        --     M-member (no descending M-chains)
        (∀ a : M, (∃ x : M, embed x ∈ embed a) →
            ∃ x : M, embed x ∈ embed a ∧ ∀ y : M, embed y ∈ embed x → embed y ∉ embed a) ∧
        -- (4) Pairing: for any a b : M there exists p : M containing exactly {a, b}
        (∀ a b : M, ∃ p : M, ∀ x : M, embed x ∈ embed p ↔ (x = a ∨ x = b)) ∧
        -- (5) Union: for any a : M there exists ua : M whose M-members are
        --     exactly the M-members of M-members of a
        (∀ a : M, ∃ ua : M, ∀ x : M, embed x ∈ embed ua ↔
            ∃ c : M, embed c ∈ embed a ∧ embed x ∈ embed c) ∧
        -- (6) Power set: for any a : M there exists pa : M whose M-members
        --     are exactly the M-subsets of a
        (∀ a : M, ∃ pa : M, ∀ x : M, embed x ∈ embed pa ↔
            ∀ y : M, embed y ∈ embed x → embed y ∈ embed a) ∧
        -- (7) Infinity: there exists an M-set containing an M-empty and closed
        --     under the von Neumann successor operation (sn = n ∪ {n})
        (∃ ω_M : M,
            (∃ e : M, embed e ∈ embed ω_M ∧ ∀ x : M, embed x ∉ embed e) ∧
            ∀ n : M, embed n ∈ embed ω_M →
                ∃ sn : M, embed sn ∈ embed ω_M ∧
                    ∀ x : M, embed x ∈ embed sn ↔
                        (embed x ∈ embed n ∨ x = n)) ∧
        -- (8) Replacement: for any M-definable function F : M → M and any
        --     a : M, the image F '' {members of a} is represented in M
        (∀ (F : M → M) (a : M), ∃ b : M,
            ∀ x : M, embed x ∈ embed b ↔ ∃ y : M, embed y ∈ embed a ∧ F y = x) ∧
        -- (9) Choice: for any a : M of non-empty M-sets, there is an
        --     M-valued choice function
        (∀ a : M, (∀ x : M, embed x ∈ embed a → ∃ y : M, embed y ∈ embed x) →
            ∃ f : M → M, ∀ x : M, embed x ∈ embed a → embed (f x) ∈ embed x)

-- ============================================================
-- §IV.6, §IX.1 Question 2 — Conjecture IV.2
-- ============================================================

/-- # Conjecture IV.2: ZFA-mode of VR-Sets is mutually interpretable with
a type-theoretic universe satisfying the Anti-Foundation Axiom (AFA).

## §IX.1, Question 2 (VR-Sets preprint, verbatim)
«Is the ZFA-mode of VR-Sets (Part IV §IV.5) mutually interpretable with
a universe of non-well-founded sets satisfying Aczel's Anti-Foundation
Axiom (AFA)? Specifically: does there exist a type U with a membership
relation admitting cyclic sets — in particular, the Quine atom — and
satisfying AFA in its graph-decoration form?»

## Status: OPEN
Open question of the author (§IX.1 Question 2). Compare with the
Stage 10 boundary results:

| Object              | Stage | Status                                          |
|---------------------|-------|-------------------------------------------------|
| `quineAtomSpec`     | 10    | Provably false in PSet (`quineAtom_impossible`) |
| `AFA_Statement`     | 10    | Provably false in PSet (`AFA_Refuted`)          |
| `Conjecture_IV_2_Statement` | 11 | Open: existence of a DIFFERENT type U satisfying AFA |

Stages 10 and 11 are logically compatible: Stage 10 proves AFA is false
*in mathlib's PSet*; Conjecture IV.2 asks whether there exists *some*
type U (possibly outside mathlib) with AFA-compatible membership. The
conjecture asks for existence, not for construction in the current type
theory.

## Classical AFA vs. Operational AFA (a critical distinction)

### This formulation: Classical AFA (Aczel 1988)

`Conjecture_IV_2_Statement` is stated using **classical AFA**: the graph
`(V, E)` ranges over ALL Lean types V and ALL Lean relations E. This is
Aczel's original formulation (1988, §3) — the «graph-decoration theorem».

Classical AFA: for every graph `(V, E)` (of any type), there exists a
unique assignment `f : V → U` such that for every vertex v, `f(v)` is
the set of images of v's neighbours.

### The preprint uses Operational AFA (§IV.7)

The preprint §IV.7 discusses a *strictly weaker* version: **operational
AFA**, restricted to graphs that are operationally describable — finitely
specifiable algorithms over a finite alphabet. Operationally describable
graphs form a *countable* subset of all graphs; classical AFA is a
universal statement over all (uncountably many) graphs.

**Why formalise the stronger version?**
- Operational AFA is not Lean-expressible: the condition «operationally
  describable» is metatheoretic (it refers to algorithms, not Lean terms).
  This is the same inexpressibility boundary as Stage 5 (power set),
  Stage 7 (replacement), Stage 8 (choice), and VR-Numbers §VIII.6 (ℝ_VR).
- Classical AFA is a strict upper bound: if a universe satisfies classical
  AFA, it satisfies operational AFA a fortiori (the preprint's condition
  is the harder-to-falsify direction). So `Conjecture_IV_2_Statement` is a
  *stronger* claim than the preprint's; its truth would imply the
  preprint's conjecture, and its falsity would not refute the preprint's.
- Recording the stronger version is methodologically honest: Lean cannot
  express the weaker version (metatheoretic), and the stronger version
  gives the conjecture a definite Lean-checkable shape.

### The extensionality condition

The extensionality conjunct `∀ a b : U, (∀ x, mem x a ↔ mem x b) → a = b`
is not a separate conjecture but a non-triviality constraint. Without it,
`U = Unit` with `mem _ _ = True` would trivially satisfy the Quine atom
condition (`mem () ()` = True) but would be a degenerate model not
satisfying AFA (all vertices would need non-empty neighbourhoods). With
extensionality, unit-like constructions fail because U cannot compress all
members into a single element if the graph has non-isomorphic vertices.
Extensionality is part of what makes U a «set-theoretic universe» rather
than an arbitrary type.

## Axiom profile: [] empty
`def : Prop` — no computation, no tactics, no axioms invoked. -/
def Conjecture_IV_2_Statement : Prop :=
    ∃ (U : Type) (mem : U → U → Prop),
        -- (i) Quine atom: there exists a self-membered element of U
        --     (the simplest cyclic set; required by ZFA-mode, §IV.7)
        (∃ q : U, mem q q) ∧
        -- (ii) Extensionality: U-elements with the same U-members are equal
        --      (non-triviality constraint: prevents unit-type witnesses)
        (∀ a b : U, (∀ x : U, mem x a ↔ mem x b) → a = b) ∧
        -- (iii) Classical AFA (Aczel 1988, graph-decoration form):
        --       for every graph (V, E), there is a unique assignment f : V → U
        --       such that the U-members of f(v) are exactly the images of v's
        --       outgoing neighbours.
        --
        --       NOTE: This is CLASSICAL AFA (all Lean types V, all relations E).
        --       The preprint §IV.7 uses OPERATIONAL AFA (only describable graphs).
        --       Classical AFA implies operational AFA; so truth of this conjecture
        --       implies the preprint's conjecture. Falsity here does NOT refute
        --       the preprint's weaker form. See docstring for full discussion.
        (∀ (V : Type) (E : V → V → Prop),
            ∃! f : V → U, ∀ v : V,
                ∀ x : U, mem x (f v) ↔ ∃ w : V, E v w ∧ f w = x)

end VR.Sets
