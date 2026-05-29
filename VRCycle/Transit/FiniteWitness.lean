-- VR-Transit: FiniteWitness (v0.1.0, Stage 1)
-- A finitely-generated witness provider for the apparatus: a second clean `[]`
-- pointwise Tier-2 → Factorisable bridge after separability, plus the first
-- *aggregating* bridge (choice-free) over an explicit finite generating set.
--
-- STAGE: Stage 1 (final, option b per FINDING TR-FW1). SOURCE: PLAN.md Stage 1 + amendment.
--
-- ## Position statement
-- VR-Apparatus showed transit is well-behaved and gave `Factorisable` as the
-- canonical Mode B witness, with `separability_provides_factorisable` as the first
-- `[]` Tier-2 → Factorisable bridge. This file adds the second such provider, built
-- on a finite generating family carried as explicit data (the Tier-2 data rule,
-- CLAUDE.md §5), and then extends it to the additive span.
--
-- Two parts, and they fall into two *kinds* of bridge — a distinction this stage
-- makes precise (see "Two kinds of bridge" below):
--   1a. `finiteGen_provides_factorisable` — generator-level (POINTWISE) bridge.
--       Mirrors `separability_provides_factorisable` with an abstract generator
--       family in place of a dense sequence. No aggregation ⇒ `[]`. A light scaffold:
--       its worth is being the second clean `[]` provider — needed before any
--       *pattern* of providers can be claimed — and the carrier for 1b.
--   1b. `finiteSpan_provides_factorisable` — additive-span (AGGREGATING) bridge.
--       The genuinely new content: for additive maps agreeing on the generators,
--       agreement propagates to every ℤ-combination over an explicit finite index
--       set, so f is Factorisable not only at the generators but at any such
--       combination. This is the operand-not-operation principle (Finding S4-A) at
--       the linear-combination level: the result's operationality is determined by
--       the operational data of the operand (the explicit index set `s : Finset ι`
--       and coefficients `c : ι → ℤ`), not by f.
--
-- ## Two kinds of bridge (the calibration behind FINDING TR-FW1)
-- The witness library now contains two structurally distinct bridge kinds:
--   • POINTWISE bridges (separability, 1a): evaluate the witness at a single named
--     operand. No summation. Achievable target `[]` (axiom-free).
--   • AGGREGATING bridges (1b; and, expectedly, completeness/locatedness in Stage 3):
--     combine the witness over a finite operand set. Any aggregation routes through
--     `Finset.sum`, which is `[propext, Quot.sound]` (the `Multiset` quotient gives
--     `Quot.sound`, set-extensionality gives `propext`). The honest achievable target
--     for an aggregating bridge is therefore **choice-free** `[propext, Quot.sound]`,
--     not `[]`. `Classical.choice` must NOT appear: its absence certifies that finite
--     additive transit is constructive, not classical.
--
-- ## Tier-2 data rule, applied correctly (FINDING TR-FW1, two faces)
-- The Tier-2 class `HasFiniteGeneratorStructure` carries ONLY the generator map
-- `gens : ι → T` — an axiom-free field type, exactly like separability's
-- `denseSeq : ℕ → T`. The finite index set and the coefficients are NOT class fields;
-- they are passed as explicit arguments (`s : Finset ι`, `c : ι → ℤ`) to the
-- aggregating bridge 1b, where they are operand data. This placement is forced by
-- the axiom profile, in two faces, both diagnosed during Stage 1:
--   FACE 1 (index encoding): summing over `Finset.univ` of a `Fin card` index pulls
--     the `Fintype (Fin n)` / `Finset.univ` infrastructure, which is
--     `[propext, Classical.choice, Quot.sound]` in mathlib v4.29.1 — even
--     `(∑ i : Fin 3, w i) = (∑ i, w i) := rfl` carries the full ceiling. Using an
--     *explicit* `Finset ι` instead keeps the aggregation choice-free. (Reproducer:
--     `tFW1_exhibit_univ_pulls_choice`, §4.)
--   FACE 2 (field placement): a `Finset ι` carried as a CLASS FIELD injects
--     `[propext, Quot.sound]` into the class type itself, and the pointwise bridge 1a
--     inherits it merely by referencing the class — collapsing the `[]` pointwise
--     tier even though 1a does no summation. Keeping `Finset` out of the class (an
--     argument to 1b) preserves 1a `[]`.
-- Consolidated rule (now in CLAUDE.md §5): data whose *type* itself carries axioms
-- (`Finset`, `Quotient`, …) must not be a field of a Tier-2 class shared with
-- pointwise bridges; it belongs to the aggregating bridge's argument list. See
-- FINDING TR-FW1 in T_FINDINGS_TRANSIT.md.
--
-- ## Scope / honesty
-- This is a witness-bridge library, not a universal transit machine: it buys one
-- family of transits (finitely-generated additive operands). The classical cost, if
-- any, lives in whatever instance constructs `HasFiniteGeneratorStructure` for a
-- concrete type and in the operation's own profile — never in the class or the
-- bridge. No spanning is asserted (the class makes no claim that `gens` generates T);
-- the span bridge is stated for the explicit combinations over the supplied index
-- set, so it holds whether or not `gens` spans T.
--
-- ## Axiom profile overview
--   HasFiniteGeneratorStructure            []
--   finiteGen_provides_factorisable        []
--   finiteSpan_provides_factorisable       [propext, Quot.sound]   (choice-free)
--
-- import VRCycle.Apparatus (for Factorisable) + minimal mathlib for finite sums and
-- AddMonoidHom. Does NOT import VRCycle.Algebra (avoids an import cycle; the additive
-- structure is taken straight from mathlib).

import VRCycle.Apparatus
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs

namespace VR.Transit

open VR.Apparatus

-- ============================================================
-- §1. HasFiniteGeneratorStructure — the Tier 2 domain structure
-- ============================================================

/-- `HasFiniteGeneratorStructure T ι`: T carries an explicit generating family indexed
by ι.

A finite-generator structure consists of one field:
  • `gens : ι → T`   — the generating family (the witness, carried as data).

**Architectural role — Tier 2 domain structure.**
This mirrors `HasSeparabilityStructure` (Apparatus.Separability): where separability
carries a dense sequence `denseSeq : ℕ → T`, this carries a generating family
`gens : ι → T`. Both follow the Tier-2 data rule (CLAUDE.md §5): the witness is an
explicit data field of an *axiom-free type*, never a `Prop`-level `∃`. Any classical
*existence* (of a basis, of generators) is pushed into whatever instance constructs
this structure for a concrete type, never into the class or the bridges below.

**Why no `Finset` field** (FINDING TR-FW1, face 2): the finite index set is NOT a
field of this class. A `Finset ι` field would inject `[propext, Quot.sound]` into the
class type itself (the `Multiset` quotient), and the pointwise bridge 1a would inherit
it merely by referencing the class — destroying the axiom-free pointwise tier. The
finite index set is therefore supplied as an explicit argument to the aggregating
bridge `finiteSpan_provides_factorisable` (§3), where it is operand data and cannot
contaminate pointwise bridges. The class stays `[]`, exactly like separability.

**Minimal.** One field — the generating family. No finiteness, algebraic, or spanning
hypothesis is bundled here. The class names the generators; a *specific* finite
combination is built from an explicit `Finset ι` and coefficients supplied at 1b.

## Axiom profile: [] (data class, one axiom-free field, no axioms introduced) -/
class HasFiniteGeneratorStructure (T ι : Type*) where
  /-- The generating family on the index ι (the witness, carried as data). -/
  gens : ι → T

-- ============================================================
-- §2. Stage 1a — generator-level (pointwise) bridge
-- ============================================================

/-- Generator-level (pointwise) bridge: if `g` is globally operational on PA-elements
and `f` agrees with `g` on every generator, then `f` is `Factorisable` at each
generator `gens i`.

**Statement.**
  [HasFiniteGeneratorStructure T ι]
  + hg_op    : ∀ x : T, PA x → PB (g x)          (g globally operational)
  + hg_agree : ∀ i : ι, f (gens i) = g (gens i)  (agreement on generators)
  → Factorisable PA PB f (gens i)                (for each specific generator i)

This is the separability pattern (`separability_provides_factorisable`) transported
to an abstract generator index with no topology: the witness `g`, its global
operationality, and the local agreement at `gens i` are exactly the three components
of `Factorisable`. The proof is the explicit tuple `⟨g, hg_op, hg_agree i⟩`.

**Pointwise ⇒ axiom-free.** No aggregation occurs (the conclusion is at a single
operand), so no `Finset.sum` is touched and the bridge is `[]` — the same reason
separability is `[]`. This holds precisely because the class carries no axiom-bearing
field (FINDING TR-FW1, face 2).

## Axiom profile: []
  Pure propositional logic: the proof is ⟨g, hg_op, hg_agree i⟩.
  No analysis, no Classical.choice, no propext, no Quot.sound. -/
theorem finiteGen_provides_factorisable
    {T ι B : Type*} [HasFiniteGeneratorStructure T ι]
    {PA : T → Prop} {PB : B → Prop} {f g : T → B}
    (hg_op : ∀ x : T, PA x → PB (g x))
    (hg_agree : ∀ i : ι, f (HasFiniteGeneratorStructure.gens (T := T) i)
                       = g (HasFiniteGeneratorStructure.gens (T := T) i))
    (i : ι) :
    Factorisable PA PB f (HasFiniteGeneratorStructure.gens (T := T) i) :=
  ⟨g, hg_op, hg_agree i⟩

-- ============================================================
-- §3. Stage 1b — additive-span (aggregating) bridge
-- ============================================================

/-- Additive-span (aggregating) bridge: for additive maps `f g : T →+ B` that agree
on every generator, with `g` globally operational, `f` is `Factorisable` at any
explicit ℤ-combination `∑ i ∈ s, c i • gens i` of the generators, for an explicit
finite index set `s : Finset ι` and coefficients `c : ι → ℤ`.

**Statement.**
  [AddCommGroup T] [AddCommGroup B] [HasFiniteGeneratorStructure T ι]
  + (f g : T →+ B)
  + hg_op    : ∀ x : T, PA x → PB (g x)
  + hg_agree : ∀ i : ι, f (gens i) = g (gens i)
  + (s : Finset ι) (c : ι → ℤ)
  → Factorisable PA PB (f : T → B) (∑ i ∈ s, c i • gens i)

**Operand-not-operation at the linear-combination level (Finding S4-A).**
Agreement on the generators forces agreement on the whole additive span, because an
`AddMonoidHom` commutes with finite sums (`map_sum`) and with integer scaling
(`map_zsmul`). The witness is `g` itself: it is globally operational by `hg_op`, and
on the specific operand `∑ i ∈ s, c i • gens i` the maps `f` and `g` coincide —
  f (∑ i ∈ s, c i • gens i) = ∑ i ∈ s, c i • f (gens i)   [map_sum, map_zsmul]
                            = ∑ i ∈ s, c i • g (gens i)   [hg_agree]
                            = g (∑ i ∈ s, c i • gens i)   [map_zsmul, map_sum].
The operationality of the output is fixed by the operational *data* of the operand —
the explicit index set `s` and coefficients `c` — not by `f`.

**Aggregating ⇒ choice-free, not axiom-free.** Summing over `s` routes through
`Finset.sum`, hence `propext` (set-extensionality) and `Quot.sound` (the `Multiset`
quotient). These are the irreducible cost of *any* aggregation and are constructive;
the point — and the Stage-1 experiment — is that `Classical.choice` does NOT appear:
finite additive transit is constructive. Passing the finite index set as an explicit
`Finset` argument (rather than as a `Fintype (Fin card)` instance) is what keeps
`Classical.choice` out (FINDING TR-FW1, face 1).

## Axiom profile: [propext, Quot.sound]
  `map_zsmul` is `[propext]`; `map_sum` over the explicit `Finset` `s` is
  `[propext, Quot.sound]` (the `Finset.sum`/`Multiset` foundation). No
  `Classical.choice`: the explicit `Finset` argument avoids the `Fintype`/`Finset.univ`
  inflation diagnosed in FINDING TR-FW1. -/
theorem finiteSpan_provides_factorisable
    {T ι B : Type*} [AddCommGroup T] [AddCommGroup B]
    [HasFiniteGeneratorStructure T ι]
    {PA : T → Prop} {PB : B → Prop}
    (f g : T →+ B)
    (hg_op : ∀ x : T, PA x → PB (g x))
    (hg_agree : ∀ i : ι, f (HasFiniteGeneratorStructure.gens (T := T) i)
                       = g (HasFiniteGeneratorStructure.gens (T := T) i))
    (s : Finset ι) (c : ι → ℤ) :
    Factorisable PA PB (f : T → B)
      (∑ i ∈ s, c i • HasFiniteGeneratorStructure.gens (T := T) i) := by
  refine ⟨g, hg_op, ?_⟩
  -- f (∑ i ∈ s, c i • gens i) = ∑ i ∈ s, c i • f (gens i)   [map_sum, map_zsmul]
  --                           = ∑ i ∈ s, c i • g (gens i)   [hg_agree]
  --                           = g (∑ i ∈ s, c i • gens i)   [map_zsmul, map_sum]
  simp only [map_sum, map_zsmul, hg_agree]

-- ============================================================
-- §4. FINDING TR-FW1 reproducer (the index-encoding artefact, in-file)
-- ============================================================
--
-- The full finding (both faces) is catalogued in T_FINDINGS_TRANSIT.md. This
-- `private` exhibit keeps face 1 reproducible inside the file: a `Fintype`/
-- `Finset.univ` index over `Fin n` inflates the profile to the full standard ceiling,
-- even for a `rfl` identity — the `Classical.choice` comes from the *index*, not from
-- additivity. It is `private` (not a public object) and uses `#print axioms`, not
-- `example`, so the inflated profile can actually be printed.

private theorem tFW1_exhibit_univ_pulls_choice {B : Type*} [AddCommGroup B]
    (w : Fin 3 → B) : (∑ i, w i) = ∑ i, w i := rfl

#print axioms tFW1_exhibit_univ_pulls_choice
-- Expected: depends on axioms: [propext, Classical.choice, Quot.sound]
--   (contrast §3: the explicit-`Finset` span bridge is [propext, Quot.sound]).

-- ============================================================
-- Axiom audit — Stage 1 (final, option b), FiniteWitness.lean
-- ============================================================
-- STAGE: Stage 1 (final). SOURCE: PLAN.md Stage 1 + amendment (option b).
-- LEAN OBJECTS (3 public objects; tFW1_exhibit_univ_pulls_choice is private):
--   HasFiniteGeneratorStructure            (class, data, 1 field)
--   finiteGen_provides_factorisable        (theorem, pointwise bridge)
--   finiteSpan_provides_factorisable       (theorem, aggregating span bridge)
-- AXIOM AUDIT (target → actual, PLAN.md Stage 1 amendment):
--   HasFiniteGeneratorStructure        [] → []                                  ✓
--   finiteGen_provides_factorisable    [] → []                                  ✓
--   finiteSpan_provides_factorisable   [propext, Quot.sound] → [propext, Quot.sound] ✓
-- 1b is choice-free: the revised kill-criterion (PLAN amendment) for the aggregating
-- bridge is the ABSENCE of Classical.choice, not []; propext / Quot.sound are the
-- admissible aggregation cost. The experiment succeeded — Classical.choice did NOT
-- enter on the explicit Finset. Pointwise tier `[]` preserved (class carries only
-- the axiom-free `gens` field; FINDING TR-FW1, face 2).
-- CHECKS: no sorry, no admit.

#print axioms HasFiniteGeneratorStructure
#print axioms finiteGen_provides_factorisable
#print axioms finiteSpan_provides_factorisable

end VR.Transit
