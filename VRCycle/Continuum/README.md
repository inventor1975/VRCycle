# VRCycle.Continuum — operational continuum via choice/lawless sequences (Path 1)

An exploratory tower giving VR a **non-enumerable continuum** built operationally, with
the Brouwerian principles carried as **tracked hypotheses** (never adopted as axioms —
adopting them over classical mathlib would be inconsistent).

**Status:** exploratory. Not in the root `VRCycle.lean` aggregator; build per-module
(`lake build VRCycle.Continuum.<Module>`). All modules green, lint-clean.

## The three registers
- **operational** — a node `s : List Bool`, a finite performed segment (the "done").
- **formal** — actual infinity as a label (the existing VR formal register).
- **becoming / potential** — a branch `ℕ → Bool`, defined start + open lawless tail.

## Honest status of each result — REAL vs DERIVATION vs (classically) VACUOUS

| result | file | hypotheses | classical status | honest reading |
|---|---|---|---|---|
| `branches_not_enumerable` | Branch | none | `[propext]` | **REAL, unconditional.** Cantor diagonal. |
| `no_node_surjection` | Registers | none | `[propext, Quot.sound]` | **REAL, unconditional.** The payoff: the countable operational register cannot exhaust the becoming register. |
| `through_meets_children`, `Meets.mono` | Cover | none | `[propext]` | **REAL.** One-step cover soundness + monotonicity. |
| `cover_sound` | BarSound | `BarInduction` | classically **TRUE** hyp | **REAL derivation.** `BarInduction` is classically valid, so this is meaningful — it just makes bar induction explicit. |
| `uniform_continuity` | UniformContinuity | `Continuity`, `FanTheorem` | `Continuity` classically **FALSE** | **DERIVATION ONLY; VACUOUS in classical Lean** (see CONT-4). A valid implication, real in an intuitionistic model — not before. |
| `not_continuity` | ClassicalBoundary | none | `[…Classical.choice…]` | **REAL (classical).** `Continuity` is classically false. |

## Finding CONT-4 (the key honesty point)
Because `not_continuity` shows `Continuity` is **classically false**, every theorem that
assumes `Continuity` (here: `uniform_continuity`) has a hypothesis unsatisfiable in the
classical ambient, hence is **vacuously true in classical Lean**. Its content is genuine
only as (a) a derivation — "IF continuity, THEN uniform continuity" — usable in any
intuitionistic metatheory, or (b) inside a model where `Continuity` holds. Establishing
such a model (Kleene–Vesley / effective topos: computable functionals are continuous) is
**Stage C** — the genuine RUSS/INT capstone, and the only thing that makes the
`Continuity`-dependent results non-vacuous. Deferred (heavy).

The asymmetry, machine-checked: `FanTheorem`, `BarInduction` classically TRUE (results
under them are real derivations); `Continuity` classically FALSE (its results are
derivations awaiting a model).

## Findings
- **CONT-1** mathlib `Encodable (List Bool)` pulls `Classical.choice` here; hand-roll to stay Tier-2.
- **CONT-2** full bar soundness is not free by `CoverGen` induction (local_/ref_mono); needs bar induction (BarSound).
- **CONT-3** `lt_or_eq_of_le` pulls `Classical.choice`; use `omega` for Nat splits.
- **CONT-4** `Continuity`-dependent results are classically vacuous; real only in a model (Stage C).

## Files
`Spread` (A) · `Branch` (B1) · `Cover` (B2) · `UniformContinuity` (B3) · `BarSound` (B4) ·
`ClassicalBoundary` (B5) · `Registers` (B6).
