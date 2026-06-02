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
| `not_continuity` | ClassicalBoundary | none | `[…Classical.choice…]` | **REAL (classical).** `Continuity` is classically false (formal register). |
| `continuity_of_nbhd` | Model | none | `[propext, Quot.sound]` | **REAL, choice-free.** `Continuity` holds for operationally-presented functionals (operational register) — earned, not assumed. |

## Finding CONT-4 (the key honesty point)
Because `not_continuity` shows `Continuity` is **classically false**, every theorem that
assumes `Continuity` (here: `uniform_continuity`) has a hypothesis unsatisfiable in the
classical ambient, hence is **vacuously true in classical Lean**. Its content is genuine
only as (a) a derivation — "IF continuity, THEN uniform continuity" — usable in any
intuitionistic metatheory, or (b) inside a model where `Continuity` holds. Establishing
such a model is **Stage C** (`Model.lean`): `continuity_of_nbhd` proves `Continuity` holds
for **operationally-presented functionals** (`NbhdFun` — a finite-information associate,
total along branches), choice-free. So CONT-4 is **addressed over the operational domain**:
the `Continuity`-dependent content is non-vacuous there.

This realises **VR's two-register thesis, machine-checked, on a genuinely Brouwerian principle**:
`Continuity` is FALSE in the formal/classical register (`not_continuity`) and TRUE in the
operational register (`continuity_of_nbhd`). The asymmetry of the three hypotheses is also
machine-checked: `FanTheorem`, `BarInduction` classically TRUE; `Continuity` classically FALSE
but operationally TRUE.

## Findings
- **CONT-1** mathlib `Encodable (List Bool)` pulls `Classical.choice` here; hand-roll to stay Tier-2.
- **CONT-2** full bar soundness is not free by `CoverGen` induction (local_/ref_mono); needs bar induction (BarSound).
- **CONT-3** `lt_or_eq_of_le` pulls `Classical.choice`; use `omega` for Nat splits.
- **CONT-4** `Continuity`-dependent results are classically vacuous; addressed over the operational domain by Stage C (`continuity_of_nbhd`).
- **CONT-5** `Nat.find_eq_iff` pulls `Classical.choice`; `Nat.find_le` / `Nat.le_find_iff` are choice-free — prove find-equalities by antisymmetry.
- **CONT-6** `Finset.sum` (`∑`) and `if (b:Bool) then …` pull `Classical.choice` here; even `simp` does on some `ℤ` order goals. Use structural recursion, `cond`, and `omega`/`decide`.
- **CONT-7** (decisive) mathlib **`ℚ` is entirely Tier-3** — `(2:ℚ)+3`, `*`, `≤` all pull `Classical.choice` (the floor is the ordered-field substrate, not only `ℝ`). `ℤ`/`ℕ` are choice-free. So an operational continuum stays below the floor only by representing points over `ℤ` (integer numerator / `2^N`), never via mathlib `ℚ`/`ℝ`.

## Operational unit interval (ℝ-recon, `UnitInterval.lean`)
First step toward operational reals, and the first VR result **below the ℚ/ℝ choice floor**.
A branch's point in `[0,1]` is carried by its integer numerator `intval α N : ℤ` over `2^N`:
- `intval` axiom-free; `intval_nonneg`, `intval_lt_pow` (point in `[0,1)`), `intval_mono_step`
  all `[propext, Quot.sound]` — **choice-free** (where the same facts via mathlib `ℝ`/`ℚ` are Tier-3).
A full operational `ℝ` (field/order/limits over hand-rolled `ℤ`-dyadics) remains a large further build.

## Files
`Spread` (A) · `Branch` (B1) · `Cover` (B2) · `UniformContinuity` (B3) · `BarSound` (B4) ·
`ClassicalBoundary` (B5) · `Registers` (B6) · `Model` (C) · `UnitInterval` (ℝ-recon).
