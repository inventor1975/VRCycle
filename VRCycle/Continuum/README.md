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
- **CONT-8** `omega` on a **conjunction** goal fails / drags `Classical.choice`+`sorryAx`; a single `ℤ` inequality via `omega` is axiom-free. Split `∧` into separate `omega` calls. (State two-sided bounds, prove each side separately.)

## Operational ℝ (`Real.lean`) — Bishop reals over `ℤ`, **below the ℚ/ℝ choice floor**
A real is a **dyadic asymptotic-Cauchy sequence** `Pre = (seq : ℕ → ℤ)` with
`∀k ∃N ∀m,n≥N, |seq m·2^n - seq n·2^m|·2^k ≤ 2^(m+n)` (pure `ℤ`, ring-closed); `Real := Quotient`
by asymptotic agreement. **All choice-free `[propext, Quot.sound]`** (plan: `PLAN_OPERATIONAL_REAL.md`).

A full commutative ring **`CommRing Real`, choice-free** — the first VR development with arithmetic
**below the floor that pins the rest of the cycle to Tier-3**:
- `Real` type + equality (setoid quotient); `Pre.ofBranch` (each branch's `[0,1]` point is a real).
- **Order/apartness**: `Pre.le`, `Pre.lt`, `Pre.apart`; `le_refl`/`le_trans`/`lt_irrefl`; `le_antisymm_equiv`.
- **`+`, `−`, `0`, `1`, ℤ-embedding** (`Real.add`/`neg`/`ofInt`); abelian-group laws.
- **`×`** `Pre.mul` (`seq n = (x_n·y_n) ediv 2^n`) — the product **capstone**: full Bishop product
  Cauchy proof (clear denominators → split `A·B−A'·B'` → bound by magnitudes (`Pre.bounded`) +
  differences via `mul_abs_bound` → cancel `2^(m+n)`).
- **All eight ring laws**: `mul_comm`/`mul_one` (pointwise); `mul_add` distributivity (floor-of-sum
  gap `∈{0,1}`, constant); `mul_respects` (single-index congruence → `Real.mul` on the quotient);
  **`mul_assoc`** — both `(xy)z`, `x(yz)` approximate `abc/2^{2n}`, and `|(xy)z−x(yz)| ≤ 2^Bx+2^Bz+1`
  is a **constant** (operand magnitudes), beaten by `2^n` — *no vanishing needed*.
- **`instance : CommRing Real`** — subsumes the abelian group (one source, no diamond); the instance
  and every law obtained through it stay `[propext, Quot.sound]`.

**Deferred:** `inv` (needs an apartness witness — field structure, the hardest) and a constructive
completeness / payoff theorem (M5).  Constructive caveats persist (no trichotomy, located-only sup) —
`Real ≠` classical ℝ; it is **Bishop's commutative ring of reals, machine-checked choice-free**.

## Operational unit interval (`UnitInterval.lean`)
The integer-numerator substrate feeding `Real` (and the first below-floor result): a branch's `[0,1]`
point is `intval α N : ℤ` over `2^N`; `intval_nonneg`/`intval_lt_pow`/`intval_mono_step` choice-free;
plus the reusable `ℤ` toolkit (`two_pow_*`, `int_two_pow_bound`, `int_ediv_bracket`, `mul_cross_pow`,
`mul_abs_bound`, `dyadic_bound`, cancellation/scaling bridges) — all `[propext, Quot.sound]`.

- **CONT-9** (the `ℤ`-arithmetic choice toolkit) general `mul_nonneg`/`mul_le_mul`/`mul_lt_mul_of_pos_*`/
  `mul_zero`/`neg_mul`/`pow_pos`/`pow_le_pow_right`/`abs_mul`/`lt_or_eq_of_le`/`Nat.le.dest` all pull
  `Classical.choice`. The **choice-free** replacements: `Int.mul_nonneg`, `Int.mul_le_mul`(4-arg),
  `Int.mul_le_mul_of_nonneg_left/right`, `Int.le_of_mul_le_mul_left/right`, `pow_add`, `Int.lt_or_le`,
  `abs_le.mp/mpr`, `ring`, `omega`, plus induction-without-dest for `2^·` monotonicity. Also: numeric
  literals in a standalone `have :` default to `ℕ` (truncated `-`); ascribe `(2:ℤ)`. `omega` does not
  atomise `z.ediv d` for a variable divisor unless terms are syntactically uniform (no `set`).
- **CONT-10** the generic order glue `le_refl` / `le_trans` / `·.trans` on `ℤ` pulls `Classical.choice`
  (the `LinearOrder ℤ` instance path); **choice-free** replacements: `omega` (reflexivity, and any
  *linear* transitivity) and `Int.le_trans` (when the terms are nonlinear products `omega` can't atomise).
  Also: `omega` over a `set`-bound nonlinear product re-distributes it — `clear_value` first to keep it
  opaque. The `CommRing Real` instance built from choice-free fields stays `[propext, Quot.sound]`.

## Files
`Spread` (A) · `Branch` (B1) · `Cover` (B2) · `UniformContinuity` (B3) · `BarSound` (B4) ·
`ClassicalBoundary` (B5) · `Registers` (B6) · `Model` (C) · `UnitInterval` (`ℤ` substrate) ·
`Real` (operational ℝ: group + multiplication, choice-free).
