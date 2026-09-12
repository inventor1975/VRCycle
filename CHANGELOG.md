# Changelog

## The perimeter: `VRCycle` = VR proper on `[]`, `VRClassical` = the classical register — 2026-09-12

The curator's question after the integrity programme: "can I say VR in Lean is without axioms?" The
answer was "not as one sentence — 51 of 111 modules", because VR proper and the classical material
around it (Mathlib's ℝ, `ZFSet`, `PSet`, Hahn–Banach, Brouwer over ℝ, the quotient bridges) lived in
one library. This commit draws the perimeter IN CODE:

* **Two Lake libraries in one package.** `VRCycle` is VR proper: `VR.lean`, the witnessed numbers
  (`Numbers/Integers` = `IntExpr`/`intEq` and its operations, `IntegersOp`, `IntegersOrd`,
  `RationalsOp`, `RealsOp`), `SetsZTL`, `SetsOp`, the forms (`Language`, `Realisability`, `Transit`,
  `Substrate`, `Examples`, `Conservativity*`), the topology tower (`FormalTopology` … `Tychonoff`), the
  continuum (`Branch`, `Spread`, `Cover`, `BarSound`, `Cantor`, `Cardinal`, `Choice`, `Model`,
  `Registers`, `UnitInterval`, `UniformContinuity`, `ListCore`), the apparatus (`Identity`, `Wrapping`,
  `Reference`, `ModeA`, `ModeB`, `Factorisation`, `InterMorphism`, `Composition`, `FormsIntegration`)
  and the instruments (`Meta/CSRNorm`, `Meta/DependsOn`). `VRClassical` depends on it and holds
  everything stated ABOUT Mathlib objects or lifted to Lean's `Quotient`: `Algebra`, `Audit`,
  `Brouwer`, `Sets` (ZFC over `ZFSet`), `SetsZFA`, `Transit`, the old `Numbers/{Rationals,Reals,Complex}`
  over Mathlib and the new `Numbers/IntegersBridge` (`ℤ_VR := Quotient …` and Theorem II.6 ≅ `Int`,
  split out of `Integers.lean`), `Continuum/{Rational,Real,GaussianRational,Spectrum,ClassicalBoundary}`,
  `Forms/Bridge` (with `mixed_AFA_two_registers`), `Topology/Bridge` and `_attic`, `Apparatus/{Instances,
  Numbers,Separability}`, the classical instances split out of the apparatus files
  (`VRClassical/Apparatus/{Wrapping,Reference,ModeA,ModeB,Factorisation,InterMorphism}` — ℝ/`IsComputableReal`,
  `OSetZFA`, Riesz, `embedPSet`), the apparatus QUOTIENT BRIDGE (`VRClassical/Apparatus/QuotientBridge`:
  `InterApparatusMorphism.lift`, `lift_mk`, `lift_compose`, `IsModeAOp_of_interApparatus`,
  `IsModeAOp_quotientMk`, `modeA_liftFn_quotientMk_eq_id`, `modeA_liftFn_comp_interApparatus`, all
  `[Quot.sound]`), `Meta/DoingNotBeing` and `Examples/`. Module names: `VRCycle.X` → `VRClassical.X`;
  imports rewritten; `defaultTargets` builds both.
* **The guard.** `VRCycle/Guard.lean` (imported by the root) runs `#assert_axiom_free_library VRCycle`
  (new command in `Meta/DependsOn.lean`): the build of the core FAILS if any declaration of any
  `VRCycle.*` module carries `propext`, `Quot.sound`, `Classical.choice` or `sorryAx`; structural
  constants and meta code (anything mentioning a `Lean.*` constant) are skipped. Measured on this
  commit: **1516 declarations checked, all on `[]`**. The sentence "VR is formalised in Lean 4 with an
  empty axiom list" is now a build invariant of the `VRCycle` library, not a claim.
* **Last residues repaid.** `SetsOp/Describable`: the enumeration of finite descriptions no longer
  uses Mathlib's `deriving Encodable` (`Classical.choice` via `Nat.unpair_pair`); it is built by nested
  finite stages (`stage n` = every description of depth ≤ n, a list) and a diagonal `descEnum k` =
  `k`-th entry of stage `k`; surjectivity by structural induction with the `[]` list lemmas of
  `ListCore` — the 2026-06-08 "decision (A)" flag is closed. `Continuum/Choice` no longer imports
  `ClassicalBoundary` (the formal-register contrast `not_continuity` is classical by design and lives
  in `VRClassical`). `SetsOp/Becoming` imports `Mathlib.Data.Nat.Init` directly instead of the whole
  continuum. `Apparatus/FormsIntegration` no longer depends on the Mathlib-number instances.
* **What "without axioms" means here, stated once:** without the three declared axioms of Lean
  (`propext`, `Quot.sound`, `Classical.choice`) and without `sorry`. Lean's type theory — the
  calculus of inductive constructions with its `Prop`, universes and the `Quot` primitive — is the
  proof checker, not an axiom of VR; that is the curator's reading and the honest one.
* Not done: the per-module README prose still cites the old paths for the classical modules; the
  blueprint likewise. Cosmetic, to be swept separately.

## Integrity programme, steps 4–5: topology verdict and the witnessed apparatus — 2026-09-12

* **Step 4 — topology.** Verdict recorded in the header of `Topology/Bridge.lean`: the operational
  tower (`FormalTopology`, `Operational`, `Continuous`, `Product`, `Compact`, `Tychonoff`) is on `[]`
  (census 0/0/0 per module); cover families are predicates `S → Prop` (Mathlib's `Set S` is that
  definition, no extensionality used), the operational content runs on finite lists of basics.
  `Topology/Bridge` is the Mathlib FRAME bridge — `SatSet.ext ← Set.ext`, `CompleteLattice`,
  `Order.Frame.ofMinimalAxioms` — kind 3 in VR-LOGIC §1, named, not hidden; no operational
  consumer imports it. Not done (a rebuild, the curator's call): moving the cover families
  themselves from predicates onto `OpSet`.
* **Step 5 — apparatus without `Quotient`.** `Apparatus/Composition.lean` §2b: witnessed Mode A
  `IsModeAOpW f := ∀ a b, a ≈ b → f a ≈ f b` for endomorphisms `f : Q → Q` (definitionally the
  endomorphism case of `InterApparatusMorphism`); identity element `id` (not `Quotient.mk`),
  composition, identity and associativity laws pointwise up to `≈` (`Setoid.refl`), invariance
  under pointwise `≈` (`of_pointwise`, the witnessed replacement for `funext` equalities of lifted
  maps), congruence of composition, the cross-level `interApparatus_comp_modeAW` and the pointwise
  functor law. 11 objects, offenders 0/0/0. The three `Quotient` theorems
  (`IsModeAOp_quotientMk`, `modeA_liftFn_quotientMk_eq_id`, `modeA_liftFn_comp_interApparatus`)
  stay as the quotient bridge on `[Quot.sound]`. The reverse bridge (`Q → Quotient s` back to a
  witnessed map) needs `Quotient.out` and is not provided — T→O absence in miniature.
* Programme 1→5 complete. Outside `[]` remain: bridges (kind 3) and Mathlib-object instances.

## Integrity programme, step 1a: `csr_ring` and the witnessed rationals — 2026-09-12

The curator's programme (2026-09-12): VR must stand on itself from arithmetic to the top — numbers
on `[]` as witnessed layers, then sets = `SetsZTL`/`SetsOp`, forms over them, topology over them,
apparatus with witnessed identity. Step 1 is the number floor.

* **New instrument `Meta/CSRNorm.lean` — `csr_ring`, a `ring` on `[]` up to an equivalence.**
  A structure `CSR α` (an equivalence `r` that is a congruence for `add`/`mul`/`neg`, and the
  commutative-ring laws up to `r`); polynomial expressions reified into `PE`, normalised into
  sorted signed monomials by a computable `norm`; `norm_sound` proved once from the fields;
  `eq_of_norm` closes `r lhs rhs` when the normal forms coincide (equality decided by kernel
  evaluation, `Nat.decEq`/`instDecidableEqList`, both on `[]`). Measured: the four-pair identity
  that `simp`-driven AC-rewriting could not finish in 300 s closes in the blink of an eye, whole
  test file 1.6 s; `#print axioms` empty. No cancellation `m + (−m) = 0` (done by hand where
  needed). Found on the way: `List.getD` and overlapping-pattern `match` splitters carry `propext`.
  Instances: `VRObj.csr` (`vr_ring`), `IntExpr.csr` up to `intEq` (`int_ring` — pairs as atoms,
  no unfolding), `QExpr.csr` up to `qEq` (`rat_ring`).
* **`Numbers/IntegersOp.lean` extended:** `vmul_right_cancel` (through `O`/`O_inv` and
  `Nat.eq_of_mul_eq_mul_right`), canonical-form products, `imul_ne_zero`, **`imul_cancel_right`**
  (`e·g ≈ f·g`, `g ≉ 0` ⟹ `e ≈ f`), `imul_eq_zero`, decidable equality of `VRObj` and of `intEq`.
* **New `Numbers/RationalsOp.lean` — ℚ_VR with witnessed identity on `[]`:** `QExpr` (numerator
  and denominator as integer pairs, denominator `≉ 0`), `qEq` by cross-multiplication, `qEq_trans`
  by cancellation, `qadd`/`qneg`/`qmul`/`qinv`/`qofInt` with their congruences (`num_nz_respects`:
  a non-zero numerator is a property of the class), the field laws up to `qEq`, `qzero_ne_one`,
  the embedding `qofInt` a ring homomorphism. Every theorem on `[]` (offenders 0/0/0).
* **Step 1b — `Numbers/IntegersOrd.lean`, the order on `[]`.** `vle a b := ∃ n, a + n = b` on VR
  numbers (a witnessed difference, decided by the structural `vleB`; total, antisymmetric, cancellation
  of a positive factor); on integer pairs `intLe` by the cross-sum criterion — respects `intEq`, total,
  decidable, compatible with `iadd` and with `imul` by a positive pair in both directions;
  `intPos_iff` (positive ⟺ `≈ (succ n, 0)`), `intLt_trichotomy`. `csr_ring` hardened: reads
  `succ x` as `x + 1`, refuses metavariables, decides equality of normal forms by evaluation before
  building the proof term.
* **Step 1c — `RationalsOp` with the order.** Denominators now positive (`den_pos : intPos den`);
  the inverse keeps them positive by a sign case (`qinv`), and the sign of the numerator is a class
  property (`num_pos_respects`); `qle`/`qlt` by cross-multiplication — congruence, transitivity by
  cancellation of a positive factor, totality, trichotomy, decidability, compatibility with `qadd`,
  positivity of sums and products (`qpos_iff`). 46 audited theorems, all on `[]`.
* **Step 1d — the continuum's ℚ and ℂ moved onto VR's own numbers.** `Continuum/Rational.lean` no
  longer builds a second ℚ over Mathlib's `ℤ`: `PreQ := QExpr`, and `Qop` is the quotient BRIDGE
  over the witnessed layer — every law lifted, so `CommRing Qop` and `Qop.mul_inv_cancel` are on
  `[Quot.sound]` (were `[propext, Quot.sound]`), the lifted order on `[propext, Quot.sound]`
  (`propext` is the price of lifting a `Prop`), and `Qop.ofRat` is axiom-free (it only reads
  `q.num`/`q.den`; `Classical.choice` has left the module entirely — it came from `Rat.add`).
  `Continuum/GaussianRational.lean` likewise: witnessed `GaussE` (pairs of pre-rationals, `gEq`
  componentwise, `g_ring` = `rat_ring` per component, `|z|² > 0` for `z ≉ 0`, total inverse
  `z̄/|z|²`, `gmul_inv_cancel` on `[]`) and the quotient bridge `GaussQ` (`CommRing`, `Inv`,
  `DecidableEq`, `mul_inv_cancel` on `[Quot.sound]`). `Spectrum.lean` table and guards updated
  (`Qop.ofRat` now asserted choice-free). Full build green.
* **Instruments for the real layer (same day).** `cr_ring`: the ring normaliser WITH cancellation
  (`CR` = `CSR` + `a + (−a) ≈ 0`; coefficient monomials, merge, cancel), so `int_ring`/`rat_ring`/
  `gauss_ring` now close `x + (−x) ≈ 0`-type identities too; the tactic also works for a variable
  structure (projection matching by arity), which is what its own soundness proofs use.
  **`cr_linarith`**: linear arithmetic on `[]` — `OCR` (ordered commutative ring up to `≈`: `le`
  respects `≈`, preorder, translation-invariant, `0 ≤ 1`, positive numerals cancel), the certificate
  theorem `OCR.le_of_cert` (`(c₀+1)(R − L) − Σ cᵢ(Bᵢ − Aᵢ)` normalises to a numeral `k` ⟹ `L ≤ R`),
  Fourier–Motzkin certificate search in meta code over `Rat`, hypotheses collected from the context
  (`lt a b` used as `le (a+1) b`). `int_linarith` (`IntExpr.ocr`) and `rat_linarith` (`QExpr.ocr`).
  This replaces `omega`/`linarith` (both `propext`) for the ℤ/ℚ inequality reasoning of the reals.
* **Step 1e — the reals on VR's own numbers.** `Continuum/UnitInterval.lean` rebuilt on integer
  pairs (`intval : Branch → ℕ → IntExpr`, prefix structure and Cauchy bound by `int_linarith`).
  New `Numbers/RealsOp.lean`: a pre-real is a sequence of pre-rationals with an explicit modulus
  (within `ε_k = 1/2^k`), identity = eventual closeness at every precision; `rneg`/`radd`/`rmul`
  termwise, the Cauchy estimates through power-of-two bounds (`rbounded`) and the four-products
  trick for `|a·c| ≤ P·Q`, closed by `rat_linarith`; every ring law termwise by `rat_ring`;
  `0 ≉ 1`; `RExpr.cr`. All on `[]`. `Continuum/Real.lean` is now the bridge: `Pre := RExpr`,
  `Real` the quotient, `CommRing Real` on `[Quot.sound]` (was `[propext, Quot.sound]` over Mathlib
  ℤ, 1087 lines), and **`Pre.ofBranch` — the point named by a branch, as the Cauchy sequence
  `intval α n / 2^n` — on `[]`**. Removed with the old file, to be rebuilt on the witnessed layer
  (step 1f): the order `le`/`lt`, apartness, the witnessed inverse `invPos`.

* **Step 1f — order, apartness, reciprocal of ℝ_op on the witnessed layer** (`RealsOp` §6):
  `rle` (eventually `x_n − y_n ≤ ε_k`, every `k`), `rlt` (eventually `y_n − x_n ≥ ε_k`, some `k` — a
  witnessed separation), `rapart`; preorder, antisymmetry up to `rEq`, congruences, irreflexivity
  of `<`; `PosWitness x k N` (`ε_k ≤ x_n` from `N` on) and **`rinvPos`**: the reciprocal of a
  positive pre-real is the termwise `qinv'` — no Euclidean division at all in this design —
  Cauchy through `|1/x_m − 1/x_n| = |x_n − x_m|·(1/x_m)(1/x_n)` and `1/x ≤ 2^k` (`qinv'_bound`);
  `rinvPos_mul : x · (1/x) ≈ 1`. All on `[]`. Lifted to `Real` (`≤`, `<`, `apart`, `le_antisymm`)
  on `[propext, Quot.sound]` (the `Prop` lift); `Pre.invPos` is an alias on `[]`.

## Integrity programme, steps 2–3: sets and forms on the operational universe — 2026-09-12

* **Step 2 — the set floor.** No code: `SetsOp` (set = revealing functionality, identity = witnessed
  bisimulation, ZF without Foundation, AFA as a theorem, all on `[]`) and `SetsZTL` are THE set
  floor of the tower; `Sets/` (Mathlib `ZFSet`, the ZFC register) is a bridge, kind 3.
* **Step 3 — VR-Forms over `OpSet`.** `Realisability.lean`: `isRealisable` classifies a term by
  `DecidableEq FormalTerm` (a `match` on string literals compiles to a splitter that reaches
  `propext`) and reads ⌜∅⌝, ⌜omega⌝, ⌜pair⌝ in `OpSet` — membership `Mem`, identity `Equiv`
  (the pair has as members the sets *identical by witness* to `a` or `b`); new ⌜AFA⌝, realised by
  `OpSet.decorate`. `Transit.lean`: π likewise, `translate_implies_realisable` by cases on the
  class. `Substrate.lean`: the 2026-05-28 gate's `Acc (· ∈ ·)` is refuted as a substrate on the
  operational universe (AFA holds there — groundedness is a MODE, `OpSet.IsGrounded`, not the
  substrate); the substrate of an operational set is its own revealing, witnessed by the identity
  bisimulation. `Examples.lean`: Russell/Vitali/ℝ/℘(ℕ) as before; `mixed_omega_two_register` over
  `OpSet`. All of these on `[]`. `Bridge.lean` keeps the ZFC-register reading as
  `isRealisableZFC` (Mathlib `ZFSet`/`PSet`: `bridge_AFA` refuted, Conjectures IV.1–2 open) and
  states the junction **`afa_two_registers`: ⌜AFA⌝ realised in `OpSet`, ⌜AFA_Statement⌝ refuted
  in `PSet`** — the ZFA boundary of VR-Sets located as a boundary of groundedness, not of
  operationality. Full build green.

**Step 1 stands.** The number floor ℤ → ℚ → ℂ → ℝ is now VR's own from `VR.lean` up: witnessed
layers on `[]` (`IntegersOp`/`IntegersOrd`, `RationalsOp`, `GaussE`, `RealsOp`), quotient bridges
on `[Quot.sound]` (`Qop`, `GaussQ`, `Real`), `Classical.choice` gone from the continuum's ℚ/ℂ/ℝ.
The instruments that made it a day's work rather than weeks: `csr_ring`/`cr_ring` (reflection,
`Meta/CSRNorm.lean`) and `cr_linarith` (Farkas certificates by Fourier–Motzkin, checked by
reflection) — both on `[]`.

## Empty-list sweep, waves 4–8 — 2026-09-12

Census: modules with no axiom at all 36 → **43** (of 107; 47 carry `Classical.choice` through
Mathlib's ℚ/ℝ/ZFSet and are the declared limit; 17 remain cleanable). Each wave was measured with
`#axiom_offenders_all` over the touched modules → 0 / 0 / 0 before its commit.

* **Wave 4 — `Forms/ConservativityComprehension.lean`.** All de Bruijn lemmas (`subst_lift`,
  `lift_lift`, `lift_subst`, `subst_subst`, `lift_subst'`), the π-commutation lemmas and
  `conservativity` / `conservativity_comprehension_concrete` on `[]`: `omega` and `simp only`
  closures replaced by a local `NatAux` (five hand lemmas) and `show`/`rw`; `genInjectivity` off.
  The third storey of conservativity is now axiom-free like the first two.
* **Wave 5 — `SetsZTL/Stages.lean`.** `ListCore` gains `nth`, `nth_ext`, `nth_append_*`,
  `take_length'`, `take_append_of_le`, `length_append'` (all by induction); the stage court
  (`through_mono`, `pad_through`, `stage_eq_super`, `through_pointwise`, `apart_earned`) no longer
  reaches propext through `List.ext_getElem` / `getElem?` / `take_range`.
* **Wave 6 — `Topology/{Operational,Compact,Continuous}.lean`.** `binaryUnion` interleaves by
  `ListCore.halve` (no `%`, `/`, `omega`); `List.toDescribable` enumerates by `ListCore.nth`
  (`mem_of_nth` / `nth_of_mem` on `List.Mem`); the pairing function behind `preimage_of_relator` is
  rebuilt on `halve` with fuel, every inequality by hand; `OpContinuous.id` / `comp` use
  `isOperationalCov_mono` and direct `IsDescribable` instances instead of `Set.ext` rewrites; the
  `Bool` compactness witness is inhabited by `List.Mem`, not `decide`.
* **Wave 7 — new `Numbers/IntegersOp.lean`.** The ring laws of ℤ_VR restated where VR performs
  them: on `IntExpr` up to the witnessed identity `intEq`, proved from `T1`/`T2`/`T3` and hand
  `vmul_comm` / `vmul_assoc` — no quotient, no Mathlib `Int`, no `ring`; every theorem on `[]`.
  `Integers.lean` (the quotient + the isomorphism with `Int`) stays as the bridge to Mathlib.
* **Wave 8 — `Topology/Tychonoff.lean`.** `ListCore` gains `mem_cons_iff`, `mem_append_iff`,
  `mem_map_iff`, `mem_filter_iff`, `mem_flatMap_iff`, `bnot_decide_eq_true_iff`, `decMem` (decidable
  membership by structural recursion) and `subl`/`filter_mem_subl` (the only fact about
  `List.sublists` the proof used). Tychonoff uses them through `.mp`/`.mpr` only — `rw` with an
  `Iff` goes through `propext` — and drops core's `LawfulBEq` membership instance for the file.
  `tychonoff_binary`, `prodWitness` and the four `prodF_*` theorems carry no axioms.

**Measured, and left to the curator.** The class-2 plan ("replace the `Quotient` carriers of
`Qop`/`Real` by witnessed identity") does not by itself reach `[]`: `PreQ` and `Pre` are built over
Mathlib's `ℤ`, and the core lemmas `Int.add_comm`, `Int.add_assoc`, `Int.mul_comm`, `Int.mul_add`,
`Int.zero_add`, … each carry `propext` (checked with `#print axioms`); only `Int.natCast_add/mul`,
`Int.sub_eq_add_neg`, `Int.add_zero`, `Int.one_mul`, `Int.neg_neg` are free. Dropping the quotient
removes `Quot.sound` and leaves `propext`. Reaching `[]` for the operational continuum's arithmetic
floor means rebuilding its integer substrate (ℤ_VR / Nat pairs with hand lemmas, as `IntegersOp`
does) under `Rational.lean` (468 lines), `Real.lean` (1087), `GaussianRational.lean`, `UnitInterval.lean`
— a rebuild, not a wave. Also found: `ac_rfl` carries `[propext, Quot.sound]`; `Nat.mul_assoc`,
`Nat.right_distrib`, `Nat.add_left_cancel`, `Nat.sub_add_cancel` carry `propext` while
`Nat.add_comm/assoc`, `Nat.mul_comm`, `Nat.left_distrib` are free.

Remaining cleanable (propext/Quot.sound counts): `Continuum.Real` 70/53, `GaussianRational` 39/39,
`UnitInterval` 18/18 (all on the ℤ substrate above); `Sets.VRNumbers` 18/23 (ZFSet — class 3);
`Numbers.Integers` 16/34 (the bridge); `Algebra.*`, `Forms.*` bridges, `Apparatus.Composition` 0/3
(generic theorems about `Quotient`), `Transit.FiniteWitness` (Finset) — class 3. Class 1 is now
exhausted: every remaining `propext`/`Quot.sound` is either the ℤ substrate (class 2) or a statement
about a Mathlib object (class 3) — see VR-LOGIC §1, "three kinds of axiom in Lean, three verdicts".

## Empty-list sweep, waves 1–3 — 2026-09-12

The curator set the bar for the whole cycle at the EMPTY axiom list: an axiom is a thing posited,
VR is acts; where the cycle cannot reach `[]` that is a declared limit of operationalism, to be
named, not accommodated. Three instruments in `Meta/DependsOn.lean` measure it: `#axiom_census`
(per module: how many constants carry propext / Quot.sound / Classical.choice, and through which
external lemma each first arrives), `#axiom_offenders_all` (the constants, one by one, with the
lemma they inherit the axiom from) and `#axiom_frontier` (where an axiom enters one constant's
closure). Census before: 20 modules with no axiom at all; after waves 1–3: **36** (of 106).

What propext turned out to be, module by module, and what replaced it:
* auto-generated `injEq` lemmas (`Eq.propIntro`) for every inductive — never used by the cycle;
  `set_option genInjectivity false` after the namespace line in 12 files (an `… in` form cannot sit
  between a doc comment and its declaration). `Transit.lean` named one; the hand `Iff`
  `FormalTerm.mk_eq_iff` replaces it on `[]`;
* `simp only` closing goals through `eq_self`: `piTr_embed`, `piTr_subst` (two storeys), Cantor's
  diagonal, `no_node_surjection` — rewritten with `show`/`rw`/`Bool.noConfusion`;
* core list and division lemmas (`List.range_succ`, `map_append`, `length_map`, `length_range`,
  `append_inj_left'`, `prefix_refl`, every `Nat` `/` and `%` lemma) — all reach propext through
  `simp`; `Continuum/ListCore.lean` proves the needed ones by induction on `[]`, and `decodeNode`
  is now structural (fuel + `halve`), no well-founded recursion, no division;
* `Nat.find_le` / `le_find_iff` in `continuity_of_nbhd` — `find_spec`/`find_min` are axiom-free, the
  antisymmetry is argued from them;
* `omega` (Int simp lemmas) in `trEmpty_closed` — `Nat.noConfusion`, `Nat.not_lt_zero`.

Now on the empty axiom list, among others: `Theorem_11_VR_PA` (as before), all three storeys'
central theorems — `Conservativity.conservativity`, `ConservativityFOL.conservativity`,
`conservativity_empty_concrete` — and the operational continuum's `operational_cantor`,
`powerset_diagonal`, `no_node_surjection`, `nodes_describable`, `cover_sound`,
`uniform_continuity`, `NbhdFun.continuity_of_nbhd`, `operational_choice_available`.
`ConservativityComprehension.conservativity` still carries `[propext, Quot.sound]` (de Bruijn
lemmas proved with `omega`) — next wave.

Not yet done, by kind (census of 2026-09-12): tactic artefacts in `Continuum.Real`/`GaussianRational`/
`UnitInterval`, `Numbers.Integers`, `Sets.VRNumbers` (`ring`, mathlib `Int.instMonoid`),
`ConservativityComprehension`, `SetsZTL.Stages`, `Topology.Tychonoff` — mechanical, sizeable;
carrier `Quotient` (`Quot.sound` via `Quotient.sound`/`funext`) in `Qop`/`Real`/`Apparatus.Composition`
— a redesign after the `SetsOp` pattern (witnessed identity, no quotient; `OpSet.ext` is on `[]`);
statements about mathlib objects (`ZFSet` in VR-Forms' realisability, `AddSubgroup`, `Finset`,
`Set.ext` in Topology) — a declared limit unless the referent is moved to the cycle's own universe.
The per-module tier tables in `README.md` predate this sweep; the census is the current truth.

## Preprint 12: "Choice as an Act" v1.0.0 — 2026-07-17

Twelfth work of the preprint line (`preprints/12_VR-Choice_EN_v1_0_0.pdf`,
6 pp). Russell's socks, cardinals as becomings, and the productive
continuum — the rule/act split of choice, cardinal comparison as a
witnessed act (order partial by design; trichotomy priced at full AC,
declined), the uniform Cantor–Lawvere ladder, uncountability re-signed
from wall to generator (Post productivity), the anonymous-symmetry
impossibility (Angluin, machine-checked), and the DC demarcation. Ten
central theorems on the EMPTY axiom list. Written to be verified from
zero: a single mathlib-free file `Verify_Choice_standalone.lean` reproves
all ten in under a second (`lean Verify_Choice_standalone.lean`). Zenodo
sheet: `preprints/12_VR-Choice_ZENODO.md`. Tag: `choice-v1.0.0`.

## Continuum: operational cardinals — 2026-07-17

`Continuum/Cardinal.lean`: the cardinal as a type of BECOMING (the curator's
definition). A comparison is an ACT — the witness is data: **`natIntoBranch`**
(an explicit injection ℕ ↪ Branch); **`cantor_ladder`** — the
Cantor–Lawvere diagonal, uniform over every floor, on the **empty axiom
list**: no type surjects onto its power floor — the doubling ladder never
closes from below; **`nat_strictly_below_branch`** — the first step fully
earned (injection up + `branches_not_enumerable` back). TIER PASS same day:
the whole module AND the branch diagonal (`branches_not_enumerable`, which
had carried `[propext]` since June via a `simp` on a Bool hypothesis) now
stand on the **empty axiom list** — own-recursion `beq` lemmas, explicit
`Bool.noConfusion`; `selectors_not_enumerable` cleared by cascade. The order
is partial
by design: trichotomy of cardinals ⟺ AC — cited, not claimed. Choice-free
throughout. Full build green.

## Continuum: Russell's socks — 2026-07-17

`Continuum/Choice.lean` §Socks: selection over indistinguishable pairs split
into rule and act. **`no_symmetric_selector`** — no swap-symmetric selection
rule exists (the Fraenkel–Mostowski sock statement in miniature) — on the
**empty axiom list**; **`selectors_not_enumerable`** — the selectors are
exactly the branches, so the acts are a continuum (`[propext]`, inherits the
branch diagonal). Rules: zero. Acts: uncountable. `Classical.choice` nowhere
in the section: theorems about choice that borrowed none. Full build green,
8369 jobs. Companion runs and the act/object reading live in the ZTL
workspace (dilemmas, 2026-07-17).

## VR-Transit v1.0.0 — 2026-05-29

Tenth work: transit conservativity (the apparatus is axiom-neutral) plus a
bounded, predicate-track witness library. Git tag `v1.15-vr-transit-v1.0.0`.
Zero `sorry`/`admit`; full build 3366 jobs. A clarity result, not new power.

### Witness library — two new providers (four total, counting the inherited one)

New in VR-Transit:

- **`finiteGen_provides_factorisable`** — pointwise finite-generator bridge, `[]`.
- **`finiteSpan_provides_factorisable`** — aggregating bridge over an explicit
  `Finset`, choice-free `[propext, Quot.sound]`.
- **`located_witness_operational` / `located_provides_factorisable`** — the located
  subspace structure supplies the witness `f ∘ P_M` (realised Level-B),
  `[propext, Classical.choice, Quot.sound]` (source: the operation, not the apparatus).

Inherited: the **separability** provider (VR-Apparatus, Stage 6) completes the
spanning set — density, projection, finiteness — all predicate-track.

### Conservativity (I), exhibited

- **`Conservativity.lean`** — no public objects; `#print axioms` attribution shows the
  apparatus column empty across representatives. Four-source cost decomposition:
  operation ⊕ pointwise-witness ⊕ aggregation ⊕ carrier-encoding ⊕ apparatus ∅.
  The universal form is meta (kernel-level), exhibited on representatives.

### Findings (`T_FINDINGS_TRANSIT.md`)

- **TR-FW1** — finite-transit cost lives in the carrier encoding, not the algebra
  (two removable faces: `Fintype`/`Finset.univ` inflation; `Finset`-in-class contamination).
- **TR-C1** — the operation source is a spectrum (`[propext]` algebraic ↔ `[P,C,Q]` analytic).
- **TR-R1** (headline) — the witness method reaches as far as the obstacle is
  witnessable; the reference track reduces to `Classical.choice` (unwitnessable),
  so its provider was dropped (recognition discipline).

### Stages

| Stage | Content | File |
|---|---|---|
| 1 | Finite-generator providers (pointwise + aggregating) | `Transit/FiniteWitness.lean` |
| 2 | Conservativity exhibited (axiom attribution) | `Transit/Conservativity.lean` |
| 3 | Located provider (structural witness) | `Transit/Located.lean` |
| 4 | Reference-track recon → drop (TR-R1) | — |
| 5 | Blueprint Chapter 11 | `blueprint/src/chapters/10_transit.tex` |

## v1.0.0 — 2026-05-28

### Mode B audit object delivered

- **`tychonoff_binary`** — binary Tychonoff for compact formal topologies,
  multistep constructive proof via Vickers 2006 Theorem 19.
- Axiom profile `[propext, Quot.sound]` — **zero `Classical.choice`**.

### Bridge to mathlib

- **`instFrame (SatSet T)`** — `FormalTopology` produces `Order.Frame`
  constructively, without acquiring `Classical.choice` through mathlib's
  classical infrastructure (positive deviation from PLAN_7 expectation).

### Stages completed

| Stage | Content | File |
|---|---|---|
| 1 | `FormalTopology`, `CoverGen`, foundational structure | `FormalTopology.lean` |
| 2 | `OperationalFormalTopology`, `OpCoverGen` | `Operational.lean` |
| 3 | Continuous maps via relators | `Continuous.lean` |
| 4 | Binary products | `Product.lean` |
| 5 | `CompactWitness`, `OperationalCompact` | `Compact.lean` |
| 6 | Binary Tychonoff (Mode B audit object) | `Tychonoff.lean` |
| 6b | Concrete `Unit × Bool` operational compactness | `Tychonoff.lean` |
| 7 | Bridge to `Order.Frame` | `Bridge.lean` |

### T-findings catalogued

**18 distinct architectural amendments** through cycle (T0-T21 with T18
skipped, T4/T10 absorbed).  Full catalog in `T_FINDINGS.md`.

### Cumulative statistics

- **~85+ public objects**.
- **~2700 active lines** of Lean.
- **3296 build jobs** successful.
- **Zero `Classical.choice`** across all stages.
- Build dependencies: Lean 4.29.1, mathlib (as pinned).

### Files (this release)

Root:
- `README.md` — project entry document, audit summary, reproducibility.
- `CHANGELOG.md` — this file.
- `T_FINDINGS.md` — 18-finding methodology catalog.
- `FINAL_AXIOM_AUDIT.md` — `#print axioms` verification artifact.
- `VERSION` — `1.0.0`.
- `STAGE_*_REPORT.md` — per-stage completion reports.
- `T*_AMENDMENT_REPORT.md` — retroactive amendment reports.
- `PLAN_*.md` — word-first PLAN documents per stage.
- `RELEASE_PREP_v1.0.0.md` — release preparation instructions.

Lean code:
- `VRCycle/Topology.lean` — top-level module.
- `VRCycle/Topology/*.lean` — six stage files.
- `VRCycle/Topology/_attic/*.lean` — historical artifacts.

### Deferred to v1.1.0

- **Bridge B** (`FormalTopology → TopCat` via formal points).
- **Compactness payoff** (`OperationalCompact → CompactSpace`).
- **Frame functoriality** (continuous maps lift to frame homomorphisms).
- **Abstract `instProdOperationalCompact`** (currently concrete-only
  for `Unit × Bool`; requires architectural amendment per
  `STAGE_6b_HALT_DIRECTION.md` analysis).
- **Additional concrete examples** beyond `Unit × Bool`.
- **Operational `pair` continuous map** (Finding T9 territory).

### Methodological highlights

- **Recognition discipline at workflow level**: 18 architectural
  amendments all caught at word-first phase or pre-implementation paper
  sketch.  No architect direction error propagated into committed Lean code.
- **Three Classical-avoidance techniques** deployed in Stage 6
  (constructive proof of binary Tychonoff):
  1. List induction extraction (replaces `push_neg`'s Classical fallback).
  2. Direct lambda De Morgan for `¬(A ∧ B)` cases.
  3. Explicit `haveI` typeclass cascades (replaces `by_cases` Classical fallback).
- **Boundary-crossing surprise**: Stage 7's bridge to mathlib's
  `Order.Frame` remained constructive (anticipated to acquire Classical).

### License

As per the VR cycle's standard license.

---

*This is the first major release of VR-Topology.*
