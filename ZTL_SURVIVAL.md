# ZTL_SURVIVAL.md — VR Part II, step (в): the survival ledger

**Generated 2026-07-12** under criterion **C2** (curator's decision,
2026-07-12). Companion Lean spot-checks: `VRCycle/SetsZTL/Survival.lean`
(all on the empty axiom list). ZTL — Zero-Trust Logic: DOI
[10.5281/zenodo.21318982](https://doi.org/10.5281/zenodo.21318982).

## The criterion

**A proof survives the move onto ZTL iff it stands below the classical
floor — no `Classical.choice` in its measured axiom footprint.**

Why this is the right reading (each link measured in the ZTL
repository):

1. ZTL's fallen laws are exactly the **laws of free truth** — they mint
   a verdict for an unverified atom (LEM, p→p as a law, K, the fallen
   De Morgan, ¬¬-elimination…). Their Lean fingerprint is classical
   case analysis: applying LEM to a proposition is declaring every atom
   pre-verified, which is precisely what zero trust forbids.
2. At the level of **premised rules** ZTL keeps what constructive
   inference keeps (E20: the 14-rule classical battery coincides with
   IPC verdict-for-verdict, 14/14, including both casualties).
3. Alive rules are **witness constructors** (E21 §3, and the Lean twins
   `EqVerdict.refl/symm/composeT`, `memCongrVerdict` — all axiom-free):
   a constructive proof from earned premises IS a chain of ZTL-alive
   rules, delivering the conclusion's certificate.
4. VR's operational theorems are **premised by construction**
   (operationality = earned inputs), so they are rules, not laws — the
   category that survives.

Hence the four-tier axiom ledger that the VR cycle has kept since its
first work — `[]` / `[Quot.sound]` / `[propext, Quot.sound]` / Tier-3 —
turns out to have been the ZTL-survival audit all along. *"VR always
stood on ZTL"* is, by this criterion, literal.

**The reading discipline (do not overclaim).** The audit bounds the
GIVEN proof, never the theorem: Tier-3 means *this proof does not
move*, not *the theorem is false on ZTL* (the witness method is an
auditor, not a separator). And the audit is blind to impredicativity
(the Power-set finding in SetsOp §13): ZTL says nothing about it
either; noted as a shared boundary, not a defect.

## The ledger (MEASURED)

Live sweep: 405 audited public objects re-elaborated 2026-07-12
(`#print axioms`, `lake build` green, 8369 jobs). Wings without inline
`#print` statements are anchored by flagship probes (below) and their
own documented audits (`FINAL_AXIOM_AUDIT.md` for Topology, generated
2026-05-28).

### Moves wholesale (choice-free wings)

| wing | clean / choice-tainted | note |
|---|---|---|
| VR formal system (`VR.lean`) | flagship `Theorem_11_VR_PA` **axiom-free `[]`** | the VR↔PA equivalence itself survives with room to spare |
| VR-Forms | 45 / 0 | the transit apparatus moves verbatim |
| VR-SetsOp | 39 / 2 | the operational set universe; the 2 = `Describable` (see below) |
| VR-SetsZTL | 38 / 0 | Part II itself — built clean by design |
| Continuum | 88 / 4 | the operational continuum; the 4 = `Qop.ofRat` (mathlib-ℚ bridge) and hypothesis-side `not_continuity` (the *classical* boundary exhibit — its being classical is the content) |
| VR-Topology | complete ledger in `FINAL_AXIOM_AUDIT.md`: **zero choice** | `tychonoff_binary` re-probed 2026-07-12: `[propext, Quot.sound]` ✓ |
| ℤ_VR line | `Theorem_II_6_IntVR_Int`: `[propext, Quot.sound]` | the integer floor moves |
| VR-Sets (classical register) | `Pairing`/`Power`: `[propext, Quot.sound]` | notable: the ZF-closure facts over `ZFSet` are themselves choice-free — the classical register's *theorems* move even though its ambient logic is classical |

### Stays on the classical shore (and why)

| wing | clean / choice-tainted | source of the choice |
|---|---|---|
| VR-Audit | 0 / 17 | **by design**: formal-register accounting (Hahn–Banach wrapping) — choice is the subject matter, not a leak |
| VR-SetsZFA | 3 / 11 | mathlib `PFunctor.M` substrate — irreducibly Tier-3 even at its destructor; this is the *measured reason* SetsOp was built (§13) |
| ℚ/ℝ/ℂ correspondence theorems | Tier-3 | **substrate leak**: mathlib `Rat`/`Real`/`Complex` carriers pull choice at the type level; the choice-free number line lives in Continuum (`Qop`, `GaussQ`, operational `Real`) — the survivors are already built |
| Brouwer–Sperner | `brouwer_stdSimplex`: Tier-3 | the ℝ substrate again; the combinatorial Sperner layer is separate |
| Operational Algebra | 63 / 10 | the 10 = mathlib carriers (`Rat` instances, `Units` bridges) — content vs packaging split as measured in A-findings |
| Apparatus | 59 / 18 | the 18 = Mode-A/computability exhibits that *quote* classical objects deliberately |
| Transit | 5 / 2 | the 2 = the located-witness provider, whose Tier-3 source is the operation, not the apparatus (conservativity exhibit) |
| SetsOp/Describable | 2 objects | borrowed mathlib pairing plumbing; constructively true, removable at a documented price (TODO in the file header) |

**Bottom line.** Everything VR calls operational moves: the formal
system, Forms, the operational sets (both registers of Part II), the
operational continuum, formal topology, the integer line. What stays
behind is exactly what the cycle itself had already flagged as
classical — by design (Audit, the classical registers), by substrate
(mathlib ℚ/ℝ/ℂ, `PFunctor.M`), or by borrowed plumbing (Describable).
No operational theorem died in the move; the fallen laws of ZTL were
never load-bearing in the operational corpus. **Verified, not
postulated.**

## Spot-checks (Lean, `VRCycle/SetsZTL/Survival.lean`)

Three flagships exhibited in the moved form — as certificate
constructors over ZTL atoms, all `[]`:

1. **Strong extensionality**: `extVerdict` — from member-matching data
   the identity certificate is constructed (`OpSet.ext`); a law in the
   classical register, a rule in the operational one.
2. **AFA-as-theorem**: `afaVerdict` — two decorations of one graph
   carry earned identity at every vertex.
3. **Membership verdicts**: `MemVerdict` (the membership twin of
   `EqVerdict`, closing step (а)'s gap): the vn register is total and
   classical (`vnMemVerdict_ne_Z`, `vnMemVerdict_T_iff`), and earned ∈
   transports along earned ≈ (`memCongrVerdict` = the rule form of
   `mem_congr`).
4. **Continuum apartness**: already in `Stages.lean` (`apart_earned`).

## Honest caveats

* The criterion audits proofs, not theorems (auditor, not separator).
* Wings without inline `#print` are anchored by flagship probes and
  documented ledgers, not by a full live sweep (VR core, Numbers,
  Sets, Topology, Brouwer).
* The audit does not see impredicativity; shared boundary with ZTL.
* Criterion **C3** (a ZTL-valued semantic model for VR statements —
  truth in a model instead of proof audit) is stronger and deferred by
  the curator's decision as a possible separate work.

## Acknowledgements and AI disclosure

Prepared with the substantial participation of the AI system Claude
(Anthropic) under the direction of the human author, who owns all
decisions and the content. Every MEASURED claim is reproducible:
`lake build` re-emits the `#print axioms` ledger; the ZTL-side
measurements are the stands E20–E22 in the ZTL repository.
