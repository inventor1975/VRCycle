# Zenodo upload sheet — VR: Choice as an Act v1.0.0

**PUBLISHED 2026-07-17: DOI 10.5281/zenodo.21419290 (v1.0, CC BY 4.0). Verified: title/author/license/related-works as below; repo isSupplementedBy + both DOIs (ZTL, Part II) attached. DOI embedded in tex header; repo PDF NOT rebuilt — stays the exact published artifact.**

**READY. The curator publishes on Zenodo (manual step); this sheet only
prepares. New standalone record (not a new version of an existing one) —
this is a fresh work in the VRCycle preprint line (the twelfth).**

**Before uploading: create and push the git tag so the paper's
`choice-v1.0.0` reference resolves:**
```
cd VRCycle && git tag choice-v1.0.0 && git push origin choice-v1.0.0
```

**File to upload:** `preprints/12_VR-Choice_EN_v1_0_0.pdf` (6 pages)

---

**Resource type:** Publication → Preprint

**Title:** Choice as an Act: Russell's Socks, Cardinals as Becomings, and
the Productive Continuum, Machine-Checked on the Empty Axiom List

**Authors:** Reznik, Vitaly

**Version:** 1.0.0

**License:** Creative Commons Attribution 4.0 International (CC BY 4.0)

**Description (paste as-is):**

Three classical set-theoretic themes — the axiom of choice on
indistinguishable pairs (Russell's socks), the comparison of infinite
cardinals, and the uncountability of the continuum — are re-read
operationally: an assertion counts only as an act, performed and
witnessed, never as a completed object postulated into existence. Under
this reading each theme splits cleanly in two, and both halves become
short machine-checked theorems.

For the socks: no selection rule exists (no swap-symmetric selector
beyond any finite bookkeeping bound — the Fraenkel–Mostowski statement
in miniature, on the empty axiom list), while selection acts form a
continuum (the selectors are exactly the branches, which are not
enumerable). The deterministic half is itself a theorem — in an
anonymous network of identical automata started identically the
configuration stays constant across nodes at every round, for arbitrary
wiring, so no round distinguishes a unique node (the folklore core of
Angluin 1980, machine-checked, to our knowledge for the first time).

For cardinals: a comparison is an act whose witness is data — an
explicit injection from the naturals into the branches is performed; the
Cantor–Lawvere diagonal is proved uniformly for every floor of the
power-set ladder, on the empty axiom list; the resulting order is
partial by design, since cardinal trichotomy is equivalent to full AC
and is cited as a formal-register label rather than claimed.

For uncountability: the sign is flipped from prohibition to
productivity — the fugitive from any enumeration is computed by an
explicit term, so the continuum is productive in Post's sense: the
catalogue that reads itself extends itself. And dependent choice is the
performable part of choice (recursion on a history-dependent rule,
choice-free); what remains of full AC above DC is the part that can only
be written, not performed — the same remainder whose surrender dissolves
the Banach–Tarski decomposition (Solovay's model; cited as metatheory).

Nothing here is a new classical theorem; the mathematical content of
each proof is elementary and classical. The contribution is the
operational re-reading, the split of each theme into an impossible-rule
half and a performed-act half, the axiom pricing of every step, and the
machine check. The axiom of choice is not refuted — a symmetric-selector
impossibility is a statement about rules, while AC postulates an object
exempt from symmetry.

The paper is written to be verified from zero. A single self-contained
Lean 4 file (`Verify_Choice_standalone.lean`, no mathlib, no imports)
reproves all ten empty-axiom-list theorems in under a second — any
agent, human or machine, runs `lean Verify_Choice_standalone.lean` and
reads "does not depend on any axioms" ten times. The full corpus
verifies with `lake build`, and `#print axioms` lines exhibit the axiom
profile of every object. An empty axiom list is precisely a verdict two
parties who share no axioms and no trust can both confirm: the strongest
form of a checkable claim. The reliability of the results does not
depend on trusting the author, the AI that helped write the paper, or
this text — only the Lean 4 kernel.

AI disclosure: this work was carried out with the substantial
participation of the AI system Claude (Anthropic; this preprint —
Claude Fable 5) in a dialogue setting; all design decisions, fork
choices, and final responsibility rest with the human author.

**Keywords:**
axiom of choice; dependent choice; Russell's socks; Fraenkel–Mostowski;
Cantor diagonal; Lawvere fixed point; cardinal comparison; uncountability;
productive sets; Post; Brouwer choice sequences; leader election; Angluin;
constructive mathematics; operational mathematics; Lean 4; machine-checked
proofs; empty axiom list; zero-trust; reproducibility

**Related/alternate identifiers** (relation types are DataCite/Zenodo
dropdown values — `isRelatedTo` is NOT one; use the below):
- https://github.com/inventor1975/VRCycle — **is supplemented by**
  (the Lean 4 corpus; tag `choice-v1.0.0`;
  `VRCycle/Continuum/{Choice,Cardinal}.lean` and the standalone
  `Verify_Choice_standalone.lean`)
- 10.5281/zenodo.21318981 — **references** (ZTL, Zero-Trust Logic —
  concept DOI; the logic this work operationalizes)
- 10.5281/zenodo.21326038 — **references** (VR Part II — same preprint line)

**Additional notes (paste into "Additional notes"):**
The preprint text is CC BY 4.0; the accompanying repository code is under
the VR cycle's standard license. The central theorems carry the empty
axiom list (verified by `#print axioms`); reproduce the fast path with
`lean Verify_Choice_standalone.lean` (no dependencies) or the full corpus
with `lake build` (Lean 4.29.1 + mathlib, as pinned).

---

**After publication:** paste the new version DOI back here and embed it
in the tex header + this sheet. The repo PDF is NOT rebuilt afterwards —
it stays the exact published artifact.
