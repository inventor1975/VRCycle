-- VRCycle.SetsNaive — VR-Sets, naive edition: UNRESTRICTED comprehension on ZTL's ground.
-- Curator's programme 2026-11-04/05: naive sets sit in ZTL "as if cast" — the classical laws
-- hold in every clean cell, a paradox finds itself as a dirty cell with a passport.  This
-- library is the LANGUAGE layer; the carrier (what a set is) stays SetsOp's pointed graph,
-- identity stays witnessed bisimulation.
--   N1 Syntax   — terms `{x : φ}` with no restriction, ∀ over the closed terms;
--   N2 Ground   — Kripke's least fixed point as an inductive predicate; comprehension is a law
--                 in every cell; the excluded middle is earned exactly in the clean cells;
--   N3 Passport — Russell = PARADOX (no consistent model decides it), the truth-teller set =
--                 UNDERDETERMINED (two consistent stipulations); clean cells are absolute;
--   N4 Bridge   — every term is an OpSet via its earned memberships (T-graph); earned ∈ ⇒
--                 OpSet.Mem; and the price: the two-valued carrier FORGETS the mark
--                 (`carrier_forgets_mark`: a clean ∅ and a dirty set are one OpSet);
--   N5 Ext      — extensionality as a META congruence: co-extensional sets (three-valued
--                 extension, the mark included) are indiscernible by every formula (`val_cong`);
--   N6 Strength — TOTAL cleanliness is trivial: the dirty probe D={x:R∈R} is the bottom of
--                 information, so a set deciding D is ∅ or V; every nontrivial set is dirty at D.
--                 Strength must be measured relative to clean probes;
--   N7 Leak     — …and the unbounded ∀ imports the dirt: A={x: x∈Empt ∧ ¬x∈Empt} has no member,
--                 is clean at every decided probe, yet "A is empty" is quarantined — in the LAZY
--                 register, which grounds cells and does not judge claims;
--   N8 Judge    — the verdict register (curator's correction 05.11): ZTL dispositions over
--                 completions.  "x ⊆ x for all x" and "A is empty" (by its definition) are NOT
--                 earned but EARNED IF STABLE; "A is empty" by the atom D∈A is OPEN — the
--                 disposition depends on where the judge cuts comprehension.  A completion of an
--                 infinite universe needs excluded middle: an explicit hypothesis, never an axiom.
-- Universe: potential infinity (the CLOSED terms, an inductive type of finite records); a
-- universal is earned by a RULE, never by a survey.  Axiom profile: [] throughout (guarded by VR/Guard.lean).
import VR.SetsNaive.Syntax
import VR.SetsNaive.Ground
import VR.SetsNaive.Passport
import VR.SetsNaive.Bridge
import VR.SetsNaive.Ext
import VR.SetsNaive.Strength
import VR.SetsNaive.Leak
import VR.SetsNaive.Judge
