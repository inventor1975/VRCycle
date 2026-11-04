-- VRCycle.SetsNaive — VR-Sets, naive edition: UNRESTRICTED comprehension on ZTL's ground.
-- Curator's programme 2026-11-04/05: naive sets sit in ZTL "as if cast" — the classical laws
-- hold in every clean cell, a paradox finds itself as a dirty cell with a passport.  This
-- library is the LANGUAGE layer; the carrier (what a set is) stays SetsOp's pointed graph,
-- identity stays witnessed bisimulation.  The bridge between the two memberships (two-valued
-- `OpSet.Mem` / three-valued grounded `∈`) is the next stage.
--   N1 Syntax   — terms `{x : φ}` with no restriction, ∀ over the closed terms;
--   N2 Ground   — Kripke's least fixed point as an inductive predicate; comprehension is a law
--                 in every cell; the excluded middle is earned exactly in the clean cells;
--   N3 Passport — Russell = PARADOX (no consistent model decides it), the truth-teller set =
--                 UNDERDETERMINED (two consistent stipulations); clean cells are absolute.
-- Universe: potential infinity (an inductive type of finite records); a universal is earned by
-- a RULE, never by a survey.  Axiom profile: [] throughout (guarded by VR/Guard.lean).
import VR.SetsNaive.Syntax
import VR.SetsNaive.Ground
import VR.SetsNaive.Passport
