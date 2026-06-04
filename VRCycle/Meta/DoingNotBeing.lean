-- VR — "Doing, not being": operationality is TOTAL on objects, SPLIT on constructions.
--
-- The published cycle already proved, machine-checked, both halves of one thesis:
--
--   • BEING is total.  `Forms.operational_total : ∀ c, Operational c` — every object is
--     operational; the element predicate `IsOperational` is `fun _ => True` in every algebra
--     instance (ℤ, ZMod n, ℚ, ℚˣ, …).  As a property of *what a thing is*, operationality does
--     not discriminate: it is a total substrate.
--
--   • DOING is split.  The SAME proposition admits a choice-free derivation and a
--     `Classical.choice`-dependent one.  As a property of *how a thing is established*,
--     operationality discriminates — and (unlike the element predicate) the split is DECIDABLE
--     and UNIVERSAL: `Meta/DependsOn` computes it for any declaration by finite reachability over
--     the environment, and gates the build on it.
--
-- So the universal "operational split" the curator sought does NOT live on values (there it is
-- total or undecidable) — it lives on CONSTRUCTIONS, where it is already in hand.  This file is the
-- sharpest exhibit of the contrast: ONE statement (one being), TWO proofs (two doings), the
-- operational boundary resting entirely on the acts, never on the object.
--
-- This is "nothing is — all is doing" realized at the meta level: the operational/non-operational
-- boundary itself is a property of doing, not of being.

import Mathlib
import VRCycle.Meta.DependsOn

namespace VR.DoingNotBeing

/-! ### One being, two doings

`trans_doing` and `trans_being_via_choice` have the **identical type** — the same proposition, the
same *being*.  Only the *act* of proving differs: `omega` decides linear integer order directly,
free of the classical `LinearOrder` path; the general `le_trans` resolves through that path and so
transitively invokes `Classical.choice` (Finding CONT-10). -/

/-- DOING A — choice-free.  `omega` settles the order fact without the classical order machinery. -/
theorem trans_doing : ∀ a b c : ℤ, a ≤ b → b ≤ c → a ≤ c := by
  intro a b c h₁ h₂; omega

/-- DOING B — choice-dependent.  The identical statement, proved through the general order lemma
`le_trans`, which transitively pulls `Classical.choice` over the `LinearOrder ℤ` substrate. -/
theorem trans_being_via_choice : ∀ a b c : ℤ, a ≤ b → b ≤ c → a ≤ c :=
  fun _ _ _ h₁ h₂ => le_trans h₁ h₂

end VR.DoingNotBeing

open VR.DoingNotBeing

/-! ### The split, certified at build time

| construction | proves | `Classical.choice` |
|--------------|--------|--------------------|
| `trans_doing` (omega)            | the order fact | **free**    |
| `trans_being_via_choice` (le_trans) | the SAME fact | **depends** |

Same proposition; the operational boundary is entirely on the *doing*.  Each assertion fails the
build if violated — the `depends` row certifies the split is genuine, not vacuous. -/

#assert_not_depends_on trans_doing on Classical.choice
#assert_depends_on trans_being_via_choice on Classical.choice

#print axioms trans_doing
#print axioms trans_being_via_choice

-- The contrast in one citable command — the differential witness for operationality-as-doing:
#dependency_matrix [trans_doing, trans_being_via_choice] vs [Classical.choice]
