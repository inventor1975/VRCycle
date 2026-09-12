-- VRCycle/Continuum/Spectrum.lean
-- THE OPERATIONAL NUMBER SPECTRUM ℤ → ℚ → ℂ → ℝ → Ω, consolidated and machine-witnessed.
--
-- Every node below is built BY HAND from ℤ, staying below the `Classical.choice` floor (never
-- mathlib ℚ/ℝ, which are entirely Tier-3 — Finding CONT-7).  The spectrum makes two boundaries
-- precise, both machine-checked at the bottom of this file:
--
--   node            DecidableEq   order             inverse                 axioms
--   ─────────────────────────────────────────────────────────────────────────────────────────
--   ℤ_op            ✓             ✓                 —                       [] (IntegersOp/Ord)
--   ℚ_op  (Qop)     ✓             ✓ trichotomy      ✓ TOTAL                 witnessed layer []
--                                                                           (RationalsOp);
--                                                                           quotient bridge
--                                                                           [Quot.sound]
--   ℂ_op  (GaussQ)  ✓             ✗ (ℂ unorderable, ✓ TOTAL                 witnessed layer []
--                                   a CLASSICAL fact)                       (GaussE); bridge
--                                                                           [Quot.sound]
--   ℝ_op  (Real)    ✗ (Markov)    ✗ apartness       witnessed (`Pre.invPos`) [propext, Quot.sound]
--                                                                           (still over Mathlib ℤ —
--                                                                           integrity step 1e)
--   Ω               —             —                 —                       silhouette only
--
-- BOUNDARY 1 — the Markov line (decidability of zero):  ℚ/ℂ have a TOTAL inverse, choice-free,
--   because zero is DECIDABLE there; operational ℝ cannot (¬(x≈0) gives no modulus — Markov), so its
--   reciprocal `Pre.invPos` must take an explicit positivity/apartness witness.
--
-- BOUNDARY 2 — the typeclass line (content vs packaging):  the field CONTENT (`mul_inv_cancel`) is
--   choice-free (on `[]` in the witnessed layer, `[Quot.sound]` across the bridge), but the mathlib
--   `Field` typeclass forces `ratCast : ℚ → ·`.  Since 2026-09-12 `Qop.ofRat` only READS `q.num`/
--   `q.den` from Mathlib's `ℚ` structure and is itself axiom-free; what the `Field` label would pull
--   is Mathlib's `ℚ` arithmetic (`Rat.add` carries `Classical.choice`) — the label, not the doing.
--
-- ℂ (GaussQ) is a COMPLETENESS node: it INHERITS its base `Qop`'s operational character and opens no
-- new operational boundary (its lack of order is classical algebra, not operationality).

import VRCycle.Continuum.Rational
import VRCycle.Continuum.GaussianRational
import VRCycle.Continuum.Real
import VRCycle.Meta.DependsOn

open VRCycle.Continuum

/-! ### Boundary 2, machine-checked: field CONTENT free of choice, ℚ-`ratCast` PACKAGING not -/

#assert_not_depends_on Qop.mul_inv_cancel on Classical.choice
#assert_not_depends_on GaussQ.mul_inv_cancel on Classical.choice
#assert_not_depends_on Qop.ofRat on Classical.choice   -- reading `q.num`/`q.den` is pure data

-- The whole content/packaging table in one citable command:
#dependency_matrix [Qop.mul_inv_cancel, GaussQ.mul_inv_cancel, Qop.lt_trichotomy, Qop.ofRat]
  vs [Classical.choice]

/-! ### The whole operational line — not just the inverse — stays below the choice floor.
    Guards on the core ring operations of each node, so a future edit cannot silently pull
    `Classical.choice` into the operational number line without breaking the build. -/

-- ℚ_op: core ring operations, choice-free (complements the inverse guard above).
#assert_not_depends_on Qop.add_comm on Classical.choice
#assert_not_depends_on Qop.mul_comm on Classical.choice
#assert_not_depends_on Qop.left_distrib on Classical.choice

-- ℝ_op: the by-hand real built from ℤ (computable modulus) is choice-free in its operations.
#assert_not_depends_on Real.add_comm on Classical.choice
#assert_not_depends_on Real.mul_comm on Classical.choice
#assert_not_depends_on Real.mul_assoc on Classical.choice

/-! ### The decidable pole and the field content stay below the floor -/

#print axioms Qop.lt_trichotomy        -- ℚ trichotomy (ℝ lacks it)
#print axioms Qop.mul_inv_cancel       -- ℚ total inverse
#print axioms GaussQ.mul_inv_cancel    -- ℂ total inverse
#print axioms Qop.ofRat                -- reads Mathlib ℚ's fields: axiom-free since 2026-09-12
#print axioms VR.Numbers.qmul_inv_cancel       -- ℚ inverse, witnessed layer: []
#print axioms VRCycle.Continuum.gmul_inv_cancel -- ℂ inverse, witnessed layer: []
