-- VRCycle/Continuum/Spectrum.lean
-- THE OPERATIONAL NUMBER SPECTRUM ℤ → ℚ → ℂ → ℝ → Ω, consolidated and machine-witnessed.
--
-- Every node below is built BY HAND from ℤ, staying below the `Classical.choice` floor (never
-- mathlib ℚ/ℝ, which are entirely Tier-3 — Finding CONT-7).  The spectrum makes two boundaries
-- precise, both machine-checked at the bottom of this file:
--
--   node            DecidableEq   order             inverse                 axioms
--   ─────────────────────────────────────────────────────────────────────────────────────────
--   ℤ_op            ✓             ✓                 —                       below the floor
--   ℚ_op  (Qop)     ✓             ✓ trichotomy      ✓ TOTAL                 [propext, Quot.sound]
--   ℂ_op  (GaussQ)  ✓             ✗ (ℂ unorderable, ✓ TOTAL                 [propext, Quot.sound]
--                                   a CLASSICAL fact)
--   ℝ_op  (Real)    ✗ (Markov)    ✗ apartness       witnessed (`Pre.invPos`) [propext, Quot.sound]
--   Ω               —             —                 —                       silhouette only
--
-- BOUNDARY 1 — the Markov line (decidability of zero):  ℚ/ℂ have a TOTAL inverse, choice-free,
--   because zero is DECIDABLE there; operational ℝ cannot (¬(x≈0) gives no modulus — Markov), so its
--   reciprocal `Pre.invPos` must take an explicit positivity/apartness witness.
--
-- BOUNDARY 2 — the typeclass line (content vs packaging):  the field CONTENT (`mul_inv_cancel`) is
--   choice-free, but the mathlib `Field` typeclass forces `ratCast : ℚ → ·`, which reads mathlib ℚ
--   (Tier-3) and pulls `Classical.choice`.  The DOING (operations) is operational; the `Field` LABEL
--   (packaging/being) is not — the doing/being thesis at the typeclass level.
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
#assert_depends_on Qop.ofRat on Classical.choice

-- The whole content/packaging table in one citable command:
#dependency_matrix [Qop.mul_inv_cancel, GaussQ.mul_inv_cancel, Qop.lt_trichotomy, Qop.ofRat]
  vs [Classical.choice]

/-! ### The decidable pole and the field content stay below the floor -/

#print axioms Qop.lt_trichotomy        -- ℚ trichotomy (ℝ lacks it)
#print axioms Qop.mul_inv_cancel       -- ℚ total inverse
#print axioms GaussQ.mul_inv_cancel    -- ℂ total inverse
#print axioms Qop.ofRat                -- ratCast forced by `Field`: pulls choice
