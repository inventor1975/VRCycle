-- VRCycle/Continuum/ClassicalBoundary.lean
-- Operational Continuum (Path 1) — Stage B (file 5): the classical boundary of the principles.
--
-- STAGE: B. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md.
--
-- ## Goal of (1): which Brouwerian hypotheses are "free" (classically valid) vs not?
-- The three hypotheses used in this tower are NOT on equal footing:
--   * `FanTheorem`   — classically TRUE  (compactness of Cantor space / König's lemma);
--   * `BarInduction` — classically TRUE  (monotone bar induction);
--   * `Continuity`   — classically FALSE (a discontinuous `Branch → ℕ` exists).
--
-- ## What this file proves
-- `not_continuity : ¬ Continuity` — machine-checked, classically.  This pins the
-- asymmetry sharply: `Continuity` (WC-N) is the lone IRREDUCIBLY INTUITIONISTIC
-- principle — it cannot be discharged classically, so `uniform_continuity`'s content is
-- genuinely Brouwerian and requires a model (Stage C) to be non-vacuous.  By contrast
-- `FanTheorem` and `BarInduction` are classically valid and could in principle be
-- discharged as classical theorems — but only via the compactness/König apparatus
-- (cylinder sets, continuity of projections, finite subcover), which is sizeable; those
-- discharges are deferred (honest scope note, cf. CONT-2's pattern).
--
-- ## Axiom profile: [propext, Classical.choice, Quot.sound] — and that is the POINT.
-- `not_continuity` USES classical logic; that it is provable AT ALL classically is
-- exactly the statement that `Continuity` is classically false.

import VRCycle.Continuum.Branch
import Mathlib.Data.List.Basic

namespace VRCycle.Continuum

/-- **`Continuity` (WC-N) is classically false.**  The functional that returns `0` on the
all-`false` branch and `1` on any other branch has no finite modulus at the all-`false`
branch: any depth-`n` agreement is shared by a branch that is `true` from `n` on, where
the functional jumps.  Hence `Continuity` is the lone irreducibly intuitionistic
principle of the tower; it cannot be discharged classically. -/
theorem not_continuity : ¬ Continuity := by
  classical
  intro hC
  -- `F` = 0 on the all-false branch, 1 otherwise (a discontinuous functional).
  let F : Branch → ℕ := fun α => if (∀ i, α i = false) then 0 else 1
  obtain ⟨n, hn⟩ := hC F (fun _ => false)
  -- The perturbed branch: false below `n`, true from `n` on — agrees to depth `n`.
  let β : Branch := fun i => if i < n then false else true
  have hagree : Branch.take (fun _ => false) n = Branch.take β n := by
    simp only [Branch.take]
    apply List.map_congr_left
    intro i hi
    simp [β, List.mem_range.mp hi]
  have hFz : F (fun _ => false) = 0 := if_pos (fun _ => rfl)
  have hFβ : F β = 1 := by
    apply if_neg
    intro hall
    have hn' := hall n
    simp [β] at hn'
  have hbad := hn β hagree
  rw [hFz, hFβ] at hbad
  exact absurd hbad (by decide)

-- ============================================================
-- Axiom audit — Stage B (file 5)
-- ============================================================
-- Classical by design: provability of `not_continuity` IS the asymmetry.
#print axioms not_continuity

end VRCycle.Continuum
