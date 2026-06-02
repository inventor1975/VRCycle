-- VRCycle/Continuum/Cover.lean
-- Operational Continuum (Path 1) — Stage B (file 2): A↔B cementing (the free part).
--
-- STAGE: B. SOURCE: PLAN_OPERATIONAL_CONTINUUM.md. Vehicle: HYPOTHESIS.
--
-- ## Honest scope note (a halt-and-report)
-- The FULL soundness of the formal cover for branches — `IsBar B → ∀ α, α.Meets B`
-- (`binarySpread.cov [] B → every branch meets B`) — is NOT free by structural
-- induction on `CoverGen`.  The `local_` and `ref_mono` constructors pull opposite
-- ways: `local_` (cover narrows to `{c ∈ U | c ≤ b}`) needs the witness node DEEPER
-- (≥ b), while `ref_mono` (node refined b → a, longer) only delivers a witness at the
-- depth of `b`, shallower than `a`.  Concretely `cov [false,false] {[false],[true]}`
-- is derivable (ref_mono from `cov [] {[false],[true]}`) and a branch through `[0,0]`
-- meets the bar at depth 1 — shallower than the start node — so any "witness ≥ start"
-- motive (needed for `local_`) breaks on `ref_mono`.
-- Full bar-soundness is therefore the genuine bar theorem, tied to BAR INDUCTION
-- (a Brouwerian principle) — it belongs to the hypothesis-tracked layer, NOT here.
--
-- ## What this file does (the genuinely free, choice-free A↔B cement)
--   * `Branch.take_succ` — one extra performed bit extends the segment;
--   * `through_meets_children` — a branch through `s` meets `children s` (the `basic`
--     coverage case, soundly, for branches);
--   * `Branch.Meets.mono` — meeting is monotone in the bar.

import VRCycle.Continuum.Branch

namespace VRCycle.Continuum

-- ============================================================
-- §  Helper: one-step extension of a performed segment
-- ============================================================

/-- Appending the next bit extends the performed segment by one. -/
theorem Branch.take_succ (α : Branch) (n : ℕ) :
    α.take (n + 1) = α.take n ++ [α n] := by
  simp [Branch.take, List.range_succ]

-- ============================================================
-- §  One-step soundness: a branch through `s` meets its children
-- ============================================================

/-- **One-step soundness (the `basic` coverage case, for branches).**  A branch passing
through node `s` meets the basic cover `children s`: its next performed segment is
`s ++ [α s.length]`, one of the two children.  Choice-free; this is the sound direction
of the spread's defining branching. -/
theorem through_meets_children (α : Branch) (s : List Bool)
    (h : α.Through s) : α.Meets (children s) := by
  refine ⟨s.length + 1, ?_⟩
  rw [Branch.take_succ, h]
  cases α s.length <;> simp [children]

-- ============================================================
-- §  Monotonicity of meeting
-- ============================================================

/-- Meeting a bar is monotone: a larger bar is still met. -/
theorem Branch.Meets.mono {α : Branch} {B B' : Set (List Bool)}
    (hsub : B ⊆ B') (h : α.Meets B) : α.Meets B' := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hsub hn⟩

-- ============================================================
-- Axiom audit — Stage B (file 2)
-- ============================================================
#print axioms through_meets_children
#print axioms Branch.Meets.mono

end VRCycle.Continuum
