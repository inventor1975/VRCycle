-- VR/SetsNaive/Realise.lean
-- VR-Sets, naive edition — Stage N16: the bridge completed — naive terms REALISE carrier sets.
--
-- A naive term `t` realises an operational set `X` when, at every carrier probe (every name
-- `nm Y`), the grounded verdict on `Y ∈ t` is the carrier's verdict on `Y ∈ X`: T exactly when
-- `Y.Mem X`, F exactly when not.  This is the identification of the naive layer with the carrier,
-- made at the META level — never fed back into the identity atom of the language (that is N12's
-- revocation).
--
-- Machine-checked here:
--   * `realise_unique` / `realise_congr` — realisation is well-defined up to the carrier's identity:
--     two carrier sets realised by one term are bisimilar, and bisimilar sets share realisers;
--   * `seg_realises` — the naive segment `{x : x≈0 ∨ … ∨ x≈n−1}` realises the carrier numeral
--     `vn n` at EVERY carrier probe (not only at numerals);
--   * `quine_realised` — the naive term `{x : x ≈ Ω}` realises Ω itself: "Ω = {Ω}" holds across the
--     bridge;
--   * `names_realise` — every carrier set is realised (by `{x : x ∈ nm X}`): nothing in the carrier
--     is out of reach of the naive language;
--   * `realised_but_atom_silent` — the boundary: the naive ∅ realises `vn 0`, yet the identity
--     ATOM `∅ ≈ 0` inside the language stays unexamined.  The identification lives at the meta
--     level; inside the language identity with a naive side is not earned.
--
-- Axiom profile: the empty axiom list (measured at the bottom; guarded by `VR/Guard.lean`).

import VR.SetsNaive.OmegaN

namespace VRCycle.SetsNaive

open VRCycle.SetsOp

set_option genInjectivity false

/-- `t` realises the carrier set `X` at every carrier probe. -/
def Realises (t : NTm) (X : OpSet.{0}) : Prop :=
  ∀ Y : OpSet.{0}, (NVal true (.mem (.nm Y) t) ↔ Y.Mem X) ∧ (NVal false (.mem (.nm Y) t) ↔ ¬ Y.Mem X)

/-- **Realisation is unique up to the carrier's identity.** -/
theorem realise_unique {t : NTm} {X X' : OpSet.{0}} (h : Realises t X) (h' : Realises t X') :
    X.Equiv X' :=
  OpSet.ext (fun Y => ⟨fun hy => (h' Y).1.1 ((h Y).1.2 hy), fun hy => (h Y).1.1 ((h' Y).1.2 hy)⟩)

/-- **Bisimilar carrier sets share their realisers.** -/
theorem realise_congr {t : NTm} {X X' : OpSet.{0}} (e : X.Equiv X') (h : Realises t X) :
    Realises t X' := by
  intro Y
  constructor
  · exact ⟨fun hy => OpSet.mem_congr e ((h Y).1.1 hy), fun hy => (h Y).1.2 (OpSet.mem_congr e.symm hy)⟩
  · exact ⟨fun hy hm => (h Y).2.1 hy (OpSet.mem_congr e.symm hm),
           fun hn => (h Y).2.2 (fun hm => hn (OpSet.mem_congr e hm))⟩

/-- Disjunction in the named language, both polarities. -/
theorem nor_true {A B : NFm} : NVal true (NFm.or A B) ↔ NVal true A ∨ NVal true B := by
  constructor
  · intro h
    cases h with
    | negT h =>
      cases h with
      | andFl h => cases h with | negF h => exact Or.inl h
      | andFr h => cases h with | negF h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact .negT (.andFl (.negF h))
    | inr h => exact .negT (.andFr (.negF h))

theorem nor_false {A B : NFm} : NVal false (NFm.or A B) ↔ NVal false A ∧ NVal false B := by
  constructor
  · intro h
    cases h with
    | negF h => cases h with | andT h1 h2 => cases h1 with | negT h1 => cases h2 with | negT h2 => exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    exact .negF (.andT (.negT h1) (.negT h2))

/-- **The naive segment realises the carrier numeral at every carrier probe.** -/
theorem seg_realises : ∀ n, Realises (seg n) (OpSet.vn n)
  | 0 => by
      intro Y
      constructor
      · constructor
        · intro h; cases h with | memT h => cases h with | negT h => cases h
        · intro h; exact absurd h (OpSet.not_mem_emptySup _)
      · exact ⟨fun _ => OpSet.not_mem_emptySup _, fun _ => .memF (.negF .top)⟩
  | n + 1 => by
      intro Y
      have ih := seg_realises n Y
      have hsucc := OpSet.mem_succ Y (OpSet.vn n)
      constructor
      · constructor
        · intro h
          have h' := (ncomprehension true _ _).1 h
          rw [segBody_inst] at h'
          apply hsucc.2
          cases nor_true.1 h' with
          | inl hA => exact Or.inl (ih.1.1 ((ncomprehension true _ _).2 hA))
          | inr hB => exact Or.inr ((reflect_eq Y (OpSet.vn n)).1.1 hB)
        · intro hm
          apply (ncomprehension true _ _).2
          rw [segBody_inst]
          cases hsucc.1 hm with
          | inl hA => exact nor_true.2 (Or.inl ((ncomprehension true _ _).1 (ih.1.2 hA)))
          | inr hB => exact nor_true.2 (Or.inr (.eqNT hB))
      · constructor
        · intro h hm
          have h' := (ncomprehension false _ _).1 h
          rw [segBody_inst] at h'
          obtain ⟨hA, hB⟩ := nor_false.1 h'
          cases hsucc.1 hm with
          | inl hm => exact ih.2.1 ((ncomprehension false _ _).2 hA) hm
          | inr he => exact (reflect_eq Y (OpSet.vn n)).2.1 hB he
        · intro hn
          apply (ncomprehension false _ _).2
          rw [segBody_inst]
          exact nor_false.2 ⟨(ncomprehension false _ _).1 (ih.2.2 (fun hm => hn (hsucc.2 (Or.inl hm)))),
                             .eqNF (fun he => hn (hsucc.2 (Or.inr he)))⟩

/-- Membership in Ω is identity with Ω. -/
theorem mem_quine_iff (Y : OpSet.{0}) : Y.Mem OpSet.quine.{0} ↔ Y.Equiv OpSet.quine.{0} :=
  ⟨fun ⟨a, _, h⟩ => by cases a; exact h, fun h => ⟨PUnit.unit, trivial, h⟩⟩

/-- The naive term `{x : x ≈ Ω}`. -/
def quineT : NTm := .abs (.eq (.var 0) Om)

/-- **`{x : x ≈ Ω}` realises Ω itself** — "Ω = {Ω}" across the bridge. -/
theorem quine_realised : Realises quineT OpSet.quine.{0} := by
  intro Y
  constructor
  · constructor
    · intro h; cases h with | memT h => exact (mem_quine_iff Y).2 ((reflect_eq _ _).1.1 h)
    · intro h; exact .memT (.eqNT ((mem_quine_iff Y).1 h))
  · constructor
    · intro h hm; cases h with | memF h => exact (reflect_eq _ _).2.1 h ((mem_quine_iff Y).1 hm)
    · intro h; exact .memF (.eqNF (fun he => h ((mem_quine_iff Y).2 he)))

/-- **Every carrier set is realised** — by `{x : x ∈ nm X}`. -/
theorem names_realise (X : OpSet.{0}) : Realises (.abs (.mem (.var 0) (.nm X))) X := by
  intro Y
  constructor
  · constructor
    · intro h; cases h with | memT h => exact (reflect_mem Y X).1.1 h
    · intro h; exact .memT (.memNT h)
  · constructor
    · intro h; cases h with | memF h => exact (reflect_mem Y X).2.1 h
    · intro h; exact .memF (.memNF h)

/-- **The boundary**: the naive ∅ realises `vn 0`, yet inside the language the identity atom
`∅ ≈ 0` is not examined — the identification is a meta-level fact, not an earned atom. -/
theorem realised_but_atom_silent :
    Realises NE (OpSet.vn 0) ∧ ∀ b, ¬ NVal b (.eq NE (N 0)) := by
  constructor
  · intro Y
    constructor
    · constructor
      · intro h; cases h with | memT h => cases h with | negT h => cases h
      · intro h; exact absurd h (OpSet.not_mem_emptySup _)
    · exact ⟨fun _ => OpSet.not_mem_emptySup _, fun _ => .memF (.negF .top)⟩
  · intro b h
    cases b with
    | true => cases h
    | false => cases h

end VRCycle.SetsNaive

#print axioms VRCycle.SetsNaive.realise_unique
#print axioms VRCycle.SetsNaive.realise_congr
#print axioms VRCycle.SetsNaive.seg_realises
#print axioms VRCycle.SetsNaive.quine_realised
#print axioms VRCycle.SetsNaive.names_realise
#print axioms VRCycle.SetsNaive.realised_but_atom_silent
