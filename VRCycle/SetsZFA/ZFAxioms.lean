-- VR-Sets-ZFA: ZF⁻ axioms on OSetZFA
-- Stage 9: the operational ZFA universe is a model of ZF minus Foundation.
--
-- Closes the gap flagged in review: prior stages proved AFA on OSetZFA and a
-- strict ∈-preserving embedding of the ZF-part (OSet), but did NOT verify the
-- ZF⁻ axioms on OSetZFA itself. This file proves Pairing, Union, Power,
-- Separation, Replacement, Infinity on OSetZFA (Extensionality + Empty are in
-- Membership.lean / API.lean). With AFA (Stage 5) replacing Foundation, OSetZFA
-- is an operational model of ZFA.
--
-- Method: every operation is built at the CoPSet level as `mk α A` touching only
-- the top branching levels (exactly as mathlib builds ZFSet from PSet); coinduction
-- affects only equality, for which Stage 2 already supplies isBisim_Equiv /
-- bisim_imp_Equiv. The workhorse `mk_equiv_of_coverage` turns every
-- well-definedness obligation into a child-coverage check.
--
-- Operational framing (answers Observation 11): Separation takes p : OSetZFA → Prop
-- and Replacement takes F : OSetZFA → OSetZFA — first-class objects over the
-- quotient, hence automatically Equiv-invariant. The schema collapse is not a
-- type-theory trick but the operational reification of describability.
--
-- Axiom profile: [propext, Classical.choice, Quot.sound] throughout (the work's ceiling).
--
-- Source: Aczel 1988 §6; mathlib SetTheory.ZFC.Basic (PSet → ZFSet parallel).

import VRCycle.SetsZFA.API

namespace VR.SetsZFA

universe u

-- ============================================================
-- §0. Workhorse: equality by child-coverage
-- ============================================================

/-- **Coverage ⇒ Equiv**: if every child of `mk α A` is `≈`-matched by a child of
`mk β B` and vice versa, the two pre-sets are cobisimilar.

This is the one lemma that makes every congruence below short: the operation's
result is always `mk <manifest index> <children>`, so the index type is concrete
(a Sum / Sigma / Set / Subtype), and `rintro` splits it directly — never going
through an opaque `.shape`. -/
theorem CoPSet.mk_equiv_of_coverage {α β : Type u}
    {A : α → CoPSet.{u}} {B : β → CoPSet.{u}}
    (fwd : ∀ i, ∃ j, A i ≈ B j) (bwd : ∀ j, ∃ i, A i ≈ B j) :
    CoPSet.mk α A ≈ CoPSet.mk β B := by
  apply CoPSet.bisim_imp_Equiv
    (fun c d => (c = CoPSet.mk α A ∧ d = CoPSet.mk β B) ∨ CoPSet.Equiv c d)
  · rintro c d (⟨rfl, rfl⟩ | hcd)
    · exact ⟨fun i => (fwd i).imp (fun _ hj => Or.inr hj),
             fun j => (bwd j).imp (fun _ hi => Or.inr hi)⟩
    · obtain ⟨f, b⟩ := CoPSet.isBisim_Equiv c d hcd
      exact ⟨fun i => (f i).imp (fun _ hj => Or.inr hj),
             fun j => (b j).imp (fun _ hi => Or.inr hi)⟩
  · exact Or.inl ⟨rfl, rfl⟩

-- ============================================================
-- §1. Subset
-- ============================================================

/-- Subset relation on OSetZFA: defined on the quotient, hence automatically
respects equality. Needed for the Power-set characterisation. -/
instance OSetZFA.instHasSubset : HasSubset OSetZFA.{u} :=
  ⟨fun x y => ∀ z, z ∈ x → z ∈ y⟩

theorem OSetZFA.subset_def {x y : OSetZFA.{u}} :
    x ⊆ y ↔ ∀ z, z ∈ x → z ∈ y := Iff.rfl

-- ============================================================
-- §2. Insert (helper for Pairing and Infinity)
-- ============================================================

/-- `CoPSet.insert a x`: prepend `a` as a new member to `x`. Members are
`{a} ∪ members(x)`. -/
def CoPSet.insert (a x : CoPSet.{u}) : CoPSet.{u} :=
  CoPSet.mk (PUnit.{u+1} ⊕ x.shape) (Sum.elim (fun _ => a) x.children)

theorem CoPSet.insert_congr {a₁ a₂ x₁ x₂ : CoPSet.{u}}
    (ha : a₁ ≈ a₂) (hx : x₁ ≈ x₂) :
    CoPSet.insert a₁ x₁ ≈ CoPSet.insert a₂ x₂ := by
  obtain ⟨fwdx, bwdx⟩ := CoPSet.isBisim_Equiv x₁ x₂ hx
  apply CoPSet.mk_equiv_of_coverage
  · rintro (i | i)
    · exact ⟨Sum.inl PUnit.unit, ha⟩
    · obtain ⟨j, hj⟩ := fwdx i; exact ⟨Sum.inr j, hj⟩
  · rintro (j | j)
    · exact ⟨Sum.inl PUnit.unit, ha⟩
    · obtain ⟨i, hi⟩ := bwdx j; exact ⟨Sum.inr i, hi⟩

/-- `OSetZFA.insert a x`: insert element `a` into set `x`. -/
noncomputable def OSetZFA.insert (a x : OSetZFA.{u}) : OSetZFA.{u} :=
  OSetZFA.liftOn₂ a x (fun a' x' => OSetZFA.mk (CoPSet.insert a' x'))
    (fun _ _ _ _ ha hx => OSetZFA.sound (CoPSet.insert_congr ha hx))

theorem OSetZFA.insert_mk (a x : CoPSet.{u}) :
    OSetZFA.insert (OSetZFA.mk a) (OSetZFA.mk x)
      = OSetZFA.mk (CoPSet.insert a x) := rfl

@[simp] theorem OSetZFA.mem_insert (z a x : OSetZFA.{u}) :
    z ∈ OSetZFA.insert a x ↔ z = a ∨ z ∈ x := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨a, rfl⟩ := OSetZFA.mk_surjective a
  obtain ⟨x, rfl⟩ := OSetZFA.mk_surjective x
  rw [OSetZFA.insert_mk, OSetZFA.mem_mk]
  change (∃ i : PUnit.{u+1} ⊕ x.shape, z ≈ Sum.elim (fun _ => a) x.children i) ↔ _
  constructor
  · rintro ⟨(i | i), hi⟩
    · exact Or.inl (OSetZFA.sound hi)
    · exact Or.inr ((OSetZFA.mem_mk z x).mpr ⟨i, hi⟩)
  · rintro (h | h)
    · exact ⟨Sum.inl PUnit.unit, OSetZFA.exact h⟩
    · obtain ⟨i, hi⟩ := (OSetZFA.mem_mk z x).mp h
      exact ⟨Sum.inr i, hi⟩

-- ============================================================
-- §3. Pairing
-- ============================================================

/-- `OSetZFA.pair a b = {a, b}`, built as `insert a {b}`. -/
noncomputable def OSetZFA.pair (a b : OSetZFA.{u}) : OSetZFA.{u} :=
  OSetZFA.insert a (OSetZFA.singleton b)

/-- **Pairing**: `z ∈ {a, b} ↔ z = a ∨ z = b`. -/
@[simp] theorem OSetZFA.mem_pair (z a b : OSetZFA.{u}) :
    z ∈ OSetZFA.pair a b ↔ z = a ∨ z = b := by
  simp only [OSetZFA.pair, OSetZFA.mem_insert, OSetZFA.mem_singleton]

-- ============================================================
-- §4. Union (sUnion)
-- ============================================================

/-- `CoPSet.sUnion x = ⋃ x`: members are the members of members of `x`. -/
def CoPSet.sUnion (x : CoPSet.{u}) : CoPSet.{u} :=
  CoPSet.mk (Σ i : x.shape, (x.children i).shape)
            (fun p => (x.children p.1).children p.2)

theorem CoPSet.sUnion_congr {x₁ x₂ : CoPSet.{u}} (hx : x₁ ≈ x₂) :
    CoPSet.sUnion x₁ ≈ CoPSet.sUnion x₂ := by
  apply CoPSet.mk_equiv_of_coverage
  · rintro ⟨i, k⟩
    obtain ⟨j, hj⟩ := (CoPSet.isBisim_Equiv x₁ x₂ hx).1 i
    obtain ⟨k', hk'⟩ := (CoPSet.isBisim_Equiv (x₁.children i) (x₂.children j) hj).1 k
    exact ⟨⟨j, k'⟩, hk'⟩
  · rintro ⟨j, k'⟩
    obtain ⟨i, hi⟩ := (CoPSet.isBisim_Equiv x₁ x₂ hx).2 j
    obtain ⟨k, hk⟩ := (CoPSet.isBisim_Equiv (x₁.children i) (x₂.children j) hi).2 k'
    exact ⟨⟨i, k⟩, hk⟩

/-- `OSetZFA.sUnion x = ⋃ x`. -/
noncomputable def OSetZFA.sUnion (x : OSetZFA.{u}) : OSetZFA.{u} :=
  OSetZFA.lift (fun a => OSetZFA.mk (CoPSet.sUnion a))
    (fun _ _ h => OSetZFA.sound (CoPSet.sUnion_congr h)) x

theorem OSetZFA.sUnion_mk (x : CoPSet.{u}) :
    OSetZFA.sUnion (OSetZFA.mk x) = OSetZFA.mk (CoPSet.sUnion x) := rfl

/-- **Union**: `z ∈ ⋃ x ↔ ∃ y, y ∈ x ∧ z ∈ y`. -/
@[simp] theorem OSetZFA.mem_sUnion (z x : OSetZFA.{u}) :
    z ∈ OSetZFA.sUnion x ↔ ∃ y, y ∈ x ∧ z ∈ y := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨x, rfl⟩ := OSetZFA.mk_surjective x
  rw [OSetZFA.sUnion_mk, OSetZFA.mem_mk]
  change (∃ p : Σ i : x.shape, (x.children i).shape,
          z ≈ (x.children p.1).children p.2) ↔ _
  constructor
  · rintro ⟨⟨i, k⟩, hk⟩
    exact ⟨OSetZFA.mk (x.children i),
           (OSetZFA.mem_mk _ _).mpr ⟨i, CoPSet.Equiv.refl _⟩,
           (OSetZFA.mem_mk _ _).mpr ⟨k, hk⟩⟩
  · rintro ⟨y, hyx, hzy⟩
    obtain ⟨y, rfl⟩ := OSetZFA.mk_surjective y
    obtain ⟨i, hi⟩ := (OSetZFA.mem_mk _ _).mp hyx
    obtain ⟨k, hk⟩ := (OSetZFA.mem_mk _ _).mp hzy
    obtain ⟨k', hk'⟩ := (CoPSet.isBisim_Equiv y (x.children i) hi).1 k
    exact ⟨⟨i, k'⟩, CoPSet.Equiv.trans hk hk'⟩

-- ============================================================
-- §5. Power set
-- ============================================================

/-- `CoPSet.powerset x = 𝒫 x`: branching type `Set x.shape`, the subset indexed by
`s` being `{ x.children i | i ∈ s }`. -/
def CoPSet.powerset (x : CoPSet.{u}) : CoPSet.{u} :=
  CoPSet.mk (Set x.shape)
            (fun s => CoPSet.mk (Subtype s) (fun b => x.children b.val))

theorem CoPSet.powerset_congr {x₁ x₂ : CoPSet.{u}} (hx : x₁ ≈ x₂) :
    CoPSet.powerset x₁ ≈ CoPSet.powerset x₂ := by
  apply CoPSet.mk_equiv_of_coverage
  · intro s₁
    refine ⟨fun j => ∃ i, s₁ i ∧ x₁.children i ≈ x₂.children j, ?_⟩
    apply CoPSet.mk_equiv_of_coverage
    · rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := (CoPSet.isBisim_Equiv x₁ x₂ hx).1 i
      exact ⟨⟨j, ⟨i, hi, hj⟩⟩, hj⟩
    · rintro ⟨j, i, hsi, hij⟩
      exact ⟨⟨i, hsi⟩, hij⟩
  · intro s₂
    refine ⟨fun i => ∃ j, s₂ j ∧ x₁.children i ≈ x₂.children j, ?_⟩
    apply CoPSet.mk_equiv_of_coverage
    · rintro ⟨i, j, hsj, hij⟩
      exact ⟨⟨j, hsj⟩, hij⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, hij⟩ := (CoPSet.isBisim_Equiv x₁ x₂ hx).2 j
      exact ⟨⟨i, ⟨j, hj, hij⟩⟩, hij⟩

/-- `OSetZFA.powerset x = 𝒫 x`. -/
noncomputable def OSetZFA.powerset (x : OSetZFA.{u}) : OSetZFA.{u} :=
  OSetZFA.lift (fun a => OSetZFA.mk (CoPSet.powerset a))
    (fun _ _ h => OSetZFA.sound (CoPSet.powerset_congr h)) x

theorem OSetZFA.powerset_mk (x : CoPSet.{u}) :
    OSetZFA.powerset (OSetZFA.mk x) = OSetZFA.mk (CoPSet.powerset x) := rfl

/-- **Power set**: `z ∈ 𝒫 x ↔ z ⊆ x`. -/
@[simp] theorem OSetZFA.mem_powerset (z x : OSetZFA.{u}) :
    z ∈ OSetZFA.powerset x ↔ z ⊆ x := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨x, rfl⟩ := OSetZFA.mk_surjective x
  rw [OSetZFA.powerset_mk, OSetZFA.mem_mk]
  change (∃ s : Set x.shape,
          z ≈ CoPSet.mk (Subtype s) (fun b => x.children b.val)) ↔ _
  constructor
  · rintro ⟨s, hs⟩ w hw
    obtain ⟨w, rfl⟩ := OSetZFA.mk_surjective w
    rw [OSetZFA.mem_mk] at hw ⊢
    obtain ⟨i, hi⟩ := hw
    obtain ⟨k, hk⟩ :=
      (CoPSet.isBisim_Equiv z (CoPSet.mk (Subtype s) (fun b => x.children b.val)) hs).1 i
    exact ⟨k.val, CoPSet.Equiv.trans hi hk⟩
  · intro hsub
    refine ⟨fun i => OSetZFA.mk (x.children i) ∈ OSetZFA.mk z, ?_⟩
    rw [← OSetZFA.eq_iff]
    apply OSetZFA.ext
    intro w
    constructor
    · intro hw
      have hwx : w ∈ OSetZFA.mk x := hsub w hw
      obtain ⟨w, rfl⟩ := OSetZFA.mk_surjective w
      obtain ⟨i, hi⟩ := (OSetZFA.mem_mk _ _).mp hwx
      have hmem : OSetZFA.mk (x.children i) ∈ OSetZFA.mk z := by
        rw [← OSetZFA.sound hi]; exact hw
      rw [OSetZFA.mem_mk]
      exact ⟨⟨i, hmem⟩, hi⟩
    · intro hw
      obtain ⟨w, rfl⟩ := OSetZFA.mk_surjective w
      rw [OSetZFA.mem_mk] at hw
      obtain ⟨b, hb⟩ := hw
      have hz : OSetZFA.mk (x.children b.val) ∈ OSetZFA.mk z := b.property
      rw [OSetZFA.sound hb]; exact hz

-- ============================================================
-- §6. Separation (operational predicate)
-- ============================================================

/-- `OSetZFA.sep p x = { z ∈ x | p z }`, for an operational predicate `p`. -/
noncomputable def OSetZFA.sep (p : OSetZFA.{u} → Prop) (x : OSetZFA.{u}) :
    OSetZFA.{u} :=
  OSetZFA.lift
    (fun a => OSetZFA.mk (CoPSet.mk {i : a.shape // p (OSetZFA.mk (a.children i))}
                                     (fun b => a.children b.val)))
    (fun a b hab => OSetZFA.sound (by
      apply CoPSet.mk_equiv_of_coverage
      · rintro ⟨i, hi⟩
        obtain ⟨j, hj⟩ := (CoPSet.isBisim_Equiv a b hab).1 i
        refine ⟨⟨j, ?_⟩, hj⟩
        rwa [← OSetZFA.sound hj]
      · rintro ⟨j, hj⟩
        obtain ⟨i, hi⟩ := (CoPSet.isBisim_Equiv a b hab).2 j
        refine ⟨⟨i, ?_⟩, hi⟩
        rwa [OSetZFA.sound hi]))
    x

theorem OSetZFA.sep_mk (p : OSetZFA.{u} → Prop) (a : CoPSet.{u}) :
    OSetZFA.sep p (OSetZFA.mk a)
      = OSetZFA.mk (CoPSet.mk {i : a.shape // p (OSetZFA.mk (a.children i))}
                              (fun b => a.children b.val)) := rfl

/-- **Separation**: `z ∈ { w ∈ x | p w } ↔ z ∈ x ∧ p z`. -/
@[simp] theorem OSetZFA.mem_sep (p : OSetZFA.{u} → Prop) (z x : OSetZFA.{u}) :
    z ∈ OSetZFA.sep p x ↔ z ∈ x ∧ p z := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨x, rfl⟩ := OSetZFA.mk_surjective x
  rw [OSetZFA.sep_mk, OSetZFA.mem_mk]
  change (∃ b : {i : x.shape // p (OSetZFA.mk (x.children i))}, z ≈ x.children b.val) ↔ _
  constructor
  · rintro ⟨⟨i, hi⟩, hz⟩
    refine ⟨(OSetZFA.mem_mk _ _).mpr ⟨i, hz⟩, ?_⟩
    rwa [OSetZFA.sound hz]
  · rintro ⟨hzx, hp⟩
    obtain ⟨i, hi⟩ := (OSetZFA.mem_mk _ _).mp hzx
    refine ⟨⟨i, ?_⟩, hi⟩
    rwa [← OSetZFA.sound hi]

-- ============================================================
-- §7. Replacement (operational function)
-- ============================================================

/-- Well-definedness of the replacement construction. -/
private theorem CoPSet.image_aux_congr (F : OSetZFA.{u} → OSetZFA.{u})
    {a b : CoPSet.{u}} (hab : a ≈ b) :
    CoPSet.mk a.shape (fun i => (F (OSetZFA.mk (a.children i))).out) ≈
    CoPSet.mk b.shape (fun j => (F (OSetZFA.mk (b.children j))).out) := by
  apply CoPSet.mk_equiv_of_coverage
  · intro i
    obtain ⟨j, hj⟩ := (CoPSet.isBisim_Equiv a b hab).1 i
    refine ⟨j, ?_⟩
    rw [OSetZFA.sound hj]; exact CoPSet.Equiv.refl _
  · intro j
    obtain ⟨i, hi⟩ := (CoPSet.isBisim_Equiv a b hab).2 j
    refine ⟨i, ?_⟩
    rw [OSetZFA.sound hi]; exact CoPSet.Equiv.refl _

/-- `OSetZFA.image F x = { F y | y ∈ x }`, for an operational function `F`. -/
noncomputable def OSetZFA.image (F : OSetZFA.{u} → OSetZFA.{u}) (x : OSetZFA.{u}) :
    OSetZFA.{u} :=
  OSetZFA.lift
    (fun a => OSetZFA.mk (CoPSet.mk a.shape (fun i => (F (OSetZFA.mk (a.children i))).out)))
    (fun _ _ hab => OSetZFA.sound (CoPSet.image_aux_congr F hab)) x

theorem OSetZFA.image_mk (F : OSetZFA.{u} → OSetZFA.{u}) (a : CoPSet.{u}) :
    OSetZFA.image F (OSetZFA.mk a)
      = OSetZFA.mk (CoPSet.mk a.shape (fun i => (F (OSetZFA.mk (a.children i))).out)) := rfl

/-- **Replacement**: `z ∈ { F y | y ∈ x } ↔ ∃ y, y ∈ x ∧ F y = z`. -/
@[simp] theorem OSetZFA.mem_image (F : OSetZFA.{u} → OSetZFA.{u}) (z x : OSetZFA.{u}) :
    z ∈ OSetZFA.image F x ↔ ∃ y, y ∈ x ∧ F y = z := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  obtain ⟨x, rfl⟩ := OSetZFA.mk_surjective x
  rw [OSetZFA.image_mk, OSetZFA.mem_mk]
  change (∃ i : x.shape, z ≈ (F (OSetZFA.mk (x.children i))).out) ↔ _
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨OSetZFA.mk (x.children i),
            (OSetZFA.mem_mk _ _).mpr ⟨i, CoPSet.Equiv.refl _⟩, ?_⟩
    rw [← Quotient.out_eq (F (OSetZFA.mk (x.children i)))]
    exact (OSetZFA.sound hi).symm
  · rintro ⟨y, hyx, hFy⟩
    obtain ⟨y, rfl⟩ := OSetZFA.mk_surjective y
    obtain ⟨i, hi⟩ := (OSetZFA.mem_mk _ _).mp hyx
    refine ⟨i, ?_⟩
    have h1 : F (OSetZFA.mk y) = F (OSetZFA.mk (x.children i)) := by rw [OSetZFA.sound hi]
    have h2 : OSetZFA.mk z = F (OSetZFA.mk (x.children i)) := by rw [← h1]; exact hFy.symm
    rw [← Quotient.out_eq (F (OSetZFA.mk (x.children i)))] at h2
    exact OSetZFA.exact h2

-- ============================================================
-- §8. Infinity (von Neumann ω)
-- ============================================================

/-- The `n`-th von Neumann ordinal as a CoPSet: `ofNat (n+1) = ofNat n ∪ {ofNat n}`
(`= insert (ofNat n) (ofNat n)`). Matches mathlib's `ZFSet.omega` and VR's `O_n`. -/
def CoPSet.ofNat : ℕ → CoPSet.{u}
  | 0     => CoPSet.mk PEmpty.{u+1} PEmpty.elim
  | n + 1 => CoPSet.insert (CoPSet.ofNat n) (CoPSet.ofNat n)

/-- `CoPSet.omega`: the ℕ-indexed family of von Neumann ordinals. -/
def CoPSet.omega : CoPSet.{u} :=
  CoPSet.mk (ULift.{u} ℕ) (fun n => CoPSet.ofNat n.down)

/-- `OSetZFA.omega = ω`. -/
def OSetZFA.omega : OSetZFA.{u} := OSetZFA.mk CoPSet.omega

theorem OSetZFA.mem_omega (z : OSetZFA.{u}) :
    z ∈ OSetZFA.omega ↔ ∃ n : ℕ, z = OSetZFA.mk (CoPSet.ofNat n) := by
  obtain ⟨z, rfl⟩ := OSetZFA.mk_surjective z
  rw [show OSetZFA.omega = OSetZFA.mk CoPSet.omega from rfl, OSetZFA.mem_mk]
  change (∃ i : ULift.{u} ℕ, z ≈ CoPSet.ofNat i.down) ↔ _
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i.down, OSetZFA.sound hi⟩
  · rintro ⟨n, hn⟩; exact ⟨ULift.up n, OSetZFA.exact hn⟩

/-- `∅ ∈ ω`. -/
theorem OSetZFA.empty_mem_omega : (OSetZFA.empty : OSetZFA.{u}) ∈ OSetZFA.omega :=
  (OSetZFA.mem_omega _).mpr ⟨0, rfl⟩

/-- `ω` is closed under von Neumann successor `x ↦ x ∪ {x} = insert x x`. -/
theorem OSetZFA.insert_self_mem_omega (x : OSetZFA.{u}) (hx : x ∈ OSetZFA.omega) :
    OSetZFA.insert x x ∈ OSetZFA.omega := by
  obtain ⟨n, rfl⟩ := (OSetZFA.mem_omega x).mp hx
  rw [OSetZFA.mem_omega]
  refine ⟨n + 1, ?_⟩
  rw [OSetZFA.insert_mk]
  simp only [CoPSet.ofNat]

/-- **Infinity**: `ω` contains `∅` and is closed under von Neumann successor. -/
theorem OSetZFA.infinity :
    (OSetZFA.empty : OSetZFA.{u}) ∈ OSetZFA.omega ∧
    ∀ x : OSetZFA.{u}, x ∈ OSetZFA.omega → OSetZFA.insert x x ∈ OSetZFA.omega :=
  ⟨OSetZFA.empty_mem_omega, OSetZFA.insert_self_mem_omega⟩

-- ============================================================
-- §9. Axiom audit
-- ============================================================

-- Every ZF⁻ axiom-witness sits at the work's ceiling
-- [propext, Classical.choice, Quot.sound] (Classical.choice from CoPSet.bisim).

section AxiomAudit
#print axioms OSetZFA.mem_insert    -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_pair      -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_sUnion    -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_powerset  -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_sep       -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.mem_image     -- [propext, Classical.choice, Quot.sound]
#print axioms OSetZFA.infinity      -- [propext, Classical.choice, Quot.sound]
end AxiomAudit

end VR.SetsZFA
