-- VR/Prelude/Set.lean — families of basics as predicates, on `[]`.
--
-- The VR core used Mathlib's `Set α` (which is literally `α → Prop`) for the cover families of the
-- topology and the continuum, without ever using its extensionality. To make the core depend on
-- Lean alone (curator, 2026-09-13), the same definition is made here: a set is a predicate, `∈` is
-- application, `⊆`/`∪`/`∩`/`{x | p x}` are the obvious definitions. No extensionality is provided —
-- two families with the same members are not equal here, only mutually included; that is the
-- operational reading (a family is a rule, identity of rules is not a given).
-- The set-builder notation is SCOPED (`open scoped VRCycle.Set`) so that it never collides with
-- Mathlib's in the classical library.

namespace VRCycle

universe u

/-- A family of elements of `α`, given as a predicate. -/
def Set (α : Type u) : Type u := α → Prop

namespace Set

variable {α : Type u}

/-- The family of the `x` with `p x`. -/
def setOf (p : α → Prop) : Set α := p

instance : Membership α (Set α) := ⟨fun s a => s a⟩

/-- Everything. -/
protected def univ : Set α := fun _ => True

instance : EmptyCollection (Set α) := ⟨fun _ => False⟩
instance : HasSubset (Set α) := ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩
instance : Union (Set α) := ⟨fun s t => fun a => a ∈ s ∨ a ∈ t⟩
instance : Inter (Set α) := ⟨fun s t => fun a => a ∈ s ∧ a ∈ t⟩
instance : Singleton α (Set α) := ⟨fun b => fun a => a = b⟩
instance : Insert α (Set α) := ⟨fun b s => fun a => a = b ∨ a ∈ s⟩

scoped syntax "{" ident " | " term "}" : term
scoped syntax "{" ident " : " term " | " term "}" : term
scoped syntax "{" ident " ∈ " term " | " term "}" : term
scoped macro_rules
  | `({ $x:ident | $p }) => `(VRCycle.Set.setOf fun $x => $p)
  | `({ $x:ident : $t | $p }) => `(VRCycle.Set.setOf fun ($x : $t) => $p)
  | `({ $x:ident ∈ $s | $p }) => `(VRCycle.Set.setOf fun $x => $x ∈ $s ∧ $p)

/-- Inhabited family. -/
protected def Nonempty (s : Set α) : Prop := ∃ a, a ∈ s

/-- Direct image. -/
def image {β : Type u} (f : α → β) (s : Set α) : Set β := fun b => ∃ a, a ∈ s ∧ f a = b

/-- Pre-image. -/
def preimage {β : Type u} (f : α → β) (t : Set β) : Set α := fun a => f a ∈ t

scoped infixl:80 " '' " => VRCycle.Set.image
scoped infixl:80 " ⁻¹' " => VRCycle.Set.preimage

theorem mem_image {β : Type u} {f : α → β} {s : Set α} {b : β} :
    b ∈ image f s ↔ ∃ a, a ∈ s ∧ f a = b := Iff.rfl
theorem mem_image_of_mem {β : Type u} (f : α → β) {s : Set α} {a : α} (h : a ∈ s) :
    f a ∈ image f s := ⟨a, h, rfl⟩
theorem image_subset {β : Type u} (f : α → β) {s t : Set α} (h : s ⊆ t) : image f s ⊆ image f t :=
  fun _ ⟨a, ha, e⟩ => ⟨a, h ha, e⟩
theorem mem_preimage {β : Type u} {f : α → β} {t : Set β} {a : α} : a ∈ preimage f t ↔ f a ∈ t := Iff.rfl

theorem mem_setOf_eq {a : α} {p : α → Prop} : (a ∈ setOf p) = p a := rfl
theorem mem_setOf {a : α} {p : α → Prop} : a ∈ setOf p ↔ p a := Iff.rfl
theorem mem_univ (a : α) : a ∈ (Set.univ : Set α) := trivial
theorem not_mem_empty (a : α) : ¬ a ∈ (∅ : Set α) := fun h => h
theorem mem_union {a : α} {s t : Set α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl
theorem mem_inter {a : α} {s t : Set α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := Iff.rfl
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) := rfl
theorem mem_insert_iff {a b : α} {s : Set α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := Iff.rfl
theorem subset_def {s t : Set α} : (s ⊆ t) = ∀ ⦃a⦄, a ∈ s → a ∈ t := rfl
protected theorem Subset.refl (s : Set α) : s ⊆ s := fun _ h => h
protected theorem Subset.trans {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : s ⊆ u :=
  fun _ h => h₂ (h₁ h)
theorem subset_univ (s : Set α) : s ⊆ Set.univ := fun _ _ => trivial
theorem empty_subset (s : Set α) : (∅ : Set α) ⊆ s := fun _ h => absurd h (fun h => h)
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := fun _ h => Or.inl h
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := fun _ h => Or.inr h
theorem union_subset {s t u : Set α} (h₁ : s ⊆ u) (h₂ : t ⊆ u) : s ∪ t ⊆ u :=
  fun _ h => h.elim (fun h => h₁ h) (fun h => h₂ h)

end Set
end VRCycle
