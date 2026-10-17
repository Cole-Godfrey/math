import Math.Logic.Basic
import Math.Foundations.Equality

namespace Math.Sets

universe u v

variable {α : Type u} {β : Type v}

/-- a set is a predicate on its ambient type. -/
def Set (α : Type u) := α → Prop

/-- membership applies a set's predicate to an element. -/
def member (x : α) (s : Set α) : Prop := s x

/-- a subset contains only elements of the containing set. -/
def Subset (s t : Set α) : Prop := ∀ x, s x → t x

/-- the empty set contains no elements. -/
def empty : Set α := fun _ => False

/-- the universal set contains every element of its ambient type. -/
def universal : Set α := fun _ => True

/-- union contains elements of either set. -/
def union (s t : Set α) : Set α := fun x => s x ∨ t x

/-- intersection contains elements common to both sets. -/
def inter (s t : Set α) : Set α := fun x => s x ∧ t x

/-- complement contains elements outside a set. -/
def complement (s : Set α) : Set α := fun x => ¬ s x

/-- a singleton contains exactly its specified element. -/
def singleton (a : α) : Set α := fun x => x = a

/-- an image contains values attained on a set. -/
def image (f : α → β) (s : Set α) : Set β := fun y => ∃ x, s x ∧ f x = y

/-- a preimage contains arguments mapped into a set. -/
def preimage (f : α → β) (s : Set β) : Set α := fun x => s (f x)

/-- sets with equivalent membership predicates are equal. -/
theorem ext {s t : Set α} (h : ∀ x, s x ↔ t x) : s = t :=
  Math.Equality.function_ext (fun x => Math.Equality.proposition_ext (h x))

/-- the subset relation is reflexive. -/
theorem subset_refl (s : Set α) : Subset s s := fun _ h => h

/-- the subset relation is transitive. -/
theorem subset_trans {r s t : Set α} (hrs : Subset r s) (hst : Subset s t) :
    Subset r t := fun x h => hst x (hrs x h)

/-- mutual inclusion gives set equality. -/
theorem subset_antisymm {s t : Set α} (hst : Subset s t) (hts : Subset t s) :
    s = t := ext (fun x => ⟨hst x, hts x⟩)

/-- intersection is commutative. -/
theorem inter_comm (s t : Set α) : inter s t = inter t s :=
  ext (fun _ => Math.Logic.and_comm)

/-- union is commutative. -/
theorem union_comm (s t : Set α) : union s t = union t s :=
  ext (fun _ => Math.Logic.or_comm)

/-- intersection distributes over union. -/
theorem inter_union_distrib (r s t : Set α) :
    inter r (union s t) = union (inter r s) (inter r t) :=
  ext (fun _ => Math.Logic.and_or_distrib)

/-- preimages preserve intersection. -/
theorem preimage_inter (f : α → β) (s t : Set β) :
    preimage f (inter s t) = inter (preimage f s) (preimage f t) := rfl

/-- images preserve union. -/
theorem image_union (f : α → β) (s t : Set α) :
    image f (union s t) = union (image f s) (image f t) := by
  apply ext
  intro y
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := h
    cases hx with
    | inl hs => exact Or.inl ⟨x, hs, hxy⟩
    | inr ht => exact Or.inr ⟨x, ht, hxy⟩
  · intro h
    cases h with
    | inl hs =>
      obtain ⟨x, hx, hxy⟩ := hs
      exact ⟨x, Or.inl hx, hxy⟩
    | inr ht =>
      obtain ⟨x, hx, hxy⟩ := ht
      exact ⟨x, Or.inr hx, hxy⟩

end Math.Sets
