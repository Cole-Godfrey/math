import Math.Foundations.Equality

namespace Math.Functions

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

/-- an injective function sends distinct arguments to distinct values. -/
def Injective (f : α → β) : Prop := ∀ ⦃a b⦄, f a = f b → a = b

/-- a surjective function has a preimage for every value. -/
def Surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y

/-- a bijective function is injective and surjective. -/
def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

/-- function composition applies the right function first. -/
def comp (g : β → γ) (f : α → β) : α → γ := fun x => g (f x)

/-- function composition is associative. -/
theorem comp_assoc (h : γ → δ) (g : β → γ) (f : α → β) :
    comp h (comp g f) = comp (comp h g) f := rfl

/-- composition preserves injectivity. -/
theorem injective_comp {f : α → β} {g : β → γ}
    (hf : Injective f) (hg : Injective g) : Injective (comp g f) :=
  fun {_ _} h => hf (hg h)

/-- composition preserves surjectivity. -/
theorem surjective_comp {f : α → β} {g : β → γ}
    (hf : Surjective f) (hg : Surjective g) : Surjective (comp g f) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  exact ⟨x, (congrArg g hx).trans hy⟩

/-- composition preserves bijectivity. -/
theorem bijective_comp {f : α → β} {g : β → γ}
    (hf : Bijective f) (hg : Bijective g) : Bijective (comp g f) :=
  ⟨injective_comp hf.1 hg.1, surjective_comp hf.2 hg.2⟩

/-- a left inverse implies injectivity. -/
theorem left_inverse_injective {f : α → β} {g : β → α}
    (h : ∀ x, g (f x) = x) : Injective f := by
  intro a b hab
  exact (h a).symm.trans ((congrArg g hab).trans (h b))

/-- a right inverse implies surjectivity. -/
theorem right_inverse_surjective {f : α → β} {g : β → α}
    (h : ∀ y, f (g y) = y) : Surjective f := fun y => ⟨g y, h y⟩

end Math.Functions
