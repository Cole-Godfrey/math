namespace Math.Equality

universe u v

variable {α : Sort u} {β : Sort v} {a b c : α}

/-- equality is reflexive. -/
theorem refl (a : α) : a = a := rfl

/-- equality is symmetric. -/
theorem symm (h : a = b) : b = a := h.symm

/-- equality is transitive. -/
theorem trans (hab : a = b) (hbc : b = c) : a = c := hab.trans hbc

/-- functions preserve equality. -/
theorem congr (f : α → β) (h : a = b) : f a = f b := congrArg f h

/-- predicates transport along equality. -/
theorem transport (p : α → Prop) (h : a = b) (ha : p a) : p b := h ▸ ha

/-- pointwise equality gives function equality. -/
theorem function_ext {f g : α → β} (h : ∀ x, f x = g x) : f = g := funext h

/-- equivalent propositions are equal. -/
theorem proposition_ext {P Q : Prop} (h : P ↔ Q) : P = Q := propext h

end Math.Equality
