import Math.Order.Bekic

set_option autoImplicit false
set_option warningAsError true

open Math.OrderTheory

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

section Preorders

variable [Preorder α] [Preorder β] [Preorder γ]

example (f : α →o β →o γ) : β →o α →o γ := swapArguments f

example (f : α →o β →o α) (g : α →o β →o β) : (α × β) →o (α × β) := jointStep f g

end Preorders

section OrderedParameters

variable [Preorder α] [CompleteLattice β]
  (f : α →o β →o α) (g : α →o β →o β)

example : α →o α := leastOuterStep f g

example : α →o α := greatestOuterStep f g

end OrderedParameters

section CompleteLattices

variable [CompleteLattice α] [CompleteLattice β]
  (f : α →o β →o α) (g : α →o β →o β)

example : α × β := leastPair f g

example : α × β := greatestPair f g

example : f (leastPair f g).1 (leastPair f g).2 = (leastPair f g).1 := leastPair_left f g

example : g (leastPair f g).1 (leastPair f g).2 = (leastPair f g).2 := leastPair_right f g

example : jointStep f g (leastPair f g) = leastPair f g := leastPair_fixed f g

example (a : α) (b : β) (hf : f a b ≤ a) (hg : g a b ≤ b) : leastPair f g ≤ (a, b) :=
  leastPair_le_of_prefixed f g a b hf hg

example : IsLeast {p | jointStep f g p ≤ p} (leastPair f g) := leastPair_isLeast_prefixed f g

example : (jointStep f g).lfp =
    ((leastOuterStep f g).lfp, (g (leastOuterStep f g).lfp).lfp) :=
  (leastPair_eq_lfp f g).symm

example {f' : α →o β →o α} {g' : α →o β →o β} (hf : f ≤ f') (hg : g ≤ g') :
    leastPair f g ≤ leastPair f' g' := leastPair_mono hf hg

example : f (greatestPair f g).1 (greatestPair f g).2 = (greatestPair f g).1 :=
  greatestPair_left f g

example : g (greatestPair f g).1 (greatestPair f g).2 = (greatestPair f g).2 :=
  greatestPair_right f g

example : jointStep f g (greatestPair f g) = greatestPair f g := greatestPair_fixed f g

example (a : α) (b : β) (hf : a ≤ f a b) (hg : b ≤ g a b) : (a, b) ≤ greatestPair f g :=
  le_greatestPair_of_postfixed f g a b hf hg

example : IsGreatest {p | p ≤ jointStep f g p} (greatestPair f g) :=
  greatestPair_isGreatest_postfixed f g

example : (jointStep f g).gfp =
    ((greatestOuterStep f g).gfp, (g (greatestOuterStep f g).gfp).gfp) :=
  (greatestPair_eq_gfp f g).symm

example {f' : α →o β →o α} {g' : α →o β →o β} (hf : f ≤ f') (hg : g ≤ g') :
    greatestPair f g ≤ greatestPair f' g' := greatestPair_mono hf hg

example : leastPair f g ≤ greatestPair f g := leastPair_le_greatestPair f g

example : (leastPair f g).swap = leastPair (swapArguments g) (swapArguments f) :=
  leastPair_swap f g

example : (greatestPair f g).swap = greatestPair (swapArguments g) (swapArguments f) :=
  greatestPair_swap f g

example : (∃! p, jointStep f g p = p) ↔ leastPair f g = greatestPair f g :=
  existsUnique_fixed_iff_extrema_eq f g

end CompleteLattices

section Powersets

example (f : Set α →o Set β →o Set α) (g : Set α →o Set β →o Set β) :
    jointStep f g (leastPair f g) = leastPair f g := leastPair_fixed f g

example (f : Set α →o Set β →o Set α) (g : Set α →o Set β →o Set β)
    (a : Set α) (b : Set β) (hf : f a b ⊆ a) (hg : g a b ⊆ b) :
    (leastPair f g).1 ⊆ a ∧ (leastPair f g).2 ⊆ b := leastPair_le_of_prefixed f g a b hf hg

end Powersets
