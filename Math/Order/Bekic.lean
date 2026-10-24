module

public import Mathlib.Order.FixedPoints

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace Math.OrderTheory

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- exchanging curried arguments retains monotonicity in both variables. -/
def swapArguments [Preorder α] [Preorder β] [Preorder γ]
    (f : α →o β →o γ) : β →o α →o γ where
  toFun b := { toFun := fun a => f a b, monotone' := fun _ _ h => f.mono h b }
  monotone' _ _ h a := (f a).mono h

/-- two monotone equations define a monotone map on the product lattice. -/
def jointStep [Preorder α] [Preorder β]
    (f : α →o β →o α) (g : α →o β →o β) : (α × β) →o (α × β) where
  toFun p := (f p.1 p.2, g p.1 p.2)
  monotone' p q h :=
    ⟨(f.mono h.1 p.2).trans ((f q.1).mono h.2),
     (g.mono h.1 p.2).trans ((g q.1).mono h.2)⟩

/-- eliminate the second variable by its least fixed point. -/
def leastOuterStep [Preorder α] [CompleteLattice β]
    (f : α →o β →o α) (g : α →o β →o β) : α →o α where
  toFun a := f a (g a).lfp
  monotone' a b h :=
    (f.mono h (g a).lfp).trans ((f b).mono (OrderHom.lfp.mono (g.mono h)))

/-- eliminate the second variable by its greatest fixed point. -/
def greatestOuterStep [Preorder α] [CompleteLattice β]
    (f : α →o β →o α) (g : α →o β →o β) : α →o α where
  toFun a := f a (g a).gfp
  monotone' a b h :=
    (f.mono h (g a).gfp).trans ((f b).mono (OrderHom.gfp.mono (g.mono h)))

variable [CompleteLattice α] [CompleteLattice β]

/-- nested least fixed points give the least simultaneous solution. -/
def leastPair (f : α →o β →o α) (g : α →o β →o β) : α × β :=
  let a := (leastOuterStep f g).lfp
  (a, (g a).lfp)

/-- nested greatest fixed points give the greatest simultaneous solution. -/
def greatestPair (f : α →o β →o α) (g : α →o β →o β) : α × β :=
  let a := (greatestOuterStep f g).gfp
  (a, (g a).gfp)

/-- the least construction satisfies the first equation. -/
theorem leastPair_left (f : α →o β →o α) (g : α →o β →o β) :
    f (leastPair f g).1 (leastPair f g).2 = (leastPair f g).1 :=
  (leastOuterStep f g).map_lfp

/-- the least construction satisfies the second equation. -/
theorem leastPair_right (f : α →o β →o α) (g : α →o β →o β) :
    g (leastPair f g).1 (leastPair f g).2 = (leastPair f g).2 :=
  (g (leastPair f g).1).map_lfp

/-- the least construction is a fixed point of the coupled map. -/
theorem leastPair_fixed (f : α →o β →o α) (g : α →o β →o β) :
    jointStep f g (leastPair f g) = leastPair f g :=
  Prod.ext (leastPair_left f g) (leastPair_right f g)

/-- every simultaneous upper bound bounds the least solution. -/
theorem leastPair_le_of_prefixed (f : α →o β →o α) (g : α →o β →o β)
    (a : α) (b : β) (hf : f a b ≤ a) (hg : g a b ≤ b) :
    leastPair f g ≤ (a, b) := by
  have hb : (g a).lfp ≤ b := (g a).lfp_le hg
  have ha : (leastOuterStep f g).lfp ≤ a :=
    (leastOuterStep f g).lfp_le (((f a).mono hb).trans hf)
  exact ⟨ha, (OrderHom.lfp.mono (g.mono ha)).trans hb⟩

/-- the nested construction is the least simultaneous pre-fixed point. -/
theorem leastPair_isLeast_prefixed (f : α →o β →o α) (g : α →o β →o β) :
    IsLeast {p | jointStep f g p ≤ p} (leastPair f g) := by
  refine ⟨(leastPair_fixed f g).le, ?_⟩
  intro p hp
  exact leastPair_le_of_prefixed f g p.1 p.2 hp.1 hp.2

/-- the bekić least fixed-point identity holds for different complete lattices. -/
theorem leastPair_eq_lfp (f : α →o β →o α) (g : α →o β →o β) :
    leastPair f g = (jointStep f g).lfp := by
  apply le_antisymm
  · exact leastPair_le_of_prefixed f g _ _
      (congrArg Prod.fst (jointStep f g).map_lfp).le
      (congrArg Prod.snd (jointStep f g).map_lfp).le
  · exact (jointStep f g).lfp_le_fixed (leastPair_fixed f g)

/-- enlarging both equations enlarges the least solution. -/
theorem leastPair_mono {f f' : α →o β →o α} {g g' : α →o β →o β}
    (hf : f ≤ f') (hg : g ≤ g') : leastPair f g ≤ leastPair f' g' := by
  apply leastPair_le_of_prefixed
  · exact (hf _ _).trans (leastPair_left f' g').le
  · exact (hg _ _).trans (leastPair_right f' g').le

/-- the greatest construction satisfies the first equation. -/
theorem greatestPair_left (f : α →o β →o α) (g : α →o β →o β) :
    f (greatestPair f g).1 (greatestPair f g).2 = (greatestPair f g).1 :=
  (greatestOuterStep f g).map_gfp

/-- the greatest construction satisfies the second equation. -/
theorem greatestPair_right (f : α →o β →o α) (g : α →o β →o β) :
    g (greatestPair f g).1 (greatestPair f g).2 = (greatestPair f g).2 :=
  (g (greatestPair f g).1).map_gfp

/-- the greatest construction is a fixed point of the coupled map. -/
theorem greatestPair_fixed (f : α →o β →o α) (g : α →o β →o β) :
    jointStep f g (greatestPair f g) = greatestPair f g :=
  Prod.ext (greatestPair_left f g) (greatestPair_right f g)

/-- every simultaneous lower bound lies below the greatest solution. -/
theorem le_greatestPair_of_postfixed (f : α →o β →o α) (g : α →o β →o β)
    (a : α) (b : β) (hf : a ≤ f a b) (hg : b ≤ g a b) :
    (a, b) ≤ greatestPair f g := by
  have hb : b ≤ (g a).gfp := (g a).le_gfp hg
  have ha : a ≤ (greatestOuterStep f g).gfp :=
    (greatestOuterStep f g).le_gfp (hf.trans ((f a).mono hb))
  exact ⟨ha, hb.trans (OrderHom.gfp.mono (g.mono ha))⟩

/-- the nested construction is the greatest simultaneous post-fixed point. -/
theorem greatestPair_isGreatest_postfixed (f : α →o β →o α) (g : α →o β →o β) :
    IsGreatest {p | p ≤ jointStep f g p} (greatestPair f g) := by
  refine ⟨(greatestPair_fixed f g).ge, ?_⟩
  intro p hp
  exact le_greatestPair_of_postfixed f g p.1 p.2 hp.1 hp.2

/-- the bekić greatest fixed-point identity holds for different complete lattices. -/
theorem greatestPair_eq_gfp (f : α →o β →o α) (g : α →o β →o β) :
    greatestPair f g = (jointStep f g).gfp := by
  apply le_antisymm
  · exact (jointStep f g).le_gfp (greatestPair_fixed f g).ge
  · exact le_greatestPair_of_postfixed f g _ _
      (congrArg Prod.fst (jointStep f g).map_gfp).ge
      (congrArg Prod.snd (jointStep f g).map_gfp).ge

/-- enlarging both equations enlarges the greatest solution. -/
theorem greatestPair_mono {f f' : α →o β →o α} {g g' : α →o β →o β}
    (hf : f ≤ f') (hg : g ≤ g') : greatestPair f g ≤ greatestPair f' g' := by
  apply le_greatestPair_of_postfixed
  · exact ((greatestPair_left f g).ge).trans (hf _ _)
  · exact ((greatestPair_right f g).ge).trans (hg _ _)

/-- every least simultaneous solution lies below the greatest one. -/
theorem leastPair_le_greatestPair (f : α →o β →o α) (g : α →o β →o β) :
    leastPair f g ≤ greatestPair f g :=
  leastPair_le_of_prefixed f g _ _ (greatestPair_left f g).le (greatestPair_right f g).le

/-- exchanging the equation order exchanges the least solution coordinates. -/
theorem leastPair_swap (f : α →o β →o α) (g : α →o β →o β) :
    (leastPair f g).swap = leastPair (swapArguments g) (swapArguments f) := by
  apply le_antisymm
  · have h := leastPair_le_of_prefixed f g
      (leastPair (swapArguments g) (swapArguments f)).2
      (leastPair (swapArguments g) (swapArguments f)).1
      (leastPair_right (swapArguments g) (swapArguments f)).le
      (leastPair_left (swapArguments g) (swapArguments f)).le
    exact ⟨h.2, h.1⟩
  · exact leastPair_le_of_prefixed (swapArguments g) (swapArguments f) _ _
      (leastPair_right f g).le (leastPair_left f g).le

/-- exchanging the equation order exchanges the greatest solution coordinates. -/
theorem greatestPair_swap (f : α →o β →o α) (g : α →o β →o β) :
    (greatestPair f g).swap = greatestPair (swapArguments g) (swapArguments f) := by
  apply le_antisymm
  · exact le_greatestPair_of_postfixed (swapArguments g) (swapArguments f) _ _
      (greatestPair_right f g).ge (greatestPair_left f g).ge
  · have h := le_greatestPair_of_postfixed f g
      (greatestPair (swapArguments g) (swapArguments f)).2
      (greatestPair (swapArguments g) (swapArguments f)).1
      (greatestPair_right (swapArguments g) (swapArguments f)).ge
      (greatestPair_left (swapArguments g) (swapArguments f)).ge
    exact ⟨h.2, h.1⟩

/-- uniqueness of the simultaneous solution is exactly equality of both extrema. -/
theorem existsUnique_fixed_iff_extrema_eq (f : α →o β →o α) (g : α →o β →o β) :
    (∃! p, jointStep f g p = p) ↔ leastPair f g = greatestPair f g := by
  constructor
  · rintro ⟨p, _, hp⟩
    exact (hp _ (leastPair_fixed f g)).trans (hp _ (greatestPair_fixed f g)).symm
  · intro h
    refine ⟨leastPair f g, leastPair_fixed f g, ?_⟩
    intro p hp
    apply le_antisymm
    · rw [h]
      exact le_greatestPair_of_postfixed f g p.1 p.2
        (congrArg Prod.fst hp).ge (congrArg Prod.snd hp).ge
    · exact leastPair_le_of_prefixed f g p.1 p.2
        (congrArg Prod.fst hp).le (congrArg Prod.snd hp).le

end Math.OrderTheory
