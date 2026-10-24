import Mathlib.Order.BourbakiWitt
import Mathlib.Order.Closure
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.JordanHolder
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.ScottContinuity
import Mathlib.Order.TransfiniteIteration
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Zorn

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u v w

section CompleteFixedPoints

variable {α : Type u} [CompleteLattice α] (f : α →o α)

example : f f.lfp = f.lfp := f.map_lfp

example : f f.gfp = f.gfp := f.map_gfp

example : IsLeast {a | f a ≤ a} f.lfp := f.isLeast_lfp_le

example : IsGreatest {a | a ≤ f a} f.gfp := f.isGreatest_gfp_le

example : IsLeast (Function.fixedPoints f) f.lfp := f.isLeast_lfp

example : IsGreatest (Function.fixedPoints f) f.gfp := f.isGreatest_gfp

example : f.lfp ≤ f.gfp := f.lfp_le_gfp

example : CompleteLattice (Function.fixedPoints f) := inferInstance

example (h : OmegaCompletePartialOrder.ωScottContinuous f) :
    f.lfp = ⨆ n : ℕ, f^[n] ⊥ := fixedPoints.lfp_eq_sSup_iterate f h

example (h : OmegaCompletePartialOrder.ωScottContinuous f.dual) :
    f.gfp = ⨅ n : ℕ, f^[n] ⊤ := fixedPoints.gfp_eq_sInf_iterate f h

end CompleteFixedPoints

section FixedPointFusion

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]
  (f : α →o β) (g : β →o α)

example : f (g.comp f).lfp = (f.comp g).lfp := f.map_lfp_comp g

example : f (g.comp f).gfp = (f.comp g).gfp := f.map_gfp_comp g

end FixedPointFusion

section ChainCompleteness

variable {α : Type u} [ChainCompletePartialOrder α] [Nonempty α]

example (f : α → α) (h : ∀ a, a ≤ f a) : (Function.fixedPoints f).Nonempty :=
  ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary h

end ChainCompleteness

section Maximality

variable {α : Type u} [Preorder α]

example (h : ∀ c : Set α, IsChain (· ≤ ·) c → BddAbove c) :
    ∃ a : α, IsMax a := zorn_le h

example [Nonempty α]
    (h : ∀ c : Set α, IsChain (· ≤ ·) c → c.Nonempty → BddAbove c) :
    ∃ a : α, IsMax a := zorn_le_nonempty h

example (s : Set α)
    (h : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ b ∈ s, ∀ a ∈ c, a ≤ b) :
    ∃ a, Maximal (· ∈ s) a := zorn_le₀ s h

example {r : α → α → Prop} {c : Set α} (h : IsChain r c) :
    ∃ m, IsMaxChain r m ∧ c ⊆ m := h.exists_maxChain

end Maximality

section AdjointSuprema

variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β]
  {l : α → β} {r : β → α} (gc : GaloisConnection l r)

example (a b : α) : l (a ⊔ b) = l a ⊔ l b := gc.l_sup

example {ι : Sort w} (s : ι → α) : l (⨆ i, s i) = ⨆ i, l (s i) := gc.l_iSup

example (s : Set α) : l (sSup s) = sSup (l '' s) := gc.l_sSup_eq_sSup_image

example : ClosureOperator α := gc.closureOperator

example (a : α) : gc.closureOperator a = r (l a) := rfl

end AdjointSuprema

section AbstractClosure

variable {α : Type u} [PartialOrder α] (c : ClosureOperator α)

example (a : α) : a ≤ c a := c.le_closure a

example (a : α) : c (c a) = c a := c.idempotent a

example (a : α) : IsGLB {b | a ≤ b ∧ c.IsClosed b} (c a) := c.closure_isGLB a

example : GaloisInsertion c.toCloseds Subtype.val := c.gi

end AbstractClosure

section ClosureSuprema

variable {α : Type u} [CompleteLattice α] (c : ClosureOperator α)

example {ι : Sort v} (s : ι → α) : c (⨆ i, c (s i)) = c (⨆ i, s i) :=
  c.closure_iSup_closure s

end ClosureSuprema

section ScottMaps

variable {α : Type u} {β : Type v} {γ : Type w}
  [Preorder α] [Preorder β] [Preorder γ]

example {f : α → β} (h : ScottContinuous f) : Monotone f := h.monotone

example {f : α → β} {g : β → γ} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (g ∘ f) := hf.comp hg

end ScottMaps

section WellQuasiRelations

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

example {a : Set α} (ha : IsAntichain r a) (hr : WellQuasiOrdered r) : a.Finite :=
  ha.finite_of_wellQuasiOrdered hr

example [IsPreorder α r] (hr : WellQuasiOrdered r) (f : ℕ → α) :
    ∃ e : ℕ ↪o ℕ, ∀ m n, m ≤ n → r (f (e m)) (f (e n)) :=
  hr.exists_monotone_subseq f

example [IsPreorder α r] (hr : WellQuasiOrdered r) (hs : WellQuasiOrdered s) :
    WellQuasiOrdered (fun a b : α × β => r a.1 b.1 ∧ s a.2 b.2) := hr.prod hs

example [IsPreorder α r] (hr : WellQuasiOrdered r) :
    WellFounded (fun a b => r a b ∧ ¬ r b a) := hr.wellFounded

example {ι : Type w} {A : ι → Type u} [Finite ι]
    {R : ∀ i, A i → A i → Prop} [∀ i, IsPreorder (A i) (R i)]
    (h : ∀ i, WellQuasiOrdered (R i)) :
    WellQuasiOrdered (fun a b : ∀ i, A i => ∀ i, R i (a i) (b i)) :=
  WellQuasiOrdered.pi h

end WellQuasiRelations

section WellQuasiOrders

variable {α : Type u} [LinearOrder α]

example : WellQuasiOrderedLE α ↔ WellFoundedLT α := wellQuasiOrderedLE_iff_wellFoundedLT

end WellQuasiOrders

section CompositionSeries

variable {α : Type u} [Lattice α] [JordanHolderLattice α]

example (s t : CompositionSeries α) (h : s.head = t.head) (k : s.last = t.last) :
    CompositionSeries.Equivalent s t := s.jordan_holder t h k

example (s t : CompositionSeries α) (h : s.head = t.head) (k : s.last = t.last) :
    s.length = t.length := (s.jordan_holder t h k).length_eq

end CompositionSeries

section TransfiniteIteration

variable {α : Type u} [CompleteLattice α] (f : α → α)
  {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

example (a : α) : transfiniteIterate f (⊥ : J) a = a := transfiniteIterate_bot f a

example (a : α) (j : J) (h : ¬ IsMax j) :
    transfiniteIterate f (Order.succ j) a = f (transfiniteIterate f j a) :=
  transfiniteIterate_succ f a j h

example (a : α) (j : J) (h : Order.IsSuccLimit j) :
    transfiniteIterate f j a = ⨆ k : Set.Iio j, transfiniteIterate f k.1 a :=
  transfiniteIterate_limit f a j h

example (a : α) (h : ∀ b, b ≤ f b) :
    Monotone (fun j : J => transfiniteIterate f j a) := monotone_transfiniteIterate f a h

end TransfiniteIteration

section Ultrafilters

variable {α : Type u}

example (f : Filter α) [f.NeBot] : ∃ u : Ultrafilter α, (u : Filter α) ≤ f :=
  Ultrafilter.exists_le f

example (u : Ultrafilter α) (s : Set α) : s ∈ u ∨ sᶜ ∈ u := u.mem_or_compl_mem s

example (s : Set (Set α))
    (h : ∀ t : Finset (Set α), (t : Set (Set α)) ⊆ s →
      (⋂₀ (t : Set (Set α))).Nonempty) :
    ∃ u : Ultrafilter α, s ⊆ u.sets :=
  Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty s h

end Ultrafilters
