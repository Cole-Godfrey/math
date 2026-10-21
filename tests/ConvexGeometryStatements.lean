module

import Math.Geometry.ConvexFinite
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StoneSeparation

set_option autoImplicit false
set_option warningAsError true

open Module Set

universe u

section FiniteDimensional

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E}

example (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧ t.card ≤ finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (t : Set E) :=
  Math.ConvexGeometry.exists_finset_card_le_finrank_succ hx

example : convexHull ℝ s = ⋃ (t : Finset E) (_ : (t : Set E) ⊆ s)
    (_ : t.card ≤ finrank ℝ E + 1), convexHull ℝ (t : Set E) :=
  Math.ConvexGeometry.convexHull_eq_union_card_le_finrank_succ

example (hx : x ∈ convexHull ℝ s) :
    ∃ (ι : Type u) (_ : Fintype ι) (z : ι → E) (w : ι → ℝ),
      Fintype.card ι ≤ finrank ℝ E + 1 ∧ range z ⊆ s ∧ AffineIndependent ℝ z ∧
        (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x :=
  Math.ConvexGeometry.exists_positive_weights_card_le_finrank_succ hx

example {ι : Type*} [Fintype ι] (f : ι → E) (hc : finrank ℝ E + 1 < Fintype.card ι) :
    ∃ I : Set ι, (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty :=
  Math.ConvexGeometry.radon_partition_of_finrank_lt_card f hc

example (f : Fin (finrank ℝ E + 2) → E) :
    ∃ I : Set (Fin (finrank ℝ E + 2)),
      (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty :=
  Math.ConvexGeometry.radon_partition_finrank_add_two f

example {ι : Type*} {F : ι → Set E} {A : Finset ι}
    (hcard : finrank ℝ E + 1 ≤ A.card) (hc : ∀ i ∈ A, Convex ℝ (F i))
    (hi : ∀ I ⊆ A, I.card = finrank ℝ E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ A, F i).Nonempty :=
  Convex.helly_theorem hcard hc hi

end FiniteDimensional

example {s : Set (Fin 2 → ℝ)} {x : Fin 2 → ℝ} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset (Fin 2 → ℝ), (t : Set (Fin 2 → ℝ)) ⊆ s ∧ t.card ≤ 3 ∧
      x ∈ convexHull ℝ (t : Set (Fin 2 → ℝ)) := by
  obtain ⟨t, ht, hc, hxt⟩ := Math.ConvexGeometry.exists_finset_card_le_finrank_succ hx
  exact ⟨t, ht, by simpa using hc, hxt⟩

example (f : Fin 4 → Fin 2 → ℝ) :
    ∃ I : Set (Fin 4), (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty := by
  apply Math.ConvexGeometry.radon_partition_of_finrank_lt_card
  norm_num

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {s t : Set E}

example (hs : Convex ℝ s) (ht : Convex ℝ t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex ℝ C ∧ Convex ℝ Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
  exists_convex_convex_compl_subset hs ht hst

example : convexHull ℝ s = ⋃ (t : Finset E) (_ : (t : Set E) ⊆ s)
    (_ : AffineIndependent ℝ ((↑) : t → E)), convexHull ℝ (t : Set E) :=
  convexHull_eq_union

example {ι : Type*} {f : ι → E} (h : ¬AffineIndependent ℝ f) :
    ∃ I : Set ι, (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty :=
  Convex.radon_partition h

example {ι : Type*} {A : Finset ι} {w : ι → ℝ} {p : ι → E} {f : E → ℝ}
    (hf : ConvexOn ℝ s f) (hw : ∀ i ∈ A, 0 ≤ w i) (hsum : ∑ i ∈ A, w i = 1)
    (hp : ∀ i ∈ A, p i ∈ s) :
    f (∑ i ∈ A, w i • p i) ≤ ∑ i ∈ A, w i * f (p i) := by
  simpa only [smul_eq_mul] using hf.map_sum_le hw hsum hp

example {ι : Type*} {A : Finset ι} {w : ι → ℝ} {p : ι → E} {f : E → ℝ}
    (hf : StrictConvexOn ℝ s f) (hw : ∀ i ∈ A, 0 < w i) (hsum : ∑ i ∈ A, w i = 1)
    (hp : ∀ i ∈ A, p i ∈ s) :
    f (∑ i ∈ A, w i • p i) = ∑ i ∈ A, w i * f (p i) ↔
      ∀ ⦃j⦄, j ∈ A → ∀ ⦃k⦄, k ∈ A → p j = p k := by
  simpa only [smul_eq_mul] using hf.map_sum_eq_iff_of_pos hw hsum hp

end Algebraic

section Topological

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {s : Set E}

example (hc : IsCompact s) (hn : s.Nonempty) : (extremePoints ℝ s).Nonempty :=
  hc.extremePoints_nonempty hn

example (hc : IsCompact s) (hv : Convex ℝ s) :
    closure (convexHull ℝ (extremePoints ℝ s)) = s :=
  closure_convexHull_extremePoints hc hv

example (hv : Convex ℝ s) (hn : s.Nonempty) : ContractibleSpace s :=
  hv.contractibleSpace hn

end Topological

section Birkhoff

variable {n : Type*} [Fintype n] [DecidableEq n]

example : doublyStochastic ℝ n = convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm n} :=
  doublyStochastic_eq_convexHull_permMatrix

example : extremePoints ℝ (doublyStochastic ℝ n) = {σ.permMatrix ℝ | σ : Equiv.Perm n} :=
  extremePoints_doublyStochastic

example {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic ℝ n) :
    ∃ w : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      ∑ σ, w σ • σ.permMatrix ℝ = M :=
  exists_eq_sum_perm_of_mem_doublyStochastic hM

end Birkhoff

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (C : ProperCone ℝ E) :
    ProperCone.innerDual (ProperCone.innerDual (C : Set E) : Set E) = C :=
  ProperCone.innerDual_innerDual C
