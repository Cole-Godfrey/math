module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Basic.Real.Basic

set_option autoImplicit false
set_option warningAsError true

/-!
finite-dimensional convex combinations need at most the dimension plus one points.
any dimension-plus-two family admits a radon partition.
-/

@[expose] public noncomputable section

open Finset Module Set

universe u

namespace Math.ConvexGeometry

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {x : E}

/-- carathéodory's theorem with an explicit dimension-plus-one bound on the supporting set. -/
theorem exists_finset_card_le_finrank_succ (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, (t : Set E) ⊆ s ∧ t.card ≤ finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (t : Set E) := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ha : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  simpa only [Fintype.card_coe] using
    ha.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

/-- the convex hull is the union of the hulls of subsets of size at most the dimension plus one. -/
theorem convexHull_eq_union_card_le_finrank_succ :
    convexHull ℝ s = ⋃ (t : Finset E) (_ : (t : Set E) ⊆ s)
      (_ : t.card ≤ finrank ℝ E + 1), convexHull ℝ (t : Set E) := by
  ext y
  simp only [mem_iUnion, exists_prop]
  constructor
  · exact exists_finset_card_le_finrank_succ
  · rintro ⟨t, ht, _, hy⟩
    exact convexHull_mono ht hy

/-- every convex-hull point has positive barycentric coordinates on at most the dimension plus one points. -/
theorem exists_positive_weights_card_le_finrank_succ (hx : x ∈ convexHull ℝ s) :
    ∃ (ι : Type u) (_ : Fintype ι) (z : ι → E) (w : ι → ℝ),
      Fintype.card ι ≤ finrank ℝ E + 1 ∧ range z ⊆ s ∧ AffineIndependent ℝ z ∧
        (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  obtain ⟨ι, hi, z, w, hz, ha, hw, hsum, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let : Fintype ι := hi
  exact ⟨ι, hi, z, w,
    ha.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1),
    hz, ha, hw, hsum, hx⟩

/-- any family larger than the dimension plus one has a radon partition. -/
theorem radon_partition_of_finrank_lt_card {ι : Type*} [Fintype ι] (f : ι → E)
    (hc : finrank ℝ E + 1 < Fintype.card ι) :
    ∃ I : Set ι, (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty := by
  apply Convex.radon_partition
  intro ha
  exact (not_lt_of_ge (ha.card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1))) hc

/-- every dimension-plus-two family can be split into two parts with intersecting convex hulls. -/
theorem radon_partition_finrank_add_two (f : Fin (finrank ℝ E + 2) → E) :
    ∃ I : Set (Fin (finrank ℝ E + 2)),
      (convexHull ℝ (f '' I) ∩ convexHull ℝ (f '' Iᶜ)).Nonempty := by
  apply radon_partition_of_finrank_lt_card
  simp only [Fintype.card_fin]
  omega

end Math.ConvexGeometry
