module

public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false
set_option warningAsError true

/-!
holomorphic maps from compact connected complex manifolds to normed spaces are constant.
their derivatives vanish, obstructing injective maps and immersions.
-/

@[expose] public noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Math.ComplexGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [CompactSpace M] [PreconnectedSpace M] {f : M → F}

/-- the image of a holomorphic map from a compact connected complex manifold is a subsingleton. -/
theorem range_subsingleton (hf : MDifferentiable I 𝓘(ℂ, F) f) : (range f).Subsingleton := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact hf.apply_eq_of_compactSpace x y

/-- a holomorphic map from a compact connected complex manifold has zero manifold derivative. -/
theorem mfderiv_eq_zero (hf : MDifferentiable I 𝓘(ℂ, F) f) (x : M) :
    mfderiv I 𝓘(ℂ, F) f x = 0 := by
  obtain ⟨v, hv⟩ := hf.exists_eq_const_of_compactSpace
  rw [hv]
  exact mfderiv_const

/-- such a holomorphic map is injective exactly when its source is a subsingleton. -/
theorem injective_iff_subsingleton (hf : MDifferentiable I 𝓘(ℂ, F) f) :
    Injective f ↔ Subsingleton M := by
  constructor
  · intro hi
    exact ⟨fun x y => hi (hf.apply_eq_of_compactSpace x y)⟩
  · intro hs x y _
    exact @Subsingleton.elim M hs x y

/-- a nontrivial compact connected complex manifold has no injective holomorphic map to a normed space. -/
theorem not_injective [Nontrivial M] (hf : MDifferentiable I 𝓘(ℂ, F) f) : ¬Injective f := by
  obtain ⟨x, y, hne⟩ := exists_pair_ne M
  intro hi
  exact hne (hi (hf.apply_eq_of_compactSpace x y))

/-- such a holomorphic map cannot cover a nontrivial normed space. -/
theorem not_surjective [Nontrivial F] (hf : MDifferentiable I 𝓘(ℂ, F) f) : ¬Surjective f := by
  obtain ⟨a, b, hne⟩ := exists_pair_ne F
  intro hs
  obtain ⟨x, hx⟩ := hs a
  obtain ⟨y, hy⟩ := hs b
  exact hne (hx.symm.trans ((hf.apply_eq_of_compactSpace x y).trans hy))

/-- a positive-dimensional model forces every holomorphic differential to fail injectivity. -/
theorem not_injective_mfderiv [Nontrivial E] (hf : MDifferentiable I 𝓘(ℂ, F) f) (x : M) :
    ¬Injective (mfderiv I 𝓘(ℂ, F) f x) := by
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  rw [mfderiv_eq_zero hf x]
  obtain ⟨v, w, hne⟩ := exists_pair_ne (TangentSpace I x)
  intro hi
  exact hne (hi (by simp))

/-- a holomorphic map from a positive-dimensional compact connected complex manifold is not an immersion at any point. -/
theorem not_isImmersionAt [Nontrivial E] (hf : MDifferentiable I 𝓘(ℂ, F) f)
    {n : ℕ∞ω} (hn : n ≠ 0) (x : M) : ¬Manifold.IsImmersionAt I 𝓘(ℂ, F) n f x := by
  intro hi
  exact not_injective_mfderiv hf x (hi.mfderiv_injective hn)

/-- a nonempty positive-dimensional compact connected complex manifold admits no holomorphic immersion into a normed space. -/
theorem not_isImmersion [Nontrivial E] [Nonempty M] (hf : MDifferentiable I 𝓘(ℂ, F) f)
    {n : ℕ∞ω} (hn : n ≠ 0) : ¬Manifold.IsImmersion I 𝓘(ℂ, F) n f := by
  obtain ⟨x⟩ := ‹Nonempty M›
  intro hi
  exact not_injective_mfderiv hf x (hi.mfderiv_injective hn x)

end Math.ComplexGeometry
