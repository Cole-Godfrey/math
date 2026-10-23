import Math.Algebra.FittingFinite

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Module Math.LinearAlgebra

section General

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

example (f : Module.End K V) (x : V) (h : x ∈ LinearMap.ker (f ^ finrank K V)) :
    f x ∈ LinearMap.ker (f ^ finrank K V) := fittingKer_invariant f x h

example (f : Module.End K V) (x : V) (h : x ∈ LinearMap.range (f ^ finrank K V)) :
    f x ∈ LinearMap.range (f ^ finrank K V) := fittingRange_invariant f x h

example (f : Module.End K V) : fittingNilpotent f ^ finrank K V = 0 := fittingNilpotent_pow f

example {f g : Module.End K V} (h : Commute f g) (x : V)
    (hx : x ∈ LinearMap.ker (f ^ finrank K V)) :
    g x ∈ LinearMap.ker (f ^ finrank K V) := fittingKer_invariant_of_commute h x hx

example {f g : Module.End K V} (h : Commute f g) (x : V)
    (hx : x ∈ LinearMap.range (f ^ finrank K V)) :
    g x ∈ LinearMap.range (f ^ finrank K V) := fittingRange_invariant_of_commute h x hx

end General

section Finite

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (f : Module.End K V)

example {n : ℕ} (h : finrank K V ≤ n) :
    LinearMap.range (f ^ n) = LinearMap.range (f ^ finrank K V) := range_pow_eq_finrank f h

example : IsCompl (LinearMap.ker (f ^ finrank K V)) (LinearMap.range (f ^ finrank K V)) :=
  isCompl_pow_finrank f

example : (LinearMap.ker (f ^ finrank K V) × LinearMap.range (f ^ finrank K V)) ≃ₗ[K] V :=
  fittingEquiv f

example (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    fittingEquiv f (x, y) = (x : V) + (y : V) := fittingEquiv_apply f x y

example (v : V) :
    ∃! u : LinearMap.ker (f ^ finrank K V) × LinearMap.range (f ^ finrank K V),
      (u.1 : V) + (u.2 : V) = v := existsUnique_fitting f v

example : IsNilpotent f ↔ f ^ finrank K V = 0 := isNilpotent_iff_pow_finrank f

example : Module.End K (LinearMap.ker (f ^ finrank K V)) := fittingNilpotent f

example : Module.End K (LinearMap.range (f ^ finrank K V)) := fittingInvertible f

example : IsUnit (fittingInvertible f) := fittingInvertible_isUnit f

example (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    f (fittingEquiv f (x, y)) = fittingEquiv f (fittingNilpotent f x, fittingInvertible f y) :=
  fittingEquiv_intertwines f x y

example : Module.End K V := fittingProjection f

example : LinearMap.range (fittingProjection f) = LinearMap.ker (f ^ finrank K V) :=
  range_fittingProjection f

example : LinearMap.ker (fittingProjection f) = LinearMap.range (f ^ finrank K V) :=
  ker_fittingProjection f

example : IsIdempotentElem (fittingProjection f) := fittingProjection_idempotent f

example (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    fittingProjection f ((x : V) + (y : V)) = x := fittingProjection_apply_add f x y

example (g : Module.End K V) (h : Commute f g) : Commute (fittingProjection f) g :=
  fittingProjection_commutes h

example : fittingProjection f * f ^ finrank K V = 0 := fittingProjection_mul_pow f

example : f ^ finrank K V * fittingProjection f = 0 := pow_mul_fittingProjection f

end Finite

example : IsNilpotent (0 : Module.End ℚ (Fin 0 → ℚ)) ↔
    (0 : Module.End ℚ (Fin 0 → ℚ)) ^ finrank ℚ (Fin 0 → ℚ) = 0 :=
  isNilpotent_iff_pow_finrank 0

example : IsUnit (fittingInvertible (0 : Module.End ℚ (Fin 0 → ℚ))) := fittingInvertible_isUnit 0
