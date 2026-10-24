import Math.Algebra.JacobsonReduction

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Function Math.CommutativeAlgebra

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]


example (I : Ideal R) (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
  idealReduction I f

example (I : Ideal R) :
    Module.End R M →+* Module.End R (M ⧸ (I • (⊤ : Submodule R M))) := idealReductionEnd I

example [Module.Finite R N] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : M →ₗ[R] N) :
    Surjective (idealReduction I f) ↔ Surjective f := idealReduction_surjective_iff I hI f

example [Module.Finite R M] (f : Module.End R M) : IsUnit f ↔ Surjective f :=
  finiteEnd_isUnit_iff_surjective f

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M) :
    IsUnit (idealReductionEnd I f) ↔ IsUnit f := idealReductionEnd_isUnit_iff I hI f

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : idealReductionEnd I f = 0) : IsUnit (1 + f) :=
  isUnit_one_add_of_idealReductionEnd_eq_zero I hI f hf

example [IsLocalRing R] [Module.Finite R M] (f : Module.End R M) :
    IsUnit (idealReductionEnd (IsLocalRing.maximalIdeal R) f) ↔ IsUnit f :=
  maximalIdealReduction_isUnit_iff f

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (s : Set M) :
    Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤ ↔ Submodule.span R s = ⊤ :=
  span_quotient_image_eq_top_iff I hI s

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) : M ≃ₗ[R] M := automorphismOfReductionSurjective I hI f hf

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) (x : M) :
    automorphismOfReductionSurjective I hI f hf x = f x :=
  automorphismOfReductionSurjective_apply I hI f hf x

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) :
    (automorphismOfReductionSurjective I hI f hf).toLinearMap = f :=
  automorphismOfReductionSurjective_toLinearMap I hI f hf

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f g : Module.End R M)
    (h : idealReductionEnd I f = idealReductionEnd I g) : IsUnit f ↔ IsUnit g :=
  isUnit_iff_of_idealReductionEnd_eq I hI f g h


example (I : Ideal R) (f : M →ₗ[R] N) :
    idealReduction I f = 0 ↔ LinearMap.range f ≤ I • (⊤ : Submodule R N) :=
  idealReduction_eq_zero_iff I f

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (f g : Module.End R M) (hg : idealReductionEnd I g = 0) :
    IsUnit (f + g) ↔ IsUnit f := isUnit_add_iff_of_idealReductionEnd_eq_zero I hI f g hg

example [Module.Finite R M] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (f g : Module.End R M) (hf : LinearMap.range f ≤ I • (⊤ : Submodule R M)) :
    IsUnit (1 - g * f) ∧ IsUnit (1 - f * g) :=
  isUnit_one_sub_mul_of_range_le_smul_top I hI f g hf

example (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    idealReduction I f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := idealReduction_mk I f x

example (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    idealReduction I (g.comp f) = (idealReduction I g).comp (idealReduction I f) :=
  idealReduction_comp I f g

example (I : Ideal R) :
    idealReduction I (LinearMap.id : M →ₗ[R] M) = LinearMap.id := idealReduction_id I
