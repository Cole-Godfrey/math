import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Module.Equiv.Basic

set_option autoImplicit false
set_option warningAsError true

namespace Math.CommutativeAlgebra

open Module Submodule Function

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- a linear map descends modulo the ideal multiples of its source and target. -/
def idealReduction (I : Ideal R) (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- reduction agrees with the original map on quotient representatives. -/
theorem idealReduction_mk (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    idealReduction I f ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := rfl

/-- the quotient projections commute with reduction. -/
theorem idealReduction_mkQ (I : Ideal R) (f : M →ₗ[R] N) :
    (idealReduction I f).comp (I • (⊤ : Submodule R M)).mkQ =
      (I • (⊤ : Submodule R N)).mkQ.comp f := by
  ext x
  rfl

/-- reduction preserves identity maps. -/
theorem idealReduction_id (I : Ideal R) :
    idealReduction I (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  rfl

/-- reduction preserves composition. -/
theorem idealReduction_comp (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    idealReduction I (g.comp f) = (idealReduction I g).comp (idealReduction I f) := by
  ext x
  rfl

/-- every surjective linear map remains surjective after ideal reduction. -/
theorem idealReduction_surjective (I : Ideal R) (f : M →ₗ[R] N) (hf : Surjective f) :
    Surjective (idealReduction I f) := by
  intro x
  obtain ⟨n, rfl⟩ := (I • (⊤ : Submodule R N)).mkQ_surjective x
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨(I • (⊤ : Submodule R M)).mkQ m, rfl⟩

/-- surjectivity lifts from a jacobson quotient when the target is finitely generated. -/
theorem idealReduction_surjective_iff [Module.Finite R N]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : M →ₗ[R] N) :
    Surjective (idealReduction I f) ↔ Surjective f := by
  refine ⟨fun hf => ?_, idealReduction_surjective I f⟩
  apply LinearMap.surjective_of_surjective_comp_mkQ f I hI
  rw [← idealReduction_mkQ I f]
  exact hf.comp (I • (⊤ : Submodule R M)).mkQ_surjective

/-- ideal reduction is a homomorphism of endomorphism rings. -/
def idealReductionEnd (I : Ideal R) :
    Module.End R M →+* Module.End R (M ⧸ (I • (⊤ : Submodule R M))) where
  toFun := idealReduction I
  map_zero' := by ext x; rfl
  map_one' := idealReduction_id I
  map_add' f g := by ext x; rfl
  map_mul' f g := idealReduction_comp I g f

/-- reduction vanishes exactly when the map has image in the ideal multiples. -/
theorem idealReduction_eq_zero_iff (I : Ideal R) (f : M →ₗ[R] N) :
    idealReduction I f = 0 ↔ LinearMap.range f ≤ I • (⊤ : Submodule R N) := by
  constructor
  · intro h _ hx
    obtain ⟨x, rfl⟩ := hx
    have hx := DFunLike.congr_fun h ((I • (⊤ : Submodule R M)).mkQ x)
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  · intro h
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h (LinearMap.mem_range_self f x))

/-- a surjective endomorphism of a finite module over a commutative ring is a unit. -/
theorem finiteEnd_isUnit_iff_surjective [Module.Finite R M] (f : Module.End R M) :
    IsUnit f ↔ Surjective f := by
  constructor
  · exact fun h => ((Module.End.isUnit_iff f).mp h).2
  · exact fun h => (Module.End.isUnit_iff f).mpr
      (OrzechProperty.bijective_of_surjective_endomorphism f h)

/-- invertibility is detected modulo any ideal contained in the jacobson radical. -/
theorem idealReductionEnd_isUnit_iff [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M) :
    IsUnit (idealReductionEnd I f) ↔ IsUnit f := by
  constructor
  · intro h
    apply (finiteEnd_isUnit_iff_surjective f).mpr
    apply (idealReduction_surjective_iff I hI f).mp
    exact ((Module.End.isUnit_iff _).mp h).2
  · exact fun h => h.map (idealReductionEnd I)

/-- endomorphisms with the same jacobson reduction have the same invertibility. -/
theorem isUnit_iff_of_idealReductionEnd_eq [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f g : Module.End R M)
    (h : idealReductionEnd I f = idealReductionEnd I g) : IsUnit f ↔ IsUnit g := by
  rw [← idealReductionEnd_isUnit_iff I hI f, h, idealReductionEnd_isUnit_iff I hI g]

/-- a finite-module endomorphism that reduces to the identity is invertible. -/
theorem isUnit_of_idealReductionEnd_eq_one [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (h : idealReductionEnd I f = 1) : IsUnit f := by
  apply (idealReductionEnd_isUnit_iff I hI f).mp
  rw [h]
  exact isUnit_one

/-- adding an endomorphism with zero reduction preserves the identity's invertibility. -/
theorem isUnit_one_add_of_idealReductionEnd_eq_zero [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (h : idealReductionEnd I f = 0) : IsUnit (1 + f) := by
  apply isUnit_of_idealReductionEnd_eq_one I hI
  rw [map_add, map_one, h, add_zero]

/-- a perturbation with zero jacobson reduction preserves invertibility. -/
theorem isUnit_add_iff_of_idealReductionEnd_eq_zero [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f g : Module.End R M)
    (hg : idealReductionEnd I g = 0) : IsUnit (f + g) ↔ IsUnit f := by
  apply isUnit_iff_of_idealReductionEnd_eq I hI
  rw [map_add, hg, add_zero]

/-- maps into jacobson multiples give invertible left and right perturbations. -/
theorem isUnit_one_sub_mul_of_range_le_smul_top [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f g : Module.End R M)
    (hf : LinearMap.range f ≤ I • (⊤ : Submodule R M)) :
    IsUnit (1 - g * f) ∧ IsUnit (1 - f * g) := by
  have h : idealReductionEnd I f = 0 := (idealReduction_eq_zero_iff I f).mpr hf
  constructor
  · apply isUnit_of_idealReductionEnd_eq_one I hI
    rw [map_sub, map_one, map_mul, h, mul_zero, sub_zero]
  · apply isUnit_of_idealReductionEnd_eq_one I hI
    rw [map_sub, map_one, map_mul, h, zero_mul, sub_zero]

/-- over a local ring, reduction modulo the maximal ideal detects invertibility. -/
theorem maximalIdealReduction_isUnit_iff [IsLocalRing R] [Module.Finite R M]
    (f : Module.End R M) :
    IsUnit (idealReductionEnd (IsLocalRing.maximalIdeal R) f) ↔ IsUnit f :=
  idealReductionEnd_isUnit_iff _ (IsLocalRing.maximalIdeal_le_jacobson _) f

/-- a set generates a finite module exactly when its images generate a jacobson quotient. -/
theorem span_quotient_image_eq_top_iff [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (s : Set M) :
    Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤ ↔ Submodule.span R s = ⊤ := by
  rw [← Submodule.map_span]
  constructor
  · intro h
    apply top_unique
    apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
    rw [top_le_iff, sup_comm]
    exact (Submodule.map_mkQ_eq_top _ _).mp h
  · intro h
    rw [h, Submodule.map_top, Submodule.range_mkQ]

/-- a surjective reduction specifies an automorphism of the original finite module. -/
noncomputable def automorphismOfReductionSurjective [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) : M ≃ₗ[R] M :=
  LinearEquiv.ofBijective f (OrzechProperty.bijective_of_surjective_endomorphism f
    ((idealReduction_surjective_iff I hI f).mp hf))

/-- the lifted automorphism is the given endomorphism on every element. -/
theorem automorphismOfReductionSurjective_apply [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) (x : M) :
    automorphismOfReductionSurjective I hI f hf x = f x := rfl

/-- the lifted automorphism retains the original linear map. -/
theorem automorphismOfReductionSurjective_toLinearMap [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson) (f : Module.End R M)
    (hf : Surjective (idealReductionEnd I f)) :
    (automorphismOfReductionSurjective I hI f hf).toLinearMap = f := rfl

end Math.CommutativeAlgebra
