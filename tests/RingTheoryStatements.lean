import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.WittVector.Basic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Function
open scoped TensorProduct

section FiniteRings

variable {D : Type*}

example [DivisionRing D] [Finite D] : Field D := littleWedderburn D

example [DivisionRing D] [Finite D] (x y : D) : x * y = y * x := by
  let := littleWedderburn D
  exact mul_comm x y

example [Ring D] [Finite D] [IsDomain D] : IsField D := Finite.isDomain_to_isField D

end FiniteRings

section ChainConditions

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

example [IsArtinianRing R] :
    List.TFAE [Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M] :=
  IsArtinianRing.tfae R M

example [IsSemiprimaryRing R] : IsNoetherian R M ↔ IsArtinian R M :=
  IsSemiprimaryRing.isNoetherian_iff_isArtinian

example : IsArtinianRing R ↔ IsFiniteLength R R := isArtinianRing_iff_isFiniteLength R

example [IsArtinianRing R] : IsNoetherianRing R := inferInstance

end ChainConditions

section KrullDimension

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

example : IsArtinianRing R ↔ Ring.KrullDimLE 0 R := isArtinianRing_iff_krullDimLE_zero

example (I : Ideal R) [I.IsPrincipal] (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I p hp

example (x : R) (hx : ¬ IsUnit x) : (Ideal.span {x}).height ≤ 1 :=
  Ideal.height_span_singleton_le_one hx

example (s : Finset R) (hs : Ideal.span (s : Set R) ≠ ⊤) :
    (Ideal.span (s : Set R)).height ≤ s.card := Ideal.height_span_le_card_of_span_ne_top hs

end KrullDimension

section NoetherNormalization

variable {k A : Type*} [Field k] [CommRing A] [Nontrivial A]
  [Algebra k A] [Algebra.FiniteType k A]

example : ∃ s, ∃ g : MvPolynomial (Fin s) k →ₐ[k] A, Injective g ∧ g.IsIntegral :=
  exists_integral_inj_algHom_of_fg k A

example : ∃ s, ∃ g : MvPolynomial (Fin s) k →ₐ[k] A, Injective g ∧ g.Finite :=
  exists_finite_inj_algHom_of_fg k A

end NoetherNormalization

section Completion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

example : M →ₗ[R] AdicCompletion I M := AdicCompletion.of I M

example (n : ℕ) : Surjective (AdicCompletion.eval I M n) := AdicCompletion.eval_surjective I M n

example (n : ℕ) :
    (AdicCompletion.eval I M n).comp (AdicCompletion.of I M) =
      (I ^ n • (⊤ : Submodule R M)).mkQ := AdicCompletion.eval_comp_of I M n

example : Bijective (AdicCompletion.of I M) ↔ IsAdicComplete I M :=
  AdicCompletion.of_bijective_iff

example [IsAdicComplete I M] : M ≃ₗ[R] AdicCompletion I M := AdicCompletion.ofLinearEquiv I M

end Completion

section Flatness

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

example (e : M ≃ₗ[R] N) : Module.Flat R M ↔ Module.Flat R N := Module.Flat.equiv_iff e

example [Module.Flat R M] (f : N →ₗ[R] P) (hf : Injective f) : Injective (f.rTensor M) :=
  Module.Flat.rTensor_preserves_injective_linearMap f hf

example [Module.Flat R M] (f : N →ₗ[R] P) (hf : Injective f) : Injective (f.lTensor M) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

end Flatness

section EtaleAlgebras

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

example : Algebra.FormallyEtale R A ↔
    Algebra.FormallyUnramified R A ∧ Algebra.FormallySmooth R A :=
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

example : Algebra.Etale R A ↔ Algebra.FormallyUnramified R A ∧ Algebra.Smooth R A :=
  Algebra.Etale.iff_formallyUnramified_and_smooth

end EtaleAlgebras

section HopfAlgebras

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

example : HopfAlgebra.antipode R (1 : A) = 1 := HopfAlgebra.antipode_one

example (a : A) : Coalgebra.counit (R := R) (HopfAlgebra.antipode R a) = Coalgebra.counit a :=
  HopfAlgebra.counit_antipode a

example (a : A) :
    LinearMap.mul' R A ((HopfAlgebra.antipode R).rTensor A (Coalgebra.comul a)) =
      algebraMap R A (Coalgebra.counit a) := HopfAlgebra.mul_antipode_rTensor_comul_apply a

end HopfAlgebras

section WittVectors

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]

example : WittVector p R →+* (ℕ → R) := WittVector.ghostMap

example (f : R →+* S) (x : WittVector p R) (n : ℕ) :
    (WittVector.map f x).coeff n = f (x.coeff n) := WittVector.map_coeff f x n

example (f : R →+* S) (hf : Injective f) :
    Injective (WittVector.map f : WittVector p R → WittVector p S) :=
  WittVector.map_injective f hf

example (n : ℕ) (x y : WittVector p R) :
    WittVector.ghostComponent n (x + y) =
      WittVector.ghostComponent n x + WittVector.ghostComponent n y :=
  (WittVector.ghostComponent n).map_add x y

end WittVectors

section ChineseRemainder

variable {R ι : Type*} [CommRing R] [Finite ι]
  (M : Type*) [AddCommGroup M] [Module R M] (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))

example : Surjective (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) :=
  Ideal.pi_tensorProductMk_quotient_surjective M I hI

example :
    LinearMap.ker (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) =
      (⨅ i, I i) • (⊤ : Submodule R M) := Ideal.ker_tensorProductMk_quotient M I hI

end ChineseRemainder
