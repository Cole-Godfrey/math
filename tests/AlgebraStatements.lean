import Mathlib.FieldTheory.AbelRuffini
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Nullstellensatz

open scoped Polynomial IntermediateField

noncomputable section

section Extensions

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

example [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup

example [FiniteDimensional F E] [IsGalois F E] (K : IntermediateField F E) :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K :=
  IsGalois.fixedField_fixingSubgroup K

example [FiniteDimensional F E] (H : Subgroup (E ≃ₐ[F] E)) :
    IntermediateField.fixingSubgroup (IntermediateField.fixedField H) = H :=
  IntermediateField.fixingSubgroup_fixedField H

example [IsGalois F E] : IntermediateField F E ≃o (ClosedSubgroup (E ≃ₐ[F] E))ᵒᵈ :=
  InfiniteGalois.IntermediateFieldEquivClosedSubgroup

example [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ x : E, IntermediateField.adjoin F {x} = ⊤ := Field.exists_primitive_element F E

example [FiniteDimensional F E] [IsGalois F E] : Module.Basis (E ≃ₐ[F] E) F E :=
  IsGalois.normalBasis F E

example [FiniteDimensional F E] [IsGalois F E] (e : E ≃ₐ[F] E) :
    IsGalois.normalBasis F E e = e (IsGalois.normalBasis F E 1) :=
  IsGalois.normalBasis_apply e

example [IsGalois F E] : (E ≃ₐ[F] E) ≃ₜ*
    ↥(ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor F E)) :=
  InfiniteGalois.continuousMulEquivToLimit F E

example {x : E} (hx : x ∈ solvableByRad F E) {q : F[X]}
    (hq : Irreducible q) (hxq : Polynomial.aeval x q = 0) : Group.IsSolvable q.Gal :=
  isSolvable_gal_of_irreducible hx hq hxq

end Extensions

section Nullstellensatz

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
variable {σ : Type*} [Finite σ]

example (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

example (I : Ideal (MvPolynomial σ K)) :
    I.IsMaximal ↔ ∃ x : σ → K, I = MvPolynomial.vanishingIdeal K {x} :=
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

end Nullstellensatz
