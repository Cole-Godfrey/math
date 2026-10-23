import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Module Polynomial
open scoped TensorProduct Matrix Affine

section Matrices

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

example (A B : Matrix n n R) : (A * B).det = A.det * B.det := Matrix.det_mul A B

example : (1 : Matrix n n R).det = 1 := Matrix.det_one

example (A : Matrix n n R) : A.transpose.det = A.det := Matrix.det_transpose A

end Matrices

section FiniteFree

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] (f : Module.End R V)

example : f.charpoly.Monic := LinearMap.charpoly_monic f

example : aeval f f.charpoly = 0 := LinearMap.aeval_self_charpoly f

example : IsIntegral R f := LinearMap.isIntegral f

example (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  LinearMap.aeval_eq_aeval_mod_charpoly f p

example (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) :=
  LinearMap.pow_eq_aeval_mod_charpoly f k

example [StrongRankCondition R] : f.charpoly.natDegree = finrank R V :=
  LinearMap.charpoly_natDegree f

example [IsDomain R] (μ : R) : f.HasEigenvalue μ ↔ f.charpoly.IsRoot μ :=
  Module.End.hasEigenvalue_iff_isRoot_charpoly f μ

example (μ : R) : (f - μ • 1).charpoly = f.charpoly.comp (X + C μ) :=
  LinearMap.charpoly_sub_smul f μ

end FiniteFree

section Fields

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W]

example (f : V →ₗ[K] W) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

example (f : Module.End K V) : minpoly K f ∣ f.charpoly := LinearMap.minpoly_dvd_charpoly f

example (f : Module.End K V) (μ : K) : μ ∈ spectrum K f ↔ f.charpoly.IsRoot μ :=
  Module.End.mem_spectrum_iff_isRoot_charpoly f μ

example [PerfectField K] (f : Module.End K V) :
    ∃ n ∈ Algebra.adjoin K {f}, ∃ s ∈ Algebra.adjoin K {f},
      IsNilpotent n ∧ Module.End.IsSemisimple s ∧ f = n + s :=
  Module.End.exists_isNilpotent_isSemisimple

example [PerfectField K] {n₁ s₁ n₂ s₂ : Module.End K V}
    (hn₁ : IsNilpotent n₁) (hs₁ : Module.End.IsSemisimple s₁)
    (hn₂ : IsNilpotent n₂) (hs₂ : Module.End.IsSemisimple s₂)
    (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂) (h : n₁ + s₁ = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ :=
  Module.End.isNilpotent_isSemisimple_unique hn₁ hs₁ hn₂ hs₂ hc₁ hc₂ h

example : V ≃ₗ[K] Module.Dual K (Module.Dual K V) := Module.evalEquiv K V

example (S : Subspace K V) :
    finrank K S + finrank K S.dualAnnihilator = finrank K V :=
  Subspace.finrank_add_finrank_dualAnnihilator_eq S

end Fields

section Tensor

variable {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] (b : Basis ι R M) (c : Basis κ R N)

example : Basis (ι × κ) R (M ⊗[R] N) := b.tensorProduct c

example (i : ι) (j : κ) : b.tensorProduct c (i, j) = b i ⊗ₜ[R] c j :=
  Basis.tensorProduct_apply b c i j

example [StrongRankCondition R] [Module.Free R M] [Module.Free R N] :
    finrank R (M ⊗[R] N) = finrank R M * finrank R N := Module.finrank_tensorProduct

end Tensor

section Symmetric

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [CommSemiring A] [Algebra R A]

example : (M →ₗ[R] A) ≃ (SymmetricAlgebra R M →ₐ[R] A) := SymmetricAlgebra.lift

example (f : M →ₗ[R] A) (x : M) : SymmetricAlgebra.lift f (SymmetricAlgebra.ι R M x) = f x :=
  SymmetricAlgebra.lift_ι_apply f x

end Symmetric

section Affine

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AffineSpace V P]

example (c : P) (r : R) (p : P) :
    AffineMap.homothety c r p = r • (p -ᵥ c : V) +ᵥ c := AffineMap.homothety_apply c r p

example (c : P) (r : R) : AffineMap.homothety c r c = c := AffineMap.homothety_apply_same c r

end Affine

section ExteriorAndClifford

variable {R M A : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Semiring A] [Algebra R A]

example (x : M) : ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R x = 0 :=
  ExteriorAlgebra.ι_sq_zero x

example (x y : M) :
    ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y +
      ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R x = 0 := ExteriorAlgebra.ι_add_mul_swap x y

example (f : M →ₗ[R] A) (h : ∀ x, f x * f x = 0) :
    (ExteriorAlgebra.lift R ⟨f, h⟩).toLinearMap.comp (ExteriorAlgebra.ι R) = f :=
  ExteriorAlgebra.ι_comp_lift R f h

example (Q : QuadraticForm R M) (x : M) :
    CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q x = algebraMap R _ (Q x) :=
  CliffordAlgebra.ι_sq_scalar Q x

example (Q : QuadraticForm R M) (x y : M) :
    CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q y +
      CliffordAlgebra.ι Q y * CliffordAlgebra.ι Q x =
        algebraMap R _ (QuadraticMap.polar Q x y) := CliffordAlgebra.ι_mul_ι_add_swap x y

example (Q : QuadraticForm R M) (f : M →ₗ[R] A)
    (h : ∀ x, f x * f x = algebraMap R A (Q x)) :
    (CliffordAlgebra.lift Q ⟨f, h⟩).toLinearMap.comp (CliffordAlgebra.ι Q) = f :=
  CliffordAlgebra.ι_comp_lift f h

end ExteriorAndClifford

section Projective

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

example (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Projectivization.mk_eq_mk_iff K v w hv hw

example (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔ ∃ a : K, a • w = v :=
  Projectivization.mk_eq_mk_iff' K v w hv hw

end Projective

section RootSystems

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

example (i : ι) : RootPairing.Equiv.reflection P i ∈ P.weylGroup :=
  RootPairing.reflection_mem_weylGroup P i

example [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] :
    P.IsG2 ↔ ∃ i j, P.pairingIn ℤ i j = -3 := RootPairing.isG2_iff P

end RootSystems

section Quadratic

variable {R M : Type*} [CommRing R] [LinearOrder R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

example : sigPos Q ≤ finrank R M := sigPos_le_finrank Q

example [Module.Finite R M] [StrongRankCondition R] :
    ∃ S : Submodule R M, finrank R S = sigPos Q ∧ (Q.restrict S).PosDef :=
  exists_finrank_eq_sigPos_and_posDef Q

end Quadratic
