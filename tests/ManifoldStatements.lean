module

import Math.Geometry.CompactComplex
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.WhitneyEmbedding

set_option autoImplicit false
set_option warningAsError true

open Bundle Function InnerProductSpace Set Topology
open scoped Manifold ContDiff Topology

noncomputable section

section Calculus

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {f : M → N} {g : N → P} {x : M}

example (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt J K g (f x)) :
    mfderiv I K (g ∘ f) x = (mfderiv J K g (f x)).comp (mfderiv I J f x) :=
  mfderiv_comp x hg hf

example (hf : MDifferentiable I J f) (hg : MDifferentiable J K g) :
    tangentMap I K (g ∘ f) = tangentMap J K g ∘ tangentMap I J f :=
  tangentMap_comp hg hf

example (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt J K g (f x))
    (v : TangentSpace I x) :
    mfderiv I K (g ∘ f) x v = mfderiv J K g (f x) (mfderiv I J f x v) :=
  mfderiv_comp_apply x hg hf v

example {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, J⟯ N) : ContMDiff I J n e := e.contMDiff

example {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, J⟯ N) : ContMDiff J I n e.symm := e.symm.contMDiff

example {n : ℕ∞ω} (e : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    (mfderiv I J e x).IsInvertible := e.isInvertible_mfderiv hn

end Calculus

section RealManifolds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {x : M} {t a b : ℝ}

example [CompleteSpace E] (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x)
    (hx : I.IsInteriorPoint x) : ∃ γ : ℝ → M, γ t = x ∧ IsMIntegralCurveAt γ v t :=
  exists_isMIntegralCurveAt_of_contMDiffAt t hv hx

variable [T2Space M]

example [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) (hγ' : IsMIntegralCurve γ' v) (heq : γ t = γ' t) : γ = γ' :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv hγ hγ' heq

example [BoundarylessManifold I M] (hγ : IsMIntegralCurve γ v)
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (heq : γ a = γ b) : Periodic γ (a - b) := hγ.periodic_of_eq hv heq

example [BoundarylessManifold I M] (hγ : IsMIntegralCurve γ v)
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) :
    Xor (∃ T > 0, Periodic γ T) (Injective γ) := hγ.periodic_xor_injective hv

end RealManifolds

section CompactEmbeddings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

example : ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x : M, Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x) :=
  exists_embedding_euclidean_of_compact

end CompactEmbeddings

section SmoothFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {f : M → F} {ε : M → ℝ}

example (hf : Continuous f) (hε : Continuous ε) (hp : ∀ x, 0 < ε x) (n : ℕ∞) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯,
      (∀ x, dist (g x) (f x) < ε x) ∧ Function.support g ⊆ Function.support f :=
  hf.exists_contMDiff_approx I n hε hp

example (hf : Continuous f) (hε : Continuous ε) (hp : ∀ x, 0 < ε x) (n : ℕ∞)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hfu : ContMDiffOn I 𝓘(ℝ, F) n f U) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, (∀ x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧
      Function.support g ⊆ Function.support f :=
  hf.exists_contMDiff_approx_and_eqOn I n hε hp hS hU hfu

example {S T : Set M} (hS : IsClosed S) (hT : IsClosed T) (hd : Disjoint S T) (n : ℕ∞) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ) n g ∧ range g ⊆ Icc 0 1 ∧
      (∀ x, x ∈ S ↔ g x = 0) ∧ (∀ x, x ∈ T ↔ g x = 1) :=
  exists_contMDiff_zero_iff_one_iff_of_isClosed I hS hT hd

example : ∃ f : SmoothPartitionOfUnity M I M univ,
    f.IsSubordinate (fun x => (chartAt H x).source) :=
  SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M

end SmoothFunctions

section ComplexManifolds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [CompactSpace M] [PreconnectedSpace M] {f : M → F}

example (hf : MDifferentiable I 𝓘(ℂ, F) f) (x y : M) : f x = f y :=
  hf.apply_eq_of_compactSpace x y

example (hf : MDifferentiable I 𝓘(ℂ, F) f) : ∃ y : F, f = Function.const M y :=
  hf.exists_eq_const_of_compactSpace

example (hf : MDifferentiable I 𝓘(ℂ, F) f) : (range f).Subsingleton :=
  Math.ComplexGeometry.range_subsingleton hf

example (hf : MDifferentiable I 𝓘(ℂ, F) f) (x : M) : mfderiv I 𝓘(ℂ, F) f x = 0 :=
  Math.ComplexGeometry.mfderiv_eq_zero hf x

example (hf : MDifferentiable I 𝓘(ℂ, F) f) : Injective f ↔ Subsingleton M :=
  Math.ComplexGeometry.injective_iff_subsingleton hf

example [Nontrivial M] (hf : MDifferentiable I 𝓘(ℂ, F) f) : ¬Injective f :=
  Math.ComplexGeometry.not_injective hf

example [Nontrivial F] (hf : MDifferentiable I 𝓘(ℂ, F) f) : ¬Surjective f :=
  Math.ComplexGeometry.not_surjective hf

example [Nontrivial E] (hf : MDifferentiable I 𝓘(ℂ, F) f) (x : M) :
    ¬Injective (mfderiv I 𝓘(ℂ, F) f x) :=
  Math.ComplexGeometry.not_injective_mfderiv hf x

example [Nontrivial E] (hf : MDifferentiable I 𝓘(ℂ, F) f) {n : ℕ∞ω} (hn : n ≠ 0) (x : M) :
    ¬Manifold.IsImmersionAt I 𝓘(ℂ, F) n f x :=
  Math.ComplexGeometry.not_isImmersionAt hf hn x

example [Nontrivial E] [Nonempty M] (hf : MDifferentiable I 𝓘(ℂ, F) f)
    {n : ℕ∞ω} (hn : n ≠ 0) : ¬Manifold.IsImmersion I 𝓘(ℂ, F) n f :=
  Math.ComplexGeometry.not_isImmersion hf hn

end ComplexManifolds

section RiemannianGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ (x : M), ENorm (TangentSpace I x)] {x y z : M}
  [∀ (x : M), ENormSMulClass ℝ (TangentSpace I x)]

example : Manifold.riemannianEDist I x x = 0 := Manifold.riemannianEDist_self

example : Manifold.riemannianEDist I x y = Manifold.riemannianEDist I y x :=
  Manifold.riemannianEDist_comm

example : Manifold.riemannianEDist I x z ≤
    Manifold.riemannianEDist I x y + Manifold.riemannianEDist I y z :=
  Manifold.riemannianEDist_triangle

example {γ : ℝ → M} {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    Manifold.riemannianEDist I x y ≤ Manifold.pathELength I γ a b :=
  Manifold.riemannianEDist_le_pathELength hγ ha hb hab

end RiemannianGeometry

section Connections

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M => TangentSpace I x)]
  (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _))
  {Y : (x : M) → TangentSpace I x} {x : M}

example : (CovariantDerivative.leviCivitaConnection I M).IsLeviCivitaConnection :=
  CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I

example : (CovariantDerivative.leviCivitaConnection I M).torsion = 0 :=
  CovariantDerivative.torsion_leviCivitaConnection_eq_zero I

example : (CovariantDerivative.leviCivitaConnection I M).IsMetricCompatible
    (M := M) (V := TangentSpace I) :=
  CovariantDerivative.isMetricCompatible_leviCivitaConnection I

example (hcov : cov.IsLeviCivitaConnection) (hcov' : cov'.IsLeviCivitaConnection)
    (hY : MDifferentiableAt I I.tangent (fun x => (⟨x, Y x⟩ : TangentBundle I M)) x)
    (v : TangentSpace I x) : cov Y x v = cov' Y x v :=
  hcov.uniqueness I hcov' hY v

end Connections

section LieAlgebras

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness 𝕜 3) G]

example : LieAlgebra 𝕜 (GroupLieAlgebra I G) := inferInstance

example (v : GroupLieAlgebra I G) : ⁅v, v⁆ = 0 := lie_self v

example (u v w : GroupLieAlgebra I G) : ⁅u, ⁅v, w⁆⁆ = ⁅⁅u, v⁆, w⁆ + ⁅v, ⁅u, w⁆⁆ :=
  leibniz_lie u v w

end LieAlgebras
