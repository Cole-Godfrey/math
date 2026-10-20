module

import Math.Analysis.LaxMilgram
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false
set_option warningAsError true

open Set Filter Function
open scoped Topology NNReal ENNReal

noncomputable section

section NormedSpaces

example {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example [CompleteSpace E] {ι : Type*} {g : ι → E →L[𝕜] F}
    (hg : ∀ x, ∃ C : ℝ, ∀ i, ‖g i x‖ ≤ C) : ∃ C : ℝ, ∀ i, ‖g i‖ ≤ C :=
  banach_steinhaus hg

example [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (hT : Surjective T) : IsOpenMap T :=
  T.isOpenMap hT

example [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (hinj : T.ker = ⊥) (hsurj : T.range = ⊤) : E ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective T hinj hsurj

example [CompleteSpace E] [CompleteSpace F] (T : E →ₗ[𝕜] F)
    (hT : IsClosed (T.graph : Set (E × F))) : Continuous T :=
  T.continuous_of_isClosed_graph hT

example [CompleteSpace 𝕜] [CompleteSpace E] :
    IsOpen {T : E →L[𝕜] F | T.IsFredholm} :=
  ContinuousLinearMap.isOpen_setOfPred_isFredholm

example [CompleteSpace 𝕜] [CompleteSpace E] {T₀ : E →L[𝕜] F} (hT : T₀.IsFredholm) :
    ∀ᶠ T in 𝓝 T₀, T.index = T₀.index :=
  hT.eventually_nhds_index_eq

example [CompleteSpace E] {T : E →L[𝕜] E} {μ : 𝕜}
    (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T : Module.End 𝕜 E) μ ∨ μ ∈ resolventSet 𝕜 T :=
  hT.hasEigenvalue_or_mem_resolventSet hμ

example [CompleteSpace E] {T : E →L[𝕜] E} {μ : 𝕜}
    (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T : Module.End 𝕜 E) μ ↔ μ ∈ spectrum 𝕜 T :=
  hT.hasEigenvalue_iff_mem_spectrum hμ

example [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact ((WeakDual.toStrongDual : WeakDual 𝕜 E → StrongDual 𝕜 E) ⁻¹'
      Metric.closedBall x' r) :=
  WeakDual.isCompact_closedBall x' r

end NormedSpaces

section HilbertSpaces

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

example [CompleteSpace E] : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  InnerProductSpace.toDual 𝕜 E

example [CompleteSpace E] (ℓ : StrongDual 𝕜 E) (x : E) :
    inner 𝕜 ((InnerProductSpace.toDual 𝕜 E).symm ℓ) x = ℓ x :=
  InnerProductSpace.toDual_symm_apply

example (K : Submodule 𝕜 E) (hK : IsComplete (K : Set E)) (u : E) :
    ∃ v ∈ K, ‖u - v‖ = ⨅ w : (K : Set E), ‖u - w‖ :=
  K.exists_norm_eq_iInf_of_complete_subspace hK u

example [CompleteSpace E] (T : E →L[𝕜] E) (hT : ‖T‖ ≤ 1) (x : E) :
    Tendsto (birkhoffAverage 𝕜 T id · x) atTop
      (𝓝 ((T.eqLocus (1 : E →L[𝕜] E)).orthogonalProjectionOnto x)) :=
  T.tendsto_birkhoffAverage_orthogonalProjection hT x

example [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  hT.apply_eigenvectorBasis hn i

example [CompleteSpace E] {T : E →L[𝕜] E}
    (hc : IsCompactOperator T) (hs : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs

example [CompleteSpace E] {T : E →L[𝕜] E} (hc : IsCompactOperator T)
    (μ : 𝕜) (hμ : μ ≠ 0) : FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ) :=
  T.finite_dimensional_eigenspace hc μ hμ

example [FiniteDimensional 𝕜 E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F)
    {n : ℕ} (hn : n < Module.finrank 𝕜 E) :
    Module.End.HasEigenvalue (LinearMap.adjoint T ∘ₗ T) (T.singularValues n ^ 2) :=
  T.hasEigenvalue_adjoint_comp_self_sq_singularValues hn

end HilbertSpaces

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hne : K.Nonempty) (hc : IsComplete K) (hv : Convex ℝ K) (u : E) :
    ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ :=
  exists_norm_eq_iInf_of_complete_convex hne hc hv u

section WeakSolutions

open Math.FunctionalAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

example (hB : IsCoercive B) : StrongDual ℝ V ≃L[ℝ] V := weakSolutionEquiv hB

example (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  existsUnique_weak_solution hB ℓ

example (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (weakSolution hB ℓ) v = ℓ v :=
  bilinear_weakSolution hB ℓ v

example (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v, B u v = ℓ v) : u = weakSolution hB ℓ :=
  eq_weakSolution hB hu

example (hB : IsCoercive B) (c : ℝ) (ℓ₁ ℓ₂ : StrongDual ℝ V) :
    weakSolution hB (c • ℓ₁ + ℓ₂) = c • weakSolution hB ℓ₁ + weakSolution hB ℓ₂ := by
  rw [weakSolution_add, weakSolution_smul]

example (hB : IsCoercive B) : Continuous (weakSolution hB) := continuous_weakSolution hB

example (hB : IsCoercive B) (ℓ : StrongDual ℝ V) {C : ℝ} (hC : 0 < C)
    (hc : ∀ v : V, C * ‖v‖ * ‖v‖ ≤ B v v) : ‖weakSolution hB ℓ‖ ≤ ‖ℓ‖ / C :=
  norm_weakSolution_le hB ℓ hC hc

example (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) {C : ℝ} (hC : 0 < C)
    (hc : ∀ v : V, C * ‖v‖ * ‖v‖ ≤ B v v) :
    dist (weakSolution hB ℓ₁) (weakSolution hB ℓ₂) ≤ ‖ℓ₁ - ℓ₂‖ / C :=
  dist_weakSolution_le hB ℓ₁ ℓ₂ hC hc

end WeakSolutions

section BanachAlgebras

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

example (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) atTop
      (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a

example [Nontrivial A] (a : A) : (spectrum ℂ a).Nonempty := spectrum.nonempty a

example (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) : ℂ ≃ₐ[ℂ] A :=
  NormedRing.algEquivComplexOfComplete hA

example [Nontrivial A] (a : A) (p : Polynomial ℂ) :
    spectrum ℂ (Polynomial.aeval a p) = (Polynomial.eval · p) '' spectrum ℂ a :=
  spectrum.map_polynomial_aeval a p

end BanachAlgebras

example {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]
    {x y : A} (hxy : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute hxy

example {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {s t : Set E} (hs : Convex ℝ s) (hsc : IsCompact s)
    (ht : Convex ℝ t) (htc : IsClosed t) (hd : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (a b : ℝ), (∀ x ∈ s, f x < a) ∧ a < b ∧ ∀ y ∈ t, b < f y :=
  geometric_hahn_banach_compact_closed hs hsc ht htc hd
