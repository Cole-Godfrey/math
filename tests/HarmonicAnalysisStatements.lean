module

import Math.Analysis.BesselEquation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory FourierTransform Filter
open scoped FourierTransform SchwartzMap Laplacian LineDeriv Real Topology ENNReal Distributions Convolution

noncomputable section

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

example {f : E → F} (hf : Integrable f) (hFf : Integrable (𝓕 f)) {x : E}
    (hx : ContinuousAt f x) : 𝓕⁻ (𝓕 f) x = f x :=
  hf.fourierInv_fourier_eq hFf hx

example {f : E → F} (hc : Continuous f) (hf : Integrable f)
    (hFf : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f :=
  hc.fourierInv_fourier_eq hf hFf

example {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : E) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ = 𝓕 f ξ * 𝓕 g ξ :=
  Real.fourier_mul_convolution_eq hf hg ξ

example (f : 𝓢(E, F)) : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f

example (f : 𝓢(E, F)) : 𝓕 (𝓕⁻ f) = f := FourierTransform.fourier_fourierInv_eq f

example (f : 𝓢(E, F)) : 𝓕 (f : E → F) = (𝓕 f : 𝓢(E, F)) := rfl

example (f : 𝓢(E, F)) :
    𝓕 (f : 𝓢'(E, F)) = (𝓕 f : 𝓢(E, F)) :=
  TemperedDistribution.fourier_toTemperedDistributionCLM_eq f

example (f : 𝓢(E, F)) {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    TemperedDistribution.MemSobolev s p (f : 𝓢'(E, F)) :=
  f.memSobolev

example (f : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) : (Δ f) φ = f (Δ φ) :=
  TemperedDistribution.laplacian_apply_apply f φ

example (f : 𝓢'(E, F)) :
    Δ f = -(2 * π) ^ 2 • TemperedDistribution.fourierMultiplierCLM F
      (fun x : E => Complex.ofReal (‖x‖ ^ 2)) f :=
  TemperedDistribution.laplacian_eq_fourierMultiplierCLM f

end Euclidean

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

example : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) := Lp.fourierTransformₗᵢ E F

example (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ := Lp.norm_fourier_eq f

example (f g : Lp (α := E) F 2) :
    inner ℂ (𝓕 f) (𝓕 g) = inner ℂ f g :=
  Lp.inner_fourier_eq f g

example (f : Lp (α := E) F 2) : 𝓕⁻ (𝓕 f) = f :=
  FourierTransform.fourierInv_fourier_eq f

example (f : Lp (α := E) F 2) :
    𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2) :=
  Lp.fourier_toTemperedDistribution_eq f

example (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 :=
  f.toLp_fourier_eq

example {f : 𝓢'(E, F)} {s : ℝ} (hf : TemperedDistribution.MemSobolev s 2 f) (m : E) :
    TemperedDistribution.MemSobolev (s - 1) 2 (∂_{m} f) :=
  hf.lineDerivOp

example {f : 𝓢'(E, F)} {s : ℝ} (hf : TemperedDistribution.MemSobolev s 2 f) :
    TemperedDistribution.MemSobolev (s - 2) 2 (Δ f) :=
  hf.laplacian

example {f : 𝓢'(E, F)} {s : ℝ} (hf : TemperedDistribution.MemSobolev s 2 f)
    (hs : Module.finrank ℝ E < 2 * s) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 f = (v : 𝓢'(E, F)) :=
  hf.fourier_memL1 hs

end Hilbert

section Circle

variable {T : ℝ} [Fact (0 < T)]

example : HilbertBasis ℤ ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle T _)) := fourierBasis

example (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    HasSum (fun n : ℤ => fourierCoeff f n • fourierLp 2 n) f :=
  hasSum_fourier_series_L2 f

example (f : Lp ℂ 2 (@AddCircle.haarAddCircle T _)) :
    ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 =
      ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle :=
  tsum_sq_fourierCoeff f

end Circle

example (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  f.tsum_eq_tsum_fourier x

example {N : ℕ} [NeZero N] : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ) := ZMod.dft

example {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ZMod.dft (ZMod.dft f) = fun j => (N : ℂ) • f (-j) :=
  ZMod.dft_dft f

example {A : Type*} [AddCommGroup A] [Finite A] :
    A ≃+ AddChar (AddChar A ℂ) ℂ :=
  AddChar.doubleDualEquiv

example (f : ℝ → ℂ) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  Real.zero_at_infty_fourier f

example (b : ℝ) : ∫ x : ℝ, Real.exp (-b * x ^ 2) = Real.sqrt (π / b) :=
  integral_gaussian b

example {b : ℂ} (hb : 0 < b.re) :
    (𝓕 fun x : ℝ => Complex.exp (-π * b * x ^ 2)) =
      fun t : ℝ => 1 / b ^ (1 / 2 : ℂ) * Complex.exp (-π / b * t ^ 2) :=
  fourier_gaussian_pi hb

example {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2)) =
      (1 : ℝ) / a ^ (1 / 2 : ℝ) * ∑' n : ℤ, Real.exp (-π / a * (n : ℝ) ^ 2) :=
  Real.tsum_exp_neg_mul_int_sq ha

example (x : ℝ) : Distribution.dsupport (TemperedDistribution.delta x) = {x} :=
  Distribution.TemperedDistribution.dsupport_delta x

example (Ω : TopologicalSpace.Opens ℝ) (x : ℝ) (φ : 𝓓(Ω, ℝ)) :
    (Distribution.delta (Ω := Ω) (n := ⊤) x) φ = φ x :=
  Distribution.delta_apply x φ

example (Ω : TopologicalSpace.Opens ℝ) (u : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ)) (m : ℝ) :
    (∂_{m} u) φ = u (- ∂_{m} φ) :=
  Distribution.lineDerivOp_apply_apply u φ m

section EllipticEquation

open Math.HarmonicAnalysis TemperedDistribution

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

example (s : ℝ) : 𝓢'(E, F) ≃L[ℂ] 𝓢'(E, F) := besselPotentialEquiv s

example (f : 𝓢'(E, F)) :
    ∃! u : 𝓢'(E, F), u - ((2 * π) ^ 2)⁻¹ • Δ u = f :=
  existsUnique_elliptic_solution f

example (f : 𝓢'(E, F)) :
    ellipticSolution f - ((2 * π) ^ 2)⁻¹ • Δ (ellipticSolution f) = f :=
  ellipticSolution_spec f

example {u f : 𝓢'(E, F)} (hu : u - ((2 * π) ^ 2)⁻¹ • Δ u = f) :
    u = ellipticSolution f :=
  eq_ellipticSolution hu

example (u : 𝓢'(E, F)) : u - ((2 * π) ^ 2)⁻¹ • Δ u = 0 ↔ u = 0 :=
  elliptic_homogeneous_iff u

example : Continuous (ellipticSolution : 𝓢'(E, F) → 𝓢'(E, F)) :=
  continuous_ellipticSolution

example (f : 𝓢'(E, F)) :
    𝓕 (ellipticSolution f) =
      smulLeftCLM F (fun x : E => (((1 + ‖x‖ ^ 2)⁻¹ : ℝ) : ℂ)) (𝓕 f) :=
  fourier_ellipticSolution f

example [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev (s + 2) p (ellipticSolution f) :=
  ellipticSolution_memSobolev hf

example [CompleteSpace F] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : 𝓢'(E, F)) :
    MemSobolev (s + 2) p (ellipticSolution f) ↔ MemSobolev s p f :=
  ellipticSolution_memSobolev_iff f

end EllipticEquation
