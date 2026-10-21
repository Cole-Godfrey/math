module

import Math.Analysis.EntireAffine
import Math.Analysis.HarmonicPoisson
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Harmonic.Liouville
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Meromorphic.Complex

set_option autoImplicit false
set_option warningAsError true

open Complex Metric Set Filter Bornology Asymptotics MeasureTheory MeromorphicOn
open Real Complex.HadamardThreeLines
open scoped Topology Real UpperHalfPlane

noncomputable section

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

example {f : E → F} {R : ℝ} {z : E} (hf : DifferentiableOn ℂ f (ball 0 R))
    (hm : MapsTo f (ball 0 R) (closedBall 0 R)) (h0 : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ :=
  Complex.norm_le_norm_of_mapsTo_ball hf hm h0 hz

example {f : ℂ → F} {c : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hm : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) :
    ‖deriv f c‖ ≤ 1 :=
  Complex.norm_deriv_le_one_of_mapsTo_ball hf hm hR

example {f : ℂ → F} {c : ℂ} {R S : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hm : MapsTo f (ball c R) (closedBall (f c) S)) (hR : 0 < R) :
    ‖deriv f c‖ ≤ S / R :=
  Complex.norm_deriv_le_div_of_mapsTo_ball hf hm hR

example [Nontrivial E] {f : E → F} {U : Set E} {C : ℝ} {z : E}
    (hU : IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hC : ∀ w ∈ frontier U, ‖f w‖ ≤ C) (hz : z ∈ closure U) : ‖f z‖ ≤ C :=
  Complex.norm_le_of_forall_mem_frontier_norm_le hU hf hC hz

example [Nontrivial E] {f g : E → F} {U : Set E} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U)
    (hfg : EqOn f g (frontier U)) : EqOn f g (closure U) :=
  Complex.eqOn_closure_of_eqOn_frontier hU hf hg hfg

end Normed

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f g : ℂ → F} {c z w : ℂ} {R C : ℝ}

example (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 ≤ R) :
    (∮ z in C(c, R), f z) = 0 :=
  hf.circleIntegral_eq_zero hR

example (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  hf.circleIntegral_sub_inv_smul hw

example (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) = f w :=
  hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

example (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w • f) c R = f w :=
  hf.circleAverage_poissonKernel_smul hw

example (hf : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w :=
  hf.circleIntegral_sub_inv_smul hw

example (n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n :=
  Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hC

example (hf : Differentiable ℂ f) : Differentiable ℂ (deriv f) := hf.deriv

example (hf : Differentiable ℂ f) : AnalyticOnNhd ℂ f univ :=
  hf.differentiableOn.analyticOnNhd isOpen_univ

example (hf : DifferentiableOn ℂ f (ball c R)) (hz : z ∈ ball c R) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  Complex.hasSum_taylorSeries_on_ball hf hz

example (hf : Differentiable ℂ f) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z) :=
  Complex.hasSum_taylorSeries_of_entire hf c z

example (hf : AnalyticAt ℂ f c) :
    (∀ᶠ z in 𝓝 c, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 :=
  hf.eventually_eq_zero_or_eventually_ne_zero

example (hf : AnalyticAt ℂ f c) (hg : AnalyticAt ℂ g c) :
    (∃ᶠ z in 𝓝[≠] c, f z = g z) ↔ ∀ᶠ z in 𝓝 c, f z = g z :=
  hf.frequently_eq_iff_eventually_eq hg

example {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) (hc : c ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] c, f z = g z) : EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU hc hfg

example (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hfg : ∃ᶠ z in 𝓝[≠] c, f z = g z) : f = g :=
  hf.eq_of_frequently_eq hg hfg

example (hf : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) :
    AnalyticAt ℂ f c :=
  Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hf hc

example (hf : Differentiable ℂ f) (hb : IsBounded (range f)) : ∃ a, ∀ z, f z = a :=
  hf.exists_const_forall_eq_of_bounded hb

example {l u a b : ℝ} (hlu : l < u) (hz : z ∈ verticalClosedStrip l u)
    (hf : DiffContOnCl ℂ f (verticalStrip l u))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip l u))
    (ha : ∀ w ∈ Complex.re ⁻¹' {l}, ‖f w‖ ≤ a)
    (hb : ∀ w ∈ Complex.re ⁻¹' {u}, ‖f w‖ ≤ b) :
    ‖f z‖ ≤ a ^ (1 - (z.re - l) / (u - l)) * b ^ ((z.re - l) / (u - l)) :=
  Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hlu hz hf hB ha hb

open Math.ComplexAnalysis

example (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f))) :
    ∀ z : ℂ, f z = z • deriv f 0 + f 0 :=
  eq_smul_deriv_add_of_bounded_deriv hf hb

example (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f))) :
    ∃! coefficients : F × F, ∀ z : ℂ, f z = z • coefficients.1 + coefficients.2 :=
  existsUnique_affine_of_bounded_deriv hf hb

example (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f))) :
    dist (f z) (f w) = dist z w * ‖deriv f 0‖ :=
  dist_eq_of_bounded_deriv hf hb z w

example (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f))) :
    LipschitzWith ‖deriv f 0‖₊ f :=
  lipschitzWith_of_bounded_deriv hf hb

example (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f))) :
    IsBounded (range f) ↔ deriv f 0 = 0 :=
  isBounded_range_iff_deriv_eq_zero hf hb

end Banach

example {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    (∃ a, ∀ z, f z = a) ∨ IsOpenMap f :=
  hf.is_constant_or_isOpenMap

example {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f)))
    (hne : deriv f 0 ≠ 0) : Function.Bijective f :=
  Math.ComplexAnalysis.bijective_of_bounded_deriv hf hb hne

example {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hb : IsBounded (range (deriv f)))
    (hne : deriv f 0 ≠ 0) : ∃! z : ℂ, f z = 0 :=
  Math.ComplexAnalysis.existsUnique_zero_of_bounded_deriv hf hb hne

section Harmonic

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℂ → F} {c w : ℂ} {R : ℝ}

example (hf : HarmonicOnNhd f (closedBall c |R|)) : circleAverage f c R = f c :=
  hf.circleAverage_eq

example (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w • f) c R = f w :=
  Math.ComplexAnalysis.harmonicOnNhd_poisson_formula hf hw

example (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w • f) c R = f w :=
  Math.ComplexAnalysis.harmonic_poisson_formula hf hw

example {g : ℂ → F} (hf : HarmonicContOnCl f (ball c R))
    (hg : HarmonicContOnCl g (ball c R)) (hfg : EqOn f g (sphere c R)) :
    EqOn f g (closedBall c R) :=
  Math.ComplexAnalysis.harmonic_eqOn_closedBall_of_eqOn_sphere hf hg hfg

example (hf : HarmonicOnNhd f univ) (hb : IsBounded (range f)) : ∀ z w : ℂ, f z = f w :=
  InnerProductSpace.bounded_harmonic_on_complex_plane_is_constant f hf hb

example {f : ℂ → ℝ} (hf : HarmonicOnNhd f univ) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g univ ∧ (fun z => (g z).re) = f :=
  hf.exists_analyticOnNhd_univ_re_eq

end Harmonic

section Meromorphic

variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}

example (hR : R ≠ 0) (hf : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (fun z => Real.log ‖f z‖) c R =
      ∑ᶠ z, divisor f (closedBall c |R|) z * Real.log (R * ‖c - z‖⁻¹) +
      divisor f (closedBall c |R|) c * Real.log R + Real.log ‖meromorphicTrailingCoeffAt f c‖ :=
  hf.circleAverage_log_norm hR

example (hR : R ≠ 0) (hf : AnalyticOnNhd ℂ f (closedBall c |R|)) (h0 : f c ≠ 0) :
    circleAverage (fun z => Real.log ‖f z‖) c R =
      ∑ᶠ z, divisor f (closedBall c |R|) z * Real.log (R * ‖c - z‖⁻¹) + Real.log ‖f c‖ :=
  hf.circleAverage_log_norm hR h0

example : Meromorphic Complex.Gamma := Meromorphic.Gamma

open ValueDistribution

example (hf : Meromorphic f) (hR : R ≠ 0) :
    characteristic f ⊤ R - characteristic f⁻¹ ⊤ R = Real.log ‖meromorphicTrailingCoeffAt f 0‖ :=
  ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero hf hR

example (hf : Meromorphic f) :
    |characteristic f ⊤ R - characteristic f⁻¹ ⊤ R| ≤
      max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
  ValueDistribution.characteristic_sub_characteristic_inv_le hf

example (hf : Meromorphic f) :
    (characteristic f ⊤ - characteristic f⁻¹ ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  ValueDistribution.isBigO_characteristic_sub_characteristic_inv hf

example (hf : Meromorphic f) (a : ℂ) :
    |characteristic f ⊤ R - characteristic (fun z => f z - a) ⊤ R| ≤
      Real.posLog ‖a‖ + Real.log 2 :=
  ValueDistribution.abs_characteristic_sub_characteristic_shift_le hf

end Meromorphic

example (z w : ℍ) : dist (Real.log z.im) (Real.log w.im) ≤ dist z w :=
  UpperHalfPlane.dist_log_im_le z w

example (a : ℝ) :
    Isometry (fun y : ℝ => UpperHalfPlane.mk ⟨a, Real.exp y⟩ (Real.exp_pos y)) :=
  UpperHalfPlane.isometry_vertical_line a

example (p : Polynomial ℂ) (hp : 0 < p.degree) :
    p.derivative.rootSet ℂ ⊆ convexHull ℝ (p.rootSet ℂ) :=
  Polynomial.rootSet_derivative_subset_convexHull_rootSet hp
