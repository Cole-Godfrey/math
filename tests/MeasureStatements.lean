module

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
set_option warningAsError true

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology MeasureTheory CompactlySupported

noncomputable section

section Integration

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β}

example {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hm : Monotone f) :
    ∫⁻ x, ⨆ n, f n x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ :=
  lintegral_iSup hf hm

example {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ x, liminf (fun n => f n x) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop :=
  lintegral_liminf_le' hf

example {F : ℕ → α → E} {f : α → E} (b : α → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (F n) μ) (hb : Integrable b μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence b hm hb hbound hlim

example [SFinite ν] (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  lintegral_prod f hf

example [SFinite μ] [SFinite ν] (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf

example [SFinite μ] [SFinite ν] {f : α → β → E}
    (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  integral_integral_swap hf

example {f g : α → E} (h : f =ᵐ[μ] g) : ∫ x, f x ∂μ = ∫ x, g x ∂μ :=
  integral_congr_ae h

example {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  lintegral_eq_zero_iff' hf

example {f : α → E} : ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
  norm_integral_le_integral_norm f

example {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → α → E} {f : α → E} (b : α → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ b x) (hbi : Integrable b μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence b hm hb hbi hlim

end Integration

section Decomposition

variable {α : Type*} [MeasurableSpace α] {μ ν ξ : Measure α}

example [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    ν.withDensity (μ.rnDeriv ν) = μ :=
  Measure.withDensity_rnDeriv_eq μ ν h

example [SigmaFinite μ] [SigmaFinite ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  Measure.haveLebesgueDecomposition_add μ ν

example : μ.singularPart ν ⟂ₘ ν := Measure.mutuallySingular_singularPart μ ν

example : Measurable (μ.rnDeriv ν) := Measure.measurable_rnDeriv μ ν

example [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ :=
  lintegral_rnDeriv_mul h hf

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) {f : α → E} :
    ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ :=
  integral_rnDeriv_smul h

end Decomposition

section ConditionalExpectation

variable {α : Type*} {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α}

example {f : α → ℝ} (hm : m₁ ≤ m₀) [SigmaFinite (μ.trim hm)] :
    ∫ x, μ[f | m₁] x ∂μ = ∫ x, f x ∂μ :=
  integral_condExp hm

example {f : α → ℝ} (hm : m₁ ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet[m₁] s) :
    ∫ x in s, μ[f | m₁] x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_condExp hm hf hs

example {f : α → ℝ} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim h₂)] :
    μ[μ[f | m₂] | m₁] =ᵐ[μ] μ[f | m₁] :=
  condExp_condExp_of_le h₁₂ h₂

example {f g : α → ℝ} (hm : m₁ ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf : AEStronglyMeasurable[m₁] f μ) (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    μ[f * g | m₁] =ᵐ[μ] f * μ[g | m₁] :=
  condExp_mul_of_aestronglyMeasurable_left hf hfg hg

end ConditionalExpectation

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {f f' : ℝ → E}

example (hd : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

example {u v u' v' : ℝ → ℝ} (hu : ContinuousOn u (uIcc a b)) (hv : ContinuousOn v (uIcc a b))
    (hdu : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hdv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hiu : IntervalIntegrable u' volume a b) (hiv : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hu hv hdu hdv hiu hiv

example (F G : ℝ × ℝ → E) (F' G' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E)
    (a b : ℝ × ℝ) (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hdF : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt F (F' x) x)
    (hdG : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2, HasFDerivAt G (G' x) x)
    (hi : IntegrableOn (fun x => F' x (1, 0) + G' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, F' x (1, 0) + G' x (0, 1)) =
      (((∫ x in a.1..b.1, G (x, b.2)) - ∫ x in a.1..b.1, G (x, a.2)) +
        ∫ y in a.2..b.2, F (b.1, y)) - ∫ y in a.2..b.2, F (a.1, y) :=
  integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G F' G' a b hab hF hG hdF hdG hi

end Calculus

example {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) (f : C_c(X, ℝ)) :
    ∫ x, f x ∂(RealRMK.rieszMeasure Λ) = Λ f :=
  RealRMK.integral_rieszMeasure Λ f

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (K : PositiveCompacts G) :
    μ = μ K • Measure.haarMeasure K :=
  Measure.haarMeasure_unique μ K
