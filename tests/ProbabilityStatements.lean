import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ProbabilityTheory ENNReal NNReal

noncomputable section

section ConditionalExpectation

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

example {m : MeasurableSpace Ω} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ} (hf : Integrable f μ) {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫ x in s, (μ[f | m]) x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_condExp hm hf hs

example {m₁ m₂ : MeasurableSpace Ω} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    [SigmaFinite (μ.trim hm₂)] (f : Ω → ℝ) :
    μ[μ[f | m₂] | m₁] =ᵐ[μ] μ[f | m₁] :=
  condExp_condExp_of_le hm₁₂ hm₂

end ConditionalExpectation

section Events

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {s : ℕ → Set Ω}

example (hs : (∑' n, μ (s n)) ≠ ∞) : μ (limsup s atTop) = 0 :=
  measure_limsup_atTop_eq_zero hs

example (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ)
    (hsum : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1 :=
  measure_limsup_eq_one hsm hs hsum

example {m : ℕ → MeasurableSpace Ω} (hle : ∀ n, m n ≤ m₀) (hindep : iIndep m μ)
    {s : Set Ω} (hs : MeasurableSet[limsup m atTop] s) : μ s = 0 ∨ μ s = 1 :=
  measure_zero_or_one_of_measurableSet_limsup_atTop hle hindep hs

end Events

section StrongLaw

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

example (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (𝓝 μ[X 0]) :=
  strong_law_ae X hint hindep hident

example {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ∞) (X : ℕ → Ω → E)
    (hX : MemLp (X 0) p μ) (hindep : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) - μ[X 0]) p μ)
      atTop (𝓝 0) :=
  strong_law_Lp hp hpfin X hX hindep hident

end StrongLaw

section CentralLimit

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

example (hY : HasLaw Y (gaussianReal 0 1) P') (hmean : P[X 0] = 0)
    (hsecond : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun n : ℕ => fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      atTop Y (fun _ => P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum hY hmean hsecond hindep hident

example (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun n : ℕ => fun ω => (Real.sqrt n)⁻¹ *
        ((∑ k ∈ Finset.range n, X k ω) - n * P[X 0]))
      atTop Y (fun _ => P) P' :=
  tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

example (a : ℝ) (v : ℝ≥0) : ∫ x, x ∂gaussianReal a v = a :=
  integral_id_gaussianReal

example (a : ℝ) (v : ℝ≥0) : Var[id; gaussianReal a v] = (v : ℝ) :=
  variance_id_gaussianReal

end CentralLimit

section Martingales

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m₀} {f : ℕ → Ω → ℝ}

example [SigmaFiniteFiltration μ ℱ] (hf : Submartingale f ℱ μ)
    {τ π : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (hπ : IsStoppingTime ℱ π)
    (hle : τ ≤ π) {N : ℕ} (hbounded : ∀ ω, π ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  hf.expected_stoppedValue_mono hτ hπ hle hbounded

example [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ)
    {τ σ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hle : σ ≤ τ) {N : ℕ} (hbounded : ∀ ω, τ ω ≤ N)
    [SigmaFinite (μ.trim hσ.measurableSpace_le)] :
    stoppedValue f σ =ᵐ[μ] μ[stoppedValue f τ | hσ.measurableSpace] :=
  hf.stoppedValue_ae_eq_condExp_of_le hτ hσ hle hbounded

example [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) {R : ℝ≥0}
    (hbounded : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  hf.ae_tendsto_limitProcess hbounded

example [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) :=
  hf.tendsto_eLpNorm_one_limitProcess hunif

example [IsFiniteMeasure μ] (hf : Martingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) (n : ℕ) :
    f n =ᵐ[μ] μ[ℱ.limitProcess f μ | ℱ n] :=
  hf.ae_eq_condExp_limitProcess hunif n

end Martingales
