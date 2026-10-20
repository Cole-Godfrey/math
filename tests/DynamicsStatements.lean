module

import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Dynamics.Flow
import Mathlib.Dynamics.Newton
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.EmpiricalMeasure
import Mathlib.Dynamics.Ergodic.Extreme
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Dynamics.TopologicalEntropy.Semiconj

set_option autoImplicit false
set_option warningAsError true

open Set Filter Function MeasureTheory
open scoped Topology NNReal ENNReal Uniformity

noncomputable section

section DifferentialEquations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example [CompleteSpace E] {v : ℝ → E → E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hv : IsPicardLindelof v t₀ x₀ a r L K) (hx : x ∈ Metric.closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (v t (α t)) (Icc tmin tmax) t :=
  hv.exists_eq_forall_mem_Icc_hasDerivWithinAt hx

example [CompleteSpace E] {v : ℝ → E → E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hv : IsPicardLindelof v t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E, (∀ x ∈ Metric.closedBall x₀ r, α (x, t₀) = x ∧
      ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun t => α (x, t)) (v t (α (x, t))) (Icc tmin tmax) t) ∧
      ContinuousOn α (Metric.closedBall x₀ r ×ˢ Icc tmin tmax) :=
  hv.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn

example [CompleteSpace E] {v : E → E} {x₀ : E}
    (hv : ContDiffAt ℝ 1 v x₀) (t₀ : ℝ) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (v (α t)) t :=
  hv.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

example {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f g : ℝ → E} {t₀ : ℝ}
    (hv : ∀ t, LipschitzOnWith K (v t) (s t))
    (hf : ∀ t, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ t, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (h₀ : f t₀ = g t₀) : f = g :=
  ODE_solution_unique_univ hv hf hg h₀

example {f f' : ℝ → E} {δ K ε a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (h₀ : ‖f a‖ ≤ δ) (hbound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  norm_le_gronwallBound_of_norm_deriv_right_le hf hf' h₀ hbound

example {u b c : ℕ → ℝ} {n₀ n : ℕ} (h₀ : 0 ≤ u n₀)
    (hu : ∀ k ≥ n₀, u (k + 1) ≤ (1 + c k) * u k + b k)
    (hc : ∀ k ≥ n₀, 0 ≤ c k) (hb : ∀ k ≥ n₀, 0 ≤ b k) (hn : n₀ ≤ n) :
    u n ≤ (u n₀ + ∑ k ∈ Finset.Ico n₀ n, b k) *
      Real.exp (∑ k ∈ Finset.Ico n₀ n, c k) :=
  discrete_gronwall h₀ hu hc hb hn

end DifferentialEquations

section ErgodicTheory

variable {X : Type*} [MeasurableSpace X] {f : X → X} {μ : Measure X}

example [IsFiniteMeasure μ] (hf : MeasurePreserving f μ μ) : Conservative f μ :=
  hf.conservative

example (hf : Conservative f μ) {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s :=
  hf.ae_mem_imp_frequently_image_mem hs

example [IsProbabilityMeasure μ] (hf : PreErgodic f μ) {s : Set X}
    (hs : NullMeasurableSet s μ) (hinv : f ⁻¹' s =ᵐ[μ] s) : μ s = 0 ∨ μ s = 1 :=
  hf.prob_eq_zero_or_one hs hinv

example [TopologicalSpace X] [BorelSpace X] [T2Space X]
    [CompactSpace X] [Nonempty X] (hf : Continuous f) :
    ∃ μ : Measure X, MeasurePreserving f μ μ ∧ Measure.Regular μ ∧ IsProbabilityMeasure μ :=
  exists_measurePreserving_probabilityMeasure hf

example [IsProbabilityMeasure μ] :
    Ergodic f μ ↔
      μ ∈ extremePoints ℝ≥0∞ {ν : Measure X | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  Ergodic.iff_mem_extremePoints

example {p : ℝ} [Fact (0 < p)] {a : AddCircle p} :
    Ergodic (a + ·) ↔ addOrderOf a = 0 :=
  AddCircle.ergodic_add_left

example {p : ℝ} [Fact (0 < p)] {n : ℕ} (hn : 1 < n) :
    Ergodic (fun x : AddCircle p => n • x) :=
  AddCircle.ergodic_nsmul hn

end ErgodicTheory

section TopologicalDynamics

example {τ X : Type*} [AddMonoid τ] [TopologicalSpace τ] [TopologicalSpace X]
    (ϕ : Flow τ X) (s t : τ) (x : X) : ϕ (s + t) x = ϕ s (ϕ t x) :=
  ϕ.map_add s t x

example {X : Type*} {f : X → X} {x : X} {m n : ℕ}
    (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) : IsPeriodicPt f (m + n) x :=
  hm.add hn

example {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    {S : X → X} {T : Y → Y} {φ : X → Y}
    (hφ : Semiconj φ S T) (hu : UniformContinuous φ) (F : Set X) :
    Dynamics.coverEntropy T (φ '' F) ≤ Dynamics.coverEntropy S F :=
  Dynamics.coverEntropy_image_le_of_uniformContinuous hφ hu F

example {X : Type*} [UniformSpace X] {T : X → X} {F : Set X} (hF : MapsTo T F F) :
    Dynamics.coverEntropy (hF.restrict T F F) univ = Dynamics.coverEntropy T F :=
  Dynamics.coverEntropy_restrict hF

example {X : Type*} [UniformSpace X] (T : X → X) (F : Set X) :
    Dynamics.coverEntropy T F = ⨆ U ∈ 𝓤 X, Dynamics.netEntropyEntourage T F U :=
  Dynamics.coverEntropy_eq_iSup_netEntropyEntourage T F

example {f : CircleDeg1Lift} (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f.translationNumber = (m : ℝ) / n ↔ ∃ x : ℝ, (f ^ n) x = x + m :=
  f.translationNumber_eq_rat_iff hf hn

end TopologicalDynamics

example {A G : Type*} [TopologicalSpace A] [Inhabited A] [DiscreteTopology A]
    [Monoid G] [IsLeftCancelMul G]
    (F : Set (SymbolicDynamics.FullShift.Pattern A G)) :
    IsClosed (SymbolicDynamics.FullShift.mulForbidden F) :=
  SymbolicDynamics.FullShift.isClosed_mulForbidden F

example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Polynomial R) {x : S} (hx : IsNilpotent (Polynomial.aeval x P))
    (hd : IsUnit (Polynomial.aeval x P.derivative)) :
    ∃! r : S, IsNilpotent (x - r) ∧ Polynomial.aeval r P = 0 :=
  Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hx hd
