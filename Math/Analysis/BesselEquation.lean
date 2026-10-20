module

public import Mathlib.Analysis.Distribution.Sobolev

set_option autoImplicit false
set_option warningAsError true

/-!
bessel potentials solve a normalized elliptic equation on tempered distributions.
the inverse gains two sobolev orders for every exponent at least one.
-/

@[expose] public noncomputable section

open FourierTransform MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian Real ENNReal

namespace Math.HarmonicAnalysis

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- bessel potentials give continuous linear equivalences at every real order. -/
def besselPotentialEquiv (s : ℝ) : 𝓢'(E, F) ≃L[ℂ] 𝓢'(E, F) :=
  ContinuousLinearEquiv.equivOfInverse (besselPotential E F s) (besselPotential E F (-s))
    (fun u => by simp) (fun u => by simp)

@[simp]
theorem besselPotentialEquiv_apply (s : ℝ) (u : 𝓢'(E, F)) :
    besselPotentialEquiv s u = besselPotential E F s u := rfl

@[simp]
theorem besselPotentialEquiv_symm_apply (s : ℝ) (u : 𝓢'(E, F)) :
    (besselPotentialEquiv s).symm u = besselPotential E F (-s) u := rfl

/-- adding multiplier symbols adds the corresponding distribution operators. -/
theorem fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g + h) u =
      fourierMultiplierCLM F g u + fourierMultiplierCLM F h u := by
  ext φ
  simp only [fourierMultiplierCLM_apply_apply, SchwartzMap.smulLeftCLM_add hg hh,
    add_apply, FourierTransform.fourier_add, map_add]

/-- the second bessel potential is identity minus the normalized laplacian. -/
theorem besselPotential_two_eq (u : 𝓢'(E, F)) :
    besselPotential E F 2 u = u - ((2 * π) ^ 2)⁻¹ • Δ u := by
  have hs : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    simp
  rw [besselPotential, hs, fourierMultiplier_add (by fun_prop) (by fun_prop),
    fourierMultiplierCLM_const, smul_apply,
    ContinuousLinearMap.id_apply, one_smul, laplacian_eq_fourierMultiplierCLM, smul_smul]
  have hc : ((2 * π) ^ 2)⁻¹ * (-(2 * π) ^ 2) = (-1 : ℝ) := by
    field_simp
  rw [hc, neg_one_smul, sub_neg_eq_add]

/-- the inverse second bessel potential is the elliptic solution operator. -/
def ellipticSolution : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  besselPotential E F (-2)

/-- the solution satisfies the normalized elliptic equation. -/
theorem ellipticSolution_spec (f : 𝓢'(E, F)) :
    ellipticSolution f - ((2 * π) ^ 2)⁻¹ • Δ (ellipticSolution f) = f := by
  rw [← besselPotential_two_eq]
  simp [ellipticSolution]

/-- any tempered solution agrees with the specified solution. -/
theorem eq_ellipticSolution {u f : 𝓢'(E, F)}
    (hu : u - ((2 * π) ^ 2)⁻¹ • Δ u = f) : u = ellipticSolution f := by
  have hb : besselPotential E F 2 u = f := by
    rw [besselPotential_two_eq, hu]
  calc
    u = besselPotential E F (-2) (besselPotential E F 2 u) := by simp
    _ = ellipticSolution f := by rw [hb]; rfl

/-- every tempered load has exactly one tempered solution. -/
theorem existsUnique_elliptic_solution (f : 𝓢'(E, F)) :
    ∃! u : 𝓢'(E, F), u - ((2 * π) ^ 2)⁻¹ • Δ u = f :=
  ⟨ellipticSolution f, ellipticSolution_spec f, fun _ hu => eq_ellipticSolution hu⟩

@[simp]
theorem ellipticSolution_zero : ellipticSolution (0 : 𝓢'(E, F)) = 0 :=
  map_zero ellipticSolution

theorem ellipticSolution_add (f g : 𝓢'(E, F)) :
    ellipticSolution (f + g) = ellipticSolution f + ellipticSolution g :=
  map_add ellipticSolution f g

theorem ellipticSolution_smul (c : ℂ) (f : 𝓢'(E, F)) :
    ellipticSolution (c • f) = c • ellipticSolution f :=
  map_smul ellipticSolution c f

theorem continuous_ellipticSolution :
    Continuous (ellipticSolution : 𝓢'(E, F) → 𝓢'(E, F)) :=
  ellipticSolution.continuous

/-- the solution has the reciprocal quadratic symbol in fourier space. -/
theorem fourier_ellipticSolution (f : 𝓢'(E, F)) :
    𝓕 (ellipticSolution f) =
      smulLeftCLM F (fun x : E => (((1 + ‖x‖ ^ 2)⁻¹ : ℝ) : ℂ)) (𝓕 f) := by
  simp [ellipticSolution, besselPotential, fourierMultiplierCLM_apply, Real.rpow_neg_one]

/-- the normalized homogeneous equation has only the zero tempered solution. -/
theorem elliptic_homogeneous_iff (u : 𝓢'(E, F)) :
    u - ((2 * π) ^ 2)⁻¹ • Δ u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    simpa using eq_ellipticSolution hu
  · rintro rfl
    rw [laplacian_eq_fourierMultiplierCLM]
    simp

variable [CompleteSpace F]

/-- solving the equation gains exactly two sobolev orders. -/
theorem ellipticSolution_memSobolev_iff {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : 𝓢'(E, F)) :
    MemSobolev (s + 2) p (ellipticSolution f) ↔ MemSobolev s p f := by
  change MemSobolev (s + 2) p (besselPotential E F (-2) f) ↔ _
  rw [memSobolev_besselPotential_iff]
  have horder : -2 + (s + 2) = s := by ring
  rw [horder]

/-- sobolev loads give solutions with two additional orders of regularity. -/
theorem ellipticSolution_memSobolev {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : 𝓢'(E, F)} (hf : MemSobolev s p f) :
    MemSobolev (s + 2) p (ellipticSolution f) :=
  (ellipticSolution_memSobolev_iff f).2 hf

end Math.HarmonicAnalysis
