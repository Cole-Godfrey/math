module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.Complex.Harmonic.MeanValue

set_option autoImplicit false
set_option warningAsError true

/-!
the poisson formula extends from scalar harmonic functions to real banach targets.
-/

@[expose] public noncomputable section

open InnerProductSpace Metric Real Set

namespace Math.ComplexAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : ℂ → F} {c w : ℂ} {R : ℝ}

/-- the poisson boundary integral recovers a banach-valued harmonic function. -/
theorem harmonic_poisson_formula (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w • f) c R = f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hc : ContinuousOn f (sphere c R) :=
    hf.2.mono (by rw [closure_ball c hR.ne']; exact sphere_subset_closedBall)
  have hn : w ∉ sphere c |R| := by
    simpa only [mem_sphere, abs_of_pos hR] using (mem_ball.mp hw).ne
  have hk : ContinuousOn (poissonKernel c w) (sphere c R) := by
    simpa only [poissonKernel_eq_re_herglotzRieszKernel, abs_of_pos hR] using
      Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hn)
  have hi : CircleIntegrable (poissonKernel c w • f) c R :=
    (by simpa only [abs_of_pos hR] using hk.smul hc :
      ContinuousOn (poissonKernel c w • f) (sphere c |R|)).circleIntegrable'
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro g
  rw [← g.circleAverage_comp_comm hi]
  have heq : (g ∘ (poissonKernel c w • f)) = poissonKernel c w • (g ∘ f) := by
    funext z
    simp [Function.comp_def]
  rw [heq]
  exact (hf.comp_CLM g).circleAverage_poissonKernel_smul hw

/-- harmonicity near the closed disc also gives the poisson representation. -/
theorem harmonicOnNhd_poisson_formula (hf : HarmonicOnNhd f (closedBall c R))
    (hw : w ∈ ball c R) : circleAverage (poissonKernel c w • f) c R = f w :=
  harmonic_poisson_formula
    ⟨hf.mono ball_subset_closedBall, hf.continuousOn.mono closure_ball_subset_closedBall⟩ hw

/-- equal boundary values determine a banach-valued harmonic map on the closed disc. -/
theorem harmonic_eqOn_closedBall_of_eqOn_sphere {g : ℂ → F}
    (hf : HarmonicContOnCl f (ball c R)) (hg : HarmonicContOnCl g (ball c R))
    (hfg : EqOn f g (sphere c R)) : EqOn f g (closedBall c R) := by
  intro z hz
  rcases (mem_closedBall.mp hz).lt_or_eq with hinside | hboundary
  · have hmem : z ∈ ball c R := mem_ball.mpr hinside
    have hR : 0 < R := pos_of_mem_ball hmem
    rw [← harmonic_poisson_formula hf hmem, ← harmonic_poisson_formula hg hmem]
    apply circleAverage_congr_sphere
    intro w hw
    have hs : w ∈ sphere c R := by simpa only [abs_of_pos hR] using hw
    exact congrArg (fun v : F => poissonKernel c z w • v) (hfg hs)
  · exact hfg (mem_sphere.mpr hboundary)

end Math.ComplexAnalysis
