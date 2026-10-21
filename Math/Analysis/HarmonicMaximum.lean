module

public import Math.Analysis.HarmonicPoisson

set_option autoImplicit false
set_option warningAsError true

/-!
the poisson formula gives a boundary maximum principle and stability for banach-valued harmonic maps.
-/

@[expose] public noncomputable section

open InnerProductSpace Metric Real Set

namespace Math.ComplexAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f g : ℂ → F} {c w : ℂ} {R M : ℝ}

/-- the poisson kernel is nonnegative on the boundary for an interior evaluation point. -/
theorem poissonKernel_nonneg_on_sphere {z : ℂ} (hz : z ∈ sphere c R)
    (hw : w ∈ ball c R) : 0 ≤ poissonKernel c w z := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hp : 0 < (R - ‖w - c‖) / (R + ‖w - c‖) :=
    div_pos (sub_pos.mpr (mem_ball_iff_norm.mp hw))
      (add_pos_of_pos_of_nonneg hR (norm_nonneg _))
  have hk : (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
    simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def] using le_re_herglotzRieszKernel hz hw
  exact hp.le.trans hk

/-- the poisson kernel has unit circle average at every interior point. -/
theorem circleAverage_poissonKernel_eq_one (hw : w ∈ ball c R) :
    circleAverage (poissonKernel c w) c R = 1 := by
  have hf : HarmonicContOnCl (fun _ : ℂ => (1 : ℝ)) (ball c R) := harmonicContOnCl_const
  have heq : (poissonKernel c w • fun _ : ℂ => (1 : ℝ)) = poissonKernel c w := by
    ext z
    change poissonKernel c w z * 1 = poissonKernel c w z
    exact mul_one _
  simpa only [heq] using harmonic_poisson_formula hf hw

/-- a boundary norm bound controls a banach-valued harmonic map on the whole closed disc. -/
theorem harmonic_norm_le_boundary_bound (hf : HarmonicContOnCl f (ball c R))
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hw : w ∈ closedBall c R) : ‖f w‖ ≤ M := by
  rcases (mem_closedBall.mp hw).lt_or_eq with hi | he
  · have hw' : w ∈ ball c R := mem_ball.mpr hi
    have hR : 0 < R := pos_of_mem_ball hw'
    have hn : w ∉ sphere c |R| := by
      simpa only [mem_sphere, abs_of_pos hR] using hi.ne
    have hk : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hn)
    have hc : ContinuousOn f (sphere c |R|) :=
      hf.continuousOn_ball.mono (by simpa only [abs_of_pos hR] using
        (sphere_subset_closedBall : sphere c R ⊆ closedBall c R))
    have havg : circleAverage (fun z => poissonKernel c w z * M) c R = M := by
      have heq : (fun z => poissonKernel c w z * M) = M • poissonKernel c w := by
        ext z
        simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [heq, circleAverage_smul, circleAverage_poissonKernel_eq_one hw']
      exact mul_one M
    rw [← harmonic_poisson_formula hf hw', ← havg]
    apply norm_circleAverage_le_circleAverage_norm.trans
    apply circleAverage_mono (hk.smul hc).norm.circleIntegrable'
      (hk.mul continuousOn_const).circleIntegrable'
    intro z hz
    have hs : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
    have hp := poissonKernel_nonneg_on_sphere hs hw'
    change ‖poissonKernel c w z • f z‖ ≤ poissonKernel c w z * M
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hb z hs) hp
  · exact hb w (mem_sphere.mpr he)

/-- boundary perturbations control the distance between two harmonic maps throughout the disc. -/
theorem harmonic_dist_le_boundary_bound (hf : HarmonicContOnCl f (ball c R))
    (hg : HarmonicContOnCl g (ball c R)) (hb : ∀ z ∈ sphere c R, dist (f z) (g z) ≤ M)
    (hw : w ∈ closedBall c R) : dist (f w) (g w) ≤ M := by
  have hb' : ∀ z ∈ sphere c R, ‖(f - g) z‖ ≤ M := by
    simpa only [Pi.sub_apply, dist_eq_norm] using hb
  simpa only [Pi.sub_apply, dist_eq_norm] using harmonic_norm_le_boundary_bound (hf.sub hg) hb' hw

end Math.ComplexAnalysis
