module

import Math.Analysis.HarmonicMaximum

set_option autoImplicit false
set_option warningAsError true

open InnerProductSpace Metric Real Set
open Math.ComplexAnalysis

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f g : ℂ → F} {c z w : ℂ} {R M : ℝ}

example (hz : z ∈ sphere c R) (hw : w ∈ ball c R) : 0 ≤ poissonKernel c w z :=
  poissonKernel_nonneg_on_sphere hz hw

example (hw : w ∈ ball c R) : circleAverage (poissonKernel c w) c R = 1 :=
  circleAverage_poissonKernel_eq_one hw

example (hf : HarmonicContOnCl f (ball c R)) (hb : ∀ v ∈ sphere c R, ‖f v‖ ≤ M)
    (hw : w ∈ closedBall c R) : ‖f w‖ ≤ M :=
  harmonic_norm_le_boundary_bound hf hb hw

example (hf : HarmonicContOnCl f (ball c R)) (hg : HarmonicContOnCl g (ball c R))
    (hb : ∀ v ∈ sphere c R, dist (f v) (g v) ≤ M) (hw : w ∈ closedBall c R) :
    dist (f w) (g w) ≤ M :=
  harmonic_dist_le_boundary_bound hf hg hb hw

example (hf : HarmonicContOnCl f (ball c 0)) (hg : HarmonicContOnCl g (ball c 0))
    (hb : ∀ v ∈ sphere c 0, dist (f v) (g v) ≤ M) : dist (f c) (g c) ≤ M :=
  harmonic_dist_le_boundary_bound hf hg hb (by simp)
