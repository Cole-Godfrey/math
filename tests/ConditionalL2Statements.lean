module

import Math.Probability.ConditionalL2

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

variable {α E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {m m' m0 : MeasurableSpace α} {μ : Measure α}

example (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm f : α → E) μ :=
  Math.Probability.aestronglyMeasurable_l2Predictor hm f

example (hm : m ≤ m0) (f : α →₂[μ] E) :
    (condExpL2 E 𝕜 hm f : α →₂[μ] E) = f ↔ AEStronglyMeasurable[m] f μ :=
  Math.Probability.l2Predictor_eq_self_iff hm f

example (hm : m ≤ m0) (f : α →₂[μ] E) :
    (condExpL2 E 𝕜 hm (condExpL2 E 𝕜 hm f : α →₂[μ] E) : α →₂[μ] E) =
      (condExpL2 E 𝕜 hm f : α →₂[μ] E) :=
  Math.Probability.l2Predictor_idempotent hm f

example (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AEStronglyMeasurable[m] g μ) :
    inner 𝕜 (f - (condExpL2 E 𝕜 hm f : α →₂[μ] E)) g = 0 :=
  Math.Probability.inner_residual_l2Predictor_eq_zero hm f g hg

example (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - g‖ ^ 2 = ‖f - (condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ^ 2 +
      ‖(condExpL2 E 𝕜 hm f : α →₂[μ] E) - g‖ ^ 2 :=
  Math.Probability.l2_prediction_error_sq hm f g hg

example (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖f‖ ^ 2 = ‖(condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ^ 2 +
      ‖f - (condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ^ 2 :=
  Math.Probability.l2_norm_sq_decomposition hm f

example (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - (condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f - g‖ :=
  Math.Probability.l2_prediction_error_minimal hm f g hg

example (hm : m ≤ m0) (f g : α →₂[μ] E) (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - g‖ = ‖f - (condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ↔
      g = (condExpL2 E 𝕜 hm f : α →₂[μ] E) :=
  Math.Probability.l2_prediction_error_eq_iff hm f g hg

example (hm : m ≤ m0) (f g : α →₂[μ] E) :
    dist (condExpL2 E 𝕜 hm f : α →₂[μ] E) (condExpL2 E 𝕜 hm g : α →₂[μ] E) ≤ dist f g :=
  Math.Probability.dist_l2Predictor_le hm f g

example (hmm' : m ≤ m') (hm' : m' ≤ m0) (f : α →₂[μ] E) :
    (condExpL2 E 𝕜 hm' (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E) : α →₂[μ] E) =
      (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E) :=
  Math.Probability.l2Predictor_larger_fixes_smaller hmm' hm' f

example (hmm' : m ≤ m') (hm' : m' ≤ m0) (f : α →₂[μ] E) :
    (condExpL2 E 𝕜 (hmm'.trans hm') (condExpL2 E 𝕜 hm' f : α →₂[μ] E) : α →₂[μ] E) =
      (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E) :=
  Math.Probability.l2Predictor_tower hmm' hm' f

example (hmm' : m ≤ m') (hm' : m' ≤ m0) (f : α →₂[μ] E) :
    ‖f - (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E)‖ ^ 2 =
      ‖f - (condExpL2 E 𝕜 hm' f : α →₂[μ] E)‖ ^ 2 +
        ‖(condExpL2 E 𝕜 hm' f : α →₂[μ] E) - (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E)‖ ^ 2 :=
  Math.Probability.l2_prediction_information_gap hmm' hm' f

example (hmm' : m ≤ m') (hm' : m' ≤ m0) (f : α →₂[μ] E) :
    ‖f - (condExpL2 E 𝕜 hm' f : α →₂[μ] E)‖ ≤
      ‖f - (condExpL2 E 𝕜 (hmm'.trans hm') f : α →₂[μ] E)‖ :=
  Math.Probability.l2_prediction_error_antitone hmm' hm' f
