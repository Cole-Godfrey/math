module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

set_option autoImplicit false
set_option warningAsError true

/-!
conditional expectation is the unique least-squares predictor among measurable l2 functions.
orthogonality gives exact error decompositions and stability.
-/

@[expose] public noncomputable section

open MeasureTheory Submodule
open scoped ENNReal

namespace Math.Probability

variable {α E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {m m' m0 : MeasurableSpace α} {μ : Measure α}

/-- the conditional l2 projection viewed as an operator on the ambient l2 space. -/
def l2Predictor (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] (α →₂[μ] E) :=
  (lpMeas E 𝕜 m 2 μ).subtypeL.comp (condExpL2 E 𝕜 hm)

private theorem predictor_eq_projection (hm : m ≤ m0) [Fact (m ≤ m0)] :
    l2Predictor (E := E) (𝕜 := 𝕜) (μ := μ) hm = (lpMeas E 𝕜 m 2 μ).starProjection := rfl

/-- the predictor is almost everywhere measurable for the conditioning sigma-algebra. -/
theorem aestronglyMeasurable_l2Predictor (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable[m] (l2Predictor (𝕜 := 𝕜) hm f) μ :=
  aestronglyMeasurable_condExpL2 hm f

/-- the predictor fixes exactly the functions measurable for the conditioning sigma-algebra. -/
theorem l2Predictor_eq_self_iff (hm : m ≤ m0) (f : α →₂[μ] E) :
    l2Predictor (𝕜 := 𝕜) hm f = f ↔ AEStronglyMeasurable[m] f μ := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  rw [predictor_eq_projection, starProjection_eq_self_iff]
  exact mem_lpMeas_iff_aestronglyMeasurable

/-- repeating the conditional projection does not change the predictor. -/
theorem l2Predictor_idempotent (hm : m ≤ m0) (f : α →₂[μ] E) :
    l2Predictor (𝕜 := 𝕜) hm (l2Predictor (𝕜 := 𝕜) hm f) = l2Predictor (𝕜 := 𝕜) hm f :=
  (l2Predictor_eq_self_iff hm _).mpr (aestronglyMeasurable_l2Predictor hm f)

/-- the residual is orthogonal to every measurable l2 predictor. -/
theorem inner_residual_l2Predictor_eq_zero (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    inner 𝕜 (f - l2Predictor (𝕜 := 𝕜) hm f) g = 0 := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  rw [predictor_eq_projection]
  exact (lpMeas E 𝕜 m 2 μ).starProjection_inner_eq_zero f g
    (mem_lpMeas_iff_aestronglyMeasurable.mpr hg)

/-- squared prediction error is the optimal residual error plus the squared distance to the predictor. -/
theorem l2_prediction_error_sq (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - g‖ ^ 2 = ‖f - l2Predictor (𝕜 := 𝕜) hm f‖ ^ 2 +
      ‖l2Predictor (𝕜 := 𝕜) hm f - g‖ ^ 2 := by
  have hp : AEStronglyMeasurable[m] (l2Predictor (𝕜 := 𝕜) hm f - g) μ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp ((lpMeas E 𝕜 m 2 μ).sub_mem
      (mem_lpMeas_iff_aestronglyMeasurable.mpr (aestronglyMeasurable_l2Predictor hm f))
      (mem_lpMeas_iff_aestronglyMeasurable.mpr hg))
  have hi := inner_residual_l2Predictor_eq_zero (𝕜 := 𝕜) hm f _ hp
  have heq : f - g = (f - l2Predictor (𝕜 := 𝕜) hm f) +
      (l2Predictor (𝕜 := 𝕜) hm f - g) := by abel
  rw [heq]
  simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi

/-- the l2 norm splits into the squared predictor norm and squared residual norm. -/
theorem l2_norm_sq_decomposition (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖f‖ ^ 2 = ‖l2Predictor (𝕜 := 𝕜) hm f‖ ^ 2 +
      ‖f - l2Predictor (𝕜 := 𝕜) hm f‖ ^ 2 := by
  have hz : AEStronglyMeasurable[m] (0 : α →₂[μ] E) μ :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (lpMeas E 𝕜 m 2 μ).zero_mem
  simpa only [sub_zero, add_comm] using
    l2_prediction_error_sq (𝕜 := 𝕜) hm f 0 hz

/-- conditional projection minimizes l2 prediction error. -/
theorem l2_prediction_error_minimal (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - l2Predictor (𝕜 := 𝕜) hm f‖ ≤ ‖f - g‖ := by
  have heq := l2_prediction_error_sq (𝕜 := 𝕜) hm f g hg
  nlinarith [norm_nonneg (f - l2Predictor (𝕜 := 𝕜) hm f), norm_nonneg (f - g),
    sq_nonneg ‖l2Predictor (𝕜 := 𝕜) hm f - g‖]

/-- equality in the error bound holds exactly for the conditional predictor. -/
theorem l2_prediction_error_eq_iff (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ‖f - g‖ = ‖f - l2Predictor (𝕜 := 𝕜) hm f‖ ↔ g = l2Predictor (𝕜 := 𝕜) hm f := by
  constructor
  · intro h
    have heq := l2_prediction_error_sq (𝕜 := 𝕜) hm f g hg
    rw [h] at heq
    have hz : ‖l2Predictor (𝕜 := 𝕜) hm f - g‖ ^ 2 = 0 := by linarith only [heq]
    have hz' : ‖l2Predictor (𝕜 := 𝕜) hm f - g‖ = 0 := sq_eq_zero_iff.mp hz
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz')).symm
  · rintro rfl
    rfl

/-- perturbations of an l2 function can only decrease under conditional projection. -/
theorem dist_l2Predictor_le (hm : m ≤ m0) (f g : α →₂[μ] E) :
    dist (l2Predictor (𝕜 := 𝕜) hm f) (l2Predictor (𝕜 := 𝕜) hm g) ≤ dist f g := by
  have : Fact (m ≤ m0) := ⟨hm⟩
  rw [predictor_eq_projection]
  exact (lpMeas E 𝕜 m 2 μ).lipschitzWith_starProjection.dist_le_mul f g |>.trans_eq (one_mul _)

/-- conditioning on a larger sigma-algebra fixes every predictor for the smaller one. -/
theorem l2Predictor_larger_fixes_smaller (hmm' : m ≤ m') (hm' : m' ≤ m0)
    (f : α →₂[μ] E) :
    l2Predictor (𝕜 := 𝕜) hm' (l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f) =
      l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f := by
  apply (l2Predictor_eq_self_iff hm' _).mpr
  exact AEStronglyMeasurable.mono hmm'
    (aestronglyMeasurable_l2Predictor (hmm'.trans hm') f)

/-- nested conditional l2 projections satisfy the tower identity. -/
theorem l2Predictor_tower (hmm' : m ≤ m') (hm' : m' ≤ m0) (f : α →₂[μ] E) :
    l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') (l2Predictor (𝕜 := 𝕜) hm' f) =
      l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f := by
  have : Fact (m ≤ m0) := ⟨hmm'.trans hm'⟩
  have : Fact (m' ≤ m0) := ⟨hm'⟩
  have hle : lpMeas E 𝕜 m 2 μ ≤ lpMeas E 𝕜 m' 2 μ := by
    intro g hg
    exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      (AEStronglyMeasurable.mono hmm' (mem_lpMeas_iff_aestronglyMeasurable.mp hg))
  simp only [predictor_eq_projection]
  exact congrArg (fun T : (α →₂[μ] E) →L[𝕜] (α →₂[μ] E) => T f)
    (starProjection_comp_starProjection_of_le hle)

/-- extra measurable information reduces squared error by the squared change in the predictor. -/
theorem l2_prediction_information_gap (hmm' : m ≤ m') (hm' : m' ≤ m0)
    (f : α →₂[μ] E) :
    ‖f - l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f‖ ^ 2 =
      ‖f - l2Predictor (𝕜 := 𝕜) hm' f‖ ^ 2 +
        ‖l2Predictor (𝕜 := 𝕜) hm' f - l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f‖ ^ 2 := by
  apply l2_prediction_error_sq
  exact AEStronglyMeasurable.mono hmm'
    (aestronglyMeasurable_l2Predictor (hmm'.trans hm') f)

/-- enlarging the conditioning sigma-algebra cannot increase prediction error. -/
theorem l2_prediction_error_antitone (hmm' : m ≤ m') (hm' : m' ≤ m0)
    (f : α →₂[μ] E) :
    ‖f - l2Predictor (𝕜 := 𝕜) hm' f‖ ≤
      ‖f - l2Predictor (𝕜 := 𝕜) (hmm'.trans hm') f‖ := by
  apply l2_prediction_error_minimal
  exact AEStronglyMeasurable.mono hmm'
    (aestronglyMeasurable_l2Predictor (hmm'.trans hm') f)

end Math.Probability
