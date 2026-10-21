module

public import Math.Analysis.HarmonicPoisson
public import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option warningAsError true

/-!
nonnegative harmonic functions satisfy sharp two-sided harnack bounds on discs.
-/

@[expose] public noncomputable section

open Filter InnerProductSpace Metric Real Set

open scoped Topology

namespace Math.ComplexAnalysis

variable {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

private theorem poisson_circleIntegrable (hf : HarmonicContOnCl f (ball c R))
    (hw : w ∈ ball c R) : CircleIntegrable (poissonKernel c w • f) c R := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hn : w ∉ sphere c |R| := by
    simpa only [mem_sphere, abs_of_pos hR] using (mem_ball.mp hw).ne
  have hk : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hn)
  exact (hk.smul (hf.continuousOn_ball.mono (by
    simpa only [abs_of_pos hR] using (sphere_subset_closedBall :
      sphere c R ⊆ closedBall c R)))).circleIntegrable'

/-- boundary nonnegativity gives the sharp lower harnack bound at every interior point. -/
theorem harnack_lower (hf : HarmonicContOnCl f (ball c R))
    (hn : ∀ z ∈ sphere c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hi : CircleIntegrable f c R := by
    exact (hf.continuousOn_ball.mono (by
      simpa only [abs_of_pos hR] using (sphere_subset_closedBall :
        sphere c R ⊆ closedBall c R))).circleIntegrable'
  have hm : circleAverage f c R = f c := by
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
    simpa only [abs_of_pos hR] using hf
  rw [← hm, ← harmonic_poisson_formula hf hw, ← smul_eq_mul, ← circleAverage_smul]
  apply circleAverage_mono hi.const_smul (poisson_circleIntegrable hf hw)
  intro z hz
  have hs : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
  have hk : (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
    simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def] using le_re_herglotzRieszKernel hs hw
  exact mul_le_mul_of_nonneg_right hk (hn z hs)

/-- boundary nonnegativity gives the sharp upper harnack bound at every interior point. -/
theorem harnack_upper (hf : HarmonicContOnCl f (ball c R))
    (hn : ∀ z ∈ sphere c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hi : CircleIntegrable f c R := by
    exact (hf.continuousOn_ball.mono (by
      simpa only [abs_of_pos hR] using (sphere_subset_closedBall :
        sphere c R ⊆ closedBall c R))).circleIntegrable'
  have hm : circleAverage f c R = f c := by
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_eq
    simpa only [abs_of_pos hR] using hf
  rw [← hm, ← harmonic_poisson_formula hf hw, ← smul_eq_mul, ← circleAverage_smul]
  apply circleAverage_mono (poisson_circleIntegrable hf hw) hi.const_smul
  intro z hz
  have hs : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
  have hk : poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
    simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def] using re_herglotzRieszKernel_le hs hw
  exact mul_le_mul_of_nonneg_right hk (hn z hs)

/-- the lower harnack bound needs harmonicity and nonnegativity only on the open disc. -/
theorem harnack_lower_on_ball (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) * f c ≤ f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hd : R + ‖w - c‖ ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hR (norm_nonneg _))
  have hc : ContinuousAt (fun r : ℝ => (r - ‖w - c‖) / (r + ‖w - c‖) * f c) R :=
    ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) hd).mul continuousAt_const
  apply le_of_tendsto (hc.tendsto.mono_left (show 𝓝[<] R ≤ 𝓝 R from nhdsWithin_le_nhds))
  filter_upwards [Ioo_mem_nhdsLT (mem_ball_iff_norm.mp hw)] with r hr
  have hg : HarmonicContOnCl f (ball c r) :=
    (hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hr.2))).harmonicContOnCl
  exact harnack_lower hg (fun z hz => hn z (sphere_subset_ball hr.2 hz))
    (mem_ball_iff_norm.mpr hr.1)

/-- the upper harnack bound needs harmonicity and nonnegativity only on the open disc. -/
theorem harnack_upper_on_ball (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    f w ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * f c := by
  have hd : R - ‖w - c‖ ≠ 0 := ne_of_gt (sub_pos.mpr (mem_ball_iff_norm.mp hw))
  have hc : ContinuousAt (fun r : ℝ => (r + ‖w - c‖) / (r - ‖w - c‖) * f c) R :=
    ((continuousAt_id.add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) hd).mul continuousAt_const
  apply ge_of_tendsto (hc.tendsto.mono_left (show 𝓝[<] R ≤ 𝓝 R from nhdsWithin_le_nhds))
  filter_upwards [Ioo_mem_nhdsLT (mem_ball_iff_norm.mp hw)] with r hr
  have hg : HarmonicContOnCl f (ball c r) :=
    (hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hr.2))).harmonicContOnCl
  exact harnack_upper hg (fun z hz => hn z (sphere_subset_ball hr.2 hz))
    (mem_ball_iff_norm.mpr hr.1)

/-- harnack bounds hold uniformly on every smaller closed disc. -/
theorem harnack_on_closedBall (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < R)
    (hw : w ∈ closedBall c r) :
    (R - r) / (R + r) * f c ≤ f w ∧ f w ≤ (R + r) / (R - r) * f c := by
  have hR : 0 < R := hr0.trans_lt hr
  have hd : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw' : w ∈ ball c R := mem_ball_iff_norm.mpr (hd.trans_lt hr)
  have hc : 0 ≤ f c := hn c (mem_ball_self hR)
  have hl : (R - r) / (R + r) ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := by
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hR hr0)
      (add_pos_of_pos_of_nonneg hR (norm_nonneg _))).mpr
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hd)]
  have hu : (R + ‖w - c‖) / (R - ‖w - c‖) ≤ (R + r) / (R - r) := by
    apply (div_le_div_iff₀ (sub_pos.mpr (hd.trans_lt hr)) (sub_pos.mpr hr)).mpr
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hd)]
  exact ⟨(mul_le_mul_of_nonneg_right hl hc).trans (harnack_lower_on_ball hf hn hw'),
    (harnack_upper_on_ball hf hn hw').trans (mul_le_mul_of_nonneg_right hu hc)⟩

/-- a nonnegative harmonic function vanishing at the center vanishes on the disc. -/
theorem eq_zero_on_ball_of_harmonic_nonneg (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) (hz : f c = 0) : EqOn f (fun _ => 0) (ball c R) := by
  intro w hw
  exact le_antisymm (by simpa only [hz, mul_zero] using harnack_upper_on_ball hf hn hw)
    (hn w hw)

/-- a nonnegative harmonic function has an interior zero exactly when its center value is zero. -/
theorem eq_zero_iff_center_of_harmonic_nonneg (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) (hw : w ∈ ball c R) : f w = 0 ↔ f c = 0 := by
  constructor
  · intro hz
    have hR : 0 < R := pos_of_mem_ball hw
    have hp : 0 < (R - ‖w - c‖) / (R + ‖w - c‖) :=
      div_pos (sub_pos.mpr (mem_ball_iff_norm.mp hw))
        (add_pos_of_pos_of_nonneg hR (norm_nonneg _))
    have hl := harnack_lower_on_ball hf hn hw
    have hle : f c ≤ 0 := (mul_le_mul_iff_of_pos_left hp).mp (by
      simpa only [hz, mul_zero] using hl)
    exact le_antisymm hle (hn c (mem_ball_self hR))
  · intro hz
    exact eq_zero_on_ball_of_harmonic_nonneg hf hn hz hw

/-- a positive center value forces positivity throughout the disc. -/
theorem pos_on_ball_of_harmonic_nonneg (hf : HarmonicOnNhd f (ball c R))
    (hn : ∀ z ∈ ball c R, 0 ≤ f z) (hc : 0 < f c) (hw : w ∈ ball c R) : 0 < f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hp : 0 < (R - ‖w - c‖) / (R + ‖w - c‖) :=
    div_pos (sub_pos.mpr (mem_ball_iff_norm.mp hw))
      (add_pos_of_pos_of_nonneg hR (norm_nonneg _))
  exact (mul_pos hp hc).trans_le (harnack_lower_on_ball hf hn hw)

/-- an interior zero forces a nonnegative harmonic function to vanish on a connected domain. -/
theorem eq_zero_on_preconnected_of_harmonic_nonneg {s : Set ℂ} (hs : IsOpen s)
    (hp : IsPreconnected s) (hf : HarmonicOnNhd f s) (hn : ∀ z ∈ s, 0 ≤ f z)
    (hc : c ∈ s) (hz : f c = 0) : EqOn f (fun _ => 0) s := by
  let u : Set s := {x | f x = 0}
  let : PreconnectedSpace s := Subtype.preconnectedSpace hp
  have hclosed : IsClosed u := isClosed_eq hf.continuousOn.domRestrict continuous_const
  have hopen : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs x x.property
    have heq : EqOn f (fun _ => 0) (ball (x : ℂ) r) :=
      eq_zero_on_ball_of_harmonic_nonneg (hf.mono hrs) (fun z hz => hn z (hrs hz)) hx
    have hb : (Subtype.val ⁻¹' ball (x : ℂ) r : Set s) ∈ 𝓝 x :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hr)
    exact mem_of_superset hb (fun y hy => heq hy)
  have hall : u = univ := (show IsClopen u from ⟨hclosed, hopen⟩).eq_univ ⟨⟨c, hc⟩, hz⟩
  intro z hzs
  have hm : (⟨z, hzs⟩ : s) ∈ u := by rw [hall]; trivial
  exact hm

/-- a harmonic function attaining a minimum on a connected open domain is constant there. -/
theorem eq_on_preconnected_of_harmonic_min {s : Set ℂ} (hs : IsOpen s)
    (hp : IsPreconnected s) (hf : HarmonicOnNhd f s) (hc : c ∈ s)
    (hm : ∀ z ∈ s, f c ≤ f z) : EqOn f (fun _ => f c) s := by
  have hg : HarmonicOnNhd (fun z => f z - f c) s :=
    hf.sub (harmonicOnNhd_const (f c))
  have heq := eq_zero_on_preconnected_of_harmonic_nonneg hs hp hg
    (fun z hz => sub_nonneg.mpr (hm z hz)) hc (sub_self _)
  intro z hz
  have h := heq hz
  exact sub_eq_zero.mp h

/-- a harmonic function attaining a maximum on a connected open domain is constant there. -/
theorem eq_on_preconnected_of_harmonic_max {s : Set ℂ} (hs : IsOpen s)
    (hp : IsPreconnected s) (hf : HarmonicOnNhd f s) (hc : c ∈ s)
    (hm : ∀ z ∈ s, f z ≤ f c) : EqOn f (fun _ => f c) s := by
  have hg : HarmonicOnNhd (fun z => f c - f z) s :=
    (harmonicOnNhd_const (f c)).sub hf
  have heq := eq_zero_on_preconnected_of_harmonic_nonneg hs hp hg
    (fun z hz => sub_nonneg.mpr (hm z hz)) hc (sub_self _)
  intro z hz
  have h := heq hz
  exact (sub_eq_zero.mp h).symm

private theorem le_of_entire_harmonic_nonneg (hf : HarmonicOnNhd f univ)
    (hn : ∀ z, 0 ≤ f z) (z c : ℂ) : f z ≤ f c := by
  have hl : Tendsto (fun t : ℝ => (1 + 2 * ‖z - c‖ / t) * f c) atTop (𝓝 (f c)) := by
    simpa only [id_eq, add_zero, one_mul] using
      ((tendsto_id.const_div_atTop (2 * ‖z - c‖)).const_add 1).mul_const (f c)
  apply ge_of_tendsto hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hw : z ∈ ball c (‖z - c‖ + t) := by
    rw [mem_ball_iff_norm]
    linarith
  have hh := harnack_upper_on_ball (hf.mono (subset_univ _)) (fun x _ => hn x) hw
  have heq : (‖z - c‖ + t + ‖z - c‖) / (‖z - c‖ + t - ‖z - c‖) =
      1 + 2 * ‖z - c‖ / t := by
    rw [show ‖z - c‖ + t - ‖z - c‖ = t by ring]
    field_simp [ht.ne']
    ring
  simpa only [heq] using hh

/-- every nonnegative harmonic function on the complex plane is constant. -/
theorem eq_of_entire_harmonic_nonneg (hf : HarmonicOnNhd f univ)
    (hn : ∀ z, 0 ≤ f z) (z w : ℂ) : f z = f w :=
  le_antisymm (le_of_entire_harmonic_nonneg hf hn z w)
    (le_of_entire_harmonic_nonneg hf hn w z)

/-- a global lower bound suffices for the harmonic liouville theorem. -/
theorem eq_of_entire_harmonic_bddBelow (hf : HarmonicOnNhd f univ)
    (hb : BddBelow (range f)) (z w : ℂ) : f z = f w := by
  obtain ⟨m, hm⟩ := hb
  have hg : HarmonicOnNhd (fun x => f x - m) univ :=
    hf.sub (harmonicOnNhd_const m)
  have hn : ∀ x, 0 ≤ f x - m := fun x => sub_nonneg.mpr (hm (mem_range_self x))
  have heq := eq_of_entire_harmonic_nonneg hg hn z w
  linarith only [heq]

/-- a global upper bound also forces an entire harmonic function to be constant. -/
theorem eq_of_entire_harmonic_bddAbove (hf : HarmonicOnNhd f univ)
    (hb : BddAbove (range f)) (z w : ℂ) : f z = f w := by
  obtain ⟨m, hm⟩ := hb
  have hg : HarmonicOnNhd (fun x => m - f x) univ :=
    (harmonicOnNhd_const m).sub hf
  have hn : ∀ x, 0 ≤ m - f x := fun x => sub_nonneg.mpr (hm (mem_range_self x))
  have heq := eq_of_entire_harmonic_nonneg hg hn z w
  linarith only [heq]

end Math.ComplexAnalysis
