module

public import Math.Analysis.Harnack
public import Math.Analysis.HarmonicMaximum
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false
set_option warningAsError true

/-!
poisson kernels give extremizers for both harnack bounds on smaller closed discs.
-/

@[expose] public noncomputable section

open InnerProductSpace Metric Real Set

namespace Math.ComplexAnalysis

/-- the poisson kernel with its pole at the positive real boundary point. -/
def harnackExtremal (c : ℂ) (R : ℝ) (w : ℂ) : ℝ :=
  poissonKernel c w (c + (R : ℂ))

variable {c : ℂ} {R r : ℝ}

private theorem harnack_pole_mem_sphere (hR : 0 < R) : c + (R : ℂ) ∈ sphere c R := by
  simp [abs_of_pos hR]

/-- this poisson kernel is harmonic throughout the open disc. -/
theorem harmonic_harnackExtremal (hR : 0 < R) :
    HarmonicOnNhd (harnackExtremal c R) (ball c R) := by
  let z := c + (R : ℂ)
  have hz : z ∈ sphere c R := harnack_pole_mem_sphere hR
  have hden : ∀ w ∈ ball c R, z - c - (w - c) ≠ 0 := by
    intro w hw
    rw [sub_sub_sub_cancel_right, sub_ne_zero]
    intro heq
    have hs : w ∈ sphere c R := heq ▸ hz
    exact (mem_ball.mp hw).ne (mem_sphere.mp hs)
  have hn : Differentiable ℂ (fun w : ℂ => z - c + (w - c)) := by fun_prop
  have hd : Differentiable ℂ (fun w : ℂ => z - c - (w - c)) := by fun_prop
  have hg : DifferentiableOn ℂ (fun w : ℂ => (z - c + (w - c)) / (z - c - (w - c)))
      (ball c R) := hn.differentiableOn.div hd.differentiableOn hden
  have heq : harnackExtremal c R =
      (fun w : ℂ => ((z - c + (w - c)) / (z - c - (w - c))).re) := by
    funext w
    change poissonKernel c w z = _
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simp only [Function.comp_apply, herglotzRieszKernel_def]
  rw [heq]
  intro w hw
  exact (hg.analyticOnNhd isOpen_ball w hw).harmonicAt_re

/-- the extremizer is nonnegative throughout the disc. -/
theorem nonneg_harnackExtremal (hR : 0 < R) (w : ℂ) (hw : w ∈ ball c R) :
    0 ≤ harnackExtremal c R w :=
  poissonKernel_nonneg_on_sphere (harnack_pole_mem_sphere hR) hw

/-- the extremizer has unit value at the center. -/
theorem harnackExtremal_center (hR : 0 < R) : harnackExtremal c R c = 1 := by
  simp [harnackExtremal, poissonKernel_def, hR.ne']

/-- the positive real radius attains the upper harnack coefficient. -/
theorem harnackExtremal_add_real (_hr : 0 ≤ r) (hrR : r < R) :
    harnackExtremal c R (c + (r : ℂ)) = (R + r) / (R - r) := by
  have hd : R - r ≠ 0 := (sub_pos.mpr hrR).ne'
  simp only [harnackExtremal, poissonKernel_def, add_sub_cancel_left,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp [hd]
  ring

/-- the opposite real radius attains the lower harnack coefficient. -/
theorem harnackExtremal_sub_real (hr : 0 ≤ r) (hrR : r < R) :
    harnackExtremal c R (c - (r : ℂ)) = (R - r) / (R + r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hd : R + r ≠ 0 := (add_pos_of_pos_of_nonneg hR hr).ne'
  have hw : c - (r : ℂ) - c = -(r : ℂ) := by ring
  simp only [harnackExtremal, poissonKernel_def, add_sub_cancel_left, hw,
    sub_neg_eq_add, ← Complex.ofReal_add, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp [hd]
  ring

/-- uniform upper bounds for nonnegative harmonic functions normalized at the center. -/
def upperHarnackConstants (c : ℂ) (R r : ℝ) : Set ℝ :=
  {C | ∀ f : ℂ → ℝ, HarmonicOnNhd f (ball c R) →
    (∀ w ∈ ball c R, 0 ≤ f w) → f c = 1 → ∀ w ∈ closedBall c r, f w ≤ C}

/-- uniform lower bounds for nonnegative harmonic functions normalized at the center. -/
def lowerHarnackConstants (c : ℂ) (R r : ℝ) : Set ℝ :=
  {C | ∀ f : ℂ → ℝ, HarmonicOnNhd f (ball c R) →
    (∀ w ∈ ball c R, 0 ≤ f w) → f c = 1 → ∀ w ∈ closedBall c r, C ≤ f w}

/-- the upper harnack coefficient is the least uniform upper bound on the smaller disc. -/
theorem upperHarnackConstants_eq_Ici (hr : 0 ≤ r) (hrR : r < R) :
    upperHarnackConstants c R r = Ici ((R + r) / (R - r)) := by
  have hR : 0 < R := hr.trans_lt hrR
  ext C
  constructor
  · intro h
    have hw : c + (r : ℂ) ∈ closedBall c r := by simp [abs_of_nonneg hr]
    have hb := h (harnackExtremal c R) (harmonic_harnackExtremal hR)
      (nonneg_harnackExtremal hR) (harnackExtremal_center hR) (c + (r : ℂ)) hw
    simpa only [mem_Ici, harnackExtremal_add_real hr hrR] using hb
  · intro h f hf hn hc w hw
    have hb := (harnack_on_closedBall hf hn hr hrR hw).2
    rw [hc, mul_one] at hb
    exact hb.trans h

/-- the lower harnack coefficient is the greatest uniform lower bound on the smaller disc. -/
theorem lowerHarnackConstants_eq_Iic (hr : 0 ≤ r) (hrR : r < R) :
    lowerHarnackConstants c R r = Iic ((R - r) / (R + r)) := by
  have hR : 0 < R := hr.trans_lt hrR
  ext C
  constructor
  · intro h
    have hw : c - (r : ℂ) ∈ closedBall c r := by simp [abs_of_nonneg hr]
    have hb := h (harnackExtremal c R) (harmonic_harnackExtremal hR)
      (nonneg_harnackExtremal hR) (harnackExtremal_center hR) (c - (r : ℂ)) hw
    simpa only [mem_Iic, harnackExtremal_sub_real hr hrR] using hb
  · intro h f hf hn hc w hw
    have hb := (harnack_on_closedBall hf hn hr hrR hw).1
    rw [hc, mul_one] at hb
    exact h.trans hb

end Math.ComplexAnalysis
