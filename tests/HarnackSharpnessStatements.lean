module

public import Math.Analysis.HarnackSharpness

set_option autoImplicit false
set_option warningAsError true

open InnerProductSpace Metric Set

example (c : ℂ) (R : ℝ) (hR : 0 < R) :
    HarmonicOnNhd (Math.ComplexAnalysis.harnackExtremal c R) (ball c R) :=
  Math.ComplexAnalysis.harmonic_harnackExtremal hR

example (c : ℂ) (R : ℝ) (hR : 0 < R) (w : ℂ) (hw : w ∈ ball c R) :
    0 ≤ Math.ComplexAnalysis.harnackExtremal c R w :=
  Math.ComplexAnalysis.nonneg_harnackExtremal hR w hw

example (c : ℂ) (R : ℝ) (hR : 0 < R) :
    Math.ComplexAnalysis.harnackExtremal c R c = 1 :=
  Math.ComplexAnalysis.harnackExtremal_center hR

example (c : ℂ) (R r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    Math.ComplexAnalysis.harnackExtremal c R (c + (r : ℂ)) = (R + r) / (R - r) :=
  Math.ComplexAnalysis.harnackExtremal_add_real hr hrR

example (c : ℂ) (R r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    Math.ComplexAnalysis.harnackExtremal c R (c - (r : ℂ)) = (R - r) / (R + r) :=
  Math.ComplexAnalysis.harnackExtremal_sub_real hr hrR

example (c : ℂ) (R r : ℝ) (hr : 0 ≤ r) (hrR : r < R) (C : ℝ) :
    (∀ f : ℂ → ℝ, HarmonicOnNhd f (ball c R) →
      (∀ w ∈ ball c R, 0 ≤ f w) → f c = 1 → ∀ w ∈ closedBall c r, f w ≤ C) ↔
      (R + r) / (R - r) ≤ C := by
  change C ∈ Math.ComplexAnalysis.upperHarnackConstants c R r ↔ _
  rw [Math.ComplexAnalysis.upperHarnackConstants_eq_Ici hr hrR, mem_Ici]

example (c : ℂ) (R r : ℝ) (hr : 0 ≤ r) (hrR : r < R) (C : ℝ) :
    (∀ f : ℂ → ℝ, HarmonicOnNhd f (ball c R) →
      (∀ w ∈ ball c R, 0 ≤ f w) → f c = 1 → ∀ w ∈ closedBall c r, C ≤ f w) ↔
      C ≤ (R - r) / (R + r) := by
  change C ∈ Math.ComplexAnalysis.lowerHarnackConstants c R r ↔ _
  rw [Math.ComplexAnalysis.lowerHarnackConstants_eq_Iic hr hrR, mem_Iic]

example : Math.ComplexAnalysis.harnackExtremal 0 2 (1 : ℂ) = 3 := by
  have h := Math.ComplexAnalysis.harnackExtremal_add_real (c := 0) (r := 1) (R := 2)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : Math.ComplexAnalysis.harnackExtremal 0 2 (-1 : ℂ) = (1 : ℝ) / 3 := by
  have h := Math.ComplexAnalysis.harnackExtremal_sub_real (c := 0) (r := 1) (R := 2)
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h
