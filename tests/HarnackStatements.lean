module

import Math.Analysis.Harnack
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false
set_option warningAsError true

open InnerProductSpace Metric Set
open Math.ComplexAnalysis

noncomputable section

variable {f : ℂ → ℝ} {c z : ℂ} {R r : ℝ} {s : Set ℂ}

example (hf : HarmonicContOnCl f (ball c R)) (hn : ∀ w ∈ sphere c R, 0 ≤ f w)
    (hz : z ∈ ball c R) : (R - ‖z - c‖) / (R + ‖z - c‖) * f c ≤ f z :=
  harnack_lower hf hn hz

example (hf : HarmonicContOnCl f (ball c R)) (hn : ∀ w ∈ sphere c R, 0 ≤ f w)
    (hz : z ∈ ball c R) : f z ≤ (R + ‖z - c‖) / (R - ‖z - c‖) * f c :=
  harnack_upper hf hn hz

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (hz : z ∈ ball c R) : (R - ‖z - c‖) / (R + ‖z - c‖) * f c ≤ f z :=
  harnack_lower_on_ball hf hn hz

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (hz : z ∈ ball c R) : f z ≤ (R + ‖z - c‖) / (R - ‖z - c‖) * f c :=
  harnack_upper_on_ball hf hn hz

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (hr0 : 0 ≤ r) (hr : r < R) (hz : z ∈ closedBall c r) :
    (R - r) / (R + r) * f c ≤ f z ∧ f z ≤ (R + r) / (R - r) * f c :=
  harnack_on_closedBall hf hn hr0 hr hz

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (h0 : f c = 0) : EqOn f (fun _ => 0) (ball c R) :=
  eq_zero_on_ball_of_harmonic_nonneg hf hn h0

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (hz : z ∈ ball c R) : f z = 0 ↔ f c = 0 :=
  eq_zero_iff_center_of_harmonic_nonneg hf hn hz

example (hf : HarmonicOnNhd f (ball c R)) (hn : ∀ w ∈ ball c R, 0 ≤ f w)
    (hc : 0 < f c) (hz : z ∈ ball c R) : 0 < f z :=
  pos_on_ball_of_harmonic_nonneg hf hn hc hz

example (hs : IsOpen s) (hp : IsPreconnected s) (hf : HarmonicOnNhd f s)
    (hn : ∀ w ∈ s, 0 ≤ f w) (hc : c ∈ s) (h0 : f c = 0) : EqOn f (fun _ => 0) s :=
  eq_zero_on_preconnected_of_harmonic_nonneg hs hp hf hn hc h0

example (hs : IsOpen s) (hp : IsPreconnected s) (hf : HarmonicOnNhd f s)
    (hc : c ∈ s) (hm : ∀ w ∈ s, f c ≤ f w) : EqOn f (fun _ => f c) s :=
  eq_on_preconnected_of_harmonic_min hs hp hf hc hm

example (hs : IsOpen s) (hp : IsPreconnected s) (hf : HarmonicOnNhd f s)
    (hc : c ∈ s) (hm : ∀ w ∈ s, f w ≤ f c) : EqOn f (fun _ => f c) s :=
  eq_on_preconnected_of_harmonic_max hs hp hf hc hm

example (hf : HarmonicOnNhd f univ) (hn : ∀ w, 0 ≤ f w) : f z = f c :=
  eq_of_entire_harmonic_nonneg hf hn z c

example (hf : HarmonicOnNhd f univ) (hb : BddBelow (range f)) : f z = f c :=
  eq_of_entire_harmonic_bddBelow hf hb z c

example (hf : HarmonicOnNhd f univ) (hb : BddAbove (range f)) : f z = f c :=
  eq_of_entire_harmonic_bddAbove hf hb z c

example : ∃ g : ℂ → ℝ, HarmonicOnNhd g univ ∧ g 0 ≠ g 1 := by
  refine ⟨Complex.re, ?_, by simp⟩
  intro w _
  exact (show AnalyticAt ℂ (fun v : ℂ => v) w from analyticAt_id).harmonicAt_re
