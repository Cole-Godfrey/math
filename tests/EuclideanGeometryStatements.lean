module

import Mathlib.Geometry.Euclidean.BritishFlag
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.NinePointCircle
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Volume.MeasureSimplex

set_option autoImplicit false
set_option warningAsError true

open EuclideanGeometry
open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

example (a b c : P) :
    dist a c * dist a c = dist a b * dist a b + dist c b * dist c b -
      2 * dist a b * dist c b * Real.cos (∠ a b c) :=
  dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle a b c

example (a b c : P) :
    Real.sin (∠ a b c) * dist b c = Real.sin (∠ c a b) * dist c a :=
  sin_angle_mul_dist_eq_sin_angle_mul_dist a b c

example {a b : P} (c : P) (h : b ≠ a) :
    ∠ a b c + ∠ b c a + ∠ c a b = Real.pi :=
  angle_add_angle_add_angle_eq_pi c h

example (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * dist a (midpoint ℝ b c) ^ 2 + dist b c ^ 2 / 2 := by
  nlinarith [dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq a b c]

example {a b c d : P} (h : midpoint ℝ a c = midpoint ℝ b d)
    (ha : ∠ b a d = Real.pi / 2) (p : P) :
    dist p a ^ 2 + dist p c ^ 2 = dist p b ^ 2 + dist p d ^ 2 :=
  dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_of_angle_eq_pi_div_two h ha p

example (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d :=
  mul_dist_le_mul_dist_add_mul_dist (V := V) a b c d

example {a b c d p : P} (hc : Cospherical ({a, b, c, d} : Set P))
    (hac : ∠ a p c = Real.pi) (hbd : ∠ b p d = Real.pi) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d :=
  mul_dist_add_mul_dist_eq_mul_dist_of_cospherical hc hac hbd

example (c x : P) {R : ℝ} (hR : R ≠ 0) : inversion c R (inversion c R x) = x :=
  inversion_inversion c hR x

example {c x y : P} (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y :=
  dist_inversion_inversion hx hy R

example (s : Affine.Triangle ℝ P) (i : Fin 3) : s.altitudeFoot i ∈ s.ninePointCircle :=
  Affine.Triangle.altitudeFoot_mem_ninePointCircle s i

example {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    s.eulerPoint i ∈ s.ninePointCircle :=
  Affine.Simplex.eulerPoint_mem_ninePointCircle s i

example {n : ℕ} (s : Affine.Simplex ℝ P n) :
    s.ninePointCircle.radius = s.circumradius / (n : ℝ) :=
  Affine.Simplex.ninePointCircle_radius s

example {n : ℕ} [MeasurableSpace P] [BorelSpace P] (s : Affine.Simplex ℝ P n) :
    s.volume = (MeasureTheory.Measure.euclideanHausdorffMeasure n).real s.closedInterior :=
  Affine.Simplex.volume_eq_euclideanHausdorffMeasure_real_closedInterior s
