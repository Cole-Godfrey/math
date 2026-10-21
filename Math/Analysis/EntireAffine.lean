module

public import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option warningAsError true

/-!
an entire map with bounded derivative is affine.
the slope determines its distances, boundedness, and scalar invertibility.
-/

@[expose] public noncomputable section

open Bornology Set Function

namespace Math.ComplexAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {f : ℂ → F}

/-- a globally bounded derivative of an entire map is constant. -/
theorem deriv_eq_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) (z : ℂ) : deriv f z = deriv f 0 :=
  hf.deriv.apply_eq_apply_of_bounded hb z 0

/-- an entire map with bounded derivative is given by its value and derivative at zero. -/
theorem eq_smul_deriv_add_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) (z : ℂ) :
    f z = z • deriv f 0 + f 0 := by
  have hg : Differentiable ℂ (fun w => f w - w • deriv f 0) :=
    hf.sub (differentiable_id.smul_const _)
  have hd (w : ℂ) : deriv (fun v => f v - v • deriv f 0) w = 0 := by
    have h := ((hf w).hasDerivAt.sub
      ((hasDerivAt_id w).smul_const (deriv f 0))).deriv
    change deriv (fun v => f v - v • deriv f 0) w = deriv f w - 1 • deriv f 0 at h
    simpa [deriv_eq_of_bounded_deriv hf hb w] using h
  have h : f z - z • deriv f 0 = f 0 := by
    simpa using is_const_of_deriv_eq_zero hg hd z 0
  exact sub_eq_iff_eq_add'.mp h

/-- the affine slope and offset are unique. -/
theorem existsUnique_affine_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) :
    ∃! coefficients : F × F, ∀ z : ℂ, f z = z • coefficients.1 + coefficients.2 := by
  refine ⟨(deriv f 0, f 0), eq_smul_deriv_add_of_bounded_deriv hf hb, ?_⟩
  rintro ⟨a, b⟩ h
  have hb0 : b = f 0 := by simpa using (h 0).symm
  have ha : a = deriv f 0 := by
    have h1 := h 1
    rw [eq_smul_deriv_add_of_bounded_deriv hf hb 1] at h1
    simpa [hb0] using h1.symm
  exact Prod.ext ha hb0

/-- distances are scaled by the norm of the derivative at zero. -/
theorem dist_eq_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) (z w : ℂ) :
    dist (f z) (f w) = dist z w * ‖deriv f 0‖ := by
  rw [dist_eq_norm, eq_smul_deriv_add_of_bounded_deriv hf hb z,
    eq_smul_deriv_add_of_bounded_deriv hf hb w, add_sub_add_right_eq_sub,
    ← sub_smul, norm_smul, dist_eq_norm]

/-- the affine derivative gives a global lipschitz constant. -/
theorem lipschitzWith_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) : LipschitzWith ‖deriv f 0‖₊ f := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro z w
  simp [dist_eq_of_bounded_deriv hf hb z w, mul_comm]

/-- the entire map obeys a linear norm bound. -/
theorem norm_le_of_bounded_deriv (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) (z : ℂ) :
    ‖f z‖ ≤ ‖z‖ * ‖deriv f 0‖ + ‖f 0‖ := by
  rw [eq_smul_deriv_add_of_bounded_deriv hf hb z]
  simpa [norm_smul] using norm_add_le (z • deriv f 0) (f 0)

/-- the affine range is bounded exactly when its slope vanishes. -/
theorem isBounded_range_iff_deriv_eq_zero (hf : Differentiable ℂ f)
    (hb : IsBounded (range (deriv f))) : IsBounded (range f) ↔ deriv f 0 = 0 := by
  constructor
  · intro h
    have h1 := hf.apply_eq_apply_of_bounded h 1 0
    rw [eq_smul_deriv_add_of_bounded_deriv hf hb 1] at h1
    simpa using h1
  · intro h
    have heq : f = fun _ => f 0 := by
      funext z
      simp [eq_smul_deriv_add_of_bounded_deriv hf hb z, h]
    rw [heq, range_const]
    exact isBounded_singleton

variable {g : ℂ → ℂ}

/-- a nonzero affine slope makes an entire scalar map injective. -/
theorem injective_of_bounded_deriv (hg : Differentiable ℂ g)
    (hb : IsBounded (range (deriv g))) (hne : deriv g 0 ≠ 0) : Injective g := by
  intro z w h
  rw [eq_smul_deriv_add_of_bounded_deriv hg hb z,
    eq_smul_deriv_add_of_bounded_deriv hg hb w, add_left_inj] at h
  exact mul_right_cancel₀ hne h

/-- a nonzero affine slope makes an entire scalar map surjective. -/
theorem surjective_of_bounded_deriv (hg : Differentiable ℂ g)
    (hb : IsBounded (range (deriv g))) (hne : deriv g 0 ≠ 0) : Surjective g := by
  intro y
  refine ⟨(y - g 0) / deriv g 0, ?_⟩
  rw [eq_smul_deriv_add_of_bounded_deriv hg hb]
  simp [smul_eq_mul, div_mul_cancel₀ _ hne]

/-- every entire scalar map with bounded, nonzero derivative is bijective. -/
theorem bijective_of_bounded_deriv (hg : Differentiable ℂ g)
    (hb : IsBounded (range (deriv g))) (hne : deriv g 0 ≠ 0) : Bijective g :=
  ⟨injective_of_bounded_deriv hg hb hne, surjective_of_bounded_deriv hg hb hne⟩

/-- the nonconstant affine map has a unique zero. -/
theorem existsUnique_zero_of_bounded_deriv (hg : Differentiable ℂ g)
    (hb : IsBounded (range (deriv g))) (hne : deriv g 0 ≠ 0) :
    ∃! z : ℂ, g z = 0 := by
  obtain ⟨z, hz⟩ := surjective_of_bounded_deriv hg hb hne 0
  exact ⟨z, hz, fun w hw => injective_of_bounded_deriv hg hb hne (hw.trans hz.symm)⟩

end Math.ComplexAnalysis
