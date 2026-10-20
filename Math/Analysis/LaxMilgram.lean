module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

set_option autoImplicit false
set_option warningAsError true

/-!
a coercive bounded bilinear form on a real hilbert space defines a continuous
linear solution operator on the dual space. norm bounds give quantitative stability.
-/

@[expose] public section

namespace Math.FunctionalAnalysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- continuous linear correspondence between loads and weak solutions. -/
noncomputable def weakSolutionEquiv (hB : IsCoercive B) : StrongDual ℝ V ≃L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.trans
    hB.continuousLinearEquivOfBilin.symm

/-- the unique vector solving the bounded variational problem. -/
noncomputable def weakSolution (hB : IsCoercive B) (ℓ : StrongDual ℝ V) : V :=
  weakSolutionEquiv hB ℓ

/-- the solution satisfies the variational identity for every test vector. -/
theorem bilinear_weakSolution (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (weakSolution hB ℓ) v = ℓ v := by
  change B (hB.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm ℓ)) v = ℓ v
  rw [← hB.continuousLinearEquivOfBilin_apply,
    ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]

/-- every weak solution agrees with the specified solution. -/
theorem eq_weakSolution (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v, B u v = ℓ v) : u = weakSolution hB ℓ := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply (InnerProductSpace.toDual ℝ V).injective
  ext v
  simpa only [InnerProductSpace.toDual_apply_apply,
    hB.continuousLinearEquivOfBilin_apply, bilinear_weakSolution] using hu v

/-- each continuous linear load has exactly one weak solution. -/
theorem existsUnique_weak_solution (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨weakSolution hB ℓ, bilinear_weakSolution hB ℓ, fun _ hu => eq_weakSolution hB hu⟩

@[simp]
theorem weakSolution_zero (hB : IsCoercive B) : weakSolution hB 0 = 0 :=
  (weakSolutionEquiv hB).map_zero

theorem weakSolution_add (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) :
    weakSolution hB (ℓ₁ + ℓ₂) = weakSolution hB ℓ₁ + weakSolution hB ℓ₂ :=
  (weakSolutionEquiv hB).map_add ℓ₁ ℓ₂

theorem weakSolution_sub (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) :
    weakSolution hB (ℓ₁ - ℓ₂) = weakSolution hB ℓ₁ - weakSolution hB ℓ₂ :=
  (weakSolutionEquiv hB).map_sub ℓ₁ ℓ₂

theorem weakSolution_smul (hB : IsCoercive B) (c : ℝ) (ℓ : StrongDual ℝ V) :
    weakSolution hB (c • ℓ) = c • weakSolution hB ℓ :=
  (weakSolutionEquiv hB).map_smul c ℓ

theorem continuous_weakSolution (hB : IsCoercive B) : Continuous (weakSolution hB) :=
  (weakSolutionEquiv hB).continuous

/-- a positive coercivity constant bounds the solution norm. -/
theorem norm_weakSolution_le (hB : IsCoercive B) (ℓ : StrongDual ℝ V) {C : ℝ}
    (hC : 0 < C) (hbound : ∀ v : V, C * ‖v‖ * ‖v‖ ≤ B v v) :
    ‖weakSolution hB ℓ‖ ≤ ‖ℓ‖ / C := by
  let u := weakSolution hB ℓ
  change ‖u‖ ≤ ‖ℓ‖ / C
  by_cases hu : u = 0
  · simp only [hu, norm_zero]
    exact div_nonneg (norm_nonneg ℓ) hC.le
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have h : C * ‖u‖ * ‖u‖ ≤ ‖ℓ‖ * ‖u‖ := calc
      C * ‖u‖ * ‖u‖ ≤ B u u := hbound u
      _ = ℓ u := bilinear_weakSolution hB ℓ u
      _ ≤ ‖ℓ u‖ := le_abs_self _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u
    apply (le_div_iff₀ hC).2
    rw [mul_comm ‖u‖ C]
    exact (mul_le_mul_iff_left₀ hu_pos).mp h

/-- perturbing the load changes the solution by at most the coercivity bound. -/
theorem dist_weakSolution_le (hB : IsCoercive B) (ℓ₁ ℓ₂ : StrongDual ℝ V) {C : ℝ}
    (hC : 0 < C) (hbound : ∀ v : V, C * ‖v‖ * ‖v‖ ≤ B v v) :
    dist (weakSolution hB ℓ₁) (weakSolution hB ℓ₂) ≤ ‖ℓ₁ - ℓ₂‖ / C := by
  rw [dist_eq_norm, ← weakSolution_sub]
  exact norm_weakSolution_le hB (ℓ₁ - ℓ₂) hC hbound

end Math.FunctionalAnalysis
