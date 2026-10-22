module

import Math.NumberTheory.SturmFinite
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Petersson

set_option autoImplicit false
set_option warningAsError true

open UpperHalfPlane hiding I
open Complex ModularForm EisensteinSeries
open scoped MatrixGroups Topology

noncomputable section

example (k : ℕ) (h : Even k) : Module.rank ℂ (ModularForm 𝒮ℒ k) =
    if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 :=
  ModularForm.dimension_level_one k h

example {k : ℤ} (h : k < 0) : Module.rank ℂ (ModularForm 𝒮ℒ k) = 0 :=
  ModularForm.levelOne_neg_weight_rank_zero h

example {k : ℤ} (h : Odd k) (f : ModularForm 𝒮ℒ k) : f = 0 :=
  ModularForm.levelOne_odd_weight_eq_zero h f

example : Module.rank ℂ (CuspForm 𝒮ℒ 12) = 1 :=
  CuspForm.rank_eq_one_of_weight_eq_twelve

example (f : CuspForm 𝒮ℒ 12) : ∃ c : ℂ, c • CuspForm.discriminant = f :=
  CuspForm.exists_smul_discriminant_of_weight_eq_twelve f

example (k : ℤ) : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) :=
  CuspForm.discriminantEquiv

example {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (h : (↑(k.toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 :=
  ModularForm.sturm_bound_levelOne h

example (z : ℍ) : ModularForm.discriminant z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 :=
  ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z

example (z : ℍ) : ModularForm.discriminant z ≠ 0 :=
  ModularForm.discriminant_ne_zero z

example : (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 :=
  ModularForm.discriminant_qExpansion_coeff_one

example : (qExpansion 1 E₄).coeff 1 = 240 := ModularForm.E₄_qExpansion_coeff_one

example : (qExpansion 1 E₆).coeff 1 = -504 := ModularForm.E₆_qExpansion_coeff_one

example (z : ℂ) : jacobiTheta (2 + z) = jacobiTheta z := jacobiTheta_two_add z

example (z : ℍ) :
    jacobiTheta (ModularGroup.S • z : ℍ) = (-I * z) ^ (1 / 2 : ℂ) * jacobiTheta z :=
  jacobiTheta_S_smul z

example {z : ℂ} (h : 0 < z.im) : DifferentiableAt ℂ jacobiTheta z :=
  differentiableAt_jacobiTheta h

example (k : ℤ) (f g : ℍ → ℂ) (z : ℍ) : petersson k g f z = star (petersson k f g z) :=
  petersson_symm k f g z

example {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (h : 0 < k) (f : CuspForm Γ k) : Differentiable ℂ (ModularForm.L h f) :=
  CuspForm.differentiable_L h f

example {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (h : 0 < k) (f : CuspForm Γ k) : Differentiable ℂ (ModularForm.Λ h f) :=
  CuspForm.differentiable_Λ h f

example {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    f = 0 ↔ ∀ n ≤ k.toNat / 12, (qExpansion 1 f).coeff n = 0 :=
  Math.NumberTheory.modularForm_eq_zero_iff_coeffs f

example {k : ℤ} (f g : ModularForm 𝒮ℒ k) :
    f = g ↔ ∀ n ≤ k.toNat / 12, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n :=
  Math.NumberTheory.modularForm_eq_iff_coeffs f g

example (k : ℤ) : Function.Injective (fun f : ModularForm 𝒮ℒ k =>
    fun n : Fin (k.toNat / 12 + 1) => (qExpansion 1 f).coeff n) :=
  Math.NumberTheory.sturmCoefficients_injective k

example (f g : ModularForm 𝒮ℒ 12)
    (h0 : (qExpansion 1 f).coeff 0 = (qExpansion 1 g).coeff 0)
    (h1 : (qExpansion 1 f).coeff 1 = (qExpansion 1 g).coeff 1) : f = g := by
  apply (Math.NumberTheory.modularForm_eq_iff_coeffs f g).mpr
  intro n hn
  have h : n = 0 ∨ n = 1 := by norm_num at hn; omega
  rcases h with rfl | rfl
  · exact h0
  · exact h1
