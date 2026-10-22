module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option autoImplicit false
set_option warningAsError true

/-!
level-one modular identities admit finite certificates from their initial fourier coefficients.
the coefficient bound is the integer weight's nonnegative part divided by twelve.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace Math.NumberTheory

variable {k : ℤ}

/-- a level-one modular form vanishes exactly when its initial coefficients vanish. -/
theorem modularForm_eq_zero_iff_coeffs (f : ModularForm 𝒮ℒ k) :
    f = 0 ↔ ∀ n ≤ k.toNat / 12, (qExpansion 1 f).coeff n = 0 := by
  constructor
  · rintro rfl n _
    simp [qExpansion_zero]
  · intro h
    apply ModularForm.sturm_bound_levelOne
    have hle : ((k.toNat / 12 + 1 : ℕ) : ℕ∞) ≤ (qExpansion 1 f).order :=
      PowerSeries.nat_le_order _ (k.toNat / 12 + 1) (fun n hn => h n (Nat.le_of_lt_succ hn))
    have hlt : ((k.toNat / 12 : ℕ) : ℕ∞) < ((k.toNat / 12 + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self (k.toNat / 12)
    exact hlt.trans_le hle

/-- equality of level-one modular forms is determined by finitely many initial coefficients. -/
theorem modularForm_eq_iff_coeffs (f g : ModularForm 𝒮ℒ k) :
    f = g ↔ ∀ n ≤ k.toNat / 12, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n := by
  rw [← sub_eq_zero, modularForm_eq_zero_iff_coeffs]
  simp only [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    map_sub, sub_eq_zero]

/-- the initial coefficients through the sturm bound, viewed as a finite linear map. -/
def sturmCoefficients (k : ℤ) :
    ModularForm 𝒮ℒ k →ₗ[ℂ] (Fin (k.toNat / 12 + 1) → ℂ) where
  toFun f n := (qExpansion 1 f).coeff n
  map_add' f g := by
    funext n
    simp [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL]
  map_smul' c f := by
    funext n
    simp [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]

/-- finite coefficient certificates distinguish every level-one modular form of a fixed weight. -/
theorem sturmCoefficients_injective (k : ℤ) : Function.Injective (sturmCoefficients k) := by
  intro f g h
  apply (modularForm_eq_iff_coeffs f g).mpr
  intro n hn
  exact congrFun h ⟨n, by omega⟩

end Math.NumberTheory
