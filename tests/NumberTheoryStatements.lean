import Mathlib.Algebra.Module.NatInt
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Pell

open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

section Reciprocity

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

example : Field (ZMod p) := inferInstance

example (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1 : ℤ) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq

example {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSym (a : ℤ) b = (-1 : ℤ) ^ (a / 2 * (b / 2)) * jacobiSym (b : ℤ) a :=
  jacobiSym.quadratic_reciprocity ha hb

end Reciprocity

section Pell

example {d : ℤ} (hpos : 0 < d) (hns : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare hpos hns

example {d : ℤ} (hpos : 0 < d) (hns : ¬IsSquare d) :
    ∃! a₁ : Pell.Solution₁ d,
      1 < a₁.x ∧ 0 < a₁.y ∧
        ∀ a : Pell.Solution₁ d, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n :=
  Pell.existsUnique_pos_generator hpos hns

end Pell

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

example : UniqueFactorizationMonoid (Ideal R) := inferInstance

example {I : Ideal R} (hI : I ≠ 0) :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, v.maxPowDividing I) = I :=
  Ideal.finprod_heightOneSpectrum_factorization hI

example {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ (FractionalIdeal.count K v I)) = I :=
  FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

end Dedekind

section NumberFields

variable (K : Type*) [Field K] [NumberField K]

-- specify the carrier to select the canonical integer action.
local instance : Module ℤ (Additive ((𝓞 K)ˣ ⧸ (NumberField.Units.torsion K))) :=
  AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ (NumberField.Units.torsion K)))

example : Fintype (ClassGroup (𝓞 K)) := inferInstance

example : 0 < NumberField.classNumber K := NumberField.classNumber_pos K

example : NumberField.classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  NumberField.classNumber_eq_one_iff

example (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (((Module.finrank ℚ K).factorial : ℝ) /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(NumberField.discr K : ℝ)|) :=
  NumberField.exists_ideal_in_class_of_norm_le C

example : NumberField.Units.rank K = Fintype.card (NumberField.InfinitePlace K) - 1 := rfl

example : Module.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) =
    NumberField.Units.rank K := NumberField.Units.finrank_modTorsion K

example : Module.Basis (Fin (NumberField.Units.rank K)) ℤ
    (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) :=
  NumberField.Units.basisModTorsion K

example (x : (𝓞 K)ˣ) :
    ∃! ζe : NumberField.Units.torsion K × (Fin (NumberField.Units.rank K) → ℤ),
      x = (ζe.1 : (𝓞 K)ˣ) * ∏ i, (NumberField.Units.fundSystem K i) ^ (ζe.2 i) :=
  NumberField.Units.exist_unique_eq_mul_prod K x

example : 0 < NumberField.Units.regulator K := NumberField.Units.regulator_pos K

example {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) *
      (∏ᶠ w : NumberField.FinitePlace K, w x) = 1 :=
  NumberField.prod_abs_eq_one hx

example (θ : 𝓞 K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ) :
    ↥(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)) ≃
      ↥(RingOfIntegers.monicFactorsMod θ p) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp

end NumberFields
