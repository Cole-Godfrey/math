module

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false
set_option warningAsError true

open Complex Filter LSeries
open scoped Topology

example : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀

example (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

example {s : ℂ} (h : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta h

example : riemannZeta 0 = -1 / 2 := riemannZeta_zero

example (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

example {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (h1 : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * Real.pi : ℂ) ^ (-s) * Gamma s *
      cos (Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs h1

example {s : ℂ} (h : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_add_one_cpow h

example : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  riemannZeta_residue_one

example {s : ℂ} (h : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re h

example : IsDiscrete riemannZetaZeros := isDiscrete_riemannZetaZeros

example {K : Set ℂ} (h : IsCompact K) : (K ∩ riemannZetaZeros).Finite :=
  h.inter_riemannZetaZeros_finite

example : RiemannHypothesis ↔ ∀ s : ℂ, riemannZeta s = 0 →
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2 := Iff.rfl

example {s : ℂ} (h : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd h

example {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (h : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (LSeries (χ ·) s) :=
  χ.LSeries_eulerProduct_hasProd h

example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (h : 1 < s.re) :
    χ.LFunction s = LSeries (χ ·) s :=
  χ.LFunction_eq_LSeries h

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) :
    Differentiable ℂ χ.LFunction :=
  DirichletCharacter.differentiable_LFunction h

example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hc : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : χ.LFunction s ≠ 0 :=
  χ.LFunction_ne_zero_of_one_le_re hc hs

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero h

example {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  Nat.infinite_setOfPred_prime_and_modEq hq h

example : (ArithmeticFunction.moebius * (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ)) = 1 :=
  ArithmeticFunction.moebius_mul_coe_zeta

example {R : Type*} [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • g x.2 = f n :=
  ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq

example : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

example : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (Real.pi ^ 4 / 90) :=
  hasSum_zeta_four

example {f g : ℕ → ℂ} (hf : abscissaOfAbsConv f < ⊤) (hg : abscissaOfAbsConv g < ⊤)
    (h : (fun x : ℝ => LSeries f x) =ᶠ[atTop] fun x => LSeries g x)
    {n : ℕ} (hn : n ≠ 0) : f n = g n :=
  LSeries.eq_of_LSeries_eventually_eq hf hg h hn

example {s : ℂ} (h : ∀ n : ℤ, s ≠ n) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s = -logDeriv riemannZeta (1 - s) + log (2 * Real.pi) - digamma s +
      Real.pi / 2 * tan (Real.pi * s / 2) :=
  logDeriv_riemannZeta_one_sub h hz
