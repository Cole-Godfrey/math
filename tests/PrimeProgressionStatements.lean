module

import Math.NumberTheory.PrimeProgressions

set_option autoImplicit false
set_option warningAsError true

variable {a q p : ℕ}

example (h : ¬ a.Coprime q) (hp : p.Prime) (hm : p ≡ a [MOD q]) : p = a.gcd q :=
  Math.NumberTheory.prime_eq_gcd_of_not_coprime h hp hm

example (h : ¬ a.Coprime q) : Set.Finite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  Math.NumberTheory.finite_primes_modEq_of_not_coprime h

example : Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} ↔ q ≠ 0 ∧ a.Coprime q :=
  Math.NumberTheory.infinite_primes_modEq_iff

example (N : ℕ) (s : Finset ℕ) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q] ∧ N < p ∧ p ∉ s} ↔
      q ≠ 0 ∧ a.Coprime q :=
  Math.NumberTheory.infinite_primes_modEq_above_avoiding_iff N s

example (hq : q ≠ 0) (h : a.Coprime q) (N : ℕ) (s : Finset ℕ) :
    ∃ p, N < p ∧ p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q] :=
  Math.NumberTheory.exists_prime_modEq_above_avoiding hq h N s

example (hq : q ≠ 0) (h : a.Coprime q) (N n : ℕ) (s : Finset ℕ) :
    ∃ t : Finset ℕ, t.card = n ∧ ∀ p ∈ t, N < p ∧ p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q] :=
  Math.NumberTheory.exists_finset_primes_modEq_card hq h N n s

example : (∀ s : Finset ℕ, ∃ p, p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q]) ↔
    q ≠ 0 ∧ a.Coprime q :=
  Math.NumberTheory.forall_finset_exists_prime_modEq_iff

example (a : ℕ) : Set.Finite {p : ℕ | p.Prime ∧ p ≡ a [MOD 0]} := by
  classical
  simpa using (Math.NumberTheory.infinite_primes_modEq_iff (a := a) (q := 0)).not.mpr
    (by simp)

example (a : ℕ) : Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD 1]} :=
  Math.NumberTheory.infinite_primes_modEq_iff.mpr ⟨by decide, Nat.coprime_one_right a⟩

example : Set.Infinite {p : ℕ | p.Prime ∧ p ≡ 5 [MOD 6]} :=
  Math.NumberTheory.infinite_primes_modEq_iff.mpr (by decide)

example {p : ℕ} : (p.Prime ∧ p ≡ 3 [MOD 6]) ↔ p = 3 := by
  constructor
  · intro h
    simpa using Math.NumberTheory.prime_eq_gcd_of_not_coprime (by decide) h.1 h.2
  · rintro rfl
    exact ⟨by decide, by decide⟩

example : ¬ ∃ p : ℕ, p.Prime ∧ p ≡ 4 [MOD 6] := by
  rintro ⟨p, hp, hm⟩
  have h : p = 2 := by
    simpa using Math.NumberTheory.prime_eq_gcd_of_not_coprime (by decide) hp hm
  subst p
  norm_num [Nat.ModEq] at hm
