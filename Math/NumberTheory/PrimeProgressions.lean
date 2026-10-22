module

public import Mathlib.NumberTheory.LSeries.PrimesInAP

set_option autoImplicit false
set_option warningAsError true

/-!
prime residue classes are infinite exactly for nonzero moduli and coprime residues.
noncoprime classes contain at most their common divisor with the modulus.
-/

@[expose] public section

namespace Math.NumberTheory

variable {a q p : ℕ}

/-- a prime in a noncoprime residue class must equal the common divisor. -/
theorem prime_eq_gcd_of_not_coprime (ha : ¬ a.Coprime q) (hp : p.Prime)
    (hmod : p ≡ a [MOD q]) : p = a.gcd q := by
  have hd : a.gcd q ∣ p :=
    (hmod.dvd_iff (Nat.gcd_dvd_right a q)).mpr (Nat.gcd_dvd_left a q)
  exact ((hp.eq_one_or_self_of_dvd _ hd).resolve_left
    (fun h => ha (Nat.coprime_iff_gcd_eq_one.mpr h))).symm

/-- a noncoprime residue class contains only finitely many primes. -/
theorem finite_primes_modEq_of_not_coprime (ha : ¬ a.Coprime q) :
    Set.Finite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} := by
  apply (Set.finite_singleton (a.gcd q)).subset
  intro p hp
  exact Set.mem_singleton_iff.mpr (prime_eq_gcd_of_not_coprime ha hp.1 hp.2)

/-- a residue class contains infinitely many primes exactly for a nonzero coprime modulus. -/
theorem infinite_primes_modEq_iff :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} ↔ q ≠ 0 ∧ a.Coprime q := by
  constructor
  · intro hi
    have hq : q ≠ 0 := by
      intro hq
      subst q
      apply hi
      apply (Set.finite_singleton a).subset
      intro p hp
      exact Set.mem_singleton_iff.mpr (Nat.modEq_zero_iff.mp hp.2)
    refine ⟨hq, ?_⟩
    by_contra ha
    exact hi (finite_primes_modEq_of_not_coprime ha)
  · rintro ⟨hq, ha⟩
    exact Nat.infinite_setOfPred_prime_and_modEq hq ha

/-- finite exclusions and a lower bound leave infinitely many primes in a coprime class. -/
theorem infinite_primes_modEq_above_avoiding_iff (N : ℕ) (s : Finset ℕ) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q] ∧ N < p ∧ p ∉ s} ↔
      q ≠ 0 ∧ a.Coprime q := by
  classical
  constructor
  · intro hi
    apply infinite_primes_modEq_iff.mp
    exact hi.mono (fun _ hp => ⟨hp.1, hp.2.1⟩)
  · intro h
    have hi := (infinite_primes_modEq_iff.mpr h).sdiff
      (s ∪ Finset.range (N + 1)).finite_toSet
    apply hi.mono
    intro p hp
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe, Finset.mem_union,
      Finset.mem_range, not_or] at hp
    exact ⟨hp.1.1, hp.1.2, by omega, hp.2.1⟩

/-- arbitrarily large primes in a coprime class avoid every given finite set. -/
theorem exists_prime_modEq_above_avoiding (hq : q ≠ 0) (ha : a.Coprime q)
    (N : ℕ) (s : Finset ℕ) : ∃ p, N < p ∧ p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q] := by
  obtain ⟨p, hp⟩ := (infinite_primes_modEq_above_avoiding_iff N s).mpr ⟨hq, ha⟩ |>.nonempty
  exact ⟨p, hp.2.2.1, hp.2.2.2, hp.1, hp.2.1⟩

/-- a coprime residue class supplies any finite number of distinct primes above a bound. -/
theorem exists_finset_primes_modEq_card (hq : q ≠ 0) (ha : a.Coprime q)
    (N n : ℕ) (s : Finset ℕ) :
    ∃ t : Finset ℕ, t.card = n ∧ ∀ p ∈ t, N < p ∧ p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q] := by
  classical
  obtain ⟨t, ht, hcard⟩ :=
    ((infinite_primes_modEq_above_avoiding_iff N s).mpr ⟨hq, ha⟩).exists_subset_card_eq n
  refine ⟨t, hcard, ?_⟩
  intro p hp
  have h := ht hp
  exact ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩

/-- avoiding every finite set of exceptions characterizes the infinite prime residue classes. -/
theorem forall_finset_exists_prime_modEq_iff :
    (∀ s : Finset ℕ, ∃ p, p ∉ s ∧ p.Prime ∧ p ≡ a [MOD q]) ↔
      q ≠ 0 ∧ a.Coprime q := by
  classical
  rw [← infinite_primes_modEq_iff]
  constructor
  · intro h hf
    obtain ⟨p, hp, hprime, hmod⟩ := h hf.toFinset
    exact hp (hf.mem_toFinset.mpr ⟨hprime, hmod⟩)
  · intro hi s
    obtain ⟨p, hp, hnot⟩ := hi.exists_notMem_finset s
    exact ⟨p, hnot, hp.1, hp.2⟩

end Math.NumberTheory
