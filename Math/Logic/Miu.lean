module

public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Basic
public import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace Math.Miu

inductive Symbol where
  | M | I | U
  deriving DecidableEq

abbrev Word := List Symbol

open Symbol

/-- derivability follows the exact four rules and initial word of miu.mm. -/
inductive Derivable : Word → Prop where
  | ax : Derivable [M, I]
  | I_ (x : Word) : Derivable (x ++ [I]) → Derivable (x ++ [I, U])
  | II (x : Word) : Derivable (M :: x) → Derivable (M :: (x ++ x))
  | III (x y : Word) : Derivable (x ++ [I, I, I] ++ y) → Derivable (x ++ [U] ++ y)
  | IV (x y : Word) : Derivable (x ++ [U, U] ++ y) → Derivable (x ++ y)

/-- the number of i symbols in a word. -/
def countI (word : Word) : ℕ := word.count I

/-- the number of i symbols in a derivable word is nonzero modulo three. -/
theorem countI_mod_three {word : Word} (h : Derivable word) : countI word % 3 ≠ 0 := by
  induction h with
  | ax => decide
  | I_ x _ ih => simpa [countI] using ih
  | II x _ ih => simp [countI] at *; omega
  | III x y _ ih => simp [countI] at *; omega
  | IV x y _ ih => simpa [countI] using ih

/-- the target word mu is not derivable. -/
theorem mu_not_derivable : ¬Derivable [M, U] := by
  intro h
  have invariant := countI_mod_three h
  simp [countI] at invariant

/-- the native theorem follows the same seven logical rule applications. -/
theorem theorem1 : Derivable [M, U, I, I, U] := by
  have h1 : Derivable [M, I, I] := .II [I] .ax
  have h2 : Derivable [M, I, I, I, I] := .II [I, I] h1
  have h3 : Derivable [M, I, I, I, I, U] := .I_ [M, I, I, I] h2
  have h4 : Derivable [M, U, I, U] := .III [M] [I, U] h3
  have h5 : Derivable [M, U, I, U, U, I, U] := .II [U, I, U] h4
  exact .IV [M, U, I] [I, U] h5

/-- a word with an initial m and a prescribed number of i symbols. -/
def pureI (n : ℕ) : Word := M :: List.replicate n I

/-- repeated duplication constructs every power-of-two pure word. -/
theorem pure_pow_two (n : ℕ) : Derivable (pureI (2 ^ n)) := by
  induction n with
  | zero => exact .ax
  | succ n ih =>
    have h := Derivable.II (List.replicate (2 ^ n) I) ih
    simpa [pureI, Nat.pow_succ, Nat.mul_two] using h

/-- the rules can delete three i symbols from a pure word. -/
theorem pure_drop_three (n : ℕ) (h : Derivable (pureI (n + 3))) :
    Derivable (pureI n) := by
  have h0 : Derivable ((M :: List.replicate (n + 2) I) ++ [I]) := by
    simpa [pureI, List.replicate_add, List.append_assoc] using h
  have h1 := Derivable.I_ (M :: List.replicate (n + 2) I) h0
  have h2 : Derivable ((M :: List.replicate n I) ++ [I, I, I] ++ [U]) := by
    simpa [List.replicate_add, List.append_assoc] using h1
  have h3 := Derivable.III (M :: List.replicate n I) [U] h2
  have h4 : Derivable ((M :: List.replicate n I) ++ [U, U] ++ []) := by
    simpa [List.append_assoc] using h3
  simpa [pureI] using Derivable.IV (M :: List.replicate n I) [] h4

/-- pure words reduce to every smaller count in the same residue class. -/
theorem pure_reduce (a b : ℕ) (hab : a ≤ b) (hmod : a % 3 = b % 3)
    (h : Derivable (pureI b)) : Derivable (pureI a) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + 3 * k := ⟨(b - a) / 3, by omega⟩
  have reduce : ∀ k, Derivable (pureI (a + 3 * k)) → Derivable (pureI a) := by
    intro k
    induction k with
    | zero => intro hk; simpa using hk
    | succ k ih =>
      intro hk
      apply ih
      apply pure_drop_three (a + 3 * k)
      simpa [Nat.mul_add, Nat.add_assoc] using hk
  exact reduce k h

/-- even powers of two have residue one modulo three. -/
theorem pow_two_even_mod_three (n : ℕ) : 2 ^ (2 * n) % 3 = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  simp

/-- odd powers of two have residue two modulo three. -/
theorem pow_two_odd_mod_three (n : ℕ) : 2 ^ (2 * n + 1) % 3 = 2 := by
  rw [Nat.pow_succ, Nat.mul_mod, pow_two_even_mod_three]

/-- every positive pure count not divisible by three is derivable. -/
theorem pure_of_mod_three (n : ℕ) (hn : n % 3 ≠ 0) : Derivable (pureI n) := by
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h
  · apply pure_reduce n (2 ^ (2 * n))
    · have bound : 2 * n < 2 ^ (2 * n) := Nat.lt_two_pow_self
      omega
    · rw [h, pow_two_even_mod_three]
    · exact pure_pow_two (2 * n)
  · apply pure_reduce n (2 ^ (2 * n + 1))
    · have bound : 2 * n + 1 < 2 ^ (2 * n + 1) := Nat.lt_two_pow_self
      omega
    · rw [h, pow_two_odd_mod_three]
    · exact pure_pow_two (2 * n + 1)

/-- the pure i count needed to realize a word by replacing triples with u. -/
def expansionCost (word : Word) : ℕ :=
  word.foldr (fun symbol total => match symbol with
    | M => total
    | I => 1 + total
    | U => 3 + total) 0

/-- expansion preserves the i count modulo three. -/
theorem expansionCost_mod_three (word : Word) : expansionCost word % 3 = countI word % 3 := by
  induction word with
  | nil => rfl
  | cons a xs ih => cases a <;> simp [expansionCost, countI] at * <;> omega

/-- every body without m symbols can be realized from its expanded i string. -/
theorem realize_body : ∀ word : Word, (∀ a ∈ word, a ≠ M) → ∀ leftWord rightWord : Word,
    Derivable (leftWord ++ List.replicate (expansionCost word) I ++ rightWord) →
      Derivable (leftWord ++ word ++ rightWord) := by
  intro word
  induction word with
  | nil =>
    intro _ leftWord rightWord h
    simpa [expansionCost] using h
  | cons a xs ih =>
    intro hm leftWord rightWord h
    have tail : ∀ b ∈ xs, b ≠ M := fun b hb => hm b (by simp [hb])
    cases a with
    | M => exact (hm M (by simp) rfl).elim
    | I =>
      have hp : Derivable ((leftWord ++ [I]) ++ List.replicate (expansionCost xs) I ++ rightWord) := by
        simpa [expansionCost, List.replicate_add, List.append_assoc] using h
      simpa [List.append_assoc] using ih tail (leftWord ++ [I]) rightWord hp
    | U =>
      have hp : Derivable (leftWord ++ [I, I, I] ++
          (List.replicate (expansionCost xs) I ++ rightWord)) := by
        simpa [expansionCost, List.replicate_add, List.append_assoc] using h
      have hu := Derivable.III leftWord (List.replicate (expansionCost xs) I ++ rightWord) hp
      have hq : Derivable ((leftWord ++ [U]) ++ List.replicate (expansionCost xs) I ++ rightWord) := by
        simpa [List.append_assoc] using hu
      simpa [List.append_assoc] using ih tail (leftWord ++ [U]) rightWord hq

/-- a valid body with nonzero i count modulo three is derivable after m. -/
theorem body_of_mod_three (word : Word) (hm : ∀ a ∈ word, a ≠ M)
    (hi : countI word % 3 ≠ 0) : Derivable (M :: word) := by
  have hp := pure_of_mod_three (expansionCost word) (by rwa [expansionCost_mod_three])
  have h : Derivable ([M] ++ List.replicate (expansionCost word) I ++ []) := by
    simpa [pureI] using hp
  simpa using realize_body word hm [M] [] h

/-- the number of m symbols in a word. -/
def countM (word : Word) : ℕ := word.count M

/-- every derivable word contains exactly one m symbol. -/
theorem countM_eq_one {word : Word} (h : Derivable word) : countM word = 1 := by
  induction h with
  | ax => decide
  | I_ x _ ih => simpa [countM] using ih
  | II x _ ih => simp [countM] at *; omega
  | III x y _ ih => simpa [countM] using ih
  | IV x y _ ih => simpa [countM] using ih

/-- every derivable word starts with m. -/
theorem head_eq_M {word : Word} (h : Derivable word) : word.head? = some M := by
  induction h with
  | ax => rfl
  | I_ x _ ih => cases x with
    | nil => simp at ih
    | cons a xs => simpa using ih
  | II => rfl
  | III x y _ ih => cases x with
    | nil => simp at ih
    | cons a xs => simpa using ih
  | IV x y _ ih => cases x with
    | nil => simp at ih
    | cons a xs => simpa using ih

/-- derivability is characterized by the first symbol and two symbol counts. -/
theorem derivable_iff (word : Word) : Derivable word ↔
    word.head? = some M ∧ countM word = 1 ∧ countI word % 3 ≠ 0 := by
  constructor
  · intro h
    exact ⟨head_eq_M h, countM_eq_one h, countI_mod_three h⟩
  · rintro ⟨head, hm, hi⟩
    cases word with
    | nil => simp at head
    | cons a xs =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst a
      have count : xs.count M = 0 := by simpa [countM] using hm
      have absent : M ∉ xs := List.count_eq_zero.mp count
      apply body_of_mod_three xs
      · intro a ha eq
        exact absent (eq ▸ ha)
      · simpa [countI] using hi

/-- the complete criterion gives a decision procedure for derivability. -/
instance : DecidablePred Derivable := fun word =>
  decidable_of_iff
    (word.head? = some M ∧ countM word = 1 ∧ countI word % 3 ≠ 0)
    (derivable_iff word).symm


end Math.Miu
