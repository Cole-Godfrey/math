import Math.Logic.Miu

set_option autoImplicit false
set_option warningAsError true

open Math.Miu Math.Miu.Symbol

example (x : Word) : Derivable (x ++ [I]) → Derivable (x ++ [I, U]) := Derivable.I_ x
example (x : Word) : Derivable (M :: x) → Derivable (M :: (x ++ x)) := Derivable.II x
example (x y : Word) : Derivable (x ++ [I, I, I] ++ y) → Derivable (x ++ [U] ++ y) :=
  Derivable.III x y
example (x y : Word) : Derivable (x ++ [U, U] ++ y) → Derivable (x ++ y) := Derivable.IV x y
example {word : Word} (h : Derivable word) : countI word % 3 ≠ 0 := countI_mod_three h
example {word : Word} (h : Derivable word) : countM word = 1 := countM_eq_one h
example {word : Word} (h : Derivable word) : word.head? = some M := head_eq_M h
example (n : ℕ) : Derivable (pureI (2 ^ n)) := pure_pow_two n
example (n : ℕ) (h : Derivable (pureI (n + 3))) : Derivable (pureI n) := pure_drop_three n h
example (a b : ℕ) (hab : a ≤ b) (hmod : a % 3 = b % 3) (h : Derivable (pureI b)) :
    Derivable (pureI a) := pure_reduce a b hab hmod h
example (n : ℕ) (h : n % 3 ≠ 0) : Derivable (pureI n) := pure_of_mod_three n h
example (word : Word) (hm : ∀ a ∈ word, a ≠ M) (hi : countI word % 3 ≠ 0) :
    Derivable (M :: word) := body_of_mod_three word hm hi
example (word : Word) : Derivable word ↔
    word.head? = some M ∧ countM word = 1 ∧ countI word % 3 ≠ 0 := derivable_iff word
example : DecidablePred Derivable := inferInstance
example : ¬Derivable [M, U] := mu_not_derivable
example : Derivable [M, U, I, I, U] := theorem1

example : Derivable [M, I] := by decide
example : Derivable [M, U, I, I, U] := by decide
example : ¬Derivable [M, U] := by decide
example : ¬Derivable [M, M, I] := by decide
example : ¬Derivable [I, M] := by decide
example : ¬Derivable [] := by decide
