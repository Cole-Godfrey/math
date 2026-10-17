import Math.Logic.Basic

namespace Math.Logic.Classical

variable {P Q : Prop}

/-- every proposition is true or false under classical logic. -/
theorem excluded_middle (P : Prop) : P ∨ ¬ P := Classical.em P

/-- double negation implies the proposition under classical logic. -/
theorem double_neg_elim (h : ¬ ¬ P) : P := by
  cases excluded_middle P with
  | inl hp => exact hp
  | inr hn => exact False.elim (h hn)

/-- a negated conjunction gives a disjunction of negations under classical logic. -/
theorem not_and : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro h
    cases excluded_middle P with
    | inl hp => exact Or.inr (fun hq => h ⟨hp, hq⟩)
    | inr hn => exact Or.inl hn
  · intro h hpq
    exact h.elim (fun hn => hn hpq.1) (fun hn => hn hpq.2)

end Math.Logic.Classical
