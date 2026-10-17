namespace Math.Logic

universe u

variable {P Q R : Prop}

/-- truth has a proof. -/
theorem truth : True := True.intro

/-- a proposition implies itself. -/
theorem identity (h : P) : P := h

/-- implication is transitive. -/
theorem implies_trans (hPQ : P → Q) (hQR : Q → R) : P → R :=
  fun h => hQR (hPQ h)

/-- falsehood implies every proposition. -/
theorem false_elim (h : False) : P := False.elim h

/-- conjunction is commutative. -/
theorem and_comm : P ∧ Q ↔ Q ∧ P :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- conjunction is associative. -/
theorem and_assoc : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
  ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- disjunction is commutative. -/
theorem or_comm : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h

/-- disjunction is associative. -/
theorem or_assoc : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  · intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h

/-- conjunction distributes over disjunction. -/
theorem and_or_distrib : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h
    cases h.2 with
    | inl hQ => exact Or.inl ⟨h.1, hQ⟩
    | inr hR => exact Or.inr ⟨h.1, hR⟩
  · intro h
    cases h with
    | inl h => exact ⟨h.1, Or.inl h.2⟩
    | inr h => exact ⟨h.1, Or.inr h.2⟩

/-- a proposition and its negation imply falsehood. -/
theorem noncontradiction : ¬ (P ∧ ¬ P) := fun h => h.2 h.1

/-- every proposition implies its double negation. -/
theorem double_neg_intro (h : P) : ¬ ¬ P := fun hn => hn h

/-- implication reverses under negation. -/
theorem contraposition (h : P → Q) : ¬ Q → ¬ P := fun hn hp => hn (h hp)

/-- a negated disjunction is a conjunction of negations. -/
theorem not_or : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
  ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
   fun h hpq => hpq.elim h.1 h.2⟩

/-- universal quantification distributes over conjunction. -/
theorem forall_and {α : Sort u} {p q : α → Prop} :
    (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩,
   fun h x => ⟨h.1 x, h.2 x⟩⟩

/-- implication transports an existential witness. -/
theorem exists_map {α : Sort u} {p q : α → Prop}
    (h : ∀ x, p x → q x) : (∃ x, p x) → ∃ x, q x := by
  intro hex
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, h x hx⟩

end Math.Logic
