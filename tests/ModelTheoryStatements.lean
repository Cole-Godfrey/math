module

import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.ModelTheory.Arithmetic.Presburger.Definability
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.Skolem
import Mathlib.ModelTheory.Ultraproducts
import all Mathlib.ModelTheory.Topology.Types

open FirstOrder Language Cardinal CategoryTheory

noncomputable section

universe u v w w'

section SyntaxAndSemantics

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
  {α β : Type*} {n : ℕ}

example (φ : L.BoundedFormula α n) (f : α → L.Term β) (x : β → M) (xs : Fin n → M) :
    (φ.subst f).Realize x xs ↔ φ.Realize (fun a => (f a).realize x) xs :=
  BoundedFormula.realize_subst

example (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  φ.toPrenex_isPrenex

example [Nonempty M] (φ : L.BoundedFormula α n) (x : α → M) (xs : Fin n → M) :
    φ.toPrenex.Realize x xs ↔ φ.Realize x xs :=
  φ.realize_toPrenex

example (S : L.Substructure M)
    (h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
      φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
        ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    S.IsElementary :=
  S.isElementary_of_exists h

end SyntaxAndSemantics

section Compactness

variable {L : Language.{u, v}} (T : L.Theory)

example : T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  Theory.isSatisfiable_iff_isFinitelySatisfiable

example (φ : L.Sentence) :
    T ⊨ᵇ φ ↔ ∃ T₀ : Finset L.Sentence, (T₀ : L.Theory) ⊆ T ∧ (T₀ : L.Theory) ⊨ᵇ φ :=
  Theory.models_iff_finset_models

example {ι : Type*} (M : ι → Type w) [∀ i, L.Structure (M i)] [∀ i, Nonempty (M i)]
    (U : Ultrafilter ι) (φ : L.Sentence) :
    (U : Filter ι).Product M ⊨ φ ↔ ∀ᶠ i : ι in U, M i ⊨ φ :=
  Ultraproduct.sentence_realize φ

end Compactness

section LowenheimSkolem

variable (L : Language.{u, v}) (M : Type w) [L.Structure M]

example (s : Set M) (κ : Cardinal.{w'}) (h₁ : ℵ₀ ≤ κ)
    (h₂ : Cardinal.lift.{w'} #s ≤ Cardinal.lift.{w} κ)
    (h₃ : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h₄ : Cardinal.lift.{w} κ ≤ Cardinal.lift.{w'} #M) :
    ∃ S : L.ElementarySubstructure M, s ⊆ S ∧ Cardinal.lift.{w'} #S = Cardinal.lift.{w} κ :=
  L.exists_elementarySubstructure_card_eq s κ h₁ h₂ h₃ h₄

example [Infinite M] (κ : Cardinal.{w'})
    (h₁ : Cardinal.lift.{w'} L.card ≤ Cardinal.lift.{max u v} κ)
    (h₂ : Cardinal.lift.{w'} #M ≤ Cardinal.lift.{w} κ) :
    ∃ N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ :=
  L.exists_elementaryEmbedding_card_eq_of_ge M κ h₁ h₂

end LowenheimSkolem

section CompleteTypes

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

example : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable :=
  Theory.CompleteType.nonempty_iff

example (p : T.CompleteType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p ∈ T.realizedTypes M α :=
  T.exists_modelType_is_realized_in p

example : CompactSpace (T.CompleteType α) := inferInstance

example : TotallySeparatedSpace (T.CompleteType α) := inferInstance

example (φ : L[[α]].Sentence) : IsClopen (T.typesWith φ) :=
  _root_.CompleteType.isClopen_typesWith φ

end CompleteTypes

section FraisseLimits

variable {L : Language.{u, v}} {K : Set (Bundled L.Structure)}
  {M N : Type w} [L.Structure M] [L.Structure N]
  [Countable (Σ n, L.Functions n)] [Countable M] [Countable N]

example (hM : L.IsFraisseLimit K M) (hN : L.IsFraisseLimit K N) :
    Nonempty (M ≃[L] N) :=
  hM.nonempty_equiv hN

end FraisseLimits

section AlgebraicallyClosedFields

example (p : ℕ) (hp : p.Prime ∨ p = 0) : (Theory.ACF p).IsComplete :=
  Field.ACF_isComplete hp

example (φ : Language.ring.Sentence) :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite {p : Nat.Primes | Theory.ACF p ⊨ᵇ φ} :=
  Field.ACF_zero_realize_iff_infinite_ACF_prime_realize

example (φ : Language.ring.Sentence) :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Finite {p : Nat.Primes | Theory.ACF p ⊨ᵇ φ}ᶜ :=
  Field.ACF_zero_realize_iff_finite_ACF_prime_not_realize

end AlgebraicallyClosedFields

section PresburgerArithmetic

variable {α : Type*} [Finite α] (A : Set ℕ)

example (s : Set (α → ℕ)) : A.Definable presburger s ↔ IsSemilinearSet s :=
  presburger.definable_iff_isSemilinearSet

example (s : Set ℕ) :
    A.Definable₁ presburger s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s :=
  presburger.definable₁_iff_ultimately_periodic

example : ¬A.Definable presburger {x : Fin 3 → ℕ | x 0 = x 1 * x 2} :=
  presburger.mul_not_definable

end PresburgerArithmetic
