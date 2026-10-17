import Mathlib.Computability.Halting
import Mathlib.Computability.Ackermann
import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.TuringDegree

example (n : ℕ) : ¬ComputablePred (fun c : Nat.Partrec.Code =>
    (Nat.Partrec.Code.eval c n).Dom) := ComputablePred.halting_problem n

example (n : ℕ) : REPred (fun c : Nat.Partrec.Code =>
    (Nat.Partrec.Code.eval c n).Dom) := ComputablePred.halting_problem_re n

example (n : ℕ) : ¬REPred (fun c : Nat.Partrec.Code =>
    ¬(Nat.Partrec.Code.eval c n).Dom) := ComputablePred.halting_problem_not_re n

example (C : Set Nat.Partrec.Code)
    (h : ∀ cf cg, Nat.Partrec.Code.eval cf = Nat.Partrec.Code.eval cg → (cf ∈ C ↔ cg ∈ C)) :
    (ComputablePred (fun c => c ∈ C)) ↔ C = ∅ ∨ C = Set.univ := ComputablePred.rice₂ C h

example : Computable₂ ack := computable₂_ack
example : ¬Primrec₂ ack := not_primrec₂_ack
example : Equivalence TuringEquivalent := TuringEquivalent.equivalence
example : PartialOrder TuringDegree := inferInstance

example (c : Turing.ToPartrec.Code) (v : List ℕ) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
      (Turing.PartrecToTM2.init c v) =
      Turing.PartrecToTM2.halt <$> Turing.ToPartrec.Code.eval c v :=
  Turing.PartrecToTM2.tr_eval c v

example (c : Turing.ToPartrec.Code) (k : Turing.PartrecToTM2.Cont') :
    @Turing.TM2.Supports _ _ _ _ ⟨Turing.PartrecToTM2.trNormal c k⟩
      Turing.PartrecToTM2.tr (Turing.PartrecToTM2.codeSupp c k) :=
  Turing.PartrecToTM2.tr_supports c k
