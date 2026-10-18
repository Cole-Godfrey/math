import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Topology.Homotopy.HomotopyGroup

open CategoryTheory Limits AlgebraicTopology
open unitInterval
open scoped ContinuousMap Topology.Homotopy

noncomputable section

section HomotopyGroups

variable {X : Type*} [TopologicalSpace X]

example (x y : X) (p : Path x y) : FundamentalGroup X x ≃* FundamentalGroup X y :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath p

example [PathConnectedSpace X] (x y : X) : FundamentalGroup X x ≃* FundamentalGroup X y :=
  FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y

example (x : X) : HomotopyGroup (Fin 0) X x ≃ ZerothHomotopy X :=
  HomotopyGroup.pi0EquivZerothHomotopy

example (x : X) : HomotopyGroup (Fin 1) X x ≃* FundamentalGroup X x :=
  HomotopyGroup.pi1MulEquivFundamentalGroup

example (n : ℕ) (x : X) : Group (HomotopyGroup (Fin (n + 1)) X x) := inferInstance

example (n : ℕ) (x : X) : CommGroup (HomotopyGroup (Fin (n + 2)) X x) := inferInstance

example [ContractibleSpace X] : SimplyConnectedSpace X := inferInstance

example [SimplyConnectedSpace X] (x : X) : Subsingleton (FundamentalGroup X x) :=
  inferInstance

example [SimplyConnectedSpace X] {x y : X} (p q : Path x y) : Path.Homotopic p q :=
  SimplyConnectedSpace.paths_homotopic p q

end HomotopyGroups

section CoveringSpaces

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  {G : Type*} [Group G] [MulAction G E]

example [SimplyConnectedSpace E] (hp : IsQuotientCoveringMap p G)
    {x : X} (e : p ⁻¹' {x}) : FundamentalGroup X x ≃* Gᵐᵒᵖ :=
  hp.fundamentalGroupEquiv e

example (p : E → X) : Group (deck p) := inferInstance

example (h : deck p) (e : E) : p (h • e) = p e := deck.proj_smul h e

end CoveringSpaces

section Circle

variable {p : ℝ} [Fact (0 < p)]

example (x : AddCircle p) : FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  AddCircle.windingNumberIso x

example (x : ℝ) (n : ℤ) :
    AddCircle.windingNumber (x := (x : AddCircle p)) (.of (.mk (AddCircle.zsmulLoop p x n))) = n :=
  AddCircle.windingNumber_zsmulLoop x n

example {x : AddCircle p} (γ : Path x x) (f : C(I, ℝ)) (hf : (↑) ∘ f = γ) :
    (AddCircle.windingNumber (.of (.mk γ)) : ℝ) = (f 1 - f 0) / p :=
  AddCircle.windingNumber_eq_div γ f hf

end Circle

universe w v u

section SingularHomology

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

example : SSet.toTop.{w} ⊣ TopCat.toSSet.{w} := sSetTopAdj

example (R : C) (X : TopCat.{w}) : ChainComplex C ℕ :=
  ((singularChainComplexFunctor C).obj R).obj X

example [CategoryWithHomology C] (R : C) (X : TopCat.{w}) :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) => R) :=
  TopCat.singularHomology₀Iso X R

example [CategoryWithHomology C] (R : C) (X : TopCat.{w}) [PathConnectedSpace X] :
    IsIso (X.singularHomology₀ε R) := inferInstance

example [CategoryWithHomology C] (n : ℕ) (R : C) (X : TopCat.{w})
    [TotallyDisconnectedSpace X] (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R X hn

variable {X Y : TopCat.{w}} {f g : X ⟶ Y}

example (H : TopCat.Homotopy f g) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  H.singularChainComplexFunctorObjMap R

example [CategoryWithHomology C] (H : TopCat.Homotopy f g) (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).map f = ((singularHomologyFunctor C n).obj R).map g :=
  H.congr_homologyMap_singularChainComplexFunctor R n

example [CategoryWithHomology C] {K L : ChainComplex C ℕ} {f g : K ⟶ L}
    (H : _root_.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n :=
  H.homologyMap_eq n

end SingularHomology
