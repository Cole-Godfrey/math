import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped BigOperators DirectSum MonoidAlgebra Classical

universe u

section Groups

variable {G : Type*} [Group G]

example (H : Subgroup G) : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H

example {X : Type*} [MulAction G X] (x : X) :
    MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

example {N : Subgroup G} [N.Normal] (h : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, Subgroup.IsComplement' N H :=
  Subgroup.exists_right_complement'_of_coprime h

example [IsFreeGroup G] (H : Subgroup G) : IsFreeGroup H := subgroupIsFreeOfIsFree H

example [Group.IsNilpotent G] : Group.IsSolvable G := inferInstance

example : Antitone (derivedSeries G) := derivedSeries_antitone G

example [Finite G] : Nat.card (Subgroup.center G) +
    ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier = Nat.card G :=
  Group.nat_card_center_add_sum_card_noncenter_eq_card G

example {N E : Type*} [Group N] [Group E] (S : GroupExtension N E G) (n : N) :
    S.rightHom (S.inl n) = 1 := S.rightHom_inl n

end Groups

section Abelian

variable (A : Type*) [AddCommGroup A]

example [AddGroup.FG A] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i))
      (e : ι → ℕ), Nonempty (A ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i)) :=
  AddCommGroup.equiv_free_prod_directSum_zmod A

example [Finite A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i))
      (e : ι → ℕ), Nonempty (A ≃+ ⨁ i : ι, ZMod (p i ^ e i)) :=
  AddCommGroup.equiv_directSum_zmod_of_finite A

end Abelian

example {α : Type*} [Fintype α] [DecidableEq α] (h : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup h

example {α : Type*} [Fintype α] [DecidableEq α] (h : Nat.card α ≤ 4) :
    Group.IsSolvable (alternatingGroup α) := alternatingGroup.isSolvable h

example : ¬Group.IsSolvable (Equiv.Perm (Fin 5)) := Equiv.Perm.not_isSolvable_fin_5

example {α : Type*} [Fintype α] [DecidableEq α] : Equiv.Perm α →* ℤˣ := Equiv.Perm.sign

section Coxeter

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

example (i : B) : cs.simple i ^ 2 = 1 := cs.simple_sq i

example (w : W) : cs.length w⁻¹ = cs.length w := cs.length_inv w

example (w v : W) : cs.length (w * v) ≤ cs.length w + cs.length v := cs.length_mul_le w v

example (w v : W) : cs.length (w * v) % 2 = (cs.length w + cs.length v) % 2 :=
  cs.length_mul_mod_two w v

end Coxeter

section GeneralRepresentations

variable {k G V W : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)

example : (Representation.linHom ρ σ).invariants ≃ₗ[k] Representation.IntertwiningMap ρ σ :=
  Representation.invariantsEquivIntertwiningMap ρ σ

example [Fintype G] [Invertible (Fintype.card G : k)] :
    LinearMap.IsProj ρ.invariants ρ.averageMap := Representation.isProj_averageMap ρ

end GeneralRepresentations

section Characters

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)

example (g h : G) : ρ.character (h * g * h⁻¹) = ρ.character g := ρ.char_conj g h

example [FiniteDimensional k V] : ρ.character 1 = Module.finrank k V := ρ.char_one

example [FiniteDimensional k V] [Finite G] (g : G) : IsIntegral ℤ (ρ.character g) :=
  ρ.isIntegral_character g

example [FiniteDimensional k V] [Fintype G] [Invertible (Nat.card G : k)] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g = Module.finrank k ρ.invariants :=
  ρ.card_inv_mul_sum_char_eq_finrank

example [FiniteDimensional k V] [FiniteDimensional k W] [Fintype G]
    [Invertible (Nat.card G : k)] :
    (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.character g⁻¹ =
      Module.finrank k (Representation.IntertwiningMap ρ σ) :=
  Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

example [FiniteDimensional k V] [FiniteDimensional k W] [Fintype G]
    [Invertible (Nat.card G : k)] [IsAlgClosed k]
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Representation.Equiv σ ρ) then (1 : k) else 0 :=
  Representation.char_orthonormal ρ σ

example [Finite G] [NeZero (Nat.card G : k)] : Representation.IsSemisimpleRepresentation ρ :=
  inferInstance

end Characters

example {k G V : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
    [AddCommGroup V] [Module k[G] V] (p : Submodule k[G] V) :
    ∃ q : Submodule k[G] V, IsCompl p q := MonoidAlgebra.Submodule.exists_isCompl p

example {k G : Type u} [CommRing k] [Group G] :
    Rep.{u} k G ≌ ModuleCat.{u} k[G] := Rep.equivalenceModuleMonoidAlgebra

example {k G : Type u} [CommRing k] [Group G] [Finite G] [IsDomain k] :
    G ≃* Aut (TannakaDuality.FiniteGroup.forget k G) := TannakaDuality.FiniteGroup.equiv k G

example {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S) (n : ℕ) :
    groupCohomology (Rep.coind S.subtype A) n ≅ groupCohomology A n :=
  groupCohomology.coindIso A n

example {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) (A : Rep k S) (n : ℕ) :
    groupHomology (Rep.ind S.subtype A) n ≅ groupHomology A n :=
  groupHomology.indIso S A n

example {k G : Type u} [CommRing k] [Group G] (A : Rep k G) :
    groupCohomology A 0 ≅ ModuleCat.of k A.ρ.invariants := groupCohomology.H0Iso A

example {k G : Type u} [CommRing k] [Group G] (A : Rep k G) :
    groupHomology A 0 ≅ (Rep.coinvariantsFunctor k G).obj A := groupHomology.H0Iso A

example {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : (L ≃ₐ[K] L) → Lˣ) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f :=
  groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf

example {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] {g : L ≃ₐ[K] L}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L} (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, (y : L) / g (y : L) = x := groupCohomology.exists_div_of_norm_eq_one hg hx

example {k A V : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k] :
    Function.Bijective (algebraMap k (Module.End A V)) :=
  IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k

example {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
    (ρ : ContRepresentation R G V) : Representation R G V := ρ.toRepresentation
