module

import Math.Geometry.FiniteEtale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Sites.Etale

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

example : CommRingCat.{u}ᵒᵖ ⥤ Scheme.{u} := Scheme.Spec

example : AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ := AffineScheme.equivCommRingCat

example (R : CommRingCat.{u}) : IsAffine (Spec R) := inferInstance

example (X : Scheme.{u}) [IsAffine X] : X ≅ Spec Γ(X, ⊤) := X.isoSpec

example (R : CommRingCat.{u}) : IsNoetherian (Spec R) ↔ IsNoetherianRing R :=
  isNoetherian_Spec

example (X : Scheme.{u}) [IsNoetherian X] : (irreducibleComponents X).Finite :=
  finite_irreducibleComponents_of_isNoetherian

example (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType

example (f : X ⟶ Y) : IsFinite f ↔ IsProper f ∧ IsAffineHom f :=
  IsFinite.iff_isProper_and_isAffineHom

example (f : X ⟶ Y) : IsFinite f ↔ IsProper f ∧ LocallyQuasiFinite f :=
  IsFinite.iff_isProper_and_locallyQuasiFinite f

example (f : X ⟶ Y) : IsClosedImmersion f ↔ IsProper f ∧ Mono f :=
  IsClosedImmersion.iff_isProper_and_mono f

example (f : X ⟶ Y) : Etale f ↔ SmoothOfRelativeDimension 0 f :=
  Etale.iff_smoothOfRelativeDimension_zero f

example (f : X ⟶ Y) :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f :=
  Etale.iff_flat_and_formallyUnramified

example (f : X ⟶ Y) (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : Etale f :=
  Etale.of_comp f g

example (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper (f ≫ g)] [IsSeparated g] : IsProper f :=
  IsProper.of_comp f g

example (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (h : ValuativeCriterion f) : IsProper f :=
  IsProper.of_valuativeCriterion f h

example : @IsProper =
    ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType :=
  IsProper.eq_valuativeCriterion

example : @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated :=
  IsSeparated.eq_valuativeCriterion

example (f : X ⟶ Y) (y : Y) : f.fiber y ≃ₜ f ⁻¹' {y} := f.fiberHomeo y

example (f : X ⟶ Y) (y : Y) :
    f.fiberι y ≫ f = f.fiberToSpecResidueField y ≫ Y.fromSpecResidueField y :=
  f.fiber_fac y

example (f : X ⟶ Y) [QuasiCompact f] (y : Y) : IsCompact (f ⁻¹' {y}) :=
  f.isCompact_preimage_singleton y

example (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    f.toNormalization ≫ f.fromNormalization = f :=
  f.toNormalization_fromNormalization

example (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    IsIntegralHom f.fromNormalization := inferInstance

example (f : X ⟶ Y) [IsIntegralHom f] : IsIso f.toNormalization := inferInstance

example (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField :=
  functionField_isFractionRing_of_affine R

example (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField :=
  functionField_isFractionRing_of_isAffineOpen X U hU

example (X : Scheme.{u}) : Abelian X.Modules := inferInstance

example : Scheme.zariskiTopology ≤ Scheme.etaleTopology :=
  Scheme.zariskiTopology_le_etaleTopology

example (X : Scheme.{u}) : GrothendieckTopology X.Etale := X.smallEtaleTopology

example {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsProper (Proj.toSpecZero 𝒜) := inferInstance

example {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    ValuativeCriterion.Existence (Proj.toSpecZero 𝒜) :=
  Proj.valuativeCriterion_existence 𝒜

example {K : Type u} [Field K] (G : Over (Spec (.of K))) [IsProper G.hom]
    [GeometricallyIntegral G.hom] [GrpObj G] : IsCommMonObj G :=
  isCommMonObj_of_isProper_of_geometricallyIntegral G

example {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : AddCommGroup W.Point :=
  inferInstance

example {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) (P Q R : W.Point) :
    (P + Q) + R = P + (Q + R) := add_assoc P Q R

example {K : Type u} [Field K] [NumberField K] (W : WeierstrassCurve K) :
    ArithmeticFunction ℤ := W.LFunction

example {K : Type u} [Field K] [NumberField K] (W : WeierstrassCurve K) (s : ℂ) :
    W.LSeries s = LSeries ((↑) ∘ W.LFunction) s := rfl
