module

public import Math.Geometry.FiniteEtale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X Y Z S : Scheme.{u}}

example (f : X ⟶ Y) [LocallyOfFiniteType f] [FormallyUnramified f] :
    LocallyQuasiFinite f :=
  Math.Geometry.locallyQuasiFinite_of_unramified f

example (f : X ⟶ Y) [IsProper f] [Etale f] : IsFinite f :=
  Math.Geometry.finite_of_proper_etale f

example (f : X ⟶ Y) [Etale f] : IsFinite f ↔ IsProper f :=
  Math.Geometry.finite_iff_proper_of_etale f

example (f : X ⟶ Y) [IsProper f] [SmoothOfRelativeDimension 0 f] : IsFinite f :=
  Math.Geometry.finite_of_proper_smooth_zero f

example (f : X ⟶ Y) :
    (IsFinite f ∧ Etale f) ↔ IsProper f ∧ SmoothOfRelativeDimension 0 f :=
  Math.Geometry.finiteEtale_iff_proper_smooth_zero f

example (X : Scheme.{u}) : IsFinite (𝟙 X) ∧ Etale (𝟙 X) :=
  Math.Geometry.finiteEtale_id X

example (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsFinite f ∧ Etale f) (hg : IsFinite g ∧ Etale g) :
    IsFinite (f ≫ g) ∧ Etale (f ≫ g) :=
  Math.Geometry.finiteEtale_comp f g hf hg

example (f : X ⟶ S) (g : Y ⟶ S) (hg : IsFinite g ∧ Etale g) :
    IsFinite (pullback.fst f g) ∧ Etale (pullback.fst f g) :=
  Math.Geometry.finiteEtale_pullback_fst f g hg

example (f : X ⟶ S) (g : Y ⟶ S) (hf : IsFinite f ∧ Etale f) :
    IsFinite (pullback.snd f g) ∧ Etale (pullback.snd f g) :=
  Math.Geometry.finiteEtale_pullback_snd f g hf

example (f : X ⟶ Y) (hf : IsFinite f ∧ Etale f) (V : Y.Opens) :
    IsFinite (f ∣_ V) ∧ Etale (f ∣_ V) :=
  Math.Geometry.finiteEtale_restrict f hf V

example (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated g] [LocallyOfFiniteType g]
    [FormallyUnramified g] (h : IsFinite (f ≫ g) ∧ Etale (f ≫ g)) : IsFinite f ∧ Etale f :=
  Math.Geometry.finiteEtale_of_comp f g h

example (f : X ⟶ Y) (g : Y ⟶ Z) (hg : IsFinite g ∧ Etale g) :
    (IsFinite (f ≫ g) ∧ Etale (f ≫ g)) ↔ IsFinite f ∧ Etale f :=
  Math.Geometry.finiteEtale_comp_iff f g hg

example (f : X ⟶ Y) [IsProper f] [Etale f] (y : Y) : (f ⁻¹' {y}).Finite :=
  Math.Geometry.finite_fibres_of_proper_etale f y

example (f : X ⟶ Y) [IsProper f] [Etale f] {s : Set Y} (hs : s.Finite) :
    (f ⁻¹' s).Finite :=
  Math.Geometry.finite_preimage_of_proper_etale f hs

example (f : X ⟶ Y) [Etale f] (y : Y) : _root_.IsDiscrete (f ⁻¹' {y}) :=
  Math.Geometry.discrete_fibres_of_etale f y
