module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Unramified.LocalStructure

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Math.Geometry

universe u

variable {X Y Z S : Scheme.{u}}

/-- locally finite-type formally unramified morphisms are locally quasi-finite. -/
theorem locallyQuasiFinite_of_unramified (f : X ⟶ Y)
    [LocallyOfFiniteType f] [FormallyUnramified f] : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have hft := f.finiteType_appLE hU hV e
  have hun := f.formallyUnramified_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- proper étale morphisms are finite. -/
theorem finite_of_proper_etale (f : X ⟶ Y) [IsProper f] [Etale f] : IsFinite f := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_unramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- properness characterizes finiteness among étale morphisms. -/
theorem finite_iff_proper_of_etale (f : X ⟶ Y) [Etale f] : IsFinite f ↔ IsProper f := by
  constructor
  · intro hf
    let := hf
    infer_instance
  · intro hf
    let := hf
    exact finite_of_proper_etale f

/-- proper smooth morphisms of relative dimension zero are finite. -/
theorem finite_of_proper_smooth_zero (f : X ⟶ Y)
    [IsProper f] [SmoothOfRelativeDimension 0 f] : IsFinite f := by
  have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
  exact finite_of_proper_etale f

/-- finite étale morphisms retain both properties explicitly. -/
def FiniteEtale (f : X ⟶ Y) : Prop := IsFinite f ∧ Etale f

/-- finite étale morphisms are exactly proper smooth morphisms of relative dimension zero. -/
theorem finiteEtale_iff_proper_smooth_zero (f : X ⟶ Y) :
    FiniteEtale f ↔ IsProper f ∧ SmoothOfRelativeDimension 0 f := by
  constructor
  · rintro ⟨hf, he⟩
    let := hf
    let := he
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hp, hs⟩
    let := hp
    let := hs
    exact ⟨finite_of_proper_smooth_zero f,
      (Etale.iff_smoothOfRelativeDimension_zero f).mpr hs⟩

/-- identity morphisms are finite étale. -/
theorem finiteEtale_id (X : Scheme.{u}) : FiniteEtale (𝟙 X) := by
  exact ⟨inferInstance, inferInstance⟩

/-- finite étale morphisms are closed under composition. -/
theorem finiteEtale_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FiniteEtale f) (hg : FiniteEtale g) : FiniteEtale (f ≫ g) := by
  let := hf.1
  let := hf.2
  let := hg.1
  let := hg.2
  exact ⟨inferInstance, inferInstance⟩

/-- the first projection preserves the finite étale property of the second morphism. -/
theorem finiteEtale_pullback_fst (f : X ⟶ S) (g : Y ⟶ S) (hg : FiniteEtale g) :
    FiniteEtale (pullback.fst f g) := by
  let := hg.1
  let := hg.2
  exact ⟨inferInstance, inferInstance⟩

/-- the second projection preserves the finite étale property of the first morphism. -/
theorem finiteEtale_pullback_snd (f : X ⟶ S) (g : Y ⟶ S) (hf : FiniteEtale f) :
    FiniteEtale (pullback.snd f g) := by
  let := hf.1
  let := hf.2
  exact ⟨inferInstance, inferInstance⟩

/-- restriction over an open subset preserves finite étale morphisms. -/
theorem finiteEtale_restrict (f : X ⟶ Y) (hf : FiniteEtale f) (V : Y.Opens) :
    FiniteEtale (f ∣_ V) := by
  let := hf.1
  let := hf.2
  exact ⟨inferInstance, inferInstance⟩

/-- finite étale composites cancel separated unramified morphisms locally of finite type. -/
theorem finiteEtale_of_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated g] [LocallyOfFiniteType g] [FormallyUnramified g]
    (h : FiniteEtale (f ≫ g)) : FiniteEtale f := by
  let := h.1
  let := h.2
  exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

/-- composition with a finite étale morphism detects finite étale morphisms. -/
theorem finiteEtale_comp_iff (f : X ⟶ Y) (g : Y ⟶ Z) (hg : FiniteEtale g) :
    FiniteEtale (f ≫ g) ↔ FiniteEtale f := by
  let := hg.1
  let := hg.2
  exact ⟨finiteEtale_of_comp f g, fun hf => finiteEtale_comp f g hf hg⟩

/-- the fibres of a proper étale morphism are finite sets. -/
theorem finite_fibres_of_proper_etale (f : X ⟶ Y) [IsProper f] [Etale f] (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_unramified f
  exact f.finite_preimage_singleton y

/-- proper étale morphisms have finite preimages of finite sets. -/
theorem finite_preimage_of_proper_etale (f : X ⟶ Y) [IsProper f] [Etale f]
    {s : Set Y} (hs : s.Finite) : (f ⁻¹' s).Finite := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_unramified f
  exact f.finite_preimage hs

/-- the point fibres of an étale morphism are discrete. -/
theorem discrete_fibres_of_etale (f : X ⟶ Y) [Etale f] (y : Y) :
    _root_.IsDiscrete (f ⁻¹' {y}) := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_unramified f
  exact f.isDiscrete_preimage_singleton y

end Math.Geometry
