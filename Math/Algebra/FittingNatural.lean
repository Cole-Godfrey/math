module

public import Math.Algebra.FittingFinite

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace Math.LinearAlgebra

open Module LinearMap

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- a linear intertwiner respects every natural power of its two operators. -/
theorem intertwines_pow {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    {f : Module.End R M} {g : Module.End R N} (h : M →ₗ[R] N)
    (hh : h.comp f = g.comp h) (n : ℕ) (x : M) :
    h ((f ^ n) x) = (g ^ n) (h x) := by
  have hc : Function.Semiconj h f g := fun y => congrArg (fun u : M →ₗ[R] N => u y) hh
  simpa only [Module.End.pow_apply] using hc.iterate_right n x

/-- an intertwiner sends the bounded kernel into the target bounded kernel. -/
theorem maps_fittingKer [FiniteDimensional K W]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W)
    (hh : h.comp f = g.comp h) (x : V) (hx : x ∈ LinearMap.ker (f ^ finrank K V)) :
    h x ∈ LinearMap.ker (g ^ finrank K W) := by
  apply Module.End.ker_pow_le_ker_pow_finrank g (finrank K V)
  change (g ^ finrank K V) (h x) = 0
  rw [← intertwines_pow h hh]
  have hz : (f ^ finrank K V) x = 0 := hx
  rw [hz, map_zero]

/-- an intertwiner sends the stable image into the target bounded image. -/
theorem maps_fittingRange [FiniteDimensional K V]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W)
    (hh : h.comp f = g.comp h) (x : V) (hx : x ∈ LinearMap.range (f ^ finrank K V)) :
    h x ∈ LinearMap.range (g ^ finrank K W) := by
  have bound : finrank K V ≤ finrank K W + finrank K V := by omega
  rw [← range_pow_eq_finrank f bound] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(g ^ finrank K V) (h y), ?_⟩
  rw [← Module.End.mul_apply, ← pow_add]
  exact (intertwines_pow h hh (finrank K W + finrank K V) y).symm

/-- restrict an intertwiner to the bounded kernels with their different dimension bounds. -/
noncomputable def mapFittingKer [FiniteDimensional K W]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    LinearMap.ker (f ^ finrank K V) →ₗ[K] LinearMap.ker (g ^ finrank K W) :=
  (h.comp (LinearMap.ker (f ^ finrank K V)).subtype).codRestrict _
    (fun x => maps_fittingKer h hh x x.property)

/-- restrict an intertwiner to the stable images with their different dimension bounds. -/
noncomputable def mapFittingRange [FiniteDimensional K V]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    LinearMap.range (f ^ finrank K V) →ₗ[K] LinearMap.range (g ^ finrank K W) :=
  (h.comp (LinearMap.range (f ^ finrank K V)).subtype).codRestrict _
    (fun x => maps_fittingRange h hh x x.property)

/-- the decomposition is natural under arbitrary linear intertwiners. -/
theorem fittingEquiv_natural [FiniteDimensional K V] [FiniteDimensional K W]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W) (hh : h.comp f = g.comp h)
    (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    h (fittingEquiv f (x, y)) = fittingEquiv g (mapFittingKer h hh x, mapFittingRange h hh y) := by
  exact map_add h (x : V) (y : V)

/-- canonical projections are natural under intertwiners between different spaces. -/
theorem fittingProjection_natural [FiniteDimensional K V] [FiniteDimensional K W]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W) (hh : h.comp f = g.comp h)
    (x : V) : h (fittingProjection f x) = fittingProjection g (h x) := by
  obtain ⟨⟨v, w⟩, rfl⟩ := (fittingEquiv f).surjective x
  change h (fittingProjection f ((v : V) + (w : V))) =
    fittingProjection g (h ((v : V) + (w : V)))
  rw [fittingProjection_apply_add, map_add]
  exact (fittingProjection_apply_add g (mapFittingKer h hh v) (mapFittingRange h hh w)).symm

/-- the naturality equation also holds as an equality of linear maps. -/
theorem comp_fittingProjection [FiniteDimensional K V] [FiniteDimensional K W]
    {f : Module.End K V} {g : Module.End K W} (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    h.comp (fittingProjection f) = (fittingProjection g).comp h := by
  ext x
  exact fittingProjection_natural h hh x

end Math.LinearAlgebra
