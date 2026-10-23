import Math.Algebra.FittingNatural

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Module Math.LinearAlgebra

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

example {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : Module.End R M) (g : Module.End R N)
    (h : M →ₗ[R] N) (hh : h.comp f = g.comp h) (n : ℕ) (x : M) :
    h ((f ^ n) x) = (g ^ n) (h x) := intertwines_pow h hh n x

example [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) (x : V)
    (hx : x ∈ LinearMap.ker (f ^ finrank K V)) :
    h x ∈ LinearMap.ker (g ^ finrank K W) := maps_fittingKer h hh x hx

example [FiniteDimensional K V] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) (x : V)
    (hx : x ∈ LinearMap.range (f ^ finrank K V)) :
    h x ∈ LinearMap.range (g ^ finrank K W) := maps_fittingRange h hh x hx

example [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    LinearMap.ker (f ^ finrank K V) →ₗ[K] LinearMap.ker (g ^ finrank K W) := mapFittingKer h hh

example [FiniteDimensional K V] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    LinearMap.range (f ^ finrank K V) →ₗ[K] LinearMap.range (g ^ finrank K W) := mapFittingRange h hh

example [FiniteDimensional K V] [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h)
    (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    h (fittingEquiv f (x, y)) = fittingEquiv g (mapFittingKer h hh x, mapFittingRange h hh y) :=
  fittingEquiv_natural h hh x y

example [FiniteDimensional K V] [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) (x : V) :
    h (fittingProjection f x) = fittingProjection g (h x) := fittingProjection_natural h hh x

example [FiniteDimensional K V] [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) :
    h.comp (fittingProjection f) = (fittingProjection g).comp h := comp_fittingProjection h hh

example [FiniteDimensional K W] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) (hv : finrank K V = 2) (hw : finrank K W = 3)
    (x : V) (hx : x ∈ LinearMap.ker (f ^ 2)) : h x ∈ LinearMap.ker (g ^ 3) := by
  have bounded : x ∈ LinearMap.ker (f ^ finrank K V) := by simpa only [hv] using hx
  simpa only [hw] using maps_fittingKer h hh x bounded

example [FiniteDimensional K V] (f : Module.End K V) (g : Module.End K W)
    (h : V →ₗ[K] W) (hh : h.comp f = g.comp h) (hv : finrank K V = 2) (hw : finrank K W = 3)
    (x : V) (hx : x ∈ LinearMap.range (f ^ 2)) : h x ∈ LinearMap.range (g ^ 3) := by
  have bounded : x ∈ LinearMap.range (f ^ finrank K V) := by simpa only [hv] using hx
  simpa only [hw] using maps_fittingRange h hh x bounded
