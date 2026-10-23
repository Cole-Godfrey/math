import Math.Algebra.FiniteAveraging

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped BigOperators
open Math.RepresentationTheory

section General

variable {k G V W : Type*} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)
  (f : Representation.IntertwiningMap ρ σ)

example : ρ.invariants →ₗ[k] σ.invariants := mapInvariants ρ σ f

example (v : ρ.invariants) : (mapInvariants ρ σ f v : W) = f v :=
  mapInvariants_coe ρ σ f v

example (hf : Function.Injective f) : Function.Injective (mapInvariants ρ σ f) :=
  mapInvariants_injective ρ σ f hf

end General

section Finite

variable {k G V W U : Type*} [CommRing k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]
  (ρ : Representation k G V) (σ : Representation k G W) (τ : Representation k G U)

example (v : V) : ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v :=
  averageMap_apply ρ v

example (g : G) (v : V) : ρ.averageMap (ρ g v) = ρ.averageMap v :=
  averageMap_action ρ g v

example (v : V) : Representation.Coinvariants.mk ρ (ρ.averageMap v) =
    Representation.Coinvariants.mk ρ v := coinvariants_mk_averageMap ρ v

example : LinearMap.ker ρ.averageMap = Representation.Coinvariants.ker ρ := ker_averageMap ρ

example (v : V) : v ∈ ρ.invariants ↔ ρ.averageMap v = v :=
  mem_invariants_iff_averageMap ρ v

example : LinearMap.range ρ.averageMap = ρ.invariants := range_averageMap ρ

example : IsCompl ρ.invariants (Representation.Coinvariants.ker ρ) :=
  isCompl_invariants_coinvariantsKer ρ

example : V →ₗ[k] ρ.invariants := reynolds ρ

example (v : V) : (reynolds ρ v : V) = ρ.averageMap v := reynolds_coe ρ v

example (v : ρ.invariants) : reynolds ρ v = v := reynolds_invariant ρ v

example (g : G) (v : V) : reynolds ρ (ρ g v) = reynolds ρ v := reynolds_action ρ g v

example : ρ.Coinvariants →ₗ[k] ρ.invariants := coinvariantsToInvariants ρ

example : ρ.invariants →ₗ[k] ρ.Coinvariants := invariantsToCoinvariants ρ

example : ρ.Coinvariants ≃ₗ[k] ρ.invariants := coinvariantsInvariantsEquiv ρ

example (v : V) : coinvariantsInvariantsEquiv ρ (Representation.Coinvariants.mk ρ v) =
    reynolds ρ v := coinvariantsInvariantsEquiv_mk ρ v

example (v : ρ.invariants) : (coinvariantsInvariantsEquiv ρ).symm v =
    Representation.Coinvariants.mk ρ v := coinvariantsInvariantsEquiv_symm ρ v

example (f : Representation.IntertwiningMap ρ σ) (v : V) :
    f (ρ.averageMap v) = σ.averageMap (f v) := averageMap_natural ρ σ f v

example (f : Representation.IntertwiningMap ρ σ) (x : ρ.Coinvariants) :
    mapInvariants ρ σ f (coinvariantsInvariantsEquiv ρ x) =
      coinvariantsInvariantsEquiv σ (Representation.Coinvariants.map ρ σ f x) :=
  coinvariantsInvariantsEquiv_natural ρ σ f x

example (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f) :
    Function.Surjective (mapInvariants ρ σ f) := mapInvariants_surjective ρ σ f hf

example (f : Representation.IntertwiningMap ρ σ) (g : Representation.IntertwiningMap σ τ)
    (hex : LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap) :
    LinearMap.range (mapInvariants ρ σ f) = LinearMap.ker (mapInvariants σ τ g) :=
  mapInvariants_exact ρ σ τ f g hex

example : (ρ.invariants × Representation.Coinvariants.ker ρ) ≃ₗ[k] V :=
  invariantDifferenceEquiv ρ

example (v : ρ.invariants) (w : Representation.Coinvariants.ker ρ) :
    invariantDifferenceEquiv ρ (v, w) = (v : V) + (w : V) :=
  invariantDifferenceEquiv_apply ρ v w

end Finite

example {k G V : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Nonempty (ρ.Coinvariants ≃ₗ[k] ρ.invariants) := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Fintype.card G : k) := invertibleOfNonzero (by
    simpa only [Fintype.card_eq_nat_card] using (NeZero.ne (Nat.card G : k)))
  exact ⟨coinvariantsInvariantsEquiv ρ⟩
