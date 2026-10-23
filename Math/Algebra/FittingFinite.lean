module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Artinian.Module

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace Math.LinearAlgebra

open Module LinearMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- the image of an iterate stabilizes by the dimension of the space. -/
theorem range_pow_eq_finrank (f : Module.End K V) {n : ℕ} (hn : finrank K V ≤ n) :
    LinearMap.range (f ^ n) = LinearMap.range (f ^ finrank K V) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add]
    exact LinearMap.range_comp_le_range _ _
  · have first := LinearMap.finrank_range_add_finrank_ker (f ^ n)
    have second := LinearMap.finrank_range_add_finrank_ker (f ^ finrank K V)
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hn] at first
    omega

/-- the kernel and image at the dimension bound form complementary subspaces. -/
theorem isCompl_pow_finrank (f : Module.End K V) :
    IsCompl (LinearMap.ker (f ^ finrank K V)) (LinearMap.range (f ^ finrank K V)) := by
  obtain ⟨n, hn, hc⟩ := Filter.Eventually.exists
    ((Filter.eventually_ge_atTop (finrank K V)).and f.eventually_isCompl_ker_pow_range_pow)
  simpa only [Module.End.ker_pow_eq_ker_pow_finrank_of_le hn, range_pow_eq_finrank f hn] using hc

/-- every vector has a unique bounded-iterate kernel and image decomposition. -/
noncomputable def fittingEquiv (f : Module.End K V) :
    (LinearMap.ker (f ^ finrank K V) × LinearMap.range (f ^ finrank K V)) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl _ _ (isCompl_pow_finrank f)

/-- the decomposition reconstructs a vector by adding its two components. -/
theorem fittingEquiv_apply (f : Module.End K V)
    (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    fittingEquiv f (x, y) = (x : V) + (y : V) := rfl

/-- the two bounded-iterate components of each vector are unique. -/
theorem existsUnique_fitting (f : Module.End K V) (v : V) :
    ∃! u : LinearMap.ker (f ^ finrank K V) × LinearMap.range (f ^ finrank K V),
      (u.1 : V) + (u.2 : V) = v :=
  Submodule.existsUnique_add_of_isCompl_prod (isCompl_pow_finrank f) v

/-- nilpotence is detected by the single iterate bounded by the space dimension. -/
theorem isNilpotent_iff_pow_finrank (f : Module.End K V) :
    IsNilpotent f ↔ f ^ finrank K V = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    have h := Module.End.ker_pow_le_ker_pow_finrank f n
    simpa [hn] using h
  · intro h
    exact ⟨finrank K V, h⟩

omit [FiniteDimensional K V] in
/-- the bounded-iterate kernel is invariant under the original operator. -/
theorem fittingKer_invariant (f : Module.End K V) (x : V)
    (hx : x ∈ LinearMap.ker (f ^ finrank K V)) :
    f x ∈ LinearMap.ker (f ^ finrank K V) := by
  change (f ^ finrank K V) (f x) = 0
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]

omit [FiniteDimensional K V] in
/-- the bounded-iterate image is invariant under the original operator. -/
theorem fittingRange_invariant (f : Module.End K V) (x : V)
    (hx : x ∈ LinearMap.range (f ^ finrank K V)) :
    f x ∈ LinearMap.range (f ^ finrank K V) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨f y, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]

/-- the restriction to the bounded kernel is the nilpotent component. -/
noncomputable def fittingNilpotent (f : Module.End K V) :
    Module.End K (LinearMap.ker (f ^ finrank K V)) :=
  f.restrict (fittingKer_invariant f)

omit [FiniteDimensional K V] in
/-- the nilpotent restriction vanishes at the same dimension bound. -/
theorem fittingNilpotent_pow (f : Module.End K V) :
    fittingNilpotent f ^ finrank K V = 0 := by
  change (f.restrict (fittingKer_invariant f)) ^ finrank K V = 0
  rw [Module.End.pow_restrict]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact x.property

/-- the restriction to the bounded image is the invertible component. -/
noncomputable def fittingInvertible (f : Module.End K V) :
    Module.End K (LinearMap.range (f ^ finrank K V)) :=
  f.restrict (fittingRange_invariant f)

/-- the bounded image restriction has zero kernel. -/
theorem fittingInvertible_isUnit (f : Module.End K V) : IsUnit (fittingInvertible f) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  apply (LinearMap.injective_restrict_iff (fittingRange_invariant f)).mpr
  exact (isCompl_pow_finrank f).symm.disjoint.mono_right
    (by simpa using Module.End.ker_pow_le_ker_pow_finrank f 1)

/-- the decomposition identifies the operator with its two invariant restrictions. -/
theorem fittingEquiv_intertwines (f : Module.End K V)
    (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    f (fittingEquiv f (x, y)) = fittingEquiv f (fittingNilpotent f x, fittingInvertible f y) := by
  exact map_add f (x : V) (y : V)

/-- the canonical projection onto the bounded-iterate kernel along its image. -/
noncomputable def fittingProjection (f : Module.End K V) : Module.End K V :=
  (LinearMap.ker (f ^ finrank K V)).projection
    (LinearMap.range (f ^ finrank K V)) (isCompl_pow_finrank f)

/-- the projection image is the bounded-iterate kernel. -/
theorem range_fittingProjection (f : Module.End K V) :
    LinearMap.range (fittingProjection f) = LinearMap.ker (f ^ finrank K V) :=
  Submodule.range_projection (isCompl_pow_finrank f)

/-- the projection kernel is the bounded-iterate image. -/
theorem ker_fittingProjection (f : Module.End K V) :
    LinearMap.ker (fittingProjection f) = LinearMap.range (f ^ finrank K V) :=
  Submodule.ker_projection (isCompl_pow_finrank f)

/-- the canonical projection is idempotent. -/
theorem fittingProjection_idempotent (f : Module.End K V) : IsIdempotentElem (fittingProjection f) :=
  Submodule.isIdempotentElem_projection (isCompl_pow_finrank f)

/-- the projection recovers the kernel component of every fitting decomposition. -/
theorem fittingProjection_apply_add (f : Module.End K V)
    (x : LinearMap.ker (f ^ finrank K V)) (y : LinearMap.range (f ^ finrank K V)) :
    fittingProjection f ((x : V) + (y : V)) = x := by
  simp only [fittingProjection, map_add]
  rw [Submodule.projection_apply_left, Submodule.projection_apply_right, add_zero]

omit [FiniteDimensional K V] in
/-- every commuting endomorphism preserves the bounded-iterate kernel. -/
theorem fittingKer_invariant_of_commute {f g : Module.End K V} (h : Commute f g) (x : V)
    (hx : x ∈ LinearMap.ker (f ^ finrank K V)) :
    g x ∈ LinearMap.ker (f ^ finrank K V) := by
  have hc := congrArg (fun u : Module.End K V => u x) (h.pow_left (finrank K V)).eq
  change (f ^ finrank K V) (g x) = g ((f ^ finrank K V) x) at hc
  change (f ^ finrank K V) (g x) = 0
  have hz : (f ^ finrank K V) x = 0 := hx
  rw [hc, hz, map_zero]

omit [FiniteDimensional K V] in
/-- every commuting endomorphism preserves the bounded-iterate image. -/
theorem fittingRange_invariant_of_commute {f g : Module.End K V} (h : Commute f g) (x : V)
    (hx : x ∈ LinearMap.range (f ^ finrank K V)) :
    g x ∈ LinearMap.range (f ^ finrank K V) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨g y, ?_⟩
  exact congrArg (fun u : Module.End K V => u y) (h.pow_left (finrank K V)).eq

/-- the canonical projection commutes with every endomorphism commuting with the operator. -/
theorem fittingProjection_commutes {f g : Module.End K V} (h : Commute f g) :
    Commute (fittingProjection f) g := by
  change fittingProjection f * g = g * fittingProjection f
  ext v
  obtain ⟨⟨x, y⟩, rfl⟩ := (fittingEquiv f).surjective v
  change fittingProjection f (g ((x : V) + (y : V))) =
    g (fittingProjection f ((x : V) + (y : V)))
  rw [fittingProjection_apply_add, map_add]
  let gx : LinearMap.ker (f ^ finrank K V) :=
    ⟨g x, fittingKer_invariant_of_commute h x x.property⟩
  let gy : LinearMap.range (f ^ finrank K V) :=
    ⟨g y, fittingRange_invariant_of_commute h y y.property⟩
  exact fittingProjection_apply_add f gx gy

/-- the projection annihilates the bounded iterate on its left. -/
theorem fittingProjection_mul_pow (f : Module.End K V) :
    fittingProjection f * f ^ finrank K V = 0 := by
  ext x
  change fittingProjection f ((f ^ finrank K V) x) = 0
  exact (Submodule.projection_apply_eq_zero_iff (isCompl_pow_finrank f)).2 ⟨x, rfl⟩

/-- the bounded iterate annihilates the projection on its left. -/
theorem pow_mul_fittingProjection (f : Module.End K V) :
    f ^ finrank K V * fittingProjection f = 0 := by
  rw [((fittingProjection_commutes (Commute.refl f)).pow_right (finrank K V)).eq.symm]
  exact fittingProjection_mul_pow f

end Math.LinearAlgebra
