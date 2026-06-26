import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Appendix, Exercise A-7: cohomology and inverse limits

The exercise constructs compatible principal one-cocycles whose inverse-limit
cocycle is not principal.  Mathlib has low-degree group cohomology and general
categorical limits, but no theorem identifying the underlying module of this
inverse limit with the coordinatewise projective limit used by the argument.
The two algebraic calculations that drive the construction are recorded here.
-/

namespace Towers.CField.COps.PCocycl

/-- The function `sigma |-> sigma*x - x` is a principal crossed
homomorphism. -/
theorem principal_isCocycle
    {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] (x : A) :
  groupCohomology.IsCocycle₁ (fun sigma : G ↦ sigma • x - x) := by
  intro sigma tau
  simp only [mul_smul, smul_sub]
  abel

/-- Principal cocycles commute with an equivariant additive map. -/
theorem map_principal
    {G A B : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (sigma : G) (x : A), f (sigma • x) = sigma • f x)
    (x : A) (sigma : G) :
    f (sigma • x - x) = sigma • f x - f x := by
  rw [map_sub, hf]

/-- If two potential primitives differ by an invariant element, they define
the same principal cocycle.  This is the compatibility step used for the
sequence `phi_n` in Exercise A-7. -/
theorem principal_sub_invariant
    {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    {x y : A} (hfixed : ∀ sigma : G, sigma • (x - y) = x - y) :
    ∀ sigma : G, sigma • x - x = sigma • y - y := by
  intro sigma
  have h := hfixed sigma
  simp only [smul_sub] at h
  rw [sub_eq_sub_iff_add_eq_add]
  have hh := sub_eq_sub_iff_add_eq_add.mp h
  simpa [add_comm] using hh

/-- Conversely, equality of two principal cocycles forces the difference of
their defining elements to be invariant.  This is the first step in the
non-principality contradiction in Milne's solution. -/
theorem sub_invariant_principal
    {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    {x y : A} (h : ∀ sigma : G, sigma • x - x = sigma • y - y) :
    ∀ sigma : G, sigma • (x - y) = x - y := by
  intro sigma
  rw [smul_sub, sub_eq_sub_iff_add_eq_add]
  have hsigma := sub_eq_sub_iff_add_eq_add.mp (h sigma)
  simpa [add_comm] using hsigma

end Towers.CField.COps.PCocycl
