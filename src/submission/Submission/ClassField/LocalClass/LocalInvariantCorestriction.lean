import Submission.ClassField.CohomologyOps.RestrictionCompatibility

/-!
# Local invariants and corestriction

After formula (29), Milne proves formula (30)

`inv_K (Cor x) = inv_L x`

by lifting `x` through the surjective restriction map and using
`Cor (Res y) = [L : K] y`.  The results below isolate that argument and
apply it to the restriction and corestriction maps constructed in Chapter II.
-/

namespace Submission.CField.LClass

open CategoryTheory Rep
open COps

universe u v

/-- The algebraic argument proving compatibility with corestriction from
compatibility with a surjective restriction map. -/
theorem invariant_corestriction_restriction
    {A B Q : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup Q]
    (res : A →+ B) (cor : B →+ A) (invA : A →+ Q) (invB : B →+ Q)
    (d : ℕ) (hres : Function.Surjective res)
    (hbase : ∀ x, invB (res x) = d • invA x)
    (hcorRes : ∀ x, cor (res x) = d • x) :
    ∀ y, invA (cor y) = invB y := by
  intro y
  obtain ⟨x, rfl⟩ := hres y
  rw [hcorRes, map_nsmul, hbase]

/-- Formula (30) for the categorical group-cohomology maps of Chapter II.
If restriction is surjective and the two invariant maps satisfy formula
(29), then the invariant commutes with corestriction. -/
theorem cohomology_invariant_corestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    {Q : Type v} [AddCommGroup Q]
    (invG : groupCohomology A n →+ Q)
    (invH : groupCohomology (res H.subtype A) n →+ Q)
    (hres : Function.Surjective (restriction A H n))
    (hbase : ∀ x, invH (restriction A H n x) = H.index • invG x) :
    ∀ y, invG (corestriction A H n y) = invH y := by
  apply invariant_corestriction_restriction
    (restriction A H n).hom.toAddMonoidHom
    (corestriction A H n).hom.toAddMonoidHom invG invH H.index hres hbase
  intro x
  have h := congrArg (fun f ↦ f x)
    (restriction_corestriction_degrees A H n)
  simpa using h

/-- Map-valued form of formula (30): `inv_G ∘ Cor = inv_H`. -/
theorem cohomology_comp_corestriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    {Q : Type v} [AddCommGroup Q]
    (invG : groupCohomology A n →+ Q)
    (invH : groupCohomology (res H.subtype A) n →+ Q)
    (hres : Function.Surjective (restriction A H n))
    (hbase : ∀ x, invH (restriction A H n x) = H.index • invG x) :
    invG.comp (corestriction A H n).hom.toAddMonoidHom = invH := by
  ext y
  exact cohomology_invariant_corestriction
    A H n invG invH hres hbase y

end Submission.CField.LClass
