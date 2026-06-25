import Submission.ClassField.CohomologyOps.RestrictionCompatibility

/-!
# Milne, Class Field Theory, Corollary II.1.31

For a finite group `G`, every positive-degree cohomology class is annihilated by the order
of `G`.  This is Milne's immediate application of restriction and corestriction to the trivial
subgroup.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **Corollary II.1.31.** If `G` is finite, multiplication by `|G|` annihilates
`H^r(G,A)` for every `r > 0`. -/
theorem nat_nsmul_cohomology
    (A : Rep k G) (r : ℕ) (hr : 0 < r) (x : groupCohomology A r) :
    Nat.card G • x = 0 := by
  let H : Subgroup G := ⊥
  letI : H.FiniteIndex := inferInstance
  have htarget : IsZero (groupCohomology (res H.subtype A) r) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    exact isZero_groupCohomology_succ_of_subsingleton (res H.subtype A) n
  have hres : restriction A H r x = 0 :=
    (ModuleCat.subsingleton_of_isZero htarget).elim _ _
  have htransfer := congrArg (fun f ↦ f x)
    (restriction_corestriction_degrees A H r)
  have hindex : H.index • x = 0 := by
    simpa [hres] using htransfer.symm
  simpa [H] using hindex

/-- Morphism form of Corollary II.1.31. -/
theorem nsmul_cohomology_identity
    (A : Rep k G) (r : ℕ) (hr : 0 < r) :
    Nat.card G • 𝟙 (groupCohomology A r) = 0 := by
  ext x
  exact nat_nsmul_cohomology A r hr x

end Submission.CField.COps
