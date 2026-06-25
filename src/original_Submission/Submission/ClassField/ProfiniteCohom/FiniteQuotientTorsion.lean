import Submission.ClassField.ProfiniteCohom.ContinuousCohomology
import Submission.ClassField.CohomologyOps.NatCardNsmul

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits
open Submission.CField.COps

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- Every class in the filtered colimit of positive-degree finite-quotient
cohomology is annihilated by a positive integer. -/
theorem cohomology_colimit_torsion
    (M : DiscreteContAction (TopModuleCat ℤ) G)
    (r : ℕ) (hr : 0 < r)
    (x : (colimit (finiteCohomologyDiagram M r) : ModuleCat ℤ)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 := by
  let F := finiteCohomologyDiagram M r
  let U := forget (ModuleCat ℤ)
  have hc : IsColimit (U.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves U (colimit.isColimit F)
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hc x
  subst x
  let N : OpenNormalSubgroup G := OrderDual.ofDual i
  let Q := G ⧸ (N : Subgroup G)
  let n := Nat.card Q
  haveI : Finite Q := inferInstance
  have hn : n ≠ 0 := Nat.card_pos.ne'
  refine ⟨n, hn, ?_⟩
  have hfinite : n • xi = 0 := by
    exact nat_nsmul_cohomology
      ((underlyingRep M).quotientToInvariants (N : Subgroup G)) r hr xi
  calc
    n • colimit.ι F i xi =
        colimit.ι F i (n • xi) :=
      (map_nsmul (colimit.ι F i).hom n xi).symm
    _ = colimit.ι F i 0 := congrArg
      (fun z ↦ ConcreteCategory.hom (colimit.ι F i) z) hfinite
    _ = 0 := map_zero (colimit.ι F i).hom

/-- **Corollary II.4.3.** Every positive-degree continuous cohomology class
of a profinite group with values in a discrete module is torsion. -/
theorem continuous_cohomology_torsion
    [TotallyDisconnectedSpace G]
    (M : DiscreteContAction (TopModuleCat ℤ) G)
    (r : ℕ) (hr : 0 < r)
    (x : (continuousInhomogeneousComplex M).homology r) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x = 0 := by
  let e := cohomologyColimitIso M r
  let y := e.inv x
  obtain ⟨n, hn, hy⟩ :=
    cohomology_colimit_torsion M r hr y
  refine ⟨n, hn, ?_⟩
  have hey : e.hom y = x := e.inv_hom_id_apply x
  calc
    n • x = n • e.hom y := congrArg (n • ·) hey.symm
    _ = e.hom (n • y) := (map_nsmul e.hom.hom n y).symm
    _ = e.hom 0 := congrArg (fun z ↦ e.hom z) hy
    _ = 0 := map_zero e.hom.hom

end

end Submission.CField.PCohom
