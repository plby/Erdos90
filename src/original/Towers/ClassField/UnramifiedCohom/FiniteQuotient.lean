import Towers.ClassField.ProfiniteCohom.ContinuousCohomology

/-!
# Milne, Class Field Theory, Corollary III.1.6: the finite-quotient step

This file isolates the formal consequence of Proposition II.4.2 used in
Milne's proof.  If every finite-quotient term `H^r(G/N, M^N)` vanishes, then
the continuous cohomology of the discrete module `M` vanishes in degree `r`.

For local units, the remaining arithmetic specialization is to identify
`M^N` with the units of the finite unramified fixed field of `N` and apply
Proposition III.1.1 at that field.
-/

namespace Towers.CField.UCohom

open CategoryTheory CategoryTheory.Limits
open Towers.CField.PCohom

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The colimit step in Milne's proof of Corollary III.1.6.  Proposition
II.4.2 identifies continuous cohomology with the filtered colimit of the
displayed finite-quotient cohomology groups, so pointwise vanishing implies
vanishing of continuous cohomology. -/
theorem continuous_subsingleton_quotients
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ)
    (hfinite : ∀ N : OpenInflationIndex G,
      Subsingleton ((finiteCohomologyDiagram M r).obj N)) :
    Subsingleton ((continuousInhomogeneousComplex M).homology r) := by
  let F := finiteCohomologyDiagram M r
  have hcol : Subsingleton
      ((CategoryTheory.Limits.colimit F : ModuleCat ℤ) : Type) := by
    constructor
    intro x y
    let U := forget (ModuleCat ℤ)
    have hc : IsColimit (U.mapCocone (colimit.cocone F)) :=
      isColimitOfPreserves U (colimit.isColimit F)
    obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hc x
    obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit hc y
    rw [← hxi, ← hyj]
    have hxi0 : xi = 0 := (hfinite i).elim xi 0
    have hyj0 : yj = 0 := (hfinite j).elim yj 0
    rw [hxi0, hyj0]
    change (colimit.ι F i) 0 = (colimit.ι F j) 0
    rw [map_zero, map_zero]
  let e := cohomologyColimitIso M r
  constructor
  intro x y
  have hinv : e.inv x = e.inv y := hcol.elim _ _
  have hhom := congrArg (fun z ↦ e.hom z) hinv
  simpa using hhom

end

end Towers.CField.UCohom
