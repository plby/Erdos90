import Submission.Group.RelatorsThreeFive.ContinuousFactorization
import Submission.Group.FinitePRelator.ResidualQuotient


open scoped Topology

noncomputable section

namespace Submission
namespace FFQuot

open PCShadow
open PRFact
open FPQuotie
open RPQuotie
open RCFact
open RRQuot
open TFFact
open FCFact

universe u

private instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

variable
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    (R : FRFam F)

/-- The quotient of `F` visible to all finite `3`-group shadows killing the five relators. -/
abbrev finiteResidualQuotient :=
  relatorResidualQuotient (p := 3) R.relator

/-- The canonical map to the finite-`3` five-relator residual quotient. -/
abbrev threeResidualQuotient :
    F →* finiteResidualQuotient R :=
  residualQuotientMap (p := 3) R.relator

abbrev threeCompletedRelator :=
  completedRelatorQuotient R.relator

abbrev completedThreeProjection :
    threeCompletedRelator R →* finiteResidualQuotient R :=
  completedResidualProjection (p := 3) R.relator

lemma three_residual_residually :
    ResiduallyFiniteThree (finiteResidualQuotient R) := by
  exact relator_residually_p (p := 3) R.relator

lemma completed_projection_kernel :
    (completedThreeProjection R).ker =
      residualKernel 3 (threeCompletedRelator R) := by
  exact completed_residual_projection (p := 3) R.relator

noncomputable def completedProjectionResidually
    (hres : ResiduallyFiniteThree (threeCompletedRelator R)) :
    threeCompletedRelator R ≃* finiteResidualQuotient R :=
  completedResiduallyP (p := 3) R.relator hres

lemma three_residual_kills :
    R.Kills (threeResidualQuotient R) := by
  intro i
  exact residual_relator_one (p := 3) R.relator i

/-- The finite-`3` five-relator residual quotient as a presented quotient candidate. -/
def residualPresentedQuotient :
    FRPresen (G := finiteResidualQuotient R) R :=
  relatorResidualPresented (p := 3) R.relator

lemma residual_presented_universal :
    (residualPresentedQuotient R).FiniteThreeUniversal R := by
  rw [(residualPresentedQuotient R).three_universal_p R]
  exact relator_presented_universal (p := 3) R.relator

lemma presented_continuously_universal :
    FCFact.FRPresen.ContinuousFinThree R
      (residualPresentedQuotient R) := by
  exact (FCFact.FRPresen.fin_continuous
    R
    (residualPresentedQuotient R)
    (relator_presented_topological (p := 3) R.relator)).mp
      (residual_presented_universal R)

namespace FRPresen

variable
    [T1Space G]
    (Q : FRPresen (G := G) R)

lemma universal_uniquely_through :
    Q.FiniteThreeUniversal R ↔
      FactorsUniquelyThrough Q.quotientMap (threeResidualQuotient R) := by
  rw [Q.three_universal_p R]
  exact RRQuot.PQuot.factors_unique_through
    (p := 3) (relator := R.relator) Q

lemma universal_residually_target
    (hUniversal : Q.FiniteThreeUniversal R)
    (hres : ResiduallyFiniteThree G) :
    Q.quotientMap.ker = relatorKernel 3 R.relator := by
  exact RRQuot.PQuot.residually_fin_target
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)
    hres

/-- The canonical projection from a finite-`3` universal candidate to the finite-`3` residual
  quotient. -/
noncomputable def finResidualProjection
    (hUniversal : Q.FiniteThreeUniversal R) :
    G →* finiteResidualQuotient R :=
  RRQuot.PQuot.residualProjection
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)

lemma residual_projection_comp
    (hUniversal : Q.FiniteThreeUniversal R) :
    (finResidualProjection R Q hUniversal).comp Q.quotientMap =
      threeResidualQuotient R := by
  exact RRQuot.PQuot.projection_comp_quotient
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)

lemma residual_projection_surjective
    (hUniversal : Q.FiniteThreeUniversal R) :
    Function.Surjective (finResidualProjection R Q hUniversal) := by
  exact RRQuot.PQuot.residualProjection_surjective
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)

lemma residual_projection_continuous
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R) :
    Continuous (finResidualProjection R Q hUniversal) := by
  exact RRQuot.PQuot.residualProjection_continuous
    R.relator
    Q
    hquot
    ((Q.three_universal_p R).mp hUniversal)

lemma projection_residually_target
    (hUniversal : Q.FiniteThreeUniversal R)
    (hres : ResiduallyFiniteThree G) :
    Function.Injective (finResidualProjection R Q hUniversal) := by
  exact RRQuot.PQuot.residual_residually_target
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)
    hres

/--
A finite-`3` universal residually finite `3` target is canonically isomorphic
to the finite-`3` five-relator residual quotient.
-/
noncomputable def
  projectionUniversalResidually
    (hUniversal : Q.FiniteThreeUniversal R)
    (hres : ResiduallyFiniteThree G) :
    G ≃* finiteResidualQuotient R :=
  RRQuot.PQuot.projectionResiduallyP
    R.relator
    Q
    ((Q.three_universal_p R).mp hUniversal)
    hres

end FRPresen

end FFQuot
end Submission
