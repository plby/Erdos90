import Submission.Group.RelatorsThreeFive.ResidualQuotient
import Submission.Group.FinitePRelator.ShadowCorrespondence


open scoped Topology

noncomputable section

namespace Submission
namespace FSCorr

open PCShadow
open PRFact
open PRQuotie
open RCFact
open RRQuot
open RSCorr
open TFFact
open FFQuot

universe u

private instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

variable
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    (R : FRFam F)
    (Q : FRPresen (G := G) R)

/--
A finite `3`-group relator quotient of `F` descends continuously and
surjectively through the five-relator quotient candidate.
-/
abbrev RelatorDescendsThrough
    (S : RQShadow 3 F R.relator) :
    Prop :=
  RelatorContinuouslyThrough Q.quotientMap S

/--
A finite `3`-group relator quotient of `F` descends continuously,
surjectively, and uniquely through the five-relator quotient candidate.
-/
abbrev DescendsContinuouslyThrough
    (S : RQShadow 3 F R.relator) :
    Prop :=
  DescendsUniquelyThrough Q.quotientMap S

lemma quotients_descend_continuously
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FiniteThreeUniversal R ↔
      ∀ S : RQShadow 3 F R.relator,
        RelatorDescendsThrough R Q S := by
  rw [Q.three_universal_p R]
  exact all_descend_continuously
    (p := 3) (relator := R.relator) Q hquot

lemma quotients_descend_unique
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FiniteThreeUniversal R ↔
      ∀ S : RQShadow 3 F R.relator,
        DescendsContinuouslyThrough R Q S := by
  rw [Q.three_universal_p R]
  exact descend_continuously_uniquely
    (p := 3) (relator := R.relator) Q hquot

/-- The canonical continuous surjective factor from `G` to one finite `3` relator quotient. -/
noncomputable def threeRelatorFactor
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (S : RQShadow 3 F R.relator) :
    G →* S.Target :=
  (RSCorr.RQShadow.descendAlongPresented
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal)
      S).map

lemma relator_factor_continuous
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (S : RQShadow 3 F R.relator) :
    Continuous (threeRelatorFactor R Q hquot hUniversal S) := by
  exact (RSCorr.RQShadow.descendAlongPresented
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal)
      S).toShadow.map_continuous

lemma relator_factor_surjective
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (S : RQShadow 3 F R.relator) :
    Function.Surjective (threeRelatorFactor R Q hquot hUniversal S) := by
  exact (RSCorr.RQShadow.descendAlongPresented
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal)
      S).map_surjective

lemma relator_factor_comp
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (S : RQShadow 3 F R.relator) :
    (threeRelatorFactor R Q hquot hUniversal S).comp
        Q.quotientMap = S.map := by
  exact RSCorr.RQShadow.descendAlongComp
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal)
      S

lemma relator_factor_unique
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (S : RQShadow 3 F R.relator)
    (β : G →* S.Target)
    (hβ : β.comp Q.quotientMap = S.map) :
    β = threeRelatorFactor R Q hquot hUniversal S := by
  exact
    RSCorr.RQShadow.descend_along_unique
    Q
    hquot
    ((Q.three_universal_p R).mp hUniversal)
    S
    β
    hβ

lemma universal_comap_target
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FiniteThreeUniversal R ↔
      relatorKernel 3 R.relator =
        (residualKernel 3 G).comap Q.quotientMap := by
  rw [Q.three_universal_p R]
  exact comap_residual_target
    (p := 3) (relator := R.relator) Q hquot

lemma residual_projection_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R) :
    (FFQuot.FRPresen.finResidualProjection
      R Q hUniversal).ker =
      residualKernel 3 G := by
  simpa [FFQuot.FRPresen.finResidualProjection] using
    (projection_p_universal
      (p := 3)
      (relator := R.relator)
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal))

lemma residually_projection_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R) :
    ResiduallyFiniteThree G ↔
      Function.Injective
        (FFQuot.FRPresen.finResidualProjection
          R Q hUniversal) := by
  simpa [ResiduallyFiniteThree,
    FFQuot.FRPresen.finResidualProjection] using
    (residually_injective_universal
      (p := 3)
      (relator := R.relator)
      Q
      hquot
      ((Q.three_universal_p R).mp hUniversal))

end FSCorr
end Submission
