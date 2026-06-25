import Submission.FieldTheory.FiniteDefect.StageFactorization
import Submission.Group.FinitePRelator.SurjectiveFactorization


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open RCFact
open RSFact
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The canonical honest finite kernel-image stage at the target depth of an
actual finite relator quotient maps continuously and surjectively onto that
quotient under the desired theorem.
-/
lemma fin_relator_target
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    SFThroug
      (initialKochImage
        (D.RelatorTargetDepth S))
      S.map := by
  exact ⟨D.initialStageTheorem
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed,
    D.stage_theorem_continuous
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed,
    D.stage_theorem_surjective
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed
      S.map_surjective,
    D.stage_theorem_comp
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed⟩

/--
Every actual finite relator quotient is a surjective continuous quotient of
its canonical honest finite kernel-image stage.
-/
def AllSurjTarget
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    SFThroug
      (initialKochImage
        (D.RelatorTargetDepth S))
      S.map

/--
The desired finite quotient Koch theorem is exactly target-depth cofinality of
the honest finite kernel-image quotient stages among actual finite relator
quotients.
-/
lemma surj_target_depth
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllSurjTarget := by
  constructor
  · intro hfactor S
    exact D.fin_relator_target
      hfactor S
  · intro hcofinal P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    rcases hcofinal S with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
    have hstage :
        (initialKochImage
          (D.RelatorTargetDepth S)).ker ≤
          S.map.ker :=
      ker_factors_through
        (initialKochImage
          (D.RelatorTargetDepth S))
        S.map
        ⟨β, hβ⟩
    have hkernel :
        initialKochQuotient.ker ≤ S.map.ker :=
      (initial_koch_image
        (D.RelatorTargetDepth S)).trans hstage
    simpa [S] using hkernel

/--
The canonical corrected finite defect stage at the target depth of an actual
finite relator quotient maps continuously and surjectively onto that quotient
under the desired theorem.
-/
lemma defect_target_depth
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    SFThroug
      (D.canonicalDefectAmbient
        (D.RelatorTargetDepth S))
      S.map := by
  exact ⟨D.defectStageTheorem
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed,
    D.defect_stage_continuous
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed,
    D.defect_stage_theorem
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed
      S.map_surjective,
    D.stage_theorem_ambient
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed⟩

/--
Every actual finite relator quotient is a surjective continuous quotient of
its corrected canonical finite defect stage.
-/
def SurjTargetDepth
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    SFThroug
      (D.canonicalDefectAmbient
        (D.RelatorTargetDepth S))
      S.map

/--
The desired finite quotient Koch theorem is exactly target-depth cofinality of
the corrected canonical finite defect stages among actual finite relator
quotients.
-/
lemma fin_surj_target
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.SurjTargetDepth := by
  constructor
  · intro hfactor S
    exact D.defect_target_depth
      hfactor S
  · intro hcofinal P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    rcases hcofinal S with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
    have hstage :
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S)).ker ≤
          S.map.ker :=
      ker_factors_through
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S))
        S.map
        ⟨β, hβ⟩
    have hkernel :
        initialKochQuotient.ker ≤ S.map.ker :=
      (initial_koch_image
        (D.RelatorTargetDepth S)).trans
        ((D.defect_ambient_image
          (D.RelatorTargetDepth S)).symm.le.trans hstage)
    simpa [S] using hkernel

end KRData

end TBluepr
end Submission
