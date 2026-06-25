import Submission.FieldTheory.FiniteDefect.StageCofinality


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
Under the desired theorem, the honest finite kernel-image stage at a finite
family's common target depth maps continuously and surjectively onto every
quotient in that family.
-/
lemma fin_image_depth
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows) :
    SFThroug
      (initialKochImage
        (D.FamilyCommonTarget shadows))
      S.map := by
  apply surjectively_continuously_factors
    (initialKochImage
      (D.FamilyCommonTarget shadows))
    S.map
    (koch_image_quotient
      (D.FamilyCommonTarget shadows))
    S.toRShadow.toShadow.map_continuous
    S.map_surjective
  exact (D.initial_target_depth
    hfactor
    (D.RelatorCommonRefinement shadows).map
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.map_continuous
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.target_p_group
    (D.RelatorCommonRefinement shadows).toRShadow.relator_killed).trans
      (D.common_refinement_kernel shadows S hS)

/--
Every finite family of actual finite relator quotients is simultaneously
dominated by the honest finite kernel-image stage at the family's common
target depth.
-/
def AllCommonTarget
    (D : KRData) :
    Prop :=
  ∀ shadows : List D.ThreeRelatorQuotient,
    ∀ S ∈ shadows,
      SFThroug
        (initialKochImage
          (D.FamilyCommonTarget shadows))
        S.map

/--
The desired finite quotient Koch theorem is exactly finite-family cofinality of
the honest finite kernel-image quotient stages.
-/
lemma common_target_depth
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllCommonTarget := by
  constructor
  · intro hfactor shadows S hS
    exact D.fin_image_depth
      hfactor shadows S hS
  · intro hfamilies P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    rcases hfamilies [S] S (by simp) with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
    have hstage :
        (initialKochImage
          (D.FamilyCommonTarget [S])).ker ≤
          S.map.ker :=
      ker_factors_through
        (initialKochImage
          (D.FamilyCommonTarget [S]))
        S.map
        ⟨β, hβ⟩
    have hkernel :
        initialKochQuotient.ker ≤ S.map.ker :=
      (initial_koch_image
        (D.FamilyCommonTarget [S])).trans hstage
    simpa [S] using hkernel

/--
Under the desired theorem, the corrected canonical finite defect stage at a
finite family's common target depth maps continuously and surjectively onto
every quotient in that family.
-/
lemma relator_defect_depth
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (shadows : List D.ThreeRelatorQuotient)
    (S : D.ThreeRelatorQuotient)
    (hS : S ∈ shadows) :
    SFThroug
      (D.canonicalDefectAmbient
        (D.FamilyCommonTarget shadows))
      S.map := by
  apply surjectively_continuously_factors
    (D.canonicalDefectAmbient
      (D.FamilyCommonTarget shadows))
    S.map
    (D.koch_defect_ambient
      (D.FamilyCommonTarget shadows))
    S.toRShadow.toShadow.map_continuous
    S.map_surjective
  rw [D.defect_ambient_image]
  exact (D.initial_target_depth
    hfactor
    (D.RelatorCommonRefinement shadows).map
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.map_continuous
    (D.RelatorCommonRefinement shadows).toRShadow.toShadow.target_p_group
    (D.RelatorCommonRefinement shadows).toRShadow.relator_killed).trans
      (D.common_refinement_kernel shadows S hS)

/--
Every finite family of actual finite relator quotients is simultaneously
dominated by the corrected canonical finite defect stage at the family's
common target depth.
-/
def CommonTargetDepth
    (D : KRData) :
    Prop :=
  ∀ shadows : List D.ThreeRelatorQuotient,
    ∀ S ∈ shadows,
      SFThroug
        (D.canonicalDefectAmbient
          (D.FamilyCommonTarget shadows))
        S.map

/--
The desired finite quotient Koch theorem is exactly finite-family cofinality of
the corrected canonical finite defect stages.
-/
lemma defect_common_target
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.CommonTargetDepth := by
  constructor
  · intro hfactor shadows S hS
    exact D.relator_defect_depth
      hfactor shadows S hS
  · intro hfamilies P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    rcases hfamilies [S] S (by simp) with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
    have hstage :
        (D.canonicalDefectAmbient
          (D.FamilyCommonTarget [S])).ker ≤
          S.map.ker :=
      ker_factors_through
        (D.canonicalDefectAmbient
          (D.FamilyCommonTarget [S]))
        S.map
        ⟨β, hβ⟩
    have hkernel :
        initialKochQuotient.ker ≤ S.map.ker :=
      (initial_koch_image
        (D.FamilyCommonTarget [S])).trans
        ((D.defect_ambient_image
          (D.FamilyCommonTarget [S])).symm.le.trans hstage)
    simpa [S] using hkernel

end KRData

end TBluepr
end Submission
