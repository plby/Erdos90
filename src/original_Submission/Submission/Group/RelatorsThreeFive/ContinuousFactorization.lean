import Submission.Group.RelatorsThreeFive.FiveRelatorFactorization
import Submission.Group.FinitePRelator.ContinuousFactorization


open scoped Topology

noncomputable section

namespace Submission
namespace FCFact

open PRFact
open PRQuotie
open RCFact
open TFFact

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
    (q : F →* G)

omit [IsTopologicalGroup F] in
lemma continuous_unique_statement
    (hquot : Topology.IsQuotientMap q) :
    (
      ∀ {P : Type u}
          [Group P]
          [TopologicalSpace P]
          [DiscreteTopology P]
          [Finite P],
          (α : F →* P) →
          Continuous α →
          IsPGroup 3 P →
          R.Kills α →
          ContinuouslyFactorsUniquely q α
    ) ↔
      (∀ {P : Type u}
        [Group P]
        [TopologicalSpace P]
        [DiscreteTopology P]
        [Finite P],
        (α : F →* P) →
        Continuous α →
        IsPGroup 3 P →
        R.Kills α →
        q.ker ≤ α.ker) := by
  constructor
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
    exact (continuously_uniquely_ker q α hquot hα).mp
      (hfactor α hα hP hkill)
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
    exact continuously_through_ker
      q α hquot hα (hfactor α hα hP hkill)

omit [IsTopologicalGroup F] in
lemma unique_factorization_statement
    (hquot : Topology.IsQuotientMap q) :
    (
      ∀ {P : Type u}
          [Group P]
          [TopologicalSpace P]
          [DiscreteTopology P]
          [Finite P],
          (α : F →* P) →
          Continuous α →
          IsPGroup 3 P →
          R.Kills α →
          ContinuouslyFactorsUniquely q α
    ) ↔
      (∀ {P : Type u}
            [Group P]
            [TopologicalSpace P]
            [DiscreteTopology P]
            [Finite P],
            (α : F →* P) →
            Continuous α →
            IsPGroup 3 P →
            R.Kills α →
            FactorsUniquelyThrough q α) := by
  rw [continuous_unique_statement R q hquot]
  exact (three_unique_statement
    R q hquot.surjective).symm

omit [IsTopologicalGroup F] in
lemma unique_statement_property
    (hquot : Topology.IsQuotientMap q) :
    (
      ∀ {P : Type u}
          [Group P]
          [TopologicalSpace P]
          [DiscreteTopology P]
          [Finite P],
          (α : F →* P) →
          Continuous α →
          IsPGroup 3 P →
          R.Kills α →
          ContinuouslyFactorsUniquely q α
    ) ↔
      QuotientFactorizationProperty 3 R.relator q := by
  rw [continuous_unique_statement R q hquot]
  exact fin_statement_property R q

namespace FRPresen

variable
    [T1Space G]
    (Q : FRPresen (G := G) R)

/-- Every finite `3`-group relator-killing map factors continuously and uniquely through `Q`. -/
def ContinuousFinThree :
    Prop :=
  (∀ {P : Type u}
        [Group P]
        [TopologicalSpace P]
        [DiscreteTopology P]
        [Finite P],
        (α : F →* P) →
        Continuous α →
        IsPGroup 3 P →
        R.Kills α →
        ContinuouslyFactorsUniquely Q.quotientMap α)

lemma continuously_three_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    ContinuousFinThree R Q ↔
      Q.FiniteThreeUniversal R := by
  exact continuous_unique_statement
    R Q.quotientMap hquot

lemma fin_continuous
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FiniteThreeUniversal R ↔
      ContinuousFinThree R Q := by
  exact (continuously_three_universal R Q hquot).symm

lemma t_1_topological
    [CompactSpace F]
    [IsTopologicalGroup G] :
    Q.FiniteThreeUniversal R ↔
      ContinuousFinThree R Q := by
  exact fin_continuous
    R
    Q
    (RCFact.PQuot.topological_t_1 Q)

lemma quotients_continuously_uniquely
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FiniteThreeUniversal R ↔
      ∀ S : RQShadow 3 F R.relator,
        ContinuouslyFactorsUniquely Q.quotientMap S.map := by
  rw [Q.three_universal_p R]
  exact RCFact.PQuot.fin_factorization_property
    (p := 3) (relator := R.relator) Q hquot

lemma fin_three_continuous
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    ContinuouslyFactorsUniquely Q.quotientMap α := by
  rw [fin_continuous R Q hquot] at hUniversal
  exact hUniversal α hα hP hkill

lemma fin_t_topological
    [CompactSpace F]
    [IsTopologicalGroup G]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    ContinuouslyFactorsUniquely Q.quotientMap α := by
  exact fin_three_continuous
    R
    Q
    (RCFact.PQuot.topological_t_1 Q)
    hUniversal
    α
    hα
    hP
    hkill

/-- The canonical continuous factor from the presented quotient candidate to
one finite `3`-group. -/
noncomputable def threeContinuousFactor
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    G →* P :=
  continuousFactorQuotient
    Q.quotientMap
    α
    hquot
    (Q.kernel_three_universal R hUniversal α hα hP hkill)

lemma three_continuous_factor
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    Continuous (threeContinuousFactor R Q hquot hUniversal α hα hP hkill) := by
  exact continuous_factor_quotient
    Q.quotientMap
    α
    hquot
    hα
    (Q.kernel_three_universal R hUniversal α hα hP hkill)

lemma continuous_factor_comp
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    (threeContinuousFactor R Q hquot hUniversal α hα hP hkill).comp
        Q.quotientMap = α := by
  exact continuous_quotient_comp
    Q.quotientMap
    α
    hquot
    (Q.kernel_three_universal R hUniversal α hα hP hkill)

lemma continuous_factor_unique
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α)
    (β : G →* P)
    (hβ : β.comp Q.quotientMap = α) :
    β = threeContinuousFactor R Q hquot hUniversal α hα hP hkill := by
  apply MonoidHom.ext
  intro y
  rcases hquot.surjective y with ⟨x, rfl⟩
  have hβx := congrArg (fun φ : F →* P => φ x) hβ
  have hfactorx := congrArg
    (fun φ : F →* P => φ x)
    (continuous_factor_comp
      R Q hquot hUniversal α hα hP hkill)
  change β (Q.quotientMap x) = α x at hβx
  change threeContinuousFactor R Q hquot hUniversal α hα hP hkill
      (Q.quotientMap x) = α x at hfactorx
  exact hβx.trans hfactorx.symm

end FRPresen

end FCFact
end Submission
