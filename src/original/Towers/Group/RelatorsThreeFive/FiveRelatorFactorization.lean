import Towers.Group.FinitePRelator.PresentedQuotients
import Towers.Group.FinitePRelator.FiniteSeparation


open scoped Topology

noncomputable section

namespace Towers
namespace TFFact

open PCShadow
open PRFact
open FPQuotie
open PRQuotie
open RPQuotie
open PRSep

universe u

private instance primeThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/--
A named family of five relators.  The intended Koch application will use the
five tame relators, indexed by `Fin 5`.
-/
structure FRFam (F : Type u) where
  relator : Fin 5 → F

namespace FRFam

variable
    {F P : Type u}
    [Group F]
    [Group P]
    (R : FRFam F)

/-- Pointwise vanishing of all five displayed relators. -/
def Kills
    (α : F →* P) :
    Prop :=
  KillsRelators R.relator α

lemma kills_iff
    (α : F →* P) :
    R.Kills α ↔ ∀ i : Fin 5, α (R.relator i) = 1 := by
  rfl

end FRFam

variable
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [Group P]
    (R : FRFam F)
    (q : F →* G)

omit [IsTopologicalGroup F] in
/--
The raw finite `3`-group kernel statement is equivalent to testing only
surjective finite `3`-group quotients killing the five relators.
-/
lemma fin_statement_property :
    (∀ {P : Type u}
        [Group P]
        [TopologicalSpace P]
        [DiscreteTopology P]
        [Finite P],
        (α : F →* P) →
        Continuous α →
        IsPGroup 3 P →
        R.Kills α →
        q.ker ≤ α.ker) ↔
      QuotientFactorizationProperty 3 R.relator q := by
  constructor
  · intro hfactor S
    exact hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
    exact factorization_property_group
      hfactor hα hP hkill

omit [IsTopologicalGroup F] in
lemma three_unique_statement
    (hq : Function.Surjective q) :
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
          FactorsUniquelyThrough q α
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
    exact ker_factors_through q α (hfactor α hα hP hkill).exists
  · intro hfactor P instGroupP instTopologicalSpaceP instDiscreteTopologyP instFiniteP α hα hP hkill
    exact factors_uniquely_ker q α hq (hfactor α hα hP hkill)

omit [IsTopologicalGroup F] in
lemma unique_factorization_property
    (hq : Function.Surjective q) :
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
          FactorsUniquelyThrough q α
    ) ↔
      QuotientFactorizationProperty 3 R.relator q := by
  rw [three_unique_statement R q hq]
  exact fin_statement_property R q

/-- Residual finite-`3` in the continuous finite-shadow sense. -/
def ResiduallyFiniteThree
    (H : Type u)
    [Group H]
    [TopologicalSpace H] :
    Prop :=
  RFP 3 H

/-- A presented quotient candidate carrying a named five-relator family. -/
abbrev FRPresen
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    (R : FRFam F) :=
  PQuot (G := G) R.relator

namespace FRPresen

variable
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    [Group P]
    (R : FRFam F)
    (Q : FRPresen (G := G) R)

/-- The exact finite-`3` five-relator universality statement for this quotient. -/
def FiniteThreeUniversal :
    Prop :=
  ∀ {P : Type u}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : F →* P) →
    Continuous α →
    IsPGroup 3 P →
    R.Kills α →
    Q.quotientMap.ker ≤ α.ker

lemma three_universal_p :
    Q.FiniteThreeUniversal R ↔
      Q.FinitePUniversal 3 := by
  exact fin_statement_property
    R Q.quotientMap

lemma universal_all_uniquely :
    Q.FiniteThreeUniversal R ↔
      (∀ {P : Type u}
            [Group P]
            [TopologicalSpace P]
            [DiscreteTopology P]
            [Finite P],
            (α : F →* P) →
            Continuous α →
            IsPGroup 3 P →
            R.Kills α →
            FactorsUniquelyThrough Q.quotientMap α) := by
  simpa [FiniteThreeUniversal] using
    (three_unique_statement
      R Q.quotientMap Q.quotientMap_surjective).symm

lemma all_quotients_uniquely :
    Q.FiniteThreeUniversal R ↔
      ∀ S : RQShadow 3 F R.relator,
        FactorsUniquelyThrough Q.quotientMap S.map := by
  rw [Q.three_universal_p R]
  exact Q.universal_quotients_uniquely

/--
Failure of the finite-`3` five-relator factorization statement has a concrete
finite `3`-group quotient witness and a kernel element it detects.
-/
lemma not_universal_counterexample :
    ¬ Q.FiniteThreeUniversal R ↔
      ∃ S : RQShadow 3 F R.relator,
        ∃ x : F, x ∈ Q.quotientMap.ker ∧ x ∉ S.map.ker := by
  rw [Q.three_universal_p R]
  exact not_property_counterexample

lemma kernel_three_universal
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    Q.quotientMap.ker ≤ α.ker := by
  exact hUniversal α hα hP hkill

lemma uniquely_through_universal
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hUniversal : Q.FiniteThreeUniversal R)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup 3 P)
    (hkill : R.Kills α) :
    FactorsUniquelyThrough Q.quotientMap α := by
  rw [Q.universal_all_uniquely R] at hUniversal
  exact hUniversal α hα hP hkill

lemma
  universal_completed_residually
    (hres : ResiduallyFiniteThree (completedRelatorQuotient R.relator)) :
    Q.FiniteThreeUniversal R ↔
      Q.quotientMap.ker = completedRelationSubgroup R.relator := by
  rw [Q.three_universal_p R]
  exact Q.completed_relation_residually
    hres

noncomputable def liftUniversalResidually
    (hres : ResiduallyFiniteThree (completedRelatorQuotient R.relator))
    (hUniversal : Q.FiniteThreeUniversal R) :
    completedRelatorQuotient R.relator ≃* G :=
  Q.pUniversalResidually
    hres
    ((Q.three_universal_p R).mp hUniversal)

end FRPresen

end TFFact
end Towers
