import Towers.Group.Zassenhaus.ReductionOuterFactory
import Towers.Group.Zassenhaus.SourceRecollectionComposition
import Towers.Group.Zassenhaus.SourceRecollectionCongruence

/-!
# Recovering outer residual factories from comparison recollections

The full basic residual of a parent factor is the product of its
atomic-to-child comparison and its child-to-parent outer residual.  Thus an
independently recollected full residual and atomic-to-child comparison recover
the outer residual by left division.

This file records that quotient construction and packages it as a factory
adapter for the non-circular outer-residual interface.  It is intentionally
not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/-- Forget the specialized full-residual wrapper as a source recollection. -/
def toSourceRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (residual :
      TSRecollb
        (n := n) factor) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (basicRawSource factor) where
  higherSource := residual.higherSource
  higher_source_truncated := residual.higher_source_truncated
  higher_weight_least :=
    residual.higher_least_succ
  list_higher_raw :=
    residual.list_higher_raw

end
  TSRecollb

namespace TSRecol

/--
Recover the child-to-parent outer quotient by dividing the independently
recollected full basic residual by the recollected atomic-to-child comparison.
-/
noncomputable def
    inner_reduction_comparison
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerComparisonSource
          factor innerWord rightWord hword))
    (residual :
      TSRecollb
        (n := n) factor) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerRawSource
        factor innerWord rightWord hword) :=
  (comparison.inverse.append residual.toSourceRecollection).of_list_eq
    fun q => by
      rw [SPFactora.listEval_append,
        SPFactora.list_eval_inverse,
        inner_comparison_source,
        reduction_raw_source,
        inner_raw_source]
      group

end TSRecol

/-- Recollection of every full basic residual below the truncation cutoff. -/
structure
    ReductionRecollectionFactory
    (d n inputWeight : ℕ) where
  residualRecollection :
    ∀ factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight,
      factor.word.weight PEAddres.weight < n →
        TSRecollb
          (n := n) factor

/--
Recollection of every atomic-to-child comparison appearing in one
recipe-correct outer-bracket inner reduction.
-/
structure
    TruncatedComparisonFactory
    (d n inputWeight : ℕ) where
  sourceRecollection :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (innerWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight < n →
        TSRecol
          (n := n)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
          (innerComparisonSource
            factor innerWord rightWord hword)

namespace
  IRFtry

open TSRecol

/--
Construct all child-to-parent outer residual recollections from independent
atomic-to-child comparison and full-basic-residual factories.
-/
noncomputable def comparisonResidualFactories
    {d n inputWeight : ℕ}
    (comparisonFactory :
      TruncatedComparisonFactory
        d n inputWeight)
    (residualFactory :
      ReductionRecollectionFactory
        d n inputWeight) :
    IRFtry
      d n inputWeight where
  sourceRecollection factor innerWord rightWord hword hfactorTruncated :=
    inner_reduction_comparison
        factor innerWord rightWord hword
        (comparisonFactory.sourceRecollection
          factor innerWord rightWord hword hfactorTruncated)
        (residualFactory.residualRecollection factor hfactorTruncated)

end
  IRFtry

end TCTex
end Towers
