import Towers.Group.Zassenhaus.ConcreteAutomaticComparison
import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.Zassenhaus.ReductionResidualNormalization

/-!
# Endpoint residual-source builders from semantic normalizer families

A semantic normalizer family directly recollects both concrete Hall-tree
sources used by endpoint interpolation.  The true atomic reduction residual
is handled by the existing residual normalizer.  The concrete-to-semantic
comparison source is also physically supported in its active layer and
evaluates in that lower-central stratum, so the generic higher-source
compiler recollects it one layer upward.

This file records the resulting direct endpoint-builder constructor.  It
also isolates the circular boundary: constructing the semantic normalizer
family remains the substantive global collection problem.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


namespace HEWord

/-- The concrete-to-semantic comparison source lies in its active physical
Hall layer. -/
theorem
    least_comparison_source
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight) :
    SPFactora.WordWeightLeast lowerWeight
      (comparisonRawSource
        hn hH factor lowerWeight) := by
  intro sourceFactor hsourceFactor
  rcases
      atom_comparison_source
        hn hH factor hfactorWeight hsourceFactor with
    ⟨address, hword, hweight⟩
  rw [hword, CWord.weight_atom]
  simpa only [PEAddres.weight, HEAddres.weight] using
    hweight.ge

end HEWord

namespace
  TCRecoll

open HEWord

/--
A semantic normalizer at the active factor weight recollects the
concrete-to-semantic comparison source one layer upward.
-/
noncomputable def ofNormalizer
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TCRecoll
      (lowerWeight := lowerWeight) hn hH factor := by
  let recollection :=
    normalizer.source_recollection_series
      hn (concreteBasicCommutators.{u} d) hH
      (comparisonRawSource
        hn hH factor lowerWeight)
      (by
        rw [← hfactorWeight]
        exact factor.word_weight_pos)
      (by omega)
      (truncated_comparison_source
        hn hH factor hfactorWeight hfactorTruncated)
      (least_comparison_source
        hn hH factor hfactorWeight)
      (comparison_raw_series
        hn hH factor hfactorWeight hfactorTruncated)
  exact
    { higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ :=
        recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw }

/-- Use a semantic normalizer family at the active factor weight. -/
noncomputable def ofNormalizerFamily
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TCRecoll
      (lowerWeight := lowerWeight) hn hH factor :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor hfactorWeight
    hfactorTruncated

end
  TCRecoll

namespace
  TSBuildc

/--
One semantic normalizer family supplies both concrete Hall-tree residual
recollections required by endpoint interpolation.
-/
noncomputable def ofNormalizerFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d)) :
    TSBuildc
      (inputWeight := inputWeight) hn hH where
  basicResidual _lowerWeight _hnonterminal factor hfactorWeight
      hfactorTruncated :=
    TSRecollb.ofNormalizerFamily
      hn hH family factor hfactorWeight hfactorTruncated
  comparisonResidual _lowerWeight _hnonterminal factor hfactorWeight
      hfactorTruncated :=
    TCRecoll.ofNormalizerFamily
      hn hH family factor hfactorWeight hfactorTruncated

end
  TSBuildc

namespace TDBuildb

/--
A universal semantic derivation builder supplies the normalizer family and
therefore both concrete Hall-tree residual recollections required by endpoint
interpolation.
-/
noncomputable def
    endpointInterpolationBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    TSBuildc
      (inputWeight := inputWeight) hn
        (forms_associated_below
          d n) :=
  TSBuildc.ofNormalizerFamily
    hn
      (forms_associated_below
        d n)
      (builder.supportedSemanticFamily
        hn (concreteBasicCommutators.{u} d)
          (forms_associated_below
            d n))

end TDBuildb

end TCTex
end Towers
