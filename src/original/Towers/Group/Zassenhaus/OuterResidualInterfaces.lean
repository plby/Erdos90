import Towers.Group.Zassenhaus.OuterBracketRecollection
import Towers.Group.Zassenhaus.LocalResidualBranches
import Towers.Group.Zassenhaus.PolynomialBracketSupport

/-!
# Non-circular interfaces for polynomial inner-reduction outer residuals

Recipe-correct reduction of an inner Hall tree under one fixed outer bracket
produces a packet of children at the parent's full word weight. The quotient
between that packet and the parent is semantically one layer deeper, but its
raw symbolic factors still live in the parent stratum.

This file isolates recollection of that quotient as a small interface. Given
such an interface, the active-atomic comparison router completes the parent
residual without assuming a coordinate normalizer at the parent's own
stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open CEWord

/--
Recollect every recipe-correct full-weight outer-child quotient one layer
above its parent stratum.
-/
structure
    TRFtrya
    {d n : ℕ}
    (ι : Type) where
  sourceRecollection :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (innerWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight HEAddres.weight < n →
        SSRecol
          (n := n)
          (lowerWeight :=
            factor.word.weight HEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
          (innerRawSource
            factor innerWord rightWord hword)

namespace
  SNFam

/--
A complete normalizer family implements the full-weight outer-residual
interface by selecting its normalizer at the parent factor's stratum.
-/
noncomputable def
    concreteRecollectionFactory
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    TRFtrya
      (d := d) (n := n) ι where
  sourceRecollection factor innerWord rightWord hword hfactorTruncated :=
    (family.normalizer
      (factor.word.weight HEAddres.weight))
        |>.recollection_inner_raw
          hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
            hfactorTruncated

end
  SNFam

namespace
  TRRecoll

/--
Complete one parent residual from recursively recollected ranked children, a
sharp active-atomic router, and the explicit full-weight outer-residual
interface.
-/
noncomputable def
    residuals_sharp_factory
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (outerFactory :
      TRFtrya
        (d := d) (n := n) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          IRChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TRRecoll
          (n := n) task.1) :
    TRRecoll
      (n := n) factor := by
  let children :=
    IRChildr.active_atoms_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  let comparison :=
    factory.child_normalized_raw
      hn hH factor sharp nextNormalizer innerWord rightWord hword
        hfactorTruncated children
  exact
    inner_child_normalization factor innerWord rightWord
      hword children.recollection
      (by
        simpa only [
          innerChildNormalized] using
            comparison)
      (outerFactory.sourceRecollection factor innerWord rightWord hword
        hfactorTruncated)

/--
Scheduler-facing specialization over the exact ranked task source used by
well-founded Hall-ranked recursion.
-/
noncomputable def
    task_residuals_factory
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (outerFactory :
      TRFtrya
        (d := d) (n := n) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          (IRChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TRRecoll
          (n := n) task.1) :
    TRRecoll
      (n := n) factor :=
  residuals_sharp_factory
    hn hH factor factory sharp nextNormalizer outerFactory innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic
          (fun task htask => residual task (by simpa using htask))

end
  TRRecoll

namespace TRBrancha

open
  TRRecoll

/--
Recipe-correct inner reduction gives a Hall-ranked branch without requiring a
coordinate normalizer at the parent stratum once the full-weight
outer-residual factory is supplied.
-/
noncomputable def
    innerComparisonFactory
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (outerFactory :
      TRFtrya
        (d := d) (n := n) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      CEWord.tree innerWord =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    TRBrancha
      (n := n) factor
      (HallTree.bracketRankDefect
        ((CEWord.tree innerWord).weight +
          unchanged.weight)
        originalLeft originalRight) where
  children :=
    IRChildr.rankedTaskSource
      (n := n) factor innerWord rightWord hword added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  recollect residual :=
    task_residuals_factory
      hn hH factor factory sharp nextNormalizer outerFactory innerWord rightWord
        hword hfactorTruncated added originalRight unchanged originalLeft
          hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual

end TRBrancha

end TCTex
end Towers

/-!
# Inner-reduction residual recollection with sharp atomic comparison

After recursively recollecting ranked children, every active comparison factor
is atomic. The sharp mixed-source router recollects that comparison using only
a correction factory, a sharp router, and the next-stratum normalizer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open CEWord

namespace
  TRRecoll

/-- Recollect inner reduction through sharp comparison and local outer normalization. -/
noncomputable def
    residuals_sharp_comparison
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          IRChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TRRecoll
          (n := n) task.1) :
    TRRecoll
      (n := n) factor := by
  let children :=
    IRChildr.active_atoms_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  let comparison :=
    factory.child_normalized_raw
      hn hH factor sharp nextNormalizer innerWord rightWord hword
        hfactorTruncated children
  let rankedOuter :=
    IRChildr.rankedResidualRecollection
      hn hH normalizer factor innerWord rightWord hword rfl
        factor.word_weight_pos hfactorTruncated added originalRight unchanged
          originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  have outer :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword) := by
    simpa only [rankedOuter,
      IRChildr.rankedResidualRecollection,
      SPFactor.RCSrc.residualRawSource,
      IRChildr.factor_ranked_task] using
        rankedOuter.residualRecollection
  exact
    inner_child_normalization factor innerWord rightWord
      hword children.recollection
      (by
        simpa only [
          innerChildNormalized] using
            comparison)
      outer

/-- Scheduler-facing sharp-comparison specialization over the exact child source. -/
noncomputable def
    task_residuals_sharp
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          (IRChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TRRecoll
          (n := n) task.1) :
    TRRecoll
      (n := n) factor :=
  residuals_sharp_comparison
    hn hH factor normalizer factory sharp nextNormalizer innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic
          (fun task htask => residual task (by simpa using htask))

end
  TRRecoll

namespace TRBrancha

open
  TRRecoll

/-- Recipe-correct inner reduction gives a sharply routed ranked branch. -/
noncomputable def inner_sharp_comparison
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight))
    (sharp :
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      CEWord.tree innerWord =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    TRBrancha
      (n := n) factor
      (HallTree.bracketRankDefect
        ((CEWord.tree innerWord).weight +
          unchanged.weight)
        originalLeft originalRight) where
  children :=
    IRChildr.rankedTaskSource
      (n := n) factor innerWord rightWord hword added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  recollect residual :=
    task_residuals_sharp
      hn hH factor normalizer factory sharp nextNormalizer innerWord rightWord
        hword hfactorTruncated added originalRight unchanged originalLeft
          hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual

end TRBrancha

end TCTex
end Towers

/-!
# Recovering polynomial outer residual factories from comparisons

The full basic residual of a parent factor is the product of its
atomic-to-child comparison and its child-to-parent outer residual. Thus an
independently recollected full residual and atomic-to-child comparison recover
the outer residual by left division.

This file records that quotient construction and packages it as a factory
adapter for the non-circular outer-residual interface. It is intentionally not
imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open CEWord

namespace
  TRRecoll

/-- Forget the specialized full-residual wrapper as a source recollection. -/
def toSourceRecollection
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (residual :
      TRRecoll
        (n := n) factor) :
    SSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (basicRawSource factor) where
  higherSource := residual.higherSource
  higher_source_truncated := residual.higher_source_truncated
  higher_weight_least :=
    residual.higher_least_succ
  list_higher_raw :=
    residual.list_higher_raw

end
  TRRecoll

namespace
  SSRecol

/--
Recover the child-to-parent outer quotient by dividing the independently
recollected full basic residual by the recollected atomic-to-child comparison.
-/
noncomputable def
    inner_reduction_comparison
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (comparison :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerComparisonSource
          factor innerWord rightWord hword))
    (residual :
      TRRecoll
        (n := n) factor) :
    SSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerRawSource
        factor innerWord rightWord hword) :=
  (comparison.inverse.append residual.toSourceRecollection).of_list_eq
    fun e => by
      rw [SPFactor.listEval_append,
        SPFactor.list_eval_inverse,
        inner_comparison_source,
        reduction_raw_source,
        inner_raw_source]
      group

end
  SSRecol

/-- Recollection of every full basic residual below the truncation cutoff. -/
structure
    ConcreteRecollectionFactory
    {d n : ℕ}
    (ι : Type) where
  residualRecollection :
    ∀ factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι,
      factor.word.weight HEAddres.weight < n →
        TRRecoll
          (n := n) factor

/--
Recollection of every atomic-to-child comparison appearing in one
recipe-correct outer-bracket inner reduction.
-/
structure
    ComparisonRecollectionFactory
    {d n : ℕ}
    (ι : Type) where
  sourceRecollection :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (innerWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight HEAddres.weight < n →
        SSRecol
          (n := n)
          (lowerWeight :=
            factor.word.weight HEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
          (innerComparisonSource
            factor innerWord rightWord hword)

namespace
  TRFtrya

open
  SSRecol

/--
Construct all child-to-parent outer residual recollections from independent
atomic-to-child comparison and full-basic-residual factories.
-/
noncomputable def comparisonResidualFactories
    {d n : ℕ}
    {ι : Type}
    (comparisonFactory :
      ComparisonRecollectionFactory
        (d := d) (n := n) ι)
    (residualFactory :
      ConcreteRecollectionFactory
        (d := d) (n := n) ι) :
    TRFtrya
      (d := d) (n := n) ι where
  sourceRecollection factor innerWord rightWord hword hfactorTruncated :=
    inner_reduction_comparison
        factor innerWord rightWord hword
        (comparisonFactory.sourceRecollection
          factor innerWord rightWord hword hfactorTruncated)
        (residualFactory.residualRecollection factor hfactorTruncated)

end
  TRFtrya

end TCTex
end Towers
