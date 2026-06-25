import Towers.Group.Zassenhaus.ReductionOuter
import Towers.Group.Zassenhaus.ResidualBranch

/-!
# Non-circular interfaces for full-weight inner-reduction residuals

Recipe-correct reduction of an inner Hall tree under one fixed outer bracket
produces a packet of children at the parent's full word weight.  The quotient
between that packet and the parent is semantically one layer deeper, but its
raw symbolic factors still live in the parent stratum.

This file isolates recollection of that quotient as a small interface.  Given
such an interface, the active-atomic comparison router completes the parent
residual without assuming a coordinate normalizer at the parent's own
stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

/--
Recollect every recipe-correct full-weight outer-child quotient one layer
above its parent stratum.

This is the remaining non-circular local input for inner reduction under an
outer bracket.
-/
structure
    IRFtry
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
          (innerRawSource
            factor innerWord rightWord hword)

namespace SSNormala

/--
A complete normalizer family implements the full-weight outer-residual
interface by selecting its normalizer at the parent factor's stratum.

This compatibility constructor records the old route without using it in the
non-circular interface.
-/
noncomputable def
    concreteRecollectionFactory
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
    IRFtry
      d n inputWeight where
  sourceRecollection factor innerWord rightWord hword hfactorTruncated :=
    (family.normalizer
      (factor.word.weight PEAddres.weight))
        |>.recollection_inner_raw
          hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
            hfactorTruncated

end SSNormala

namespace
  TSRecollb

/--
Complete one parent residual from recursively recollected ranked children, a
sharp active-atomic router, and the explicit full-weight outer-residual
interface.
-/
noncomputable def
    residuals_sharp_factory
    {d n inputWeight : ℕ}
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
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (outerFactory :
      IRFtry
        d n inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          CIChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor := by
  let children :=
    CIChildr.atoms_recollect_residuals
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
    {d n inputWeight : ℕ}
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
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (outerFactory :
      IRFtry
        d n inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          (CIChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor :=
  residuals_sharp_factory
    hn hH factor factory sharp nextNormalizer outerFactory innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic
          (fun task htask => residual task (by simpa using htask))

end
  TSRecollb

namespace RRBrancha

open
  TSRecollb

/--
Recipe-correct inner reduction gives a Hall-ranked branch without requiring a
coordinate normalizer at the parent stratum once the full-weight
outer-residual factory is supplied.
-/
noncomputable def
    innerComparisonFactory
    {d n inputWeight : ℕ}
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
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (outerFactory :
      IRFtry
        d n inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree innerWord =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    RRBrancha
      (n := n) factor
      (HallTree.bracketRankDefect
        ((HEWord.tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  children :=
    CIChildr.rankedTaskSource
      (n := n) factor innerWord rightWord hword added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  recollect residual :=
    task_residuals_factory
      hn hH factor factory sharp nextNormalizer outerFactory innerWord rightWord
        hword hfactorTruncated added originalRight unchanged originalLeft
          hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual

end RRBrancha

end TCTex
end Towers
