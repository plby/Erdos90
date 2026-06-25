import Towers.Group.Zassenhaus.ReductionOuter
import Towers.Group.Zassenhaus.ResidualBranch

/-!
# Inner-reduction residual recollection with sharp atomic comparison

After recursively recollecting the ranked outer children, every factor left
in the active comparison layer is atomic.  The sharp mixed-source router can
therefore recollect that comparison using only a correction factory, a sharp
router, and the next-stratum normalizer.

The child-to-parent quotient still uses a local current-stratum normalizer.
This file composes the two pieces and exposes the result as a Hall-ranked
branch without requiring a complete current-stratum normalizer family.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/--
Recollect an inner-reduction residual using sharp active-atomic routing for
the comparison half and a local normalizer for the child-to-parent quotient.
-/
noncomputable def
    residuals_sharp_comparison
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
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d))
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
  let rankedOuter :=
    CIChildr.rankedResidualRecollection
      hn hH normalizer factor innerWord rightWord hword rfl
        factor.word_weight_pos hfactorTruncated added originalRight unchanged
          originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  have outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword) := by
    simpa only [rankedOuter,
      CIChildr.rankedResidualRecollection,
      SPFactora.RCSrc.residualRawSource,
      CIChildr.factor_ranked_task] using
        rankedOuter.residualRecollection
  exact
    inner_child_normalization factor innerWord rightWord
      hword children.recollection
      (by
        simpa only [
          innerChildNormalized] using
            comparison)
      outer

/--
Scheduler-facing specialization: recursively recollected children are
supplied over the exact ranked task source used by well-founded induction.
-/
noncomputable def
    task_residuals_sharp
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
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d))
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
  residuals_sharp_comparison
    hn hH factor normalizer factory sharp nextNormalizer innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic
          (fun task htask => residual task (by simpa using htask))

end
  TSRecollb

namespace RRBrancha

open
  TSRecollb

/--
Recipe-correct inner reduction gives a complete Hall-ranked branch when its
comparison is routed sharply and its child-to-parent quotient is normalized
locally.
-/
noncomputable def inner_sharp_comparison
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
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d))
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
    task_residuals_sharp
      hn hH factor normalizer factory sharp nextNormalizer innerWord rightWord
        hword hfactorTruncated added originalRight unchanged originalLeft
          hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual

end RRBrancha

end TCTex
end Towers
