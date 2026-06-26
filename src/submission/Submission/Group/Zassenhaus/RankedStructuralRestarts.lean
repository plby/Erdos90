import Submission.Group.Zassenhaus.RankedChildSources
import Submission.Group.Zassenhaus.PolynomialRankedSupport
import Submission.Group.Zassenhaus.ReverseOrientationResiduals
import Submission.Group.Zassenhaus.PolynomialBracketSupport

/-!
# Ranked structural restarts for concrete polynomial outer brackets

The atomic inner-packet outer-bracket worklist is a finite source of strict
Hall-ranked child tasks.  Its normalized reconstruction quotient is supported
strictly above the full outer-bracket weight.  Together they form one
scheduler-facing structural restart whose rewrite evaluates to the original
outer commutator and whose quotient block decreases cutoff defects.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open CEWord

namespace IBRecons

/--
Package ranked atomic outer-bracket children and the normalized
reconstruction quotient as one structural restart.
-/
noncomputable def rankedStructuralRestart
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.RSRestar
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1)
      inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight)
      (factors packet inner right) where
  source :=
    IBWork.rankedTaskSource
      packet inner right hinnerTruncated added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  normalization := by
    rw [
      IBWork.factor_ranked_task]
    exact
      residual_normalization_total
        hn hH packet inner right normalizerAbove hinnerTruncated

/-- The concrete structural restart rewrites exactly to the outer commutator. -/
theorem rewrite_structural_restart
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (rankedStructuralRestart hn hH packet inner right normalizerAbove
          hinnerTruncated added originalRight unchanged originalLeft hinnerTree
            hRightLeft hRightUnchanged hunchangedBasic).rewriteSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ := by
  rw [
    (rankedStructuralRestart hn hH packet inner right normalizerAbove
      hinnerTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged
          hunchangedBasic).list_rewrite_target,
    listEval_factors]

/--
The reconstructed outer branch recollects to ranked atomic children followed
by the strictly higher restart quotient.
-/
noncomputable def recollection_structural_restart
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  (rankedStructuralRestart hn hH packet inner right normalizerAbove
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic)
    |>.targetSourceRecollection
      (by
        simpa only [rankedStructuralRestart,
          IBWork.factor_ranked_task] using
            IBWork.isTruncated_factors
              packet inner right hinnerTruncated)
      (by
        simpa only [rankedStructuralRestart,
          IBWork.factor_ranked_task] using
            IBWork.weight_least_factors
              packet inner right)
      (by
        have hrightPos := right.word_weight_pos
        omega)

/-- The concrete restart quotient decreases cutoff defects against the inner factor. -/
lemma structural_restart_multiset
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (P :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (rankedStructuralRestart hn hH packet inner right normalizerAbove
          hinnerTruncated added originalRight unchanged originalLeft hinnerTree
            hRightLeft hRightUnchanged
              hunchangedBasic).normalization.coordinates.factors (n := n))
      (P ++ [inner]) :=
  (rankedStructuralRestart hn hH packet inner right normalizerAbove
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic)
    |>.multiset_restart_singleton
      (by
        have hrightPos := right.word_weight_pos
        omega)
      P

end IBRecons
end TCTex
end Submission

/-!
# Recursive recollection of concrete polynomial inner-packet outer brackets

The concrete inner-packet outer-bracket worklist is an exact symbolic source.
Its ranked task source strictly descends lexicographically.  Once recursive
basic residual recollections are available for every emitted task, singleton
reconstruction and finite source composition recollect the complete exact
worklist.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IBWork

/--
Recollect the exact outer-bracket worklist from concrete basic residual
recollections for all of its strictly descending Hall-ranked tasks.
-/
noncomputable def recollection_basic_residuals
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈ rankedTasks packet inner right unchanged,
        TRRecoll
          (n := n) task.1) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) := by
  let source :=
    rankedTaskSource packet inner right hinnerTruncated added originalRight
      unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
        hunchangedBasic
  have hsource :
      source.factorSource = factors packet inner right := by
    dsimp only [source]
    exact
      factor_ranked_task packet inner right hinnerTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic
  rw [← hsource]
  apply source.recollection_basic_residuals
  · rw [hsource]
    exact isTruncated_factors packet inner right hinnerTruncated
  · rw [hsource]
    exact weight_least_factors packet inner right
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end IBWork
end TCTex
end Submission

/-!
# Parent residuals after recursively normalizing full outer children

Recipe-correct inner reduction emits finitely many full-weight outer children.
Once recursive Hall-ranked induction has recollected those children
individually, their complete packet has an exact same-stratum normalization.

The remaining parent residual then splits into one atomic-to-normalized-child
comparison source and the already identified child-to-parent residual source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IRChildr

/-- Recursively supplied residual recollections normalize the full child packet. -/
noncomputable def recollection_basic_residuals
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
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
          rankedTasks factor innerWord rightWord hword unchanged,
        TRRecoll
          (n := n) task.1) :
    SSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (innerOuterFactors factor innerWord rightWord hword) := by
  let source :=
    rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  have hsource :
      source.factorSource =
        innerOuterFactors factor innerWord rightWord hword := by
    dsimp only [source]
    exact
      factor_ranked_task factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic
  rw [← hsource]
  apply source.recollection_basic_residuals
  · rw [hsource]
    exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactorTruncated
  · rw [hsource]
    exact
      least_inner_factors
        factor innerWord rightWord hword
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end IRChildr

namespace
  TRRecoll

/-- Compose child normalization, atomic comparison, and outer residual recollection. -/
noncomputable def inner_child_normalization
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (comparison :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactor.inverseList (basicReductionFactors factor) ++
          children.higherSource))
    (outer :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword)) :
    TRRecoll
      (n := n) factor :=
  inner_outer factor innerWord rightWord hword
    (comparison.of_list_eq fun e => by
      rw [SPFactor.listEval_append,
        SPFactor.list_eval_inverse,
        children.list_higher_raw,
        inner_comparison_source])
    outer

/-- Specialize the parent bridge to the ranked child packet. -/
noncomputable def inner_ranked_residuals
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
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
          (n := n) task.1)
    (comparison :
      let children :=
        IRChildr.recollection_basic_residuals
          factor innerWord rightWord hword hfactorTruncated added originalRight
            unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
              hunchangedBasic residual
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactor.inverseList (basicReductionFactors factor) ++
          children.higherSource))
    (outer :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword)) :
    TRRecoll
      (n := n) factor := by
  let children :=
    IRChildr.recollection_basic_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  exact
    inner_child_normalization factor innerWord rightWord
      hword children comparison outer

end
  TRRecoll

end TCTex
end Submission

/-!
# Atomic comparison after recursively normalizing full outer children

After recursively recollecting the full-weight children emitted by inner Hall
reduction, the remaining fixed-weight comparison source consists of the
inverse canonical parent packet followed by the normalized child source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace CEWord

/-- Fixed-weight comparison source remaining after recursive child normalization. -/
noncomputable def innerChildNormalized
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    children.higherSource

/-- The post-recursion atomic comparison inherits physical truncation. -/
theorem
    truncNormalizedComparison
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (innerChildNormalized
        factor innerWord rightWord hword children) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact children.higher_source_truncated x hx

/-- The post-recursion atomic comparison remains physically in the parent layer. -/
theorem
    normalizedComparisonSource
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (innerChildNormalized
        factor innerWord rightWord hword children) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.least_inverse_list
        (least_reduction_factors factor) x hx
  · exact children.higher_weight_least x hx

/-- Recursive child normalization preserves the atomic comparison evaluation. -/
theorem
    child_normalized_comparison
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerChildNormalized
          factor innerWord rightWord hword children) =
      SPFactor.listEval e
        (innerComparisonSource
          factor innerWord rightWord hword) := by
  rw [innerChildNormalized,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    children.list_higher_raw,
    inner_comparison_source]

/-- The post-recursion atomic comparison evaluates one stratum deeper. -/
theorem
    list_inner_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerChildNormalized
          factor innerWord rightWord hword children) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [child_normalized_comparison]
  exact
    inner_comparison_series
      factor innerWord rightWord hword e

end CEWord

namespace TSNormal

/-- Recollect the post-recursion comparison into the next support layer. -/
noncomputable def
    child_normalized_raw
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (children :
      SSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (CEWord.innerOuterFactors
          factor innerWord rightWord hword)) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (CEWord.innerChildNormalized
        factor innerWord rightWord hword children) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
    (CEWord.innerChildNormalized
      factor innerWord rightWord hword children)
    hlowerWeightPos hlowerWeightTruncated
    (CEWord.truncNormalizedComparison
      factor innerWord rightWord hword children (by
        rw [hfactorWeight]
        exact hlowerWeightTruncated))
    (by
      rw [← hfactorWeight]
      exact
        CEWord.normalizedComparisonSource
          factor innerWord rightWord hword children)
    (fun e => by
      rw [← hfactorWeight]
      exact
        CEWord.list_inner_series
          factor innerWord rightWord hword children e)

end TSNormal

end TCTex
end Submission
