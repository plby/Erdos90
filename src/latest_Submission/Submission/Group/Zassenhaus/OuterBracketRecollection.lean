import Submission.Group.Zassenhaus.RankedStructuralRestarts
import Submission.Group.Zassenhaus.RankedResidualRecursion
import Submission.Group.Zassenhaus.PolynomialRankedSupport
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.SignedReductionFactors
import Submission.Group.Zassenhaus.ReverseOrientationResiduals
import Submission.Group.Zassenhaus.RankedChildSources

/-!
# Recursive recollection through concrete outer-bracket structural restarts

The concrete reconstruction restart emits strict Hall-ranked atomic
outer-bracket tasks and a normalized quotient above the full bracket weight.
Supplying recursive basic residual recollections for the emitted tasks
recollects the exact reconstructed outer bracket without a same-layer
normalizer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open CEWord

namespace IBRecons

/--
Recollect an exact reconstruction outer bracket from recursively recollected
strict Hall-ranked atomic tasks and its normalized higher quotient.
-/
noncomputable def
    recollect_restart_residuals
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
    (residual :
      ∀ task ∈
          IBWork.rankedTasks
            packet inner right unchanged,
        TRRecoll
          (n := n) task.1) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) := by
  let restart :=
    rankedStructuralRestart hn hH packet inner right normalizerAbove
      hinnerTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged hunchangedBasic
  apply restart.target_source_recollection
  · have sourceRecollection :=
      IBWork.recollection_basic_residuals
        packet inner right hinnerTruncated added originalRight unchanged
          originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
            residual
    simpa only [restart, rankedStructuralRestart,
      IBWork.factor_ranked_task] using
        sourceRecollection
  · have hrightPos := right.word_weight_pos
    omega

/--
The recursively recollected concrete restart source still evaluates exactly
to the original outer commutator.
-/
theorem
    higher_restart_residuals
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
    (residual :
      ∀ task ∈
          IBWork.rankedTasks
            packet inner right unchanged,
        TRRecoll
          (n := n) task.1)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (recollect_restart_residuals
          hn hH packet inner right normalizerAbove hinnerTruncated added
            originalRight unchanged originalLeft hinnerTree hRightLeft
              hRightUnchanged hunchangedBasic residual).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ := by
  rw [
    (recollect_restart_residuals
      hn hH packet inner right normalizerAbove hinnerTruncated added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic
            residual).list_higher_raw,
    listEval_factors]

end IBRecons

namespace IBRecons

/--
Use a global Hall-ranked basic-residual scheduler directly as the recursive
input to one concrete structural restart.
-/
noncomputable def
    structural_restart_scheduler
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
    (scheduler :
      TRSchedu
        (d := d) (n := n) (ι := ι))
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
  recollect_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (fun task _htask =>
            scheduler.residualRecollection task.1 task.2)

end IBRecons

end TCTex
end Submission

/-!
# Active-atomic recollection after recursive outer-child normalization

Recursive normalization of one full-weight child replaces it by its atomic
packet followed by a strictly heavier residual. Folding over ranked children
preserves the invariant that each active-layer factor is atomic.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u v

open CEWord

/-- An upward recollection whose remaining active-layer factors are atomic. -/
structure
    TORecoll
    {d n lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    {ι : Type}
    (rawSource : List (SPFactor H ι)) where
  recollection :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H rawSource
  active_atoms_or :
    ∀ factor ∈ recollection.higherSource,
      lowerWeight <
          factor.word.weight HEAddres.weight ∨
        ∃ address : HEAddres H,
          factor.word = .atom address ∧ address.weight = lowerWeight

namespace
  TORecoll

/-- The empty recollection preserves the active-atomic invariant. -/
def empty
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type} :
    TORecoll
      (n := n) (lowerWeight := lowerWeight) H
      ([] : List (SPFactor H ι)) where
  recollection := .empty
  active_atoms_or := by
    intro factor hfactor
    change factor ∈ ([] : List (SPFactor H ι)) at hfactor
    simp at hfactor

/-- Concatenation preserves the active-atomic invariant. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {leftSource rightSource : List (SPFactor H ι)}
    (left :
      TORecoll
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      TORecoll
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    TORecoll
      (n := n) (lowerWeight := lowerWeight) H (leftSource ++ rightSource) where
  recollection := left.recollection.append right.recollection
  active_atoms_or := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.active_atoms_or factor hfactor
    · exact right.active_atoms_or factor hfactor

/-- Fold active-atomic recollections across a finite `flatMap` source. -/
def flatMap
    {α : Type v}
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (items : List α)
    (rawSource : α → List (SPFactor H ι))
    (recollection :
      ∀ item ∈ items,
        TORecoll
          (n := n) (lowerWeight := lowerWeight) H (rawSource item)) :
    TORecoll
      (n := n) (lowerWeight := lowerWeight) H (items.flatMap rawSource) := by
  induction items with
  | nil =>
      exact empty
  | cons head tail ih =>
      exact
        append
          (recollection head (by simp))
          (ih fun item hitem => recollection item (by simp [hitem]))

/-- Route an active-atomic recollection whose value is semantically deeper. -/
noncomputable def recollectionSemanticallyHigher
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (source :
      TORecoll
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hrawSourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H rawSource := by
  let tail :=
    factory.atoms_or_higher
      hn H hH sharp nextNormalizer source.recollection.higherSource
        hlowerWeightPos hlowerWeightTruncated
          source.recollection.higher_source_truncated
            source.active_atoms_or
              (fun e => by
                rw [source.recollection.list_higher_raw]
                exact hrawSourceMem e)
  exact
    {
      higherSource := tail.higherSource
      higher_source_truncated := tail.higher_source_truncated
      higher_weight_least :=
        tail.higher_weight_least
      list_higher_raw := by
        intro e
        rw [tail.list_higher_raw,
          source.recollection.list_higher_raw]
    }

end
  TORecoll

namespace
  TRRecoll

/-- Atomic packets plus stronger residuals preserve the active-atomic invariant. -/
noncomputable def atomsOrRecollection
    {d n lowerWeight : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (recollection :
      TRRecoll
        (n := n) factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hlowerWeight :
      lowerWeight ≤ factor.word.weight HEAddres.weight) :
    TORecoll
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) [factor] where
  recollection :=
    recollection.singletonSourceRecollection hfactorTruncated hlowerWeight
  active_atoms_or := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxWeight := word_reduction_factors factor hx
      rcases lt_or_eq_of_le hlowerWeight with hlowerWeight | hlowerWeight
      · exact Or.inl (by omega)
      · right
        rcases atom_basic_factors factor hx with
          ⟨address, hword, haddressWeight⟩
        exact ⟨address, hword, by omega⟩
    · left
      have hxWeight :=
        recollection.higher_least_succ x hx
      omega

end
  TRRecoll

open TORecoll

namespace SPFactor
namespace RCSrc

/-- Fold recursively supplied residuals into an active-atomic inventory. -/
noncomputable def atoms_recollect_residuals
    {d n lowerWeight parentRankDefect : ℕ}
    {ι : Type}
    {parent :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (source : RCSrc (n := n) parent parentRankDefect)
    (hsourceTruncated :
      SPFactor.IsTruncated n source.factorSource)
    (hsourceSupported :
      SPFactor.WordWeightLeast
        lowerWeight source.factorSource)
    (residual :
      ∀ task ∈ source.tasks,
        TRRecoll
          (n := n) task.1) :
    TORecoll
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source.factorSource := by
  have hfactorSource :
      source.factorSource =
        source.tasks.flatMap
          (fun task :
              SPFactor
                  (concreteBasicCommutators.{u} d) ι ×
                ℕ =>
            [task.1]) := by
    simp only [factorSource]
    induction source.tasks with
    | nil =>
        rfl
    | cons task tasks ih =>
        simp only [List.map_cons, List.flatMap_cons, List.singleton_append, ih]
  rw [hfactorSource]
  exact
    flatMap
      (α :=
        SPFactor
            (concreteBasicCommutators.{u} d) ι ×
          ℕ)
      (n := n) (lowerWeight := lowerWeight)
      (H := concreteBasicCommutators.{u} d)
      (items := source.tasks)
      (rawSource :=
        fun task :
            SPFactor
                (concreteBasicCommutators.{u} d) ι ×
              ℕ =>
          [task.1])
      (recollection :=
        fun
            (task :
              SPFactor
                  (concreteBasicCommutators.{u} d) ι ×
                ℕ)
            (htask : task ∈ source.tasks) =>
          (residual task htask).atomsOrRecollection
            (hsourceTruncated task.1
              (source.fst_factor_tasks htask))
            (hsourceSupported task.1
              (source.fst_factor_tasks htask)))

end RCSrc
end SPFactor

namespace IRChildr

/-- Ranked recursive child normalization preserves an active-atomic inventory. -/
noncomputable def
    active_atoms_residuals
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
      ∀ task ∈ rankedTasks factor innerWord rightWord hword unchanged,
        TRRecoll
          (n := n) task.1) :
    TORecoll
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
  apply source.atoms_recollect_residuals
  · rw [hsource]
    exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactorTruncated
  · rw [hsource]
    exact
      least_inner_factors factor innerWord rightWord
        hword
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end IRChildr

namespace TSFtry

/-- Sharply route the parent comparison after recursive child recollection. -/
noncomputable def
    child_normalized_raw
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
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (children :
      TORecoll
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    SSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerChildNormalized
        factor innerWord rightWord hword children.recollection) := by
  apply
    factory.atoms_or_higher
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
  · exact factor.word_weight_pos
  · exact hfactorTruncated
  · exact
      truncNormalizedComparison
        factor innerWord rightWord hword children.recollection hfactorTruncated
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · right
      exact atom_reduction_factors factor hx
    · exact children.active_atoms_or x hx
  · exact fun e =>
      list_inner_series
        factor innerWord rightWord hword children.recollection e

end TSFtry

end TCTex
end Submission

/-!
# Automatic residual recollection after ranked inner reduction

Recipe-correct inner reduction produces strictly Hall-ranked full-weight
children. Once recursive induction has recollected those children, a
current-stratum semantic normalizer removes the remaining comparison and the
ranked child-to-parent quotient.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace
  TRRecoll

/-- Build the parent recollection from ranked children and one stratum normalizer. -/
noncomputable def
    inner_residuals_normalizer
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
    IRChildr.recollection_basic_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  let comparison :=
    normalizer.child_normalized_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
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
    inner_ranked_residuals factor innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual
          (by
            simpa only [
              innerChildNormalized]
              using comparison)
          outer

/-- Use the normalizer family at the parent factor's Hall weight. -/
noncomputable def
    ranked_residuals_normalizer
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
        (n := n) (concreteBasicCommutators.{u} d))
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
          (n := n) task.1) :
    TRRecoll
      (n := n) factor :=
  inner_residuals_normalizer hn hH factor
    (family.normalizer
      (factor.word.weight HEAddres.weight))
    innerWord rightWord hword hfactorTruncated added originalRight unchanged
      originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
        residual

/-- Scheduler-facing specialization over the actual ranked task source. -/
noncomputable def
    ranked_task_residuals
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
        (n := n) (concreteBasicCommutators.{u} d))
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
          (IRChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TRRecoll
          (n := n) task.1) :
    TRRecoll
      (n := n) factor :=
  ranked_residuals_normalizer hn hH
    family factor innerWord rightWord hword hfactorTruncated added originalRight
      unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
        hunchangedBasic
        (fun task htask => residual task (by simpa using htask))

end
  TRRecoll

end TCTex
end Submission
