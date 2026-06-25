import
  Submission.Group.Zassenhaus.PolynomialLexicographicScheduling
import Submission.Group.Zassenhaus.HallRankDescent
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.SignedCorrectionSemantics


/-!
# Ranked child sources for concrete polynomial inner-packet outer brackets

The lexicographic scheduler attaches a Hall-rank defect to every factor in an
exact inner-packet outer-bracket worklist.  This file packages those ranked
children together with their strict descent proof and records that forgetting
the ranks recovers the original exact symbolic source.

This is the source-facing interface needed by a recursive Hall collector.
The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactor

/--
A finite symbolic source whose factors carry ranks strictly below one parent
task in the cutoff-defect/Hall-rank relation.
-/
structure RCSrc
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) where
  tasks : List (SPFactor H ι × ℕ)
  tasks_descend :
    ∀ task ∈ tasks,
      HallRankedDescends n task.1 task.2 parent parentRankDefect

namespace RCSrc

/-- Forget the recursion ranks and retain the emitted symbolic factors. -/
def factorSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect) :
    List (SPFactor H ι) :=
  source.tasks.map Prod.fst

/-- Every emitted factor has a rank making it a strict child of the parent. -/
theorem rank_ranked_descends
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent factor : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (hfactor : factor ∈ source.factorSource) :
    ∃ rankDefect : ℕ,
      (factor, rankDefect) ∈ source.tasks ∧
        HallRankedDescends n factor rankDefect parent parentRankDefect := by
  rw [factorSource] at hfactor
  rcases List.mem_map.mp hfactor with ⟨task, htask, hfactor⟩
  subst factor
  exact ⟨task.2, by simpa using htask, source.tasks_descend task htask⟩

end RCSrc
end SPFactor

namespace IBWork

open CEWord

/--
Package the exact concrete outer-bracket worklist as a finite list of strict
Hall-ranked child tasks.
-/
noncomputable def rankedTaskSource
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.RCSrc
      (n := n) inner
        (HallTree.bracketRankDefect
          ((tree inner.word).weight + unchanged.weight)
          originalLeft originalRight) where
  tasks := rankedTasks packet inner right unchanged
  tasks_descend := by
    intro task htask
    exact
      ranked_descends_tasks packet inner right hinnerTruncated
        added originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic htask

/-- Forgetting task ranks recovers the exact concrete worklist source. -/
@[simp]
theorem factor_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource packet inner right hinnerTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic).factorSource =
      factors packet inner right := by
  simp [rankedTaskSource,
    SPFactor.RCSrc.factorSource,
    rankedTasks, List.map_map, Function.comp_def]

/--
The factor source underlying the ranked children still evaluates exactly to
the outer bracket of the reduced inner packet and unchanged right factor.
-/
theorem list_ranked_task
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
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (rankedTaskSource packet inner right hinnerTruncated added
          originalRight unchanged originalLeft hinnerTree hRightLeft
            hRightUnchanged hunchangedBasic).factorSource =
      ⁅SPFactor.listEval (n := n) e
          (basicReductionFactors inner),
        right.eval (n := n) e⁆ := by
  rw [factor_ranked_task]
  exact listEval_factors packet inner right e

/-- The ranked factor source remains physically truncated. -/
theorem truncated_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.IsTruncated n
      (rankedTaskSource packet inner right hinnerTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact isTruncated_factors packet inner right hinnerTruncated

/-- The ranked factor source retains the inner packet's support bound. -/
theorem least_ranked_task
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
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.WordWeightLeast
      (inner.word.weight HEAddres.weight)
      (rankedTaskSource packet inner right hinnerTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact weight_least_factors packet inner right

end IBWork
end TCTex
end Submission

/-!
# Composing signed-polynomial inner-reduction residuals

The true concrete residual splits into atomic-packet-to-children comparison
and children-to-parent comparison.  Recollections of those two pieces compose
into a concrete basic-reduction residual recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace CEWord

/-- Compare the canonical atomic packet with recipe-correct full children. -/
noncomputable def innerComparisonSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    innerOuterFactors factor innerWord rightWord hword

/-- Atomic-to-child comparison inherits parent truncation. -/
theorem truncated_inner_comparison
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor : factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (innerComparisonSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactor x hx

/-- Atomic-to-child comparison stays in the parent stratum physically. -/
theorem least_inner_comparison
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (innerComparisonSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.least_inverse_list
        (least_reduction_factors factor) x hx
  · exact
      least_inner_factors
        factor innerWord rightWord hword x hx

/-- Atomic-to-child comparison evaluates to canonical-packet division. -/
theorem inner_comparison_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerComparisonSource
          factor innerWord rightWord hword) =
      (SPFactor.listEval e
        (basicReductionFactors factor))⁻¹ *
          SPFactor.listEval e
            (innerOuterFactors factor innerWord rightWord hword) := by
  simp [innerComparisonSource,
    SPFactor.list_eval_inverse]

/-- Associated-graded agreement makes comparison one stratum deeper. -/
theorem
    inner_comparison_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerComparisonSource
          factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [inner_comparison_source]
  have hatomic :=
    reduction_inv_series
      (n := n) factor e
  have hchildren :=
    inner_inv_series
      (n := n) factor innerWord rightWord hword e
  convert Subgroup.mul_mem _ hatomic (Subgroup.inv_mem _ hchildren) using 1 ;
    group

/-- Exact two-piece decomposition of the true parent residual. -/
noncomputable def innerDecompositionSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  innerComparisonSource
      factor innerWord rightWord hword ++
    innerRawSource
      factor innerWord rightWord hword

/-- Evaluation of the decomposition recovers the true parent residual. -/
theorem
    inner_reduction_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerDecompositionSource
          factor innerWord rightWord hword) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  rw [innerDecompositionSource,
    SPFactor.listEval_append,
    inner_comparison_source,
    inner_raw_source,
    reduction_raw_source]
  group

end CEWord

namespace
  TRRecoll

/-- Compose recollections of the two inner-reduction residual pieces. -/
noncomputable def inner_outer
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
        (lowerWeight := factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (CEWord.innerComparisonSource
          factor innerWord rightWord hword))
    (outer :
      SSRecol
        (n := n)
        (lowerWeight := factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (CEWord.innerRawSource
          factor innerWord rightWord hword)) :
    TRRecoll
      (n := n) factor where
  higherSource := comparison.higherSource ++ outer.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact comparison.higher_source_truncated x hx
    · exact outer.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact comparison.higher_weight_least x hx
    · exact outer.higher_weight_least x hx
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      comparison.list_higher_raw,
      outer.list_higher_raw,
      ←
        CEWord.inner_reduction_source
          factor innerWord rightWord hword e,
      CEWord.innerDecompositionSource,
      SPFactor.listEval_append]

end
  TRRecoll

end TCTex
end Submission

/-!
# Target-weight structural recollection of concrete polynomial outer brackets

The concrete inner-packet outer-bracket worklist can be raised to any support
target between the first structurally available stratum and its full
lower-central depth.  This exposes the exact endpoint needed by callers while
retaining the non-circular requirement that normalizers are supplied only
strictly above the inner factor's weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace IBWork

/--
Structurally recollect a concrete outer-bracket worklist to any support target
bounded by its full bracket weight.
-/
noncomputable def recollect_normalizer_above
    {d n targetWeight : ℕ}
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
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) :
    SSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) := by
  let initial :=
    source_normalizer_above packet inner right normalizerAbove
      hinnerTruncated
  by_cases htargetTruncated : targetWeight ≤ n
  · exact
      initial.raiseSupportTo hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        hinitialTarget htargetTruncated
        (fun e =>
          Subgroup.lowerCentralSeries_antitone
            (Nat.sub_le_sub_right htargetTotal 1)
            (list_series_sub
              packet inner right e))
  · exact
      {
        higherSource := []
        higher_source_truncated := by
          intro factor hfactor
          simp at hfactor
        higher_weight_least := by
          intro factor hfactor
          simp at hfactor
        list_higher_raw := by
          intro e
          simp only [SPFactor.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SCFactor.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet inner right e)
      }

end IBWork
end TCTex
end Submission

/-!
# Deep normalization of concrete polynomial outer-bracket correction packets

Exact reconstruction recollects a concrete correction packet to full
inner-plus-outer depth using only normalizers strictly above the inner
factor's weight.  Weakening that endpoint back to inner support preserves
the coordinate block and exposes cutoff-defect descent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord
open TPSem

namespace IBRecons

/-- Normalize the reconstructed correction packet at an admissible target. -/
noncomputable def correction_normalization_normalizer
    {d n targetWeight : ℕ}
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
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) :
    TPSem
      (targetWeight - 1)
      (IBWork.correctionPacket
        packet inner right) :=
  (IBWork.correctionPacket
    packet inner right)
      |>.semantic_normalization_support
        (recollection_normalizer_above
          hn hH packet inner right normalizerAbove hinnerTruncated
            hinitialTarget htargetTotal)
        (normalizerAbove targetWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)

/-- Normalize the correction packet at full inner-plus-outer depth. -/
noncomputable def
    normalization_normalizer_above
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
      inner.word.weight HEAddres.weight < n) :
    TPSem
      (inner.word.weight HEAddres.weight +
        right.word.weight HEAddres.weight - 1)
      (IBWork.correctionPacket
        packet inner right) :=
  correction_normalization_normalizer hn hH packet
    inner right normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

/-- Expose the full-depth endpoint sharply above the inner parent. -/
noncomputable def
    sharp_above_total
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
      inner.word.weight HEAddres.weight < n) :
    TPSem
      (inner.word.weight HEAddres.weight)
      (IBWork.correctionPacket
        packet inner right) :=
  (normalization_normalizer_above hn hH packet
    inner right normalizerAbove hinnerTruncated).weaken (by
      have hrightPos := right.word_weight_pos
      omega)

/-- Replacing the inner parent by the sharp correction endpoint descends. -/
lemma
    normalization_total_multiset
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
    (P :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (sharp_above_total
          hn hH packet inner right normalizerAbove
            hinnerTruncated).coordinates.factors (n := n))
      (P ++ [inner]) :=
  multisetAppendSingleton
    (sharp_above_total
      hn hH packet inner right normalizerAbove hinnerTruncated)
    P

end IBRecons
end TCTex
end Submission

/-!
# Ranked signed-polynomial children for inner Hall reduction

Each full-weight outer child is indexed by a Hall-basic inner representative.
The classical reverse Hall-bracket rank defect therefore attaches directly to
the finite child packet and strictly decreases at fixed total weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IRChildr

/-- Attach the classical Hall-bracket rank defect to every full outer child. -/
noncomputable def rankedTasks
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d)) :
    List
      (SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j).map fun i =>
    (innerOuterFactor factor innerWord rightWord hword i,
      HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged)

/-- Membership in the ranked child list exposes its Hall-basic inner index. -/
theorem index_ranked_tasks
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask : task ∈ rankedTasks factor innerWord rightWord hword unchanged) :
    ∃ i :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight,
      task =
        (innerOuterFactor factor innerWord rightWord hword i,
          HallTree.bracketRankDefect
            ((tree innerWord).weight + unchanged.weight)
            (HallTree.indexedBasicTree i) unchanged) := by
  rw [rankedTasks] at htask
  rcases List.mem_map.mp htask with ⟨i, _hi, htask⟩
  exact ⟨i, htask.symm⟩

/-- Every indexed basic inner representative has smaller bracket-rank defect. -/
theorem bracket_rank_defect
    {d : ℕ}
    (innerWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged <
      HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight := by
  apply HallTree.bracket_defect_both hRightLeft
  · apply
      HallTree.weight_add_left added originalRight
        (HallTree.indexedBasicTree i)
    rw [HallTree.indexed_tree_weight, hinnerTree]
    rfl
  · exact hRightUnchanged
  · exact HallTree.indexed_tree i
  · exact hunchangedBasic
  · rw [HallTree.indexed_tree_weight]
    exact Nat.le_add_right _ _
  · exact Nat.le_add_left _ _

/-- Every recipe-correct full outer child descends at fixed total weight. -/
theorem ranked_descends_tasks
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask : task ∈ rankedTasks factor innerWord rightWord hword unchanged) :
    SPFactor.HallRankedDescends n task.1 task.2 factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) := by
  rcases
      index_ranked_tasks
        factor innerWord rightWord hword unchanged htask with
    ⟨i, rfl⟩
  apply
    SPFactor.ranked_descends_defect
  · exact
      inner_outer_factor
        factor innerWord rightWord hword i
  · exact
      bracket_rank_defect innerWord added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic i

/-- Package full outer children as strict Hall-ranked tasks. -/
noncomputable def rankedTaskSource
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.RCSrc
      (n := n) factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  tasks := rankedTasks factor innerWord rightWord hword unchanged
  tasks_descend := by
    intro task htask
    exact
      ranked_descends_tasks factor innerWord rightWord hword
        added originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic htask

@[simp]
theorem tasks_ranked_task
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic).tasks =
      rankedTasks factor innerWord rightWord hword unchanged :=
  rfl

@[simp]
theorem factor_ranked_task
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic).factorSource =
      innerOuterFactors factor innerWord rightWord hword := by
  simp [rankedTaskSource,
    SPFactor.RCSrc.factorSource,
    rankedTasks, innerOuterFactors, List.map_map, Function.comp_def]

/-- The ranked factor source evaluates to the child packet. -/
theorem list_ranked_task
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (rankedTaskSource (n := n) factor innerWord rightWord hword added
          originalRight unchanged originalLeft hinnerTree hRightLeft
            hRightUnchanged hunchangedBasic).factorSource =
      SPFactor.listEval e
        (innerOuterFactors factor innerWord rightWord hword) := by
  rw [factor_ranked_task]

/-- The ranked full outer-child source inherits parent truncation. -/
theorem truncated_ranked_task
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (rankedTaskSource (n := n) factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact
    truncated_inner_factors
      factor innerWord rightWord hword hfactorTruncated

/-- The ranked full outer-child source stays in the parent's stratum. -/
theorem least_ranked_task
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (rankedTaskSource (n := n) factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact
    least_inner_factors
      factor innerWord rightWord hword

end IRChildr
end TCTex
end Submission

/-!
# Ranked target recollections for concrete polynomial outer brackets

The exact polynomial outer-bracket worklist emitted after reducing an inner
Hall packet has two complementary properties:

* every emitted factor is a strict cutoff-defect/Hall-rank child;
* structural normalization recollects the erased source at any support target
  up to the full outer-bracket weight.

This file packages those properties together.  It is the symbolic analogue of
the inner-span branch in the classical Hall collector: recursively scheduled
outer-bracket tasks come with one exact, semantically recollected source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactor

/--
A finite strict Hall-ranked child source together with a semantic recollection
of its erased symbolic factors.
-/
structure RankedRecollectedChild
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) where
  source :
    RCSrc (n := n) parent parentRankDefect
  recollection :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource

end SPFactor

open CEWord

namespace IBWork

/--
Package the exact generated outer-bracket worklist as strict Hall-ranked
children recollected at a chosen support target.
-/
noncomputable def rankedTargetRecollection
    {d n targetWeight : ℕ}
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
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) :
    SPFactor.RankedRecollectedChild
      (n := n) (lowerWeight := targetWeight) inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) where
  source :=
    rankedTaskSource packet inner right hinnerTruncated added originalRight
      unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
        hunchangedBasic
  recollection := by
    rw [factor_ranked_task]
    exact
      recollect_normalizer_above hn hH packet inner right
        normalizerAbove hinnerTruncated hinitialTarget htargetTotal

/--
The recollected higher source still evaluates exactly to the generated
outer bracket of the reduced inner packet.
-/
theorem ranked_target_recollection
    {d n targetWeight : ℕ}
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
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (rankedTargetRecollection hn hH packet inner right normalizerAbove
          hinnerTruncated added originalRight unchanged originalLeft hinnerTree
            hRightLeft hRightUnchanged hunchangedBasic hinitialTarget
              htargetTotal).recollection.higherSource =
      ⁅SPFactor.listEval (n := n) e
          (basicReductionFactors inner),
        right.eval (n := n) e⁆ := by
  rw [(rankedTargetRecollection hn hH packet inner right normalizerAbove
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic hinitialTarget
        htargetTotal).recollection.list_higher_raw]
  exact
    list_ranked_task packet inner right hinnerTruncated
      added originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic e

/--
Specialize the ranked generated outer-bracket branch to its full
lower-central support depth.
-/
noncomputable def rankedTotalRecollection
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
    SPFactor.RankedRecollectedChild
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
      inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) :=
  rankedTargetRecollection hn hH packet inner right normalizerAbove
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic
        (by
          have hrightPos := right.word_weight_pos
          omega)
        (Nat.le_refl _)

end IBWork
end TCTex
end Submission

/-!
# Structural recollection of polynomial reconstruction-worklist residuals

The atomic and exact reconstruction outer worklists can both be recollected
at full bracket depth using only normalizers strictly above the inner factor's
weight.  Inverting the first recollection and appending the second recollects
their quotient at that same full depth.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


namespace IBRecons

/--
Structurally recollect the quotient from the atomic outer worklist to the
exact reconstruction worklist at full bracket depth.
-/
noncomputable def
    residual_normalizer_total
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
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (residualRawSource packet inner right) :=
  (IBWork.recollect_normalizer_above
      hn hH packet inner right normalizerAbove hinnerTruncated
        (by
          have hrightPos := right.word_weight_pos
          omega)
        (Nat.le_refl _))
    |>.inverse.append
      (recollection_above_total hn hH packet inner
        right normalizerAbove hinnerTruncated)

/--
Structurally recollect the reconstruction quotient one layer above the full
outer-bracket weight.  At the nilpotent cutoff the quotient vanishes.
-/
noncomputable def
    recollection_normalizer_total
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
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (residualRawSource packet inner right) := by
  let initial :=
    residual_normalizer_total
      hn hH packet inner right normalizerAbove hinnerTruncated
  by_cases htargetTruncated :
      inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1 ≤ n
  · exact
      initial.raiseSupportTo hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by
            have hrightPos := right.word_weight_pos
            omega))
        (by
          have hinnerPos := inner.word_weight_pos
          have hrightPos := right.word_weight_pos
          omega)
        (by omega)
        htargetTruncated
        (fun e => by
          simpa using
            raw_series_add
              packet inner right e)
  · exact
      recollection_terminal packet inner right (by omega)

end IBRecons
end TCTex
end Submission

/-!
# Ranked residual recollections for signed-polynomial outer children

A Hall-ranked child packet rewrites one parent at fixed symbolic weight.  The
quotient between that packet and its parent is the genuinely higher residual.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor
namespace RCSrc

/-- Invert the child packet and append its original parent. -/
def residualRawSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect) :
    List (SPFactor H ι) :=
  SPFactor.inverseList source.factorSource ++ [parent]

/-- Evaluation of the ranked residual source is child-packet division. -/
theorem list_raw_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e source.residualRawSource =
      (SPFactor.listEval e source.factorSource)⁻¹ *
        parent.eval e := by
  simp [residualRawSource, SPFactor.list_eval_inverse]

end RCSrc

/-- Strict ranked children with a deeper recollection of their quotient. -/
structure RRRecol
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) where
  source :
    RCSrc (n := n) parent parentRankDefect
  residualRecollection :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H source.residualRawSource

namespace RRRecol

/-- Ranked children followed by their deeper residual. -/
def rewriteSource
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect) :
    List (SPFactor H ι) :=
  recollection.source.factorSource ++
    recollection.residualRecollection.higherSource

/-- Ranked children followed by residual reconstruct their parent exactly. -/
theorem list_rewrite_parent
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e recollection.rewriteSource =
      parent.eval e := by
  rw [rewriteSource, SPFactor.listEval_append,
    recollection.residualRecollection.list_higher_raw,
    recollection.source.list_raw_source]
  group

/-- Truncation of ranked children extends to the one-step rewrite. -/
theorem truncated_rewrite_source
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (hsource :
      SPFactor.IsTruncated n
        recollection.source.factorSource) :
    SPFactor.IsTruncated n recollection.rewriteSource := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact hsource factor hfactor
  · exact
      recollection.residualRecollection.higher_source_truncated factor hfactor

/-- Child support extends to a rewrite when the residual is strong enough. -/
theorem least_rewrite_source
    {d n lowerWeight sourceWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (hsource :
      SPFactor.WordWeightLeast sourceWeight
        recollection.source.factorSource)
    (hweight : sourceWeight ≤ lowerWeight) :
    SPFactor.WordWeightLeast
      sourceWeight recollection.rewriteSource := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact hsource factor hfactor
  · exact hweight.trans
      (recollection.residualRecollection.higher_weight_least
        factor hfactor)

end RRRecol
end SPFactor

open CEWord

namespace IRChildr

/-- Package full outer children with their next-stratum residual recollection. -/
noncomputable def rankedResidualRecollection
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
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.RRRecol
      (n := n) (lowerWeight := lowerWeight + 1) factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  source :=
    rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  residualRecollection := by
    rw [SPFactor.RCSrc.residualRawSource,
      factor_ranked_task]
    exact
      normalizer.recollection_inner_raw
        hn hH factor innerWord rightWord hword hfactorWeight hlowerWeightPos
          hlowerWeightTruncated

end IRChildr
end TCTex
end Submission

/-!
# Normalized structural-restart quotients for polynomial outer brackets

The exact reconstruction outer worklist differs from its atomic approximation
by a quotient supported strictly above the full outer-bracket weight.  The
structural recollection endpoint therefore normalizes this quotient to a
coordinate block that both reconstructs the exact worklist and decreases the
cutoff-defect multiset when it replaces the inner factor.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


namespace IBRecons

/--
Normalize the reconstruction quotient one layer above full outer-bracket
weight using only normalizers strictly above the inner factor.
-/
noncomputable def
    residual_normalization_total
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
      inner.word.weight HEAddres.weight < n) :
    SSNorm
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (residualRawSource packet inner right) :=
  (recollection_normalizer_total
      hn hH packet inner right normalizerAbove hinnerTruncated)
    |>.toSourceNormalization
      (normalizerAbove
        (inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1)
        (by
          have hrightPos := right.word_weight_pos
          omega))

/-- The normalized quotient still evaluates to outer-worklist division. -/
theorem
    normalization_above_total
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
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        ((residual_normalization_total
          hn hH packet inner right normalizerAbove
            hinnerTruncated).coordinates.factors (n := n)) =
      (SPFactor.listEval e
        (IBWork.factors packet
          inner right))⁻¹ *
        SPFactor.listEval e
          (factors packet inner right) := by
  rw [
    (residual_normalization_total
      hn hH packet inner right normalizerAbove
        hinnerTruncated).coordinates_raw_source,
    list_raw_source]

/--
Appending the normalized quotient to the atomic outer worklist reconstructs
the exact reconstruction worklist.
-/
theorem
    atomic_normalization_reconstruction
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
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
          (IBWork.factors packet
            inner right) *
        SPFactor.listEval (n := n) e
          ((residual_normalization_total
            hn hH packet inner right normalizerAbove
              hinnerTruncated).coordinates.factors (n := n)) =
      SPFactor.listEval e
        (factors packet inner right) := by
  rw [
    normalization_above_total
      hn hH packet inner right normalizerAbove hinnerTruncated e]
  group

/-- Every retained reconstruction-quotient coordinate improves the inner defect. -/
lemma
    normalization_normalizer_total
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
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx :
      x ∈
        (residual_normalization_total
          hn hH packet inner right normalizerAbove
            hinnerTruncated).coordinates.factors (n := n)) :
    SPFactor.cutoffDefect n x <
      SPFactor.cutoffDefect n inner := by
  have hxSupported :=
    (residual_normalization_total
      hn hH packet inner right normalizerAbove
        hinnerTruncated).factors_weight_least x hx
  have hxTruncated :=
    (residual_normalization_total
      hn hH packet inner right normalizerAbove
        hinnerTruncated).factors_isTruncated x hx
  have hrightPos := right.word_weight_pos
  simp only [SPFactor.cutoffDefect]
  omega

/-- Replacing the inner factor by the normalized quotient strictly descends. -/
lemma
    normalizer_total_multiset
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
    (P :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (residual_normalization_total
          hn hH packet inner right normalizerAbove
            hinnerTruncated).coordinates.factors (n := n))
      (P ++ [inner]) := by
  unfold SPFactor.CutoffDefectMultiset
  rw [SPFactor.defect_multiset_append,
    SPFactor.defect_multiset_append,
    SPFactor.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_forall
  intro y hy
  rw [SPFactor.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact
    normalization_normalizer_total
      hn hH packet inner right normalizerAbove hinnerTruncated hx

end IBRecons
end TCTex
end Submission
