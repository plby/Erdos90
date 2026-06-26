import Submission.Group.Zassenhaus.ReductionFactors
import Submission.Group.Zassenhaus.RankedChildRecollection

/-!
# Singleton recollection from concrete basic residuals

A concrete basic-reduction residual recollects the quotient between one
symbolic factor and its finite atomic Hall packet.  Prefixing the recollected
residual by that packet reconstructs the original singleton source.

This file packages that exact reconstruction and folds it over ranked child
sources.  It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/--
Prefix a recollected concrete residual by its atomic Hall packet to recollect
the original singleton factor at any weaker support bound.
-/
noncomputable def singletonSourceRecollection
    {d n inputWeight lowerWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (hlowerWeight :
      lowerWeight ≤
        factor.word.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) [factor] where
  higherSource := basicReductionFactors factor ++ recollection.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact truncated_reduction_factors factor hfactorTruncated x hx
    · exact recollection.higher_source_truncated x hx
  higher_weight_least := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hlowerWeight.trans
        (least_reduction_factors factor x hx)
    · exact hlowerWeight.trans (Nat.le_succ _ |>.trans
        (recollection.higher_least_succ x hx))
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      recollection.list_higher_raw,
      reduction_raw_source]
    simp only [SPFactora.listEval_cons,
      SPFactora.listEval_nil, mul_one]
    group

end
  TSRecollb

namespace SPFactora
namespace RCSrc

/-- A ranked task's factor belongs to the erased source. -/
theorem fst_factor_tasks
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {task : SPFactora H inputWeight × ℕ}
    (htask : task ∈ source.tasks) :
    task.1 ∈ source.factorSource :=
  List.mem_map.mpr ⟨task, htask, rfl⟩

/--
Recollect an erased canonical Hall-ranked source from recursively supplied
concrete basic residual recollections for all of its child tasks.
-/
noncomputable def recollection_basic_residuals
    {d n inputWeight lowerWeight parentRankDefect : ℕ}
    {parent :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (source :
      RCSrc (n := n) parent parentRankDefect)
    (hsourceTruncated :
      SPFactora.IsTruncated n source.factorSource)
    (hsourceSupported :
      SPFactora.WordWeightLeast
        lowerWeight source.factorSource)
    (residual :
      ∀ task ∈ source.tasks,
        TSRecollb
          (n := n) task.1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source.factorSource :=
  source.source_recollection_singletons fun task htask =>
    (residual task htask).singletonSourceRecollection
      (hsourceTruncated task.1
        (source.fst_factor_tasks htask))
      (hsourceSupported task.1
        (source.fst_factor_tasks htask))

end RCSrc
end SPFactora

end TCTex
end Submission
