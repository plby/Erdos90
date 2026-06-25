import Submission.Group.Zassenhaus.RootSwapValue
import Submission.Group.Zassenhaus.ReductionOuter

/-!
# Recursive normalization of concrete Hall-power value residuals

The direct value-residual normalizers consume a semantic normalizer at the
current Hall-weight stratum. This file exposes a recursive alternative.

Replace every factor in a semantically higher packet by its concrete atomic
Hall reduction and already recollected intrinsic residual. The remaining
active factors are atomic, while every non-atomic factor is strictly higher.
Restricted-sharp routing then lifts the whole packet using only a correction
factory, a sharp router, and the next-stratum normalizer.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/--
Fold independently recollected concrete residuals over an arbitrary finite
Hall-power source while retaining the active-atoms-or-higher invariant.
-/
noncomputable def atoms_or_residuals
    {d n inputWeight lowerWeight : ℕ}
    (source :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hsourceTruncated :
      SPFactora.IsTruncated n source)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight source)
    (residual :
      ∀ factor ∈ source,
        TSRecollb
          (n := n) factor) :
    AORecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source := by
  have hsource :
      source.flatMap
          (fun factor :
              SPFactora
                (concreteBasicCommutators.{u} d) inputWeight =>
            [factor]) =
        source := by
    clear hsourceTruncated hsourceSupported residual
    induction source with
    | nil =>
        rfl
    | cons factor source ih =>
        simp only [List.flatMap_cons, List.singleton_append, ih]
  rw [← hsource]
  exact
    AORecol.flatMap
      source
      (fun factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight =>
        [factor])
      (fun factor hfactor =>
        (residual factor hfactor).atomsOrRecollection
          (hsourceTruncated factor hfactor)
          (hsourceSupported factor hfactor))

/--
Lift a semantically higher concrete source from recursive residual
recollections of its factors. No current-stratum normalizer is required.
-/
noncomputable def recollect_higher_residuals
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (source :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated :
      SPFactora.IsTruncated n source)
    (hsourceSupported :
      SPFactora.WordWeightLeast lowerWeight source)
    (hsourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight)
    (residual :
      ∀ factor ∈ source,
        TSRecollb
          (n := n) factor) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d) source :=
  (atoms_or_residuals
    source hsourceTruncated hsourceSupported residual)
    |>.recollectionSemanticallyHigher hn hH factory sharp
      nextNormalizer hlowerWeightPos hlowerWeightTruncated hsourceMem

end
  TSRecollb

namespace
  TJRecoll

/--
Normalize an expanded-Jacobi value packet from recursive recollections of its
three concrete factors.
-/
noncomputable def ofBasicResiduals
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (residual :
      ∀ child ∈ expandedJacobiRaw factor decomposition,
        TSRecollb
          (n := n) child) :
    TJRecoll
      (n := n) factor decomposition := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    TSRecollb.recollect_higher_residuals
      hn hH factory sharp nextNormalizer
      (expandedJacobiRaw factor decomposition)
      hlowerWeightPos (by omega)
      (expanded_jacobi_source factor decomposition
        hfactorTruncated)
      (by
        intro x hx
        simp only [expandedJacobiRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · simpa only [SPFactora.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_jacobi_factor] using
            hfactorWeight.ge
        · simpa only [expanded_second_factor] using
            hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          list_expanded_series
            factor decomposition q)
      residual
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

end
  TJRecoll

namespace
  TIRecoll

/--
Normalize the inverse two-basic-child swap packet from recursive recollections
of its concrete factors.
-/
noncomputable def ofBasicResiduals
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (residual :
      ∀ child ∈
          basicChildrenSwap factor left right
            hleftBasic hrightBasic htree,
        TSRecollb
          (n := n) child) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    TSRecollb.recollect_higher_residuals
      hn hH factory sharp nextNormalizer
      (basicChildrenSwap factor left right
        hleftBasic hrightBasic htree)
      hlowerWeightPos (by omega)
      (truncated_children_swap factor left
        right hleftBasic hrightBasic htree hfactorTruncated)
      (by
        rw [basicChildrenSwap]
        apply SPFactora.least_inverse_list
        intro x hx
        simp only [childrenSwapSource, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simpa only [SPFactora.word_neg] using
            hfactorWeight.ge
        · simpa only [basic_children_swap] using
            hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          children_swap_series
            factor left right hleftBasic hrightBasic htree q)
      residual
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

end
  TIRecoll

namespace
  TSRecolla

/--
Normalize an expanded-root swap packet from recursive recollections of its
two concrete factors.
-/
noncomputable def ofBasicResiduals
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)
            (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1)
            (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (residual :
      ∀ child ∈ expandedSwapRaw factor left right hword,
        TSRecollb
          (n := n) child) :
    TSRecolla
      (n := n) factor left right hword := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    TSRecollb.recollect_higher_residuals
      hn hH factory sharp nextNormalizer
      (expandedSwapRaw factor left right hword)
      hlowerWeightPos (by omega)
      (truncated_expanded_source factor left right
        hword hfactorTruncated)
      (by
        intro x hx
        simp only [expandedSwapRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simpa only [SPFactora.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_root_factor] using
            hfactorWeight.ge)
      (by
        intro q
        simpa only [hfactorWeight] using
          expanded_raw_series
            factor left right hword q)
      residual
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

end
  TSRecolla

end TCTex
end Submission
