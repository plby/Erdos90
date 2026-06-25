import Submission.Group.Zassenhaus.SourceRecollectionOperations
import Submission.Group.Zassenhaus.RootSwapResidual

/-!
# Recollections for sign-corrected expanded-root swaps

The exact expanded-root swap decomposition reduces the original true
residual to the true residual of the signed reversed factor and one
next-stratum skew packet.  A forward recollection of that skew packet is
enough: generic source inversion supplies the orientation used by the
decomposition.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

/-- Upward recollection of a forward expanded-root skew-value residual. -/
structure
    TSRecolla
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (expandedSwapRaw factor left right hword)

namespace
  TSRecolla

/-- View a root-swap value recollection as a generic source recollection. -/
noncomputable def toSourceRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {hword : factor.word = .commutator left right}
    (recollection :
      TSRecolla
        (n := n) factor left right hword) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (expandedSwapRaw factor left right hword) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_least_succ
  list_higher_raw :=
    recollection.list_higher_raw

end
  TSRecolla

namespace
  TSRecollb

/--
Recollect an expanded-root residual from its signed reverse and a forward
recollection of the skew-value packet.
-/
noncomputable def expanded_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (reversed :
      TSRecollb
        (n := n) (expandedSwapFactor factor left right hword))
    (valueResidual :
      TSRecolla
        (n := n) factor left right hword) :
    TSRecollb
      (n := n) factor := by
  let inverse := valueResidual.toSourceRecollection.inverse
  exact
    { higherSource := reversed.higherSource ++ inverse.higherSource
      higher_source_truncated := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact reversed.higher_source_truncated x hx
        · exact inverse.higher_source_truncated x hx
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simpa only [expanded_root_factor] using
            reversed.higher_least_succ x hx
        · exact inverse.higher_weight_least x hx
      list_higher_raw := by
        intro q
        rw [SPFactora.listEval_append,
          reversed.list_higher_raw q,
          inverse.list_higher_raw q,
          ←
            expanded_swap_decomposition
              factor left right hword q]
        rw [expandedSwapDecomposition,
          SPFactora.listEval_append,
          expandedSwapSource] }

end
  TSRecollb

end TCTex
end Submission
