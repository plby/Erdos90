import Submission.Group.Zassenhaus.SemanticallyHigherRecollection
import Submission.Group.Zassenhaus.Jacobi
import Submission.Group.Zassenhaus.ChildrenJacobiOrientation

/-!
# Normalizing basic-children swap value residuals

The sign-corrected reverse orientation for a bracket with two basic children
leaves an inverse skew-value residual.  Its factors remain physically
supported at the parent Hall weight, while skew symmetry places its value one
lower-central layer higher.  A semantic normalizer at the parent stratum
therefore recollects it into a strictly higher tail.

This removes the explicit swap-value residual input from the two-basic-child
Jacobi orientation builder.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

namespace
  TIRecoll

/-- Normalize the inverse skew-value residual into a strictly higher tail. -/
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
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
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

/-- Use a normalizer family at the parent Hall-weight stratum. -/
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
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor left right
    hleftBasic hrightBasic htree hfactorWeight hfactorTruncated

end
  TIRecoll

namespace
  JABuild

open
  TIRecoll

/--
Compile automatic expanded-Jacobi and swap-value normalization into the
two-basic-child Jacobi orientation builder.
-/
noncomputable def childrenOrientationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      JABuild.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight) :
    JOBuild
      (inputWeight := inputWeight) hn hH where
  expandedJacobi :=
    builder.expandedContinuationBuilder
      hinputWeight
  swapValueInverse :=
    fun _lowerWeight _hnonterminal factor left right hleftBasic hrightBasic
        htree hfactorWeight hfactorTruncated =>
      ofNormalizerFamily hn hH builder.normalizerFamily factor left right
        hleftBasic hrightBasic htree hfactorWeight hfactorTruncated

end
  JABuild

end TCTex
end Submission
