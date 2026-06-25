import Submission.Group.Zassenhaus.BasicTreeReduction
import Submission.Group.Zassenhaus.ConcreteValueNormalization

/-!
# Named recursive inputs for concrete Hall-power value residuals

The finite-factor recursive value normalizers accept one concrete residual
recollection for every member of a short raw packet.  This file replaces
those membership callbacks by named inputs.

For forward Jacobi and expanded-root swap packets, the inverse parent factor
is derived from the positive parent residual by the atomic sign-order router.
For the inverse two-basic-child swap packet, the positive parent residual is
retained and the reversed factor residual is routed through coefficient
negation.

These adapters deliberately keep a positive parent residual as an explicit
input.  When the packet is used while constructing that same parent residual,
the remaining circular boundary is visible in the type rather than hidden in
a list-membership callback.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

namespace
  TJRecoll

/--
Normalize a forward expanded-Jacobi value packet from named residuals of the
positive parent and its two ordinary descendants.
-/
noncomputable def namedBasicResids
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
    (factorResidual :
      TSRecollb
        (n := n) factor)
    (firstResidual :
      TSRecollb
        (n := n) (expandedJacobiFactor factor decomposition))
    (secondResidual :
      TSRecollb
        (n := n) (expandedJacobiSecond factor decomposition)) :
    TJRecoll
      (n := n) factor decomposition :=
  ofBasicResiduals hn hH factory sharp nextNormalizer factor decomposition
    hfactorWeight hfactorTruncated fun child hchild => by
      exact Classical.choice (by
        simp only [expandedJacobiRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl | rfl
        · exact
            ⟨TSRecollb.neg_of_recollection
              hn hH factory sharp nextNormalizer factor hfactorWeight
                hfactorTruncated factorResidual⟩
        · exact ⟨firstResidual⟩
        · exact ⟨secondResidual⟩)

end
  TJRecoll

namespace
  TIRecoll

/--
Normalize an inverse two-basic-child swap packet from named residuals of the
positive parent and sign-corrected reversed factor.
-/
noncomputable def namedBasicResids
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
    (factorResidual :
      TSRecollb
        (n := n) factor)
    (swapResidual :
      TSRecollb
        (n := n)
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree :=
  ofBasicResiduals hn hH factory sharp nextNormalizer factor left right
    hleftBasic hrightBasic htree hfactorWeight hfactorTruncated
      fun child hchild => by
        exact Classical.choice (by
          simp only [basicChildrenSwap,
            SPFactora.inverseList,
            childrenSwapSource, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.singleton_append,
            List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
            or_false] at hchild
          rcases hchild with rfl | rfl
          · exact
              ⟨TSRecollb.neg_of_recollection
                hn hH factory sharp nextNormalizer
                  (childrenSwapFactor factor left right hleftBasic
                    hrightBasic htree)
                  (by
                    simpa only [basic_children_swap] using
                      hfactorWeight)
                  (by
                    simpa only [basic_children_swap] using
                      hfactorTruncated)
                  swapResidual⟩
          · exact
              ⟨by
                simpa only [SPFactora.neg_neg] using
                  factorResidual⟩)

end
  TIRecoll

namespace
  TSRecolla

/--
Normalize a forward expanded-root swap packet from named residuals of its
positive parent and sign-corrected reversed factor.
-/
noncomputable def namedBasicResids
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
    (factorResidual :
      TSRecollb
        (n := n) factor)
    (swapResidual :
      TSRecollb
        (n := n) (expandedSwapFactor factor left right hword)) :
    TSRecolla
      (n := n) factor left right hword :=
  ofBasicResiduals hn hH factory sharp nextNormalizer factor left right hword
    hfactorWeight hfactorTruncated fun child hchild => by
      exact Classical.choice (by
        simp only [expandedSwapRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl
        · exact
            ⟨TSRecollb.neg_of_recollection
              hn hH factory sharp nextNormalizer factor hfactorWeight
                hfactorTruncated factorResidual⟩
        · exact ⟨swapResidual⟩)

end
  TSRecolla

end TCTex
end Submission
