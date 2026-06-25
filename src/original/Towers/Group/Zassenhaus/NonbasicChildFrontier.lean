import Towers.Group.Zassenhaus.ReverseOrientationResiduals
import Towers.Group.Zassenhaus.PolynomialRankedSupport

/-!
# Polynomial Jacobi frontiers reduced to nonbasic children

When both children of a frontier are basic, Hall admissibility orients the
bracket into expanded Jacobi recursion.  This adapter leaves only frontiers
with a genuinely nonbasic child as the next collector-facing boundary.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/-- Orientation data and recollections for frontiers with a nonbasic child. -/
structure
    NCBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  basicChildren :
    COBuild.{u}
      (d := d) (n := n) hn
  normalizerAbove :
    ∀ lowerWeight strongerWeight : ℕ,
      lowerWeight < strongerWeight →
        TSNormal
          (n := n) (lowerWeight := strongerWeight)
            (concreteBasicCommutators.{u} d)
  nonbasicChildResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(CEWord.tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  CEWord.tree factor.word =
                      HallTree.commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        (¬left.IsBasic ∨ ¬right.IsBasic) →
        TRRecoll
          (n := n) factor

namespace
  NCBuild

/-- Fill two-basic-child frontiers and leave nonbasic-child frontiers explicit. -/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      NCBuild.{u}
        (d := d) (n := n) hn) :
    JFBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.basicChildren.expandedJacobi.packet
  jacobiFrontierResidual := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      htreeNonbasic left right htree hchildrenNe hreverseNonbasic
    by_cases hleftBasic : left.IsBasic
    · by_cases hrightBasic : right.IsBasic
      · exact
          builder.basicChildren.residual lowerWeight hnonterminal
            (builder.normalizerAbove lowerWeight) factor left right
              hleftBasic hrightBasic htree
                (by simpa only [htree] using htreeNonbasic)
                  hchildrenNe hreverseNonbasic hfactorWeight
                    hfactorTruncated
      · exact
          builder.nonbasicChildResidual lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated htreeNonbasic left right htree
              hchildrenNe hreverseNonbasic (Or.inr hrightBasic)
    · exact
        builder.nonbasicChildResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic left right htree
            hchildrenNe hreverseNonbasic (Or.inl hleftBasic)

end
  NCBuild
end TCTex
end Towers
