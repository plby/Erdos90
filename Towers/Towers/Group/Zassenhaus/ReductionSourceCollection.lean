import Towers.Group.Zassenhaus.ReductionComparison
import Towers.Group.Zassenhaus.CanonicalHallRecollection

/-!
# Claim 5 collection from concrete Hall-tree residual sources

The recursive Claim 5 collector consumes intrinsic factor residual sources.
Concrete Hall-tree reduction splits each such residual into two operational
sources:

* the explicit atomic reduction residual; and
* the comparison residual between that packet and the semantic active Hall
  block.

This file packages recollection of those two concrete sources as a direct
input to the existing universal-packet collector.  Constructing these
recollections below the terminal cutoff remains the symbolic Hall-collection
problem.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A universal Hall-Petresco packet and upward recollections of the two concrete
Hall-tree residual sources.
-/
structure
    TCBuildf
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.UAInt.{u}
  basicResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TSRecollb
                (n := n) factor
  comparisonResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TCRecoll
                (lowerWeight := lowerWeight) hn hH factor

namespace
  TCBuildf

/--
Compose the two concrete recollections into the intrinsic residual-source
builder consumed by restricted-sharp recursion.
-/
noncomputable def
    restrictedUniversalBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TCBuildf.{u}
        (inputWeight := inputWeight) hn hH) :
    SUBuild.{u}
      (inputWeight := inputWeight) hn (concreteBasicCommutators.{u} d) hH where
  packet := builder.packet
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated :=
    (builder.basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated).intrinsicResidualSource
        (builder.comparisonResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated)
        hfactorWeight

end
  TCBuildf

namespace TSInput

/--
For canonical Hall families, concrete Hall-tree residual recollections and a
universal Hall-Petresco packet construct the Claim 5 coordinate polynomials.
-/
theorem
    concreteCollectionBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TCBuildf.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.universalCollectionBuilder
    hn hsourceSupported
      (by
        simpa only [concreteBasicCommutators] using
          builder.restrictedUniversalBuilder)
      hinputWeight

end TSInput
end TCTex
end Towers
