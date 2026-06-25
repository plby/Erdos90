import Towers.Group.Zassenhaus.RepeatedRightCollection

/-!
# Contextual collection for basic outer-right polynomial frontiers

For an exposed nested frontier `[[left, middle], right]`, the direct ranked
inner-span wrapper only applies when `middle < right`.  Full-context inner
reduction is stronger: if `right` is Hall-basic, reducing the immediate inner
bracket emits a finite packet `[basic_i, right]`, and each emitted child has
its own canonical two-basic-child rank.

Thus every basic outer-right frontier recollects contextually, independently
of the order or Hall shape of its inner children.  The only remaining nested
boundary has nonbasic retained right tree.  Its established root-swap Jacobi
step produces two certified descendants with proper-subtree retained rights.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open CEWord
open
  RCDecomp
  TDCase

/--
Reachable ranked routing and one recursive proper-subtree boundary for
nonbasic retained outer-right trees.
-/
structure
    TOBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  TDCase
                    factor frontier),
                  TRRecoll
                    (n := n) descendant.factor

namespace
  TOBuilda

open
  TRRecoll

/--
Swap one nonbasic retained-right frontier, recurse on the two certified
proper-subtree descendants, and reconstruct the original residual.
-/
noncomputable def retainedNonbasicResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      TOBuilda.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (frontier :
      NWCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    TRRecoll
      (n := n) factor :=
  let retained :=
    ofNonbasic factor frontier hrightNonbasic
  let reversed := retainedSwapFactor factor frontier
  let reversedResidual :=
    expanded_normalizer_family hn builder.packet
      (builder.routing ι).normalizerFamily reversed retained.decomposition
      (by simpa only [reversed, word_swap_factor] using
        hfactorWeight)
      (by
        simpa only [reversed, word_swap_factor] using
          hfactorTruncated)
      (builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (first factor frontier hrightNonbasic))
      (builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (second factor frontier hrightNonbasic))
  expanded_swap factor
    (.commutator frontier.decomposition.left frontier.decomposition.middle)
    frontier.decomposition.right frontier.decomposition.word_eq
      reversedResidual
      (builder.rootSwapResidual lowerWeight hnonterminal factor
        (.commutator frontier.decomposition.left frontier.decomposition.middle)
        frontier.decomposition.right frontier.decomposition.word_eq
          hfactorWeight hfactorTruncated)

/--
Compile contextual basic-right collection and retained-right subtree
recursion directly into the exposed nested-word frontier interface.
-/
noncomputable def
    expandedWordsBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TOBuilda.{u}
        (d := d) (n := n) hn) :
    CNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier
    by_cases hrightBasic : frontier.right.IsBasic
    · exact
        NWCase.outerResidualRecollect
          hn (builder.routing ι) factor frontier hrightBasic hfactorTruncated
    · exact
        builder.retainedNonbasicResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic

end
  TOBuilda

/--
Contextual basic-right collection and certified retained-right subtree
recursion construct product coordinate polynomials.
-/
theorem
    contextual_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TOBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_ranked_builder
    hn e builder.expandedWordsBuilder

/--
Contextual basic-right collection and certified retained-right subtree
recursion construct inverse coordinate polynomials.
-/
theorem
    commutators_contextual_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TOBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  ranked_expanded_builder
    hn e builder.expandedWordsBuilder

end TCTex
end Towers
