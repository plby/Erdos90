import Towers.Group.Zassenhaus.ReverseOrientationResiduals
import Towers.Group.Zassenhaus.JacobiFrontierRouting
import Towers.Group.Zassenhaus.SignCorrectedSwaps
import Towers.Group.Zassenhaus.CoefficientNegationRouting
import Towers.Group.Zassenhaus.JacobiContinuationBuilders
import Towers.Group.Zassenhaus.FullWeightFactory

/-!
# Normalizing expanded polynomial root-swap value residuals

The generic sign-corrected root swap leaves a forward skew-value residual.
Its factors remain physically supported at the parent Hall weight, while
skew symmetry places its evaluated value one lower-central stratum higher.
A signed semantic normalizer recollects it into a strictly higher tail.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

namespace
  PSRecoll

/-- Normalize the forward root-swap residual into a strictly higher tail. -/
noncomputable def ofNormalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    PSRecoll
      (n := n) factor left right hword := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d) hH
      (expandedSwapRaw factor left right hword)
      hlowerWeightPos (by omega)
      (truncated_expanded_source factor left right
        hword hfactorTruncated)
      (by
        intro x hx
        simp only [expandedSwapRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · simpa only [SPFactor.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_root_factor] using
            hfactorWeight.ge)
      (by
        intro e
        simpa only [hfactorWeight] using
          expanded_raw_series
            factor left right hword e)
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
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    PSRecoll
      (n := n) factor left right hword :=
  ofNormalizer hn hH (family.normalizer lowerWeight) factor left right hword
    hfactorWeight hfactorTruncated

end
  PSRecoll

/--
An arbitrary-frontier builder with automatic value-packet normalization.
Only the two ordinary expanded-Jacobi descendants remain recursive.
-/
structure
    ACBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  expandedJacobi :
    EABuild.{u}
      (d := d) (n := n) hn

namespace
  ACBuild

open
  PSRecoll

/-- Compile every automatic value-packet route into the arbitrary frontier. -/
noncomputable def expandedFrontierBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      ACBuild.{u}
        (d := d) (n := n) hn) :
    EFBuilda.{u}
      (d := d) (n := n) hn where
  basicChildren :=
    builder.expandedJacobi
      |>.childrenOrientationBuilder
  normalizerAbove :=
    fun _lowerWeight strongerWeight _ =>
      builder.expandedJacobi.normalizerFamily.normalizer strongerWeight
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        builder.expandedJacobi.normalizerFamily factor left right hword
          hfactorWeight hfactorTruncated

/-- Compile automatic frontier normalization into the existing collector. -/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      ACBuild.{u}
        (d := d) (n := n) hn) :
    JFBuild.{u}
      (d := d) (n := n) hn :=
  builder.expandedFrontierBuilder
    |>.jacobiCollectionBuilder

end
  ACBuild

/--
For canonical Hall families, recursive Jacobi-descendant recollections alone
construct product coordinate polynomials.
-/
theorem
    root_automatic_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      ACBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_collect
    hn e builder.jacobiCollectionBuilder

/--
For canonical Hall families, recursive Jacobi-descendant recollections alone
construct inverse coordinate polynomials.
-/
theorem
    commutators_collected_automatic
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      ACBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_reduction_builder
    hn e builder.jacobiCollectionBuilder

end TCTex
end Towers

/-!
# Closing expanded polynomial root collection from a normalizer family

After automatic Jacobi-value and swap-value normalization, only the two
ordinary Jacobi descendant residuals remain explicit.  The existing direct
basic-residual normalizer recollects both descendants from the same signed
semantic normalizer family.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/--
A Hall-Petresco packet and signed semantic normalizer family close every
expanded-root frontier residual automa.
-/
structure
    TRBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)

namespace
  TRBuilda

open
  TRRecoll

/-- Compile direct descendant normalization into the automatic value builder. -/
noncomputable def expandedJacobiAutomatic
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TRBuilda.{u}
        (d := d) (n := n) hn) :
    EABuild
      (d := d) (n := n) hn where
  packet := builder.packet
  normalizerFamily := builder.normalizerFamily
  firstResidual :=
    fun _lowerWeight _hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        builder.normalizerFamily
          (expandedJacobiFactor factor decomposition)
          (by
            simpa only [expanded_jacobi_factor] using
              hfactorWeight)
          (by
            simpa only [expanded_jacobi_factor] using
              hfactorTruncated)
  secondResidual :=
    fun _lowerWeight _hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        builder.normalizerFamily
          (expandedJacobiSecond factor decomposition)
          (by
            simpa only [expanded_second_factor] using
              hfactorWeight)
          (by
            simpa only [expanded_second_factor] using
              hfactorTruncated)

/-- Compile every expanded-root frontier residual automa. -/
noncomputable def expandedAutomaticCollection
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TRBuilda.{u}
        (d := d) (n := n) hn) :
    ACBuild
      (d := d) (n := n) hn where
  expandedJacobi :=
    builder.expandedJacobiAutomatic

/-- Compile the closed expanded route into the arbitrary Jacobi frontier. -/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TRBuilda.{u}
        (d := d) (n := n) hn) :
    JFBuild
      (d := d) (n := n) hn :=
  builder.expandedAutomaticCollection
    |>.jacobiCollectionBuilder

end
  TRBuilda

/--
For canonical Hall families, a packet and signed semantic normalizer family
construct product coordinate polynomials through the expanded route.
-/
theorem
    expanded_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TRBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_collect
    hn e builder.jacobiCollectionBuilder

/--
For canonical Hall families, a packet and signed semantic normalizer family
construct inverse coordinate polynomials through the expanded route.
-/
theorem
    commutators_expanded_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TRBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_reduction_builder
    hn e builder.jacobiCollectionBuilder

end TCTex
end Towers

/-!
# Reachable ranked normalization of expanded polynomial Jacobi descendants

The Hall-ranked inner-packet recursion does not classify an arbitrary
nonbasic root. It applies after a Jacobi rewrite, when the two descendants
have the forms `[[a, v], b]` and `[[b, v], a]`. Both descendants inherit the
classical rank defect of the original pair `[[a, b], v]`.

This file records those two recipe-correct ranked cases and routes reachable
ranked residual schedulers into the descendant slots of expanded Jacobi
collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

open CEWord

universe u

/-- The classical Hall-rank defect inherited by both Jacobi descendants. -/
def expandedJacobiParent
    {d : ℕ}
    {word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    (decomposition : ExpandedJacobiDecomposition word) :
    ℕ :=
  HallTree.bracketRankDefect
    ((tree (.commutator decomposition.left decomposition.middle)).weight +
      (tree decomposition.right).weight)
    (.commutator (tree decomposition.left) (tree decomposition.middle))
    (tree decomposition.right)

/--
The first Jacobi descendant `[[a, v], b]` is a recipe-correct ranked
inner-reduction case whenever `v < b`.
-/
noncomputable def expandedInnerCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hrightMiddle :
      tree decomposition.right < tree decomposition.middle)
    (hmiddleBasic : (tree decomposition.middle).IsBasic) :
    TruncatedRankedCase
      (n := n)
      (expandedJacobiFactor factor decomposition)
      (expandedJacobiParent decomposition) where
  innerWord := .commutator decomposition.left decomposition.right
  rightWord := decomposition.middle
  hword := by
    simp only [expandedJacobiFactor, SPFactor.word_reword]
  hfactorTruncated := by
    simpa only [expanded_jacobi_factor] using hfactorTruncated
  added := tree decomposition.left
  originalRight := tree decomposition.right
  unchanged := tree decomposition.middle
  originalLeft :=
    .commutator (tree decomposition.left) (tree decomposition.middle)
  hinnerTree := by
    simp only [tree_commutator]
  hRightLeft :=
    hrightMiddle.trans
      (HallTree.weight_add_left
        (tree decomposition.left) (tree decomposition.middle)
        (.commutator (tree decomposition.left) (tree decomposition.middle))
        rfl)
  hRightUnchanged := hrightMiddle
  hunchangedBasic := hmiddleBasic
  rankDefect_eq := by
    simp only [expandedJacobiParent, tree_commutator,
      HallTree.weight_commutator]
    congr 1
    omega

/--
The second Jacobi descendant `[[b, v], a]` is a recipe-correct ranked
inner-reduction case whenever `v < b < a`.
-/
noncomputable def expandedSecondCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hrightMiddle :
      tree decomposition.right < tree decomposition.middle)
    (hmiddleLeft :
      tree decomposition.middle < tree decomposition.left)
    (hleftBasic : (tree decomposition.left).IsBasic) :
    TruncatedRankedCase
      (n := n)
      (expandedJacobiSecond factor decomposition)
      (expandedJacobiParent decomposition) where
  innerWord := .commutator decomposition.middle decomposition.right
  rightWord := decomposition.left
  hword := by
    simp only [expandedJacobiSecond, SPFactor.word_neg,
      SPFactor.word_reword]
  hfactorTruncated := by
    simpa only [expanded_second_factor] using hfactorTruncated
  added := tree decomposition.middle
  originalRight := tree decomposition.right
  unchanged := tree decomposition.left
  originalLeft :=
    .commutator (tree decomposition.left) (tree decomposition.middle)
  hinnerTree := by
    simp only [tree_commutator]
  hRightLeft :=
    hrightMiddle.trans
      (HallTree.weight_add_left
        (tree decomposition.left) (tree decomposition.middle)
        (.commutator (tree decomposition.left) (tree decomposition.middle))
        rfl)
  hRightUnchanged := hrightMiddle.trans hmiddleLeft
  hunchangedBasic := hleftBasic
  rankDefect_eq := by
    simp only [expandedJacobiParent, tree_commutator,
      HallTree.weight_commutator]
    congr 1
    omega

/--
An expanded Jacobi decomposition equipped with the Hall inequalities needed
to reduce both of its ordinary descendants by ranked inner reduction.
-/
structure ERDecomp
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) where
  decomposition : ExpandedJacobiDecomposition factor.word
  right_lt_middle :
    tree decomposition.right < tree decomposition.middle
  middle_lt_left :
    tree decomposition.middle < tree decomposition.left
  left_isBasic : (tree decomposition.left).IsBasic
  middle_isBasic : (tree decomposition.middle).IsBasic

namespace
  ERDecomp

/--
Choose symbolic representatives for a recipe-correct Hall-oriented Jacobi
root while retaining the inequalities needed by ranked descendant recursion.
-/
noncomputable def nonbasic_commutator_tree
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree factor.word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hrightMiddle : right < middle)
    (hmiddleLeft : middle < left)
    (hleftBasic : left.IsBasic)
    (hmiddleBasic : middle.IsBasic) :
    ERDecomp
      factor := by
  let decomposition :=
    expandedTreeNonbasic
      factor.word left middle right htree houterNonbasic
  have hroot :
      HallTree.commutator
          (HallTree.commutator
            (tree decomposition.left) (tree decomposition.middle))
          (tree decomposition.right) =
        HallTree.commutator (HallTree.commutator left middle) right := by
    rw [← decomposition.tree_eq, htree]
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact
    { decomposition := decomposition
      right_lt_middle := by
        simpa only [hright, hmiddle] using hrightMiddle
      middle_lt_left := by
        simpa only [hmiddle, hleft] using hmiddleLeft
      left_isBasic := by
        simpa only [hleft] using hleftBasic
      middle_isBasic := by
        simpa only [hmiddle] using hmiddleBasic }

/-- Compile the first ordinary descendant into a ranked local case. -/
noncomputable def firstCase
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TruncatedRankedCase
      (n := n)
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition) :=
  expandedInnerCase factor
    ranked.decomposition hfactorTruncated ranked.right_lt_middle
      ranked.middle_isBasic

/-- Compile the second ordinary descendant into a ranked local case. -/
noncomputable def secondCase
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TruncatedRankedCase
      (n := n)
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition) :=
  expandedSecondCase factor
    ranked.decomposition hfactorTruncated ranked.right_lt_middle
      ranked.middle_lt_left ranked.left_isBasic

end
  ERDecomp

/-- Reachability of the two ranked descendants emitted by one Jacobi root. -/
structure
    RankedDescendantReachability
    {d : ℕ}
    {ι : Type}
    (Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word) : Prop where
  first :
    Reachable
      (expandedJacobiFactor factor decomposition)
      (expandedJacobiParent decomposition)
  second :
    Reachable
      (expandedJacobiSecond factor decomposition)
      (expandedJacobiParent decomposition)

/--
A reachable Hall-ranked scheduler fills the two ordinary descendant
residuals left open by expanded Jacobi routing.
-/
structure
    ERBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)
  Reachable :
    ∀ ι : Type,
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop
  scheduler :
    ∀ ι : Type,
      RRSchedu
        (n := n) (Reachable ι)
  descendants_reachable :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              RankedDescendantReachability
                (Reachable ι) factor decomposition
  valueResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (decomposition : ExpandedJacobiDecomposition factor.word),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecolla
                (n := n) factor decomposition

namespace
  ERBuild

/-- Forget ranked scheduling after compiling the two descendant residuals. -/
noncomputable def expandedForwardBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      ERBuild.{u}
        (d := d) (n := n) hn) :
    EFBuild
      (d := d) (n := n) hn where
  packet := builder.packet
  normalizerFamily := builder.normalizerFamily
  firstResidual :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      (builder.scheduler _).residualRecollection
        (expandedJacobiFactor factor decomposition)
        (expandedJacobiParent decomposition)
        (builder.descendants_reachable lowerWeight hnonterminal factor
          decomposition hfactorWeight hfactorTruncated).first
  secondResidual :=
    fun lowerWeight hnonterminal factor decomposition hfactorWeight
        hfactorTruncated =>
      (builder.scheduler _).residualRecollection
        (expandedJacobiSecond factor decomposition)
        (expandedJacobiParent decomposition)
        (builder.descendants_reachable lowerWeight hnonterminal factor
          decomposition hfactorWeight hfactorTruncated).second
  valueResidual := builder.valueResidual

end
  ERBuild

end TCTex
end Towers
