import Submission.Group.HallBasic.StandardSequence
import Submission.Group.Zassenhaus.ReachableUniversalReduction
import Submission.Group.Zassenhaus.RestrictedSharp
import Submission.Group.HallBasic.JacobiValueScaling
import Submission.Group.Zassenhaus.BasicTreeReduction
import Submission.Group.Zassenhaus.Jacobi
import Submission.Group.Zassenhaus.IntegralStrictTail
import Submission.Group.Zassenhaus.LeafExponentAddress
import Submission.Group.Zassenhaus.ChildrenJacobiOrientation
import Submission.Group.Zassenhaus.RootSwapRecollection
import Submission.Group.Zassenhaus.ConcreteAutomaticComparison
import Submission.Group.Zassenhaus.FormulaChooseSubstitution
import Submission.Group.Zassenhaus.ClassTwo
import Submission.Group.Zassenhaus.SharpHigherRouting
import Submission.Group.Zassenhaus.UniversalSourceCollection
import Submission.Group.Zassenhaus.ReductionComparison
import Submission.Group.HallBasic.AssociatedGradedSpanning
import Submission.Group.HallBasic.JacobiFrontierWeight

-- Merged from ConcreteHallRestrictedSharpCollection.lean

/-!
# Symbolic Hall-power recollection for the canonical Hall families

Right-to-left foliage contraction proves that the canonical finite Hall
families form bases in every free-group lower-central associated-graded layer.
The powered semantic collector can therefore instantiate its high-weight
normalizer with those concrete families.

This file specializes the reachable and restricted-sharp reductions.  It
deliberately preserves the correctly sourced repeated-block input: in a
noncommutative quotient, constructing that finite source is a separate part of
the universal collection theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- The canonical Hall families satisfy every graded-basis premise below a cutoff. -/
theorem forms_associated_below
    (d n : ℕ) :
    ∀ s : ℕ,
      1 ≤ s →
        s < n →
          (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
            (n := n) := by
  intro s hs hsn
  exact concrete_forms_associated d n s hs hsn

/--
The commutative region has a canonical powered semantic normalizer for the
concrete Hall families.
-/
noncomputable def
    commutators_supported_normalizer
    (d n inputWeight lowerWeight : ℕ)
    (hn : 2 ≤ n)
    (hcutoff : n ≤ 2 * lowerWeight) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteCommutatorsWeight.{u} d) :=
  TSNormalb.of_highWeight
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hcutoff

namespace TSInput

/--
A reachable powered builder constructs Claim 5 polynomial data for the
canonical finite Hall families.
-/
theorem
    reachableUniversalBuilder
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
      TDBuild
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.reachableDerivationBuilder
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hsourceSupported builder hinputWeight

/--
Restricted sharp recursive data constructs Claim 5 polynomial data for the
canonical finite Hall families.
-/
theorem
    sharpRecursiveBuilder
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
      RSRec
        (n := n) (inputWeight := inputWeight) hn
          (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.restrictedSharpRecursive
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hsourceSupported builder hinputWeight

/--
Universal correction expansions and singleton recollections construct Claim 5
polynomial data for the canonical finite Hall families.
-/
theorem
    sharpSingletonBuilder
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
      TSBuildd
        (n := n) (inputWeight := inputWeight) hn
          (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  restrictedSingletonBuilder
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      input hsourceSupported builder hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ConcreteJacobiValueResidual.lean

/-!
# Symbolic Jacobi value residuals

The atomic Jacobi coordinate packet compares explicit Hall reductions.  The
companion packet in this file compares the original powered nested
commutator value with the two powered Jacobi descendant values.  Its
evaluation lies one lower-central stratum higher and is therefore the
recursive value-level correction left by the Jacobi rewrite.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
Value-level Jacobi residual: original nested factor inverse, followed by the
two signed Jacobi descendants.
-/
noncomputable def jacobiValueSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  [factor.neg,
    jacobiFirstFactor factor left middle right hword,
    jacobiSecondFactor factor left middle right hword]

/-- Truncation of the original factor physically truncates its value residual. -/
theorem truncated_jacobi_raw
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (jacobiValueSource factor left middle right hword) := by
  intro x hx
  simp only [jacobiValueSource, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [SPFactora.word_neg] using hfactor
  · simpa only [jacobi_first_factor] using hfactor
  · simpa only [word_jacobi_second] using hfactor

/-- The symbolic Jacobi value residual evaluates one lower-central stratum higher. -/
theorem jacobi_value_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (jacobiValueSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.jacobi_zpow_series
      (tree left) (tree middle) (tree right) (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword, CWord.weight_commutator,
            CWord.weight_commutator, ← tree_weight, ← tree_weight,
            ← tree_weight]
          exact hfree))
  rw [jacobiValueSource,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  rw [← tree_commutator left middle,
    ← tree_commutator (.commutator left middle) right,
    ← tree_commutator left right,
    ← tree_commutator (.commutator left right) middle,
    ← tree_commutator middle right,
    ← tree_commutator (.commutator middle right) left] at hmap
  rw [map_mul, map_inv, map_zpow, map_mul, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  simpa only [map_mul, map_inv, map_zpow,
    SPFactora.eval_neg, SPFactora.eval,
    SPFactora.wordValue,
    exponent_jacobi_factor, exponent_jacobi_second,
    jacobiFirstFactor, jacobiSecondFactor, SPFactora.word_neg,
    SPFactora.word_reword, SPFactora.exponent_neg,
    SPFactora.exponent_reword, hword, zpow_neg] using hmap

/--
Inverse orientation of the value-level Jacobi residual.  This is convenient
when it appears at the tail of a continuation packet.
-/
noncomputable def jacobiRawSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
    (jacobiValueSource factor left middle right hword)

/-- Truncation is preserved by inversion of the Jacobi value residual. -/
theorem truncated_jacobi_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (jacobiRawSource factor left middle right hword) := by
  exact
    SPFactora.truncated_inverse_list
      (truncated_jacobi_raw
        factor left middle right hword hfactor)

/-- The inverse Jacobi value residual also lies one lower-central stratum higher. -/
theorem jacobi_raw_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (jacobiRawSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [jacobiRawSource,
    SPFactora.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).inv_mem
        (jacobi_value_series
          factor left middle right hword q)

end HEWord
end TCTex
end Submission

-- Merged from ConcreteSignedLeafHallWittStrictTraceSource.lean

/-!
# Concrete symbolic sources for signed-leaf Hall-Witt strict traces

The ordinary three-head Jacobi packet already evaluates to the signed-leaf
Hall-Witt strict trace.  Normalize that packet in its physical parent layer
to obtain a fixed ordinary symbolic Hall source supported one layer higher.
This removes visible-commutator hypotheses from expanded-Jacobi value
recollection while preserving the existing symbolic factor vocabulary.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  LCSrc


open CWTrace
open HEWord
open SLSubsti
open SLAddres
open
  PCSrc
open
  TSRecoll

universe u

private abbrev strictTailParent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y z : CWord (HEAddres H)) :
    ℕ :=
  x.weight PEAddres.weight +
      y.weight PEAddres.weight +
    z.weight PEAddres.weight

/--
The ordinary fixed three-head symbolic packet evaluates exactly to the
signed-leaf strict trace for arbitrary compressed Hall-address branches.
-/
lemma head_leaf_full
    {d n inputWeight : ℕ}
    {x y z :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {coefficient : ℕ → ℤ}
    (head :
      CHExp
        (inputWeight := inputWeight) x y z coefficient)
    (q : ℕ) :
    SPFactora.listEval (n := n) q head.headSource =
      wordListEval
        (SLeaf.eval
          (PEAddres.freeLowerTruncation
            (n := n)))
        (signedLeafStrict x y z (coefficient q)) := by
  rw [CHExp.headSource,
    SPFactora.listEval_append,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    SPFactora.list_eval_inverse,
    BCExp.list_power_factors,
    BCExp.list_power_factors,
    BCExp.list_power_factors,
    congrFun head.eval_originalExpansion q,
    congrFun head.eval_firstExpansion q,
    congrFun head.eval_secondExpansion q,
    signed_leaf_strict
      (PEAddres.freeLowerTruncation (n := n))
        x y z (coefficient q)]
  simp only [addressJacobiOriginal,
    exponentAddressJacobi, addressJacobiSecond]
  rw [← inv_zpow, ← inv_zpow, mul_assoc]

/--
A fixed ordinary symbolic Hall source for the complete signed-leaf Hall-Witt
strict trace.
-/
structure TWLeaf
    {d n inputWeight : ℕ}
    (x y z :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (coefficient : ℕ → ℤ) where
  source :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  source_isTruncated :
    SPFactora.IsTruncated n source
  source_weight_least :
    SPFactora.WordWeightLeast
      (strictTailParent x y z + 1) source
  list_full_trace :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q source =
        wordListEval
          (SLeaf.eval
            (PEAddres.freeLowerTruncation
              (n := n)))
          (signedLeafStrict x y z (coefficient q))

namespace TWLeaf

/--
Normalize the ordinary fixed three-head packet and discard its vanishing
active block.  The result is an exact signed-leaf strict-trace source
supported one layer higher.
-/
noncomputable def headExpansionNormalizer
    {d n inputWeight : ℕ}
    {x y z :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {coefficient : ℕ → ℤ}
    (hn : 2 ≤ n)
    (hparent :
      strictTailParent x y z + 1 < n)
    (head :
      CHExp
        (inputWeight := inputWeight) x y z coefficient)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight := strictTailParent x y z)
        (concreteBasicCommutators.{u} d)) :
    TWLeaf
      (n := n) (inputWeight := inputWeight) x y z coefficient := by
  have hparentPos :
      1 ≤ strictTailParent x y z := by
    have hxWeight :
        0 < x.weight PEAddres.weight :=
      CWord.weight_pos
        PEAddres.weight PEAddres.weight_pos x
    have hyWeight :
        0 < y.weight PEAddres.weight :=
      CWord.weight_pos
        PEAddres.weight PEAddres.weight_pos y
    have hzWeight :
        0 < z.weight PEAddres.weight :=
      CWord.weight_pos
        PEAddres.weight PEAddres.weight_pos z
    simp only [strictTailParent]
    omega
  let recollection :=
    normalizer.source_recollection_series hn
      (concreteBasicCommutators.{u} d)
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      head.headSource hparentPos (by omega)
      (head.truncated_head_source (by
        change strictTailParent x y z < n
        omega))
      head.least_head_source
      (by
        intro q
        rw [head_leaf_full head q]
        exact
          leaf_strict_series
            x y z (coefficient q))
  exact
    {
      source := recollection.higherSource
      source_isTruncated := recollection.higher_source_truncated
      source_weight_least := by
        simpa only [Nat.add_assoc] using
          recollection.higher_weight_least
      list_full_trace := by
        intro q
        rw [recollection.list_higher_raw,
          head_leaf_full head q]
    }

/--
Polynomial normalization of the coefficient function feeds the unrestricted
signed-leaf strict-trace compiler directly.
-/
noncomputable def headCoefficientNormalizer
    {d n inputWeight : ℕ}
    {x y z :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {coefficient : ℕ → ℤ}
    (hn : 2 ≤ n)
    (hparent :
      strictTailParent x y z + 1 < n)
    (hinputWeight : 0 < inputWeight)
    (hpolynomial :
      IVMost coefficient
        (strictTailParent x y z / inputWeight))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight := strictTailParent x y z)
        (concreteBasicCommutators.{u} d)) :
    TWLeaf
      (n := n) (inputWeight := inputWeight) x y z coefficient :=
  headExpansionNormalizer hn hparent
    (CHExp.ofPolynomial
      hinputWeight hpolynomial)
    normalizer

end TWLeaf

namespace
  TJRecoll

/--
An unrestricted fixed signed-leaf Hall-Witt strict-trace source directly
supplies the expanded-Jacobi value recollection.
-/
noncomputable def signed_leaf_witt
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (strictTrace :
      TWLeaf
        (n := n) (inputWeight := inputWeight)
        decomposition.left decomposition.middle decomposition.right
          factor.exponent) :
    TJRecoll
      (n := n) factor decomposition where
  higherSource := strictTrace.source
  higher_source_truncated := strictTrace.source_isTruncated
  higher_least_succ := by
    have hweight := congrArg HallTree.weight decomposition.tree_eq
    simp only [HallTree.weight_commutator, tree_weight] at hweight
    simpa only [strictTailParent, hweight] using
      strictTrace.source_weight_least
  list_higher_raw := by
    intro q
    rw [strictTrace.list_full_trace]
    exact
      (expanded_jacobi_leaf
        factor decomposition q).symm

end
  TJRecoll

end
  LCSrc
end TCTex
end Submission

-- Merged from ConcreteSwapValueResidualExactCancellation.lean

/-!
# Exact cancellation of signed symbolic Hall-power swap residuals

Reversing a commutator is exactly inversion for the commutator convention
used by mathlib.  The signed swap factors therefore have exactly the same
evaluated value as their original factors.  Their value-residual packets are
not merely semantically one stratum higher: they evaluate to `1`.

This file packages the resulting empty recollections for both compressed
basic-child swaps and arbitrary expanded-root swaps.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

namespace HEWord

/-- A signed swap of two basic children has inverse unpowered word value. -/
theorem children_swap_inv
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).wordValue (n := n) =
      (factor.wordValue (n := n))⁻¹ := by
  change
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).word.eval
        PEAddres.freeLowerTruncation =
      (factor.word.eval
        PEAddres.freeLowerTruncation)⁻¹
  rw [←
    lower_truncation_tree
      (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).word,
    ← lower_truncation_tree factor.word,
    tree_children_swap, htree]
  simp only [HallTree.to_commutator_commutator,
    CWord.eval_commutator]
  exact congrArg
    (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (commutatorElement_inv
      (left.toCWord.eval FreeGroup.of)
      (right.toCWord.eval FreeGroup.of)).symm

/-- A signed swap of two basic children preserves the evaluated power. -/
theorem eval_children_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).eval (n := n) q =
      factor.eval (n := n) q := by
  rw [SPFactora.eval, SPFactora.eval,
    exponent_children_swap,
    children_swap_inv, zpow_neg, inv_zpow, inv_inv]

/-- The forward two-basic-child swap value packet cancels exactly. -/
theorem children_swap_raw
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (childrenSwapSource factor left right hleftBasic
          hrightBasic htree) =
      1 := by
  simp only [childrenSwapSource,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg,
    eval_children_swap, inv_mul_cancel]

/-- The inverse two-basic-child swap value packet also cancels exactly. -/
theorem list_children_inverse
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicChildrenSwap factor left right
          hleftBasic hrightBasic htree) =
      1 := by
  rw [basicChildrenSwap,
    SPFactora.list_eval_inverse,
    children_swap_raw]
  simp

/-- A signed expanded-root swap has inverse unpowered word value. -/
theorem expanded_swap_inv
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).wordValue (n := n) =
      (factor.wordValue (n := n))⁻¹ := by
  rw [SPFactora.wordValue, SPFactora.wordValue,
    word_expanded_swap, hword]
  exact (commutatorElement_inv _ _).symm

/-- A signed expanded-root swap preserves the evaluated power. -/
theorem eval_expanded_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    (expandedSwapFactor factor left right hword).eval (n := n) q =
      factor.eval (n := n) q := by
  rw [SPFactora.eval, SPFactora.eval,
    exponent_expanded_swap, expanded_swap_inv,
    zpow_neg, inv_zpow, inv_inv]

/-- The forward expanded-root swap value packet cancels exactly. -/
theorem expanded_root_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedSwapRaw factor left right hword) =
      1 := by
  simp only [expandedSwapRaw,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg, eval_expanded_swap,
    inv_mul_cancel]

/-- The inverse expanded-root swap value packet also cancels exactly. -/
theorem expanded_swap_raw
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expandedSwapSource factor left right
          hword) =
      1 := by
  rw [expandedSwapSource,
    SPFactora.list_eval_inverse,
    expanded_root_swap]
  simp

end HEWord

namespace
  TIRecoll

/-- The inverse two-basic-child swap packet recollects to the empty source. -/
noncomputable def empty
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : HEWord.tree factor.word =
      .commutator left right) :
    TIRecoll
      (n := n) factor left right hleftBasic hrightBasic htree where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    contradiction
  higher_least_succ := by
    intro x hx
    contradiction
  list_higher_raw := by
    intro q
    simpa only [SPFactora.listEval_nil] using
      (HEWord.list_children_inverse
        factor left right hleftBasic hrightBasic htree q).symm

end
  TIRecoll

namespace
  TSRecolla

/-- The forward expanded-root swap packet recollects to the empty source. -/
noncomputable def empty
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    TSRecolla
      (n := n) factor left right hword where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    contradiction
  higher_least_succ := by
    intro x hx
    contradiction
  list_higher_raw := by
    intro q
    simpa only [SPFactora.listEval_nil] using
      (HEWord.expanded_root_swap
        factor left right hword q).symm

end
  TSRecolla

end TCTex
end Submission

-- Merged from ConcreteAutomaticComparisonCollection.lean

/-!
# Hall-power collection with automatic comparison recollection

Concrete Hall-tree reduction leaves two apparent higher-source obligations:
the true Hall-tree quotient and the comparison between its atomic packet and
the canonical semantic active Hall block. The second source is always a
fixed-weight atomic list, so restricted-sharp routing recollects it
automa.

This file exposes the reduced constructor boundary. A caller supplies only:

* one cutoff Hall-Petresco packet; and
* upward finite recollection of the true concrete Hall-tree residual.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of the true concrete
Hall-tree residual source.
-/
structure
    ACBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
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

namespace
  ACBuilda

open
  TAExp
open
  TAResolua
open
  SSNormal
open
  TCRecoll

/-- Compile the all-integral packet to an active-stratum correction factory. -/
noncomputable def packetFactoryAt
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      ACBuilda.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ) :
    TSFtrya
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) lowerWeight :=
  (builder.packet.powerSupportedFactory
    hinputWeight lowerWeight)
    |>.correctionPacketFactory

/--
Construct the powered semantic normalizer directly. Recursive uses occur only
at strictly larger support weights.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (builder :
      ACBuilda.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d) hH hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hH hinputWeight (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              ofNormalizerAbove
                (lowerWeight := lowerWeight)
                (fun strongerWeight
                    (_hstronger : lowerWeight < strongerWeight) =>
                  builder.semanticCoordinateNormalizer
                    hn hH hinputWeight strongerWeight)
            let packetFactory :=
              builder.packetFactoryAt hinputWeight lowerWeight
            let comparison :=
              of_atomicNorm
                hn hH factor hfactorWeight hfactorTruncated packetFactory
                  sharp nextNormalizer
            let factorTail :=
              ((builder.basicResidual lowerWeight hterminal factor
                hfactorWeight hfactorTruncated).intrinsicResidualSource
                  comparison hfactorWeight).factorExpansion
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  ACBuilda

namespace TSInput

/--
For canonical Hall families, a cutoff packet and true Hall-tree residual
recollections construct the Claim 5 coordinate polynomials.
-/
theorem
    automaticComparisonBuilder
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
      ACBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn
          (forms_associated_below
            d n)
          hinputWeight inputWeight)
      hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteHallClassTwoCollection.lean

/-!
# Class-two Hall-power collection for the canonical Hall families

The semantic class-two tail collector closes Claim 5 throughout
`n ≤ 3 * inputWeight` for any graded Hall bases.  Right-to-left foliage
contraction supplies those bases for the canonical finite Hall families.

This file records the resulting concrete Claim 5 theorem.  It is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
The canonical Hall families provide Claim 5 coordinate expansions throughout
the class-two source range.
-/
theorem concrete_expansion_tail
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CEData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  expansion_semantic_tail
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hinputWeight hcutoff heBelow

/--
The canonical Hall families provide the integer-valued coordinate polynomials
consumed by Claim 5 throughout the class-two source range.
-/
theorem concrete_semantic_tail
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  collected_semantic_tail
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hinputWeight hcutoff heBelow

end TCTex
end Submission

-- Merged from ConcreteHallReachableSharpHigherTailRouting.lean

/-!
# Reachable sharp higher-tail routing for powered concrete Hall families

The reachable powered recollection builder supplies a semantic normalizer at
every support stratum and selects automatic class-two correction packets
whenever possible.  The sharp powered higher-tail router consumes those two
families directly.

This file packages the generic adapter and its concrete Hall-family
specialization.  The remaining operational work is the active-block route,
not movement across the previously normalized higher tail.  This file is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace
  TDBuild

/-- A reachable builder supplies powered semantic normalizers at every bound. -/
noncomputable def supportedSemanticFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H) :
    SSNormala
      (n := n) (inputWeight := inputWeight) H where
  normalizer lowerWeight :=
    builder.semanticCoordinateNormalizer hn H hH lowerWeight

/-- A reachable builder exposes its automatic-or-custom packet choice by stratum. -/
def supportedCorrectionFactory
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H) :
    TFSched
      (n := n) (inputWeight := inputWeight) H where
  factory lowerWeight := builder.packetFactoryAt H lowerWeight

/--
The reachable builder automa routes active factors across powered
higher tails by sharp parent-relative normalization.
-/
noncomputable def recursiveSemanticSchedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H) :
    RHRoute
      (n := n) (inputWeight := inputWeight) H :=
  (builder.supportedCorrectionFactory H)
    |>.recursiveSemanticSchedule
      (builder.supportedSemanticFamily hn H hH)

end
  TDBuild

/--
For the canonical finite Hall families, every reachable powered builder
automa supplies the terminating higher-tail route schedule.
-/
noncomputable def
    recursive_reachable_builder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d)) :
    RHRoute
      (n := n) (inputWeight := inputWeight)
        (concreteCommutatorsWeight.{u} d) :=
  builder.recursiveSemanticSchedule
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)

end TCTex
end Submission

-- Merged from ConcreteHallRestrictedSharpUniversalPacketCollection.lean

/-!
# Concrete Hall-power collection from universal Hall-Petresco packets

The canonical finite Hall families satisfy the associated-graded basis
hypothesis required by the universal-packet powered collector.  A universal
all-integral Hall-Petresco packet and singleton semantic recollection therefore
construct Claim 5 coordinate polynomials from any correctly sourced powered
input.

This specialization deliberately keeps that powered source explicit:
constructing it beyond the class-two region remains a separate part of the
universal collection theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TSInput

/--
For the canonical Hall families, a universal Hall-Petresco packet and singleton
recollections construct the Claim 5 coordinate polynomials from a sourced
powered input.
-/
theorem
    restrictedSharpBuilder
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
      RSUniv
        (n := n) (inputWeight := inputWeight) hn
          (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.restrictedSharpUniversal
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hsourceSupported builder hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ConcreteHallUniversalPacketResidualSourceCollection.lean

/-!
# Concrete Hall-power collection from universal packets and residual sources

The canonical finite Hall families satisfy the associated-graded basis
hypothesis required by residual-source collection.  Thus the remaining
nonterminal input for Claim 5 is an explicit compression of each intrinsic
factor residual source into strictly heavier symbolic factors.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TSInput

/--
For canonical Hall families, a universal Hall-Petresco packet and intrinsic
residual-source recollections construct the Claim 5 coordinate polynomials.
-/
theorem
    universalCollectionBuilder
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
      SUBuild
        (n := n) (inputWeight := inputWeight) hn
          (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordSharpBuilder
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hsourceSupported builder hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ConcreteReductionPacketCollection.lean

/-!
# Hall-power collection from concrete Hall-tree residual sources

The recursive Claim 5 collector consumes intrinsic factor residual sources.
Concrete Hall-tree reduction splits each such residual into two operational
sources:

* the explicit atomic reduction residual; and
* the comparison residual between that packet and the semantic active Hall
  block.

This file packages recollection of those two concrete sources as a direct
input to the cutoff-packet collector.  Unlike the universal-packet variant,
this interface asks only for the quotient-specific Hall-Petresco packet needed
by the recursive collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollections of the two concrete
Hall-tree residual sources.
-/
structure
    TCBuilde
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
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
  TCBuilde

/--
Compose the two concrete recollections into the intrinsic residual-source
builder consumed by cutoff-packet restricted-sharp recursion.
-/
noncomputable def restrictedSharpPacket
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TCBuilde.{u}
        (inputWeight := inputWeight) hn hH) :
    TSBuilda.{u}
      (inputWeight := inputWeight) hn
        (concreteBasicCommutators.{u} d) hH where
  packet := builder.packet
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated :=
    (builder.basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated).intrinsicResidualSource
        (builder.comparisonResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated)
        hfactorWeight

end
  TCBuilde

namespace TSInput

/--
For canonical Hall families, concrete Hall-tree residual recollections and a
cutoff Hall-Petresco packet construct the Claim 5 coordinate polynomials.
-/
theorem
    coordinateCollectionBuilder
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
      TCBuilde.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.sharpCollectionBuilder
    hn (concreteCommutatorsWeight.{u} d)
      (forms_associated_below
        d n)
      hsourceSupported
      (by
        simpa only [concreteBasicCommutators] using
          builder.restrictedSharpPacket)
      hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteJacobiContinuationDecomposition.lean

/-!
# Recursive decomposition of the symbolic Jacobi continuation

After the atomic Jacobi coordinate packet is peeled from a true concrete
factor residual, the remaining continuation can be decomposed into:

* the true residual of the second Jacobi descendant;
* the true residual of the first descendant, conjugated by the second
  descendant value; and
* the inverse value-level Jacobi residual.

This is an exact symbolic-list identity.  It exposes the recursive obligations
that remain after the associated-graded Jacobi correction has been routed
upward.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
Recursive source whose evaluation is the remaining Jacobi continuation.

The singleton factors surrounding the first descendant residual encode its
conjugation by the second descendant value.
-/
noncomputable def jacobiContinuationSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  basicRawSource
      (jacobiSecondFactor factor left middle right hword) ++
    [(jacobiSecondFactor factor left middle right hword).neg] ++
      basicRawSource
          (jacobiFirstFactor factor left middle right hword) ++
        [jacobiSecondFactor factor left middle right hword] ++
          jacobiRawSource factor left middle right hword

/-- A truncated original factor gives a physically truncated recursive continuation. -/
theorem truncated_continuation_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (jacobiContinuationSource
        factor left middle right hword) := by
  have hfirst :
      (jacobiFirstFactor factor left middle right hword).word.weight
          PEAddres.weight < n := by
    simpa only [jacobi_first_factor] using hfactor
  have hsecond :
      (jacobiSecondFactor factor left middle right hword).word.weight
          PEAddres.weight < n := by
    simpa only [word_jacobi_second] using hfactor
  intro x hx
  simp only [jacobiContinuationSource, List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · exact
      truncated_reduction_source
        (jacobiSecondFactor factor left middle right hword) hsecond x hx
  · simp only [List.mem_singleton] at hx
    subst x
    simpa only [SPFactora.word_neg] using hsecond
  · exact
      truncated_reduction_source
        (jacobiFirstFactor factor left middle right hword) hfirst x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hsecond
  · exact
      truncated_jacobi_source
        factor left middle right hword hfactor x hx

/--
The recursive decomposition evaluates exactly to the continuation left after
the atomic Jacobi coordinate correction.
-/
theorem
    jacobi_continuation_decomposition
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (jacobiContinuationSource
          factor left middle right hword) =
      SPFactora.listEval q
        (jacobiContinuationRaw factor left middle right hword) := by
  simp only [jacobiContinuationSource,
    jacobiContinuationRaw, jacobiRawSource,
    jacobiValueSource, SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one,
    SPFactora.eval_neg]
  group

/-- The recursive decomposition inherits next-stratum membership. -/
theorem
    continuation_decomposition_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (jacobiContinuationSource
          factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    jacobi_continuation_decomposition
      factor left middle right hword q]
  exact
    continuation_raw_series
      factor left middle right hword q

end HEWord
end TCTex
end Submission

-- Merged from ConcreteNonbasicReductionCollection.lean

/-!
# Hall-power collection reduced to non-basic expanded trees

The concrete comparison residual is automatic, and all-weight PBW uniqueness
makes the true reduction residual trivial whenever the expanded Hall tree is
already basic.  This file exposes the remaining arbitrary-cutoff boundary:
finite upward recollection is required only for genuinely non-basic expanded
trees.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for factors whose expanded Hall trees are non-basic.
-/
structure NCBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  nonbasicResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(HEWord.tree factor.word).IsBasic →
                TSRecollb
                  (n := n) factor

namespace NCBuilda

open
  TSRecollb

/--
Fill every basic expanded-tree residual with the empty recollection and leave
only non-basic residuals to the caller.
-/
noncomputable def automaticComparisonCollection
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      NCBuilda.{u}
        (inputWeight := inputWeight) hn hH) :
    ACBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated := by
    by_cases htreeBasic :
        (HEWord.tree factor.word).IsBasic
    · exact tree_basic factor htreeBasic
    · exact
        builder.nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
          hfactorTruncated htreeBasic

end NCBuilda

namespace TSInput

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic expanded trees construct the Claim 5 coordinate polynomials.
-/
theorem
    nonbasicCollectionBuilder
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
      NCBuilda.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.automaticComparisonBuilder
    hn hsourceSupported builder.automaticComparisonCollection
      hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteJacobiContinuationRecursion.lean

/-!
# Recursive interface for the symbolic Jacobi continuation

The exact Jacobi-continuation decomposition is the collector-facing recursive
boundary:

* the two descendant true residuals remain recursive calls;
* the first descendant residual is conjugated by the second descendant value;
* the inverse value-level Jacobi packet lies one lower-central stratum higher.

This file packages recollection of that decomposition as recollection of the
original continuation.  It also records the common-total-weight rank decrease
for all four eventual right factors in the two descendant branches.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
Both Jacobi descendant branches strictly decrease the reverse finite rank of
every eventual right factor, measured in the common original total weight.
-/
theorem up_height_all
    (a b v tFirst tSecond : HallTree α)
    (hvb : v < b)
    (hba : b < a)
    (haBasic : a.IsBasic)
    (hbBasic : b.IsBasic)
    (htFirstBasic : tFirst.IsBasic)
    (htSecondBasic : tSecond.IsBasic)
    (htFirstWeight : tFirst.weight = a.weight + v.weight)
    (htSecondWeight : tSecond.weight = b.weight + v.weight) :
    let n := (a.weight + v.weight) + b.weight
    defectUpHeight n b <
        defectUpHeight n v ∧
      defectUpHeight n tFirst <
        defectUpHeight n v ∧
      defectUpHeight n a <
        defectUpHeight n v ∧
      defectUpHeight n tSecond <
        defectUpHeight n v := by
  dsimp only
  have hfirst :=
    defect_up_both
      a b v tFirst hvb hbBasic htFirstBasic htFirstWeight
  have hsecond :=
    up_height_both
      a b v tSecond hvb hba haBasic htSecondBasic htSecondWeight
  have htotal :
      (b.weight + v.weight) + a.weight =
        (a.weight + v.weight) + b.weight := by
    omega
  simpa only [htotal] using
    And.intro hfirst.1
      (And.intro hfirst.2 (And.intro hsecond.1 hsecond.2))

end HallTree

namespace TCTex

open HEWord

universe u

/--
Recollection data for the explicit recursive decomposition of a Jacobi
continuation.
-/
structure TCRecol
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight + 1) higherSource
  list_decomposition_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (jacobiContinuationSource
            factor left middle right hword)

namespace
  TCRecol

/--
An upward recollection of the explicit recursive decomposition is an upward
recollection of the original Jacobi continuation.
-/
noncomputable def jacobiContinuationRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {hword : factor.word = .commutator (.commutator left middle) right}
    (recollection :
      TCRecol
        (n := n) factor left middle right hword) :
    SymbolicContinuationRecollection
      (n := n) factor left middle right hword where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_higher_raw := by
    intro q
    rw [recollection.list_decomposition_raw q,
      jacobi_continuation_decomposition]

end
  TCRecol

/--
A decomposition-aware refinement of the syntactic Jacobi continuation
builder.  Its remaining obligation is exactly the recursive decomposition
rather than the opaque continuation source.
-/
structure
    SCBuildd
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  jacobiContinuationDecomposition :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
          (left middle right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator (.commutator left middle) right),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              TCRecol
                (n := n) factor left middle right hword

namespace
  SCBuildd

/--
Forget the explicit recursive shape after compiling it into the continuation
boundary consumed by the existing Jacobi collector.
-/
noncomputable def syntacticContinuationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
  SCBuildd.{u}
        (inputWeight := inputWeight) hn hH) :
    TSContin
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  jacobiContinuation := by
    intro lowerWeight hnonterminal factor left middle right hword
      hfactorWeight hfactorTruncated
    let recollection :=
      builder.jacobiContinuationDecomposition lowerWeight hnonterminal
        factor left middle right hword hfactorWeight hfactorTruncated
    exact recollection.jacobiContinuationRecollection

/--
Lift one syntactically exposed Jacobi factor from recollection of its explicit
recursive continuation decomposition.
-/
noncomputable def jacobiResidual
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
  SCBuildd.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  builder.syntacticContinuationBuilder.jacobiResidual
    hinputWeight lowerWeight hnonterminal normalizerAbove factor left middle
      right hword hfactorWeight hfactorTruncated

/--
Lift an expanded Jacobi root whose inner bracket is nonbasic from recollection
of its explicit recursive continuation decomposition.
-/
noncomputable def jacobiTreeNonbasic
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
  SCBuildd.{u}
        (inputWeight := inputWeight) hn hH)
    (hinputWeight : 1 ≤ inputWeight)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      HEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hinnerNonbasic :
      ¬(HallTree.commutator left middle).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  builder.syntacticContinuationBuilder
    |>.jacobiTreeNonbasic hinputWeight
      lowerWeight hnonterminal normalizerAbove factor left middle right htree
        houterNonbasic hinnerNonbasic hfactorWeight hfactorTruncated

end
  SCBuildd
end TCTex
end Submission

-- Merged from ConcreteJacobiFrontierReductionCollection.lean

/-!
# Hall-power collection reduced to the Jacobi frontier

Basic expanded Hall trees, expanded self-brackets, and reversed basic
brackets have automatic true residual recollections.  This file packages
those eliminations.  An arbitrary-cutoff collector now needs explicit
residual recollection only for nonbasic brackets with distinct children
whose reverse orientation is also nonbasic.

These are precisely the cases where the Hall reduction recursion proceeds
through a Jacobi rewrite.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for expanded brackets on the Jacobi frontier.
-/
structure
    TFBuildc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  jacobiFrontierResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(HEWord.tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  HEWord.tree factor.word =
                      HallTree.commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        TSRecollb
                          (n := n) factor

namespace
  TFBuildc

open
  TSRecollb

/--
Fill every terminal expanded-tree residual automa and leave only
Jacobi-frontier residuals to the caller.
-/
noncomputable def nonbasicReductionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TFBuildc.{u}
        (inputWeight := inputWeight) hn hH) :
    NCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic := by
    cases htree : HEWord.tree factor.word with
    | atom generator =>
        exfalso
        apply htreeNonbasic
        rw [htree]
        exact HallTree.isBasic_atom generator
    | commutator left right =>
        by_cases hsame : left = right
        · subst right
          exact tree_commutator_self factor left htree
        · by_cases hreverse : (HallTree.commutator right left).IsBasic
          · exact tree_swap_basic factor right left htree hreverse
          · exact
              builder.jacobiFrontierResidual lowerWeight hnonterminal factor
                hfactorWeight hfactorTruncated htreeNonbasic left right
                  htree hsame hreverse

end
  TFBuildc

namespace TSInput

/--
For canonical Hall families, a cutoff packet and true residual recollections
on the Jacobi frontier construct the Claim 5 coordinate polynomials.
-/
theorem
    jacobiFrontierBuilder
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
      TFBuildc.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.nonbasicCollectionBuilder
    hn hsourceSupported builder.nonbasicReductionBuilder
      hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteNonbasicNonselfReductionCollection.lean

/-!
# Hall-power collection reduced to non-basic non-self expanded trees

Basic expanded Hall trees and symbolic self-commutators have automatic true
residual recollections.  This file packages both eliminations: an arbitrary
cutoff collector now needs explicit residual recollection only for non-basic
words that are not syntactic self-commutators.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for non-basic factors that are not symbolic self-commutators.
-/
structure
    TNNonsel
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  nonbasicNonselfResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(HEWord.tree factor.word).IsBasic →
                (∀ word :
                  CWord
                    (HEAddres
                      (concreteBasicCommutators.{u} d)),
                    factor.word ≠ .commutator word word) →
                  TSRecollb
                    (n := n) factor

namespace
  TNNonsel

open
  TSRecollb

/--
Fill every symbolic self-commutator residual with the empty recollection and
leave only non-basic non-self residuals to the caller.
-/
noncomputable def nonbasicReductionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TNNonsel.{u}
        (inputWeight := inputWeight) hn hH) :
    NCBuilda.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic := by
    classical
    by_cases hself :
        ∃ word :
          CWord
            (HEAddres (concreteBasicCommutators.{u} d)),
          factor.word = .commutator word word
    · exact
        word_commutator_self factor (Classical.choose hself)
          (Classical.choose_spec hself)
    · exact
        builder.nonbasicNonselfResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic (by
            intro word hword
            exact hself ⟨word, hword⟩)

end
  TNNonsel

namespace TSInput

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic non-self words construct the Claim 5 coordinate polynomials.
-/
theorem
    nonbasicNonselfBuilder
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
      TNNonsel.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.nonbasicCollectionBuilder
    hn hsourceSupported builder.nonbasicReductionBuilder
      hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteJacobiFrontierLowCutoffCollection.lean

/-!
# Automatic Hall-power residual collection below the Jacobi frontier

At cutoff at most six, every nonterminal true Hall-tree quotient residual has
weight at most two.  The Jacobi frontier starts in weight three, so a supplied
truncated Hall-Petresco packet automa yields the Claim 5 coordinate
polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  TFBuildc

/--
At cutoff at most six, a truncated Hall-Petresco packet has no remaining
Jacobi-frontier residual obligations.
-/
noncomputable def automatic_n_six
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hn6 : n ≤ 6) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH where
  packet := packet
  jacobiFrontierResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated htreeNonbasic left right htree hne hreverse := by
    exfalso
    apply
      HallTree.false_swap_not
        left right
    · rw [← htree, HEWord.tree_weight, hfactorWeight]
      omega
    · exact hne
    · exact fun hbasic => htreeNonbasic (htree.symm ▸ hbasic)
    · exact hreverse

end
  TFBuildc

open
  TFBuildc

namespace TSInput

/--
For canonical Hall families at cutoff at most six, a supplied truncated
Hall-Petresco packet and supported input construct the Claim 5 coordinate
polynomials.
-/
theorem
    jacobiAutomaticCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.jacobiFrontierBuilder
    hn hsourceSupported (automatic_n_six packet hn6) hinputWeight

/--
For canonical Hall families at cutoff at most six, a universal Hall-Petresco
packet and supported input construct the Claim 5 coordinate polynomials.
-/
theorem
    frontierAutomaticCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.UAInt.{u})
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.jacobiAutomaticCollection
    hn hn6 (packet.truncatedAll (d := d) (n := n))
      hsourceSupported hinputWeight

end TSInput
end TCTex
end Submission

-- Merged from ConcreteNonbasicChildJacobiFrontierCollection.lean

/-!
# Concrete Jacobi frontiers reduced to nonbasic children

The arbitrary concrete Jacobi frontier contains two qualitatively different
cases.  When both children are basic, Hall admissibility orients the bracket
into expanded Jacobi recursion.  Otherwise at least one child remains
nonbasic and further recursive tree descent is required.

This file discharges the first case and exposes only the second as the next
collector-facing boundary.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Expanded basic-child orientation data together with recollections for the
remaining Jacobi frontiers that still contain a nonbasic child.
-/
structure
    NCJacobi
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  basicChildren :
    JOBuild.{u}
      (inputWeight := inputWeight) hn hH
  hinputWeight : 1 ≤ inputWeight
  normalizerAbove :
    ∀ lowerWeight strongerWeight : ℕ,
      lowerWeight < strongerWeight →
        TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)
  nonbasicChildResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(HEWord.tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  HEWord.tree factor.word =
                      HallTree.commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        (¬left.IsBasic ∨ ¬right.IsBasic) →
                          TSRecollb
                            (n := n) factor

namespace
  NCJacobi

/--
Fill every two-basic-child Jacobi frontier by orientation and expanded Jacobi
recursion.  Leave only brackets with a nonbasic child to the caller.
-/
noncomputable def jacobiCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      NCJacobi.{u}
        (inputWeight := inputWeight) hn hH) :
    TFBuildc.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.basicChildren.expandedJacobi.packet
  jacobiFrontierResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic left right htree hchildrenNe
        hreverseNonbasic := by
    by_cases hleftBasic : left.IsBasic
    · by_cases hrightBasic : right.IsBasic
      · exact
          builder.basicChildren.residual builder.hinputWeight lowerWeight
            hnonterminal (builder.normalizerAbove lowerWeight) factor
              left right hleftBasic hrightBasic htree
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
  NCJacobi

end TCTex
end Submission

-- Merged from ConcreteUnresolvedReductionCollection.lean

/-!
# Hall-power collection reduced past exact skew cases

Basic expanded Hall trees, symbolic self-commutators, and reversed-basic
brackets all have automatic true residual recollections.  This file packages
those eliminations and exposes the remaining arbitrary-cutoff collector
boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of only the unresolved
true residuals after basic, self-bracket, and reversed-basic cases are removed.
-/
structure UCBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  unresolvedResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
              ¬(HEWord.tree factor.word).IsBasic →
                (∀ word :
                  CWord
                    (HEAddres
                      (concreteBasicCommutators.{u} d)),
                    factor.word ≠ .commutator word word) →
                  ¬HEWord.IsReversedBasic factor.word →
                    TSRecollb
                      (n := n) factor

namespace
  UCBuild

open
  TSRecollb

/--
Fill every reversed-basic residual with the empty recollection and leave only
the unresolved true residuals to the caller.
-/
noncomputable def nonbasicNonselfCollection
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      UCBuild.{u}
        (inputWeight := inputWeight) hn hH) :
    TNNonsel.{u}
      (inputWeight := inputWeight) hn hH where
  packet := builder.packet
  nonbasicNonselfResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic hnonself := by
    classical
    by_cases hreversed :
        HEWord.IsReversedBasic factor.word
    · exact reversed_basic factor hreversed
    · exact
        builder.unresolvedResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic hnonself hreversed

end
  UCBuild

namespace TSInput

/--
For canonical Hall families, a cutoff packet and recollections of only the
unresolved true residuals construct the Claim 5 coordinate polynomials.
-/
theorem
    unresolvedCollectionBuilder
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
      UCBuild.{u}
        (inputWeight := inputWeight) hn
          (forms_associated_below
            d n))
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.nonbasicNonselfBuilder
    hn hsourceSupported
      builder.nonbasicNonselfCollection hinputWeight

end TSInput
end TCTex
end Submission
