import Submission.Group.HallBasic.ExplicitScaling
import Submission.Group.Zassenhaus.ReductionFactors
import Submission.Group.Zassenhaus.ReductionComparison
import Submission.Group.Zassenhaus.EndpointShapeInterpolation
import Submission.Group.HallBasic.ExplicitCoordinatePackets
import Submission.Group.Zassenhaus.ConcreteAutomaticComparison
import Submission.Group.Zassenhaus.ConjugatedHigherList
import Submission.Group.Zassenhaus.SourceRecollectionOperations
import Submission.Group.HallBasic.ExplicitZeroCoordinates
import Submission.Group.HallBasic.ExplicitSwapScaling
import Submission.Group.HallBasic.LowWeightScaling
import Submission.Group.Zassenhaus.WeightOneReduction
import Submission.Group.Zassenhaus.FormulaChooseSubstitution


-- Merged from ReductionBasicTree.lean

/-!
# Concrete Hall-power reduction residuals for basic expanded trees

All-weight PBW uniqueness makes explicit reduction exact whenever a symbolic
factor's expanded Hall tree is already basic.  Its true concrete reduction
residual therefore recollects to the empty higher source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
For a factor whose expanded tree is basic, the explicit atomic Hall-tree
reduction packet evaluates literally to the original symbolic factor.
-/
theorem reduction_factors_tree
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (htreeBasic : (tree factor.word).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      factor.eval q := by
  rw [list_basic_factors]
  rw [
    HallTree.reduction_scaled_zpow
      (tree factor.word) htreeBasic]
  rw [map_zpow, lower_truncation_tree]
  rfl

/--
For a factor whose expanded tree is basic, dividing by its explicit atomic
reduction packet has trivial value.
-/
theorem
    reduction_raw_tree
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (htreeBasic : (tree factor.word).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_factors_tree
      factor htreeBasic q]
  simp

end HEWord

namespace
  TSRecollb

open HEWord

/--
For a factor whose expanded tree is basic, its explicit Hall-tree residual
recollects to the empty higher source.
-/
noncomputable def tree_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (htreeBasic : (HEWord.tree factor.word).IsBasic) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (reduction_raw_tree
        factor htreeBasic q).symm

end
  TSRecollb
end TCTex
end Submission

-- Merged from ReductionEndpointRecipeShapeFiberInterpolationResidualSourceCollection.lean

/-!
# Endpoint-interpolation collection from concrete Hall-tree residual sources

Endpoint interpolation already supplies the powered adjacent-swap correction
packets.  For canonical Hall families, the remaining intrinsic factor
residual source splits into two concrete Hall-tree recollections:

* the explicit atomic reduction residual; and
* the comparison residual between that packet and the semantic active block.

This file packages exactly those packet-free residual inputs and composes them
into the intrinsic residual-source builder consumed by endpoint-interpolation
collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


/--
Packet-free recollections of the two concrete Hall-tree residual sources for
one Hall-power input weight.
-/
structure
    TSBuildc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)) where
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
  TSBuildc

/--
Compose the atomic and comparison recollections into the intrinsic
factor-residual source consumed by endpoint-interpolation collection.
-/
noncomputable def
    fiberInterpolationBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    (builder :
      TSBuildc.{u}
        (inputWeight := inputWeight) hn hH) :
    TSBuild.{u}
      (inputWeight := inputWeight) hn
        (concreteBasicCommutators.{u} d) hH where
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated :=
    (builder.basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated).intrinsicResidualSource
        (builder.comparisonResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated)
        hfactorWeight

end
  TSBuildc

end TCTex
end Submission

-- Merged from ReductionJacobiTree.lean

/-!
# Concrete Hall-power reduction packets for Jacobi brackets

A Jacobi rewrite preserves the ordinary Hall weight of a symbolic factor and
does not change its repeated-block recipe.  This file records the two
descendant factors and proves that the quotient of the original atomic
reduction packet by the two descendant packets lies one lower-central stratum
higher.

This is the collector-facing packet for the surviving Jacobi frontier.  It
also isolates the continuation left after that atomic correction is peeled
from the true factor residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace SPFactora

universe u

/-- Casting a repeated-block recipe along a target-weight equality preserves evaluation. -/
private theorem cast_bounded_recipe
    {inputWeight r s : ℕ}
    (h : r = s)
    (recipe : BBRecipe inputWeight r)
    (q : ℕ) :
    (cast (congrArg (BBRecipe inputWeight) h) recipe).eval q =
      recipe.eval q := by
  cases h
  rfl

/-- Replace the Hall word of a symbolic factor without changing its exponent recipe. -/
noncomputable def reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight PEAddres.weight =
        factor.word.weight PEAddres.weight) :
    SPFactora H inputWeight where
  word := word
  coefficient := factor.coefficient
  recipe :=
    cast
      (congrArg (BBRecipe inputWeight) hweight.symm)
      factor.recipe

@[simp]
theorem word_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight PEAddres.weight =
        factor.word.weight PEAddres.weight) :
    (factor.reword word hweight).word = word :=
  rfl

@[simp]
theorem exponent_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight PEAddres.weight =
        factor.word.weight PEAddres.weight)
    (q : ℕ) :
    (factor.reword word hweight).exponent q = factor.exponent q := by
  change
    factor.coefficient *
        (cast
          (congrArg (BBRecipe inputWeight) hweight.symm)
          factor.recipe).eval q =
      factor.coefficient * factor.recipe.eval q
  rw [cast_bounded_recipe hweight.symm factor.recipe q]

end SPFactora

namespace HEWord

universe u

/--
A nonbasic commutator-shaped expanded tree comes from a commutator-shaped
word.  An atomic address cannot produce this case because its concrete Hall
tree is basic.
-/
theorem words_tree_basic
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree word = .commutator left right)
    (hnonbasic : ¬(HallTree.commutator left right).IsBasic) :
    ∃ leftWord rightWord :
        CWord
          (HEAddres (concreteBasicCommutators.{u} d)),
      word = .commutator leftWord rightWord ∧
        tree leftWord = left ∧
          tree rightWord = right := by
  cases word with
  | atom address =>
      exfalso
      apply hnonbasic
      rw [← htree]
      exact concrete_hall_tree address.2
  | commutator leftWord rightWord =>
      simp only [tree_commutator] at htree
      injection htree with hleft hright
      exact ⟨leftWord, rightWord, rfl, hleft, hright⟩

/-- A syntactically exposed left-normed Jacobi bracket. -/
structure SyntacticJacobiDecomposition
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))) where
  left :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  middle :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  right :
    CWord
      (HEAddres (concreteBasicCommutators.{u} d))
  word_eq : word = .commutator (.commutator left middle) right

/--
If both layers of an expanded left-normed bracket are nonbasic, neither layer
can be hidden inside an atomic Hall address.
-/
theorem nonempty_syntactic_tree
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hinnerNonbasic :
      ¬(HallTree.commutator left middle).IsBasic) :
    Nonempty (SyntacticJacobiDecomposition word) := by
  rcases
      words_tree_basic word
        (.commutator left middle) right htree houterNonbasic with
    ⟨leftWord, rightWord, hword, hleftTree, _hrightTree⟩
  rcases
      words_tree_basic leftWord
        left middle hleftTree hinnerNonbasic with
    ⟨leftWord, middleWord, hleftWord, _hleftTree, _hmiddleTree⟩
  exact
    ⟨{ left := leftWord
       middle := middleWord
       right := rightWord
       word_eq := by rw [hword, hleftWord] }⟩

/--
Choose the exposed symbolic words underlying two nonbasic expanded Jacobi
layers.
-/
noncomputable def
    syntacticTreeNonbasic
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      tree word = .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hinnerNonbasic :
      ¬(HallTree.commutator left middle).IsBasic) :
    SyntacticJacobiDecomposition word :=
  Classical.choice
    (nonempty_syntactic_tree
      word left middle right htree houterNonbasic hinnerNonbasic)

/-- The first Jacobi descendant of `[[left, middle], right]`. -/
noncomputable def jacobiFirstFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  factor.reword (.commutator (.commutator left right) middle) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)

/-- The negatively signed second Jacobi descendant of `[[left, middle], right]`. -/
noncomputable def jacobiSecondFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  (factor.reword (.commutator (.commutator middle right) left) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)).neg

@[simp]
theorem exponent_jacobi_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    (jacobiFirstFactor factor left middle right hword).exponent q =
      factor.exponent q := by
  simp [jacobiFirstFactor]

@[simp]
theorem exponent_jacobi_second
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (q : ℕ) :
    (jacobiSecondFactor factor left middle right hword).exponent q =
      -factor.exponent q := by
  simp [jacobiSecondFactor]

@[simp]
theorem jacobi_first_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    (jacobiFirstFactor factor left middle right hword).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  change
    ((CWord.commutator
        (CWord.commutator left right) middle).weight
        PEAddres.weight) =
      factor.word.weight PEAddres.weight
  rw [hword]
  simp only [CWord.weight_commutator]
  omega

@[simp]
theorem word_jacobi_second
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    (jacobiSecondFactor factor left middle right hword).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  change
    ((CWord.commutator
        (CWord.commutator middle right) left).weight
        PEAddres.weight) =
      factor.word.weight PEAddres.weight
  rw [hword]
  simp only [CWord.weight_commutator]
  omega

/--
Atomic packet residual comparing a Jacobi bracket with its two descendants.
-/
noncomputable def jacobiReductionSource
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
  SPFactora.inverseList (basicReductionFactors factor) ++
    basicReductionFactors (jacobiFirstFactor factor left middle right hword) ++
      basicReductionFactors (jacobiSecondFactor factor left middle right hword)

/--
Continuation left after peeling the atomic Jacobi packet from the true factor
residual.  Its evaluation is `A₂⁻¹ * A₁⁻¹ * factor`, where `A₁` and `A₂` are
the two descendant atomic packets.
-/
noncomputable def jacobiContinuationRaw
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
      (basicReductionFactors
        (jacobiSecondFactor factor left middle right hword)) ++
    SPFactora.inverseList
      (basicReductionFactors
        (jacobiFirstFactor factor left middle right hword)) ++
      [factor]

/-- Truncation of the original factor physically truncates its Jacobi packet. -/
theorem truncated_jacobi_reduction
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
      (jacobiReductionSource factor left middle right hword) := by
  intro x hx
  simp only [jacobiReductionSource, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact
      truncated_reduction_factors
        (jacobiFirstFactor factor left middle right hword)
        (by simpa only [jacobi_first_factor] using hfactor)
        x hx
  · exact
      truncated_reduction_factors
        (jacobiSecondFactor factor left middle right hword)
        (by simpa only [word_jacobi_second] using hfactor)
        x hx

/-- Truncation of the original factor physically truncates the continuation. -/
theorem truncated_jacobi_continuation
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
      (jacobiContinuationRaw factor left middle right hword) := by
  intro x hx
  simp only [jacobiContinuationRaw, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors
          (jacobiSecondFactor factor left middle right hword)
          (by simpa only [word_jacobi_second] using hfactor))
        x hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors
          (jacobiFirstFactor factor left middle right hword)
          (by simpa only [jacobi_first_factor] using hfactor))
        x hx
  · subst x
    exact hfactor

/--
The atomic Jacobi packet and its continuation multiply to the original true
factor residual.
-/
theorem
    jacobi_reduction_continuation
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
        (jacobiReductionSource factor left middle right hword) *
      SPFactora.listEval q
        (jacobiContinuationRaw factor left middle right hword) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  simp only [jacobiReductionSource, jacobiContinuationRaw,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    reduction_raw_source,
    SPFactora.listEval_cons,
    SPFactora.listEval_nil, mul_one]
  group

/--
The continuation is atomic-Jacobi correction division of the original true
factor residual.
-/
theorem
    jacobi_continuation_residual
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
        (jacobiContinuationRaw factor left middle right hword) =
      (SPFactora.listEval q
        (jacobiReductionSource factor left middle right hword))⁻¹ *
        SPFactora.listEval q
          (basicRawSource factor) := by
  rw [←
    jacobi_reduction_continuation
      factor left middle right hword q]
  group

/-- Every factor in the Jacobi packet residual is an atom in the source layer. -/
theorem atom_jacobi_source
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ jacobiReductionSource factor left middle right hword) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight PEAddres.weight := by
  simp only [jacobiReductionSource, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact atom_reduction_factors factor hx
  · rcases
      atom_basic_factors
        (jacobiFirstFactor factor left middle right hword) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (jacobi_first_factor factor left middle right hword)⟩
  · rcases
      atom_basic_factors
        (jacobiSecondFactor factor left middle right hword) hx with
      ⟨address, haddress, hweight⟩
    exact
      ⟨address, haddress,
        hweight.trans
          (word_jacobi_second factor left middle right hword)⟩

/-- The Jacobi packet residual evaluates one lower-central stratum higher. -/
theorem jacobi_reduction_series
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
        (jacobiReductionSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.scaled_jacobi_series
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
  rw [jacobiReductionSource, SPFactora.listEval_append,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    list_basic_factors, list_basic_factors,
    list_basic_factors]
  simpa only [map_mul, map_inv, tree_commutator,
    exponent_jacobi_factor, exponent_jacobi_second,
    jacobiFirstFactor, jacobiSecondFactor, SPFactora.word_neg,
    SPFactora.word_reword,
    SPFactora.exponent_neg,
    SPFactora.exponent_reword, hword, mul_assoc] using hmap

/-- The remaining Jacobi continuation also evaluates one stratum higher. -/
theorem continuation_raw_series
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
        (jacobiContinuationRaw factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    jacobi_continuation_residual
      factor left middle right hword q]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).mul_mem
        (Subgroup.inv_mem _
          (jacobi_reduction_series
            factor left middle right hword q))
        (list_reduction_series
          factor q)

end HEWord

namespace TSFtrya

open HEWord

/--
Route the finite atomic Jacobi coordinate correction into a source supported
one stratum higher.
-/
noncomputable def higher_jacobi_raw
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
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ higherSource :
        List
          (SPFactora
            (concreteBasicCommutators.{u} d) inputWeight),
      SPFactora.IsTruncated n higherSource ∧
        SPFactora.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q higherSource =
                SPFactora.listEval q
                  (jacobiReductionSource
                    factor left middle right hword) := by
  apply factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
        (jacobiReductionSource factor left middle right hword)
  · have hfactorPos := factor.word_weight_pos
    omega
  · omega
  · exact
      truncated_jacobi_reduction factor left middle right hword
        hfactorTruncated
  · intro x hx
    rcases
        atom_jacobi_source
          factor left middle right hword hx with
      ⟨address, haddress, haddressWeight⟩
    exact ⟨address, haddress, haddressWeight.trans hfactorWeight⟩
  · intro q
    simpa only [hfactorWeight] using
      jacobi_reduction_series
        factor left middle right hword q

end TSFtrya
end TCTex
end Submission

-- Merged from ReductionNegResidualRouting.lean

/-!
# Routing concrete residuals through coefficient negation

Negating a concrete symbolic Hall-power factor preserves its expanded Hall
tree, but it does not literally invert the ordered atomic reduction packet:
the canonical packet order is retained while every atomic coefficient changes
sign.  The resulting order correction is nevertheless a semantically higher
atomic source and can be recollected by restricted-sharp routing.

This file packages that atomic correction and uses it to derive the concrete
residual recollection of `factor.neg` from a recollection of `factor`.  The
same-ranked inverse factor in a value packet therefore does not need to be
treated as an independent recursive child.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

namespace SPFactora

/-- Negating a symbolic Hall-power factor twice restores the original factor. -/
@[simp]
theorem neg_neg
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factor : SPFactora H inputWeight) :
    factor.neg.neg = factor := by
  cases factor
  simp [neg]

end SPFactora

namespace HEWord

/--
The atomic correction between coefficientwise negation of the canonical
packet and list inversion of that packet.
-/
noncomputable def basicReductionNeg
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor.neg) ++
    SPFactora.inverseList (basicReductionFactors factor)

/-- Inverse atomic reduction packets retain their original symbolic weight. -/
theorem basic_reduction_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx :
      x ∈ SPFactora.inverseList
        (basicReductionFactors factor)) :
    x.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [SPFactora.inverseList] at hx
  rcases List.mem_map.mp hx with ⟨sourceFactor, hsourceFactor, rfl⟩
  simpa only [SPFactora.word_neg] using
    word_reduction_factors factor
      (by simpa using hsourceFactor)

/-- The atomic sign-order correction is physically truncated. -/
theorem truncated_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (basicReductionNeg factor) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [basic_reduction_factors factor.neg hx]
    simpa only [SPFactora.word_neg] using hfactorTruncated
  · rw [basic_reduction_factors factor hx]
    exact hfactorTruncated

/-- Every factor in the atomic sign-order correction is an active-layer atom. -/
theorem atom_raw_source
    {d inputWeight lowerWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ basicReductionNeg factor) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧ address.weight = lowerWeight := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases atom_reduction_factors factor.neg hx with
      ⟨address, hword, hweight⟩
    exact
      ⟨address, hword, by
        simpa only [SPFactora.word_neg] using
          hweight.trans hfactorWeight⟩
  · rcases atom_reduction_factors factor hx with
      ⟨address, hword, hweight⟩
    exact ⟨address, hword, hweight.trans hfactorWeight⟩

/--
The atomic sign-order correction starts one lower-central stratum higher.
It is the product of the residual for `factor.neg` and a conjugate of the
residual for `factor`.
-/
theorem
    reduction_neg_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionNeg factor) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
  have hneg :
      (SPFactora.listEval (n := n) q
          (basicReductionFactors factor.neg))⁻¹ *
          factor.neg.eval q ∈ K := by
    simpa only [K, SPFactora.word_neg,
      reduction_raw_source] using
      (list_reduction_series
        (n := n) factor.neg q)
  have hfactor :
      (SPFactora.listEval (n := n) q
          (basicReductionFactors factor))⁻¹ *
          factor.eval q ∈ K := by
    simpa only [K, reduction_raw_source] using
      (list_reduction_series
        (n := n) factor q)
  have hconjugated :
      factor.eval q *
            ((SPFactora.listEval (n := n) q
                (basicReductionFactors factor))⁻¹ *
              factor.eval q) *
          (factor.eval q)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem _ hfactor _
  rw [basicReductionNeg,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    SPFactora.list_eval_inverse]
  convert K.mul_mem hneg hconjugated using 1 ;
    simp only [SPFactora.eval_neg] ;
      group

end HEWord

namespace TSFtrya

/--
Restricted-sharp atomic normalization recollects the finite sign-order
correction between a factor and its coefficientwise negation.
-/
noncomputable def basicNegRecollection
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
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (basicReductionNeg factor) := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let result :=
    factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
      (basicReductionNeg factor)
      hlowerWeightPos (by omega)
      (truncated_raw_source
        factor hfactorTruncated)
      (fun x hx =>
        atom_raw_source
          factor hfactorWeight hx)
      (fun q => by
        simpa only [hfactorWeight] using
          reduction_neg_series
            (n := n) factor q)
  exact
    {
      higherSource := result.choose
      higher_source_truncated := result.choose_spec.1
      higher_weight_least := result.choose_spec.2.1
      list_higher_raw := result.choose_spec.2.2
    }

end TSFtrya

namespace
  TSRecollb

/--
Derive the true concrete reduction residual of `factor.neg` from the residual
of `factor`.  The construction recollects the finite atomic sign-order
correction and sharply routes the inverted parent residual through the
inverse atomic packet.
-/
noncomputable def neg_of_recollection
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
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (recollection :
      TSRecollb
        (n := n) factor) :
    TSRecollb
      (n := n) factor.neg := by
  let correction :=
    factory.basicNegRecollection hn hH sharp
      nextNormalizer factor hfactorWeight hfactorTruncated
  let inverseResidual :
      TSRecol
        (n := n) (lowerWeight := lowerWeight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactora.inverseList
          (basicRawSource factor)) :=
    {
      higherSource := SPFactora.inverseList recollection.higherSource
      higher_source_truncated :=
        SPFactora.truncated_inverse_list
          recollection.higher_source_truncated
      higher_weight_least :=
        SPFactora.least_inverse_list
          (by
            intro x hx
            simpa only [hfactorWeight] using
              recollection.higher_least_succ x hx)
      list_higher_raw := by
        intro q
        rw [SPFactora.list_eval_inverse,
          SPFactora.list_eval_inverse,
          recollection.list_higher_raw]
    }
  let conjugated :=
    factory.conjugated_sharp_normalizer sharp
      (SPFactora.inverseList (basicReductionFactors factor))
      (SPFactora.inverseList
        (basicRawSource factor))
      inverseResidual.higherSource
      (fun x hx =>
        (basic_reduction_factors factor hx).trans
          hfactorWeight)
      (SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactorTruncated))
      inverseResidual.higher_source_truncated
      inverseResidual.higher_weight_least
      inverseResidual.list_higher_raw
  exact
    {
      higherSource := correction.higherSource ++ conjugated.higherSource
      higher_source_truncated := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact correction.higher_source_truncated x hx
        · exact conjugated.higher_source_truncated x hx
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simpa only [SPFactora.word_neg, hfactorWeight] using
            correction.higher_weight_least x hx
        · simpa only [SPFactora.word_neg, hfactorWeight] using
            conjugated.higher_least_succ x hx
      list_higher_raw := by
        intro q
        dsimp [correction, conjugated, inverseResidual]
        rw [SPFactora.listEval_append,
          correction.list_higher_raw,
          conjugated.list_conjugated_raw,
          SPFactora.conjugated_raw_source,
          basicReductionNeg,
          SPFactora.listEval_append,
          SPFactora.list_eval_inverse,
          SPFactora.list_eval_inverse,
          SPFactora.list_eval_inverse,
          reduction_raw_source,
          reduction_raw_source,
          SPFactora.eval_neg]
        group
    }

end
  TSRecollb

end TCTex
end Submission

-- Merged from ReductionSelfTree.lean

/-!
# Concrete Hall-power reduction residuals for expanded self-brackets

If a symbolic factor expands to a Hall-tree self-bracket, both its explicit
atomic reduction packet and its symbolic value are trivial.  Its true
concrete reduction residual therefore recollects to the empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/-- The explicit packet of an expanded Hall-tree self-bracket is trivial. -/
theorem reduction_tree_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = HallTree.commutator child child)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) = 1 := by
  rw [list_basic_factors, htree]
  exact
    congrArg
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (HallTree.basic_scaled_self
        child (factor.exponent q))

/-- The true reduction residual of an expanded Hall-tree self-bracket is trivial. -/
theorem
    raw_tree_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = HallTree.commutator child child)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_tree_self
      factor child htree q]
  simp only [inv_one, one_mul]
  unfold SPFactora.eval SPFactora.wordValue
  rw [← lower_truncation_tree factor.word]
  rw [htree]
  simp [CWord.eval_commutator]

end HEWord

namespace
  TSRecollb

open HEWord

/-- An expanded Hall-tree self-bracket has an empty true residual recollection. -/
noncomputable def tree_commutator_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : HEWord.tree factor.word =
      HallTree.commutator child child) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (raw_tree_self
        factor child htree q).symm

end
  TSRecollb
end TCTex
end Submission

-- Merged from ReductionSwapTree.lean

/-!
# Concrete Hall-power reduction residuals for reversed basic brackets

If swapping the children of an expanded Hall-tree bracket makes it basic,
the explicit Hall-tree packet evaluates literally to the original reversed
bracket.  Its true concrete reduction residual therefore recollects to the
empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
For a factor whose expanded tree is a reversed basic bracket, the explicit
atomic Hall-tree reduction packet evaluates literally to the original factor.
-/
theorem reduction_tree_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      factor.eval q := by
  rw [list_basic_factors]
  rw [htree,
    HallTree.basic_scaled_swap
      left right hswapBasic]
  rw [map_zpow]
  unfold SPFactora.eval SPFactora.wordValue
  rw [← lower_truncation_tree factor.word]
  rw [htree]

/-- The true reduction residual of a reversed basic bracket is trivial. -/
theorem
    raw_tree_swap
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_tree_swap
      factor left right htree hswapBasic q]
  simp

end HEWord

namespace
  TSRecollb

open HEWord

/-- A reversed basic bracket has an empty true residual recollection. -/
noncomputable def tree_swap_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : HEWord.tree factor.word =
      .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (raw_tree_swap
        factor left right htree hswapBasic q).symm

end
  TSRecollb
end TCTex
end Submission

-- Merged from ReductionWeightOne.lean

/-!
# Concrete Hall-tree residual reduction in weight one

A symbolic Hall-power word of ordinary weight one is one address.  For the
canonical concrete Hall family, its expanded Hall tree is therefore basic.
Low-weight coordinate exactness shows that the explicit atomic reduction
packet evaluates literally to the original factor.  Both concrete residual
sources consequently recollect to the empty list.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

open CCExpans

/--
For a weight-one factor, the explicit atomic Hall-tree reduction packet
evaluates literally to the original symbolic factor.
-/
theorem list_reduction_factors
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      factor.eval q := by
  have htreeBasic : (tree factor.word).IsBasic := by
    obtain ⟨address, hword⟩ :=
      CWord.atom_weight_one
        PEAddres.weight PEAddres.weight_pos
          factor.word hfactorWeight
    rw [hword]
    simp
  have htreeWeight : (tree factor.word).weight ≤ 3 := by
    rw [tree_weight, hfactorWeight]
    omega
  rw [list_basic_factors]
  rw [
    HallTree.basic_scaled_zpow
      (tree factor.word) htreeBasic htreeWeight]
  rw [map_zpow, lower_truncation_tree]
  rfl

/--
For a weight-one factor, dividing by its explicit atomic reduction packet has
trivial value.
-/
theorem
    reduction_raw_weight
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    list_reduction_factors
      factor hfactorWeight q]
  simp

/--
For a weight-one factor, the comparison between the explicit atomic packet
and the semantic active Hall block also has trivial value.
-/
theorem
    reduction_comparison_raw
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (comparisonRawSource
          hn hH factor 1) = 1 := by
  rw [comparison_raw_source,
    list_reduction_factors
      factor hfactorWeight q]
  have hactive :
      SPFactora.listEval (n := n) q
          ((factor.normalCoordinateExpansions hn
            (concreteBasicCommutators.{u} d) hH).weightFactors 1) =
        factor.eval q := by
    simpa only [
      CCExpans.activeNormalValue]
      using
        active_block_value
          hn (concreteBasicCommutators.{u} d) hH factor hfactorWeight q
  rw [hactive]
  simp

end HEWord

namespace
  TSRecollb

open HEWord

/--
A weight-one explicit Hall-tree residual recollects to the empty higher
source.
-/
noncomputable def of_weight_one
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (reduction_raw_weight
        factor hfactorWeight q).symm

end
  TSRecollb

namespace
  TCRecoll

open HEWord

/--
A weight-one concrete-to-semantic comparison residual recollects to the empty
higher source.
-/
noncomputable def of_weight_one
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1) :
    TCRecoll
      (lowerWeight := 1) hn hH factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (reduction_comparison_raw
        hn hH factor hfactorWeight q).symm

end
  TCRecoll
end TCTex
end Submission

-- Merged from ReductionReversedBasic.lean

/-!
# Concrete Hall-power reduction residuals for reversed basic brackets

If swapping the two children of an expanded Hall-tree bracket makes it basic,
all-weight PBW uniqueness and skew-symmetry make its explicit reduction packet
exact.  The corresponding true reduction residual recollects to the empty
higher source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
A symbolic word is reversed-basic when it is a bracket whose swapped
expanded Hall-tree orientation is basic.
-/
def IsReversedBasic
    {d : ℕ}
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))) :
    Prop :=
  ∃ left right, word = .commutator right left ∧
    (HallTree.commutator (tree left) (tree right)).IsBasic

/--
The explicit packet of a reversed basic expanded bracket evaluates literally
to the original symbolic factor.
-/
theorem
    reduction_reversed_tree
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator (tree left) (tree right)).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      factor.eval q := by
  rw [list_basic_factors]
  rw [show
      tree factor.word = HallTree.commutator (tree right) (tree left) by
        rw [hword]
        rfl]
  rw [
    HallTree.basic_scaled_swap
      (tree left) (tree right) hswapBasic]
  rw [map_zpow]
  rw [show
      HallTree.commutator (tree right) (tree left) = tree factor.word by
        rw [hword]
        rfl]
  rw [lower_truncation_tree]
  rfl

/--
The true reduction residual of a reversed basic expanded bracket is trivial.
-/
theorem
    raw_reversed_tree
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator (tree left) (tree right)).IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_reversed_tree
      factor left right hword hswapBasic q]
  simp

end HEWord

namespace
  TSRecollb

open HEWord

/-- A reversed basic expanded bracket has an empty true residual recollection. -/
noncomputable def reversed_tree_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic :
      (HallTree.commutator
        (HEWord.tree left)
        (HEWord.tree right)).IsBasic) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (raw_reversed_tree
        factor left right hword hswapBasic q).symm

/-- A reversed-basic symbolic word has an empty true residual recollection. -/
noncomputable def reversed_basic
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hreversed : HEWord.IsReversedBasic factor.word) :
    TSRecollb
      (n := n) factor :=
  let left := Classical.choose hreversed
  let right := Classical.choose (Classical.choose_spec hreversed)
  let hproperties :=
    Classical.choose_spec (Classical.choose_spec hreversed)
  reversed_tree_basic factor left right hproperties.1 hproperties.2

end
  TSRecollb
end TCTex
end Submission

-- Merged from ReductionSelfCommutator.lean

/-!
# Concrete Hall-power reduction residuals for self-commutators

The expanded Hall tree of a symbolic self-commutator has zero
associated-graded class.  Its explicit reduction packet and its own symbolic
value therefore both evaluate trivially, so the true reduction residual
recollects to the empty higher source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/-- The explicit packet of a symbolic self-commutator evaluates trivially. -/
theorem reduction_factors_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) = 1 := by
  rw [list_basic_factors]
  rw [show
      tree factor.word = .commutator (tree word) (tree word) by
        rw [hword]
        rfl]
  exact
    congrArg
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (HallTree.basic_scaled_self
        (tree word) (factor.exponent q))

/-- The true reduction residual of a symbolic self-commutator is trivial. -/
theorem
    reduction_raw_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_factors_self
      factor word hword q]
  simp [SPFactora.eval, SPFactora.wordValue,
    hword]

end HEWord

namespace
  TSRecollb

open HEWord

/-- A symbolic self-commutator has an empty true residual recollection. -/
noncomputable def word_commutator_self
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word) :
    TSRecollb
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa [SPFactora.listEval] using
      (reduction_raw_self
        factor word hword q).symm

end
  TSRecollb
end TCTex
end Submission

-- Merged from ReductionJacobiContinuation.lean

/-!
# Concrete Jacobi continuation recollection

The atomic Jacobi correction is only the first part of a true concrete
factor residual.  This file packages the remaining continuation as an
explicit boundary and composes any recollection of that continuation with
the supported atomic correction route.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u

/--
Semantic recollection data for the continuation left after peeling a Jacobi
atomic correction from a true concrete factor residual.
-/
structure SymbolicContinuationRecollection
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
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (jacobiContinuationRaw factor left middle right hword)

namespace
  TSRecollb

/--
Combine a strictly higher atomic Jacobi correction with a strictly higher
recollection of the remaining continuation.
-/
noncomputable def jacobi_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (jacobiHigherSource :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hjacobiTruncated :
      SPFactora.IsTruncated n jacobiHigherSource)
    (hjacobiSupported :
      SPFactora.WordWeightLeast
        (factor.word.weight PEAddres.weight + 1)
        jacobiHigherSource)
    (hjacobiEval :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q jacobiHigherSource =
          SPFactora.listEval q
            (jacobiReductionSource factor left middle right hword))
    (continuation :
      SymbolicContinuationRecollection
        (n := n) factor left middle right hword) :
    TSRecollb
      (n := n) factor where
  higherSource := jacobiHigherSource ++ continuation.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiTruncated x hx
    · exact continuation.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hjacobiSupported x hx
    · exact continuation.higher_least_succ x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append, hjacobiEval q,
      continuation.list_higher_raw q,
      jacobi_reduction_continuation]

/--
Use the supported correction factory for the atomic Jacobi packet, leaving
only its explicit continuation recollection as an input.
-/
noncomputable def of_jacobiReduction
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
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (continuation :
      SymbolicContinuationRecollection
        (n := n) factor left middle right hword) :
    TSRecollb
      (n := n) factor := by
  let jacobi :=
    factory.higher_jacobi_raw hn hH sharp
      nextNormalizer factor left middle right hword hfactorWeight
        hfactorTruncated
  let jacobiHigherSource := Classical.choose jacobi
  have hjacobiTruncated := (Classical.choose_spec jacobi).1
  have hjacobiSupported := (Classical.choose_spec jacobi).2.1
  have hjacobiEval := (Classical.choose_spec jacobi).2.2
  exact
    jacobi_raw_source factor left middle right hword
      jacobiHigherSource hjacobiTruncated
        (by simpa only [hfactorWeight] using hjacobiSupported)
          hjacobiEval continuation

/--
Compile the Hall-Petresco packet and a family of strictly deeper normalizers
into the data needed to lift one syntactic Jacobi residual.
-/
noncomputable def jacobi_normalizer_above
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 1 ≤ inputWeight)
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
      factor.word.weight PEAddres.weight < n)
    (continuation :
      SymbolicContinuationRecollection
        (n := n) factor left middle right hword) :
    TSRecollb
      (n := n) factor :=
  of_jacobiReduction hn hH
    ((packet.powerSupportedFactory
      hinputWeight lowerWeight).correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    (normalizerAbove (lowerWeight + 1) (by omega))
    factor left middle right hword hfactorWeight hfactorTruncated continuation

end
  TSRecollb

/--
A cutoff packet and continuation recollections for syntactically exposed
Jacobi brackets.  Compressed Hall addresses are deliberately left to a
separate expansion boundary.
-/
structure
    TSContin
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
  jacobiContinuation :
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
              SymbolicContinuationRecollection
                (n := n) factor left middle right hword

namespace
  TSContin

open
  TSRecollb

/--
Lift one syntactically exposed Jacobi factor using only normalizers at
strictly larger support bounds.
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
      TSContin.{u}
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
  jacobi_normalizer_above hn hH builder.packet hinputWeight
    normalizerAbove factor left middle right hword hfactorWeight hfactorTruncated
      (builder.jacobiContinuation lowerWeight hnonterminal factor left middle
        right hword hfactorWeight hfactorTruncated)

/--
Expanded Jacobi roots with a nonbasic inner bracket automa expose the
syntactic decomposition consumed by `jacobiResidual`.
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
      TSContin.{u}
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
  let decomposition :=
    syntacticTreeNonbasic
      factor.word left middle right htree houterNonbasic hinnerNonbasic
  builder.jacobiResidual hinputWeight lowerWeight hnonterminal normalizerAbove
    factor decomposition.left decomposition.middle decomposition.right
      decomposition.word_eq hfactorWeight hfactorTruncated

end
  TSContin
end TCTex
end Submission
