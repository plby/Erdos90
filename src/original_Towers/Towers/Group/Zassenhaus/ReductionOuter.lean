import Towers.Group.HallBasic.OuterValueScaling
import Towers.Group.Zassenhaus.BasicTreeReduction
import Towers.Group.Zassenhaus.SemanticallyHigherRecollection
import Towers.Group.Zassenhaus.ReductionPoweredBridge
import Towers.Group.Zassenhaus.SourceRecollectionComposition
import Towers.Group.Zassenhaus.SourceRecollectionCongruence
import Towers.Group.Zassenhaus.RankedTaskSource
import Towers.Group.Zassenhaus.FormulaTotalSupport
import Towers.Group.Zassenhaus.ResidualSingletonRecollection
import Towers.Group.Zassenhaus.Packet
import Towers.Group.Zassenhaus.AtomicOrNormalization
import Towers.Group.Zassenhaus.ConcreteAutomaticComparison


-- Merged from ReductionOuterChildren.lean

/-!
# Symbolic full outer children from inner Hall reduction

Reducing an inner expanded Hall tree and then retaining the fixed outer right
word gives a finite packet of full-weight symbolic children.  Each child keeps
the original factor's bounded repeated-power recipe and scales only its integer
coefficient by the corresponding inner Hall coordinate.

This is the recipe-correct symbolic form of the classical Hall step: replace
`[inner, right]` by the ordered packet `[basic_i, right]`.  The quotient of the
packet from the original factor evaluates one lower-central stratum deeper.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/-- Multiply only the signed integer coefficient of a symbolic factor. -/
def coefficientScale
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (coefficient : ℤ) :
    SPFactora H inputWeight where
  word := factor.word
  coefficient := coefficient * factor.coefficient
  recipe := factor.recipe

@[simp]
theorem word_coefficientScale
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (coefficient : ℤ) :
    (factor.coefficientScale coefficient).word = factor.word :=
  rfl

@[simp]
theorem exponent_coefficientScale
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (coefficient : ℤ)
    (q : ℕ) :
    (factor.coefficientScale coefficient).exponent q =
      coefficient * factor.exponent q := by
  simp [coefficientScale, exponent, mul_assoc]

end SPFactora

namespace HEWord

/--
One full outer child `[basic_i, right]`, carrying the original full-weight
recipe and scaled by the corresponding coordinate of the inner tree.
-/
noncomputable def innerOuterFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight :=
  (factor.reword
      (.commutator (.atom (basicReductionAddress i)) rightWord)
      (by
        rw [hword]
        simp only [CWord.weight_commutator, CWord.weight_atom,
          basic_reduction_address, tree_weight]))
    |>.coefficientScale (HallTree.basicReductionCoordinates (tree innerWord) i)

@[simp]
theorem inner_reduction_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    (innerOuterFactor factor innerWord rightWord hword i).word =
      .commutator (.atom (basicReductionAddress i)) rightWord := by
  simp [innerOuterFactor]

@[simp]
theorem exponent_inner_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight)
    (q : ℕ) :
    (innerOuterFactor factor innerWord rightWord hword i).exponent q =
      HallTree.basicReductionCoordinates (tree innerWord) i *
        factor.exponent q := by
  simp [innerOuterFactor]

@[simp]
theorem inner_outer_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    (innerOuterFactor factor innerWord rightWord hword i).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [inner_reduction_factor, hword]
  simp only [CWord.weight_commutator, CWord.weight_atom,
    basic_reduction_address, tree_weight]

/-- Ordered full-weight outer children emitted by inner Hall reduction. -/
noncomputable def innerOuterFactors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j).map
    (innerOuterFactor factor innerWord rightWord hword)

/-- Membership in the outer-child packet preserves the original full weight. -/
theorem inner_outer_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ innerOuterFactors factor innerWord rightWord hword) :
    x.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [innerOuterFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact inner_outer_factor factor innerWord rightWord hword i

/-- Full outer children inherit physical truncation from their parent factor. -/
theorem truncated_inner_factors
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerOuterFactors factor innerWord rightWord hword) := by
  intro x hx
  rw [inner_outer_factors
    factor innerWord rightWord hword hx]
  exact hfactor

/-- Every full outer child remains supported in the parent factor's stratum. -/
theorem least_inner_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerOuterFactors factor innerWord rightWord hword) := by
  intro x hx
  rw [inner_outer_factors
    factor innerWord rightWord hword hx]

/--
Truncating one full outer-child representative gives evaluation of its
recipe-correct symbolic word.
-/
@[simp]
theorem
    truncation_indexed_rep
    {d n : ℕ}
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.indexedInnerRep
          (tree innerWord) (tree rightWord) i) =
      (CWord.commutator
        (.atom (basicReductionAddress i)) rightWord).eval
        PEAddres.freeLowerTruncation := by
  rw [← lower_truncation_tree
    (CWord.commutator (.atom (basicReductionAddress i)) rightWord)]
  congr 1
  simp only [HallTree.indexedInnerRep,
    HallTree.coe_rep_weight, tree_commutator, tree_atom,
    basicReductionAddress, concreteBasicTree]

/-- Evaluation of one recipe-correct full outer child. -/
@[simp]
theorem inner_reduction_eval
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight)
    (q : ℕ) :
    (innerOuterFactor factor innerWord rightWord hword i).eval
        (n := n) q =
      ((CWord.commutator
          (.atom (basicReductionAddress i)) rightWord).eval
          PEAddres.freeLowerTruncation) ^
        (HallTree.basicReductionCoordinates (tree innerWord) i *
          factor.exponent q) := by
  rw [SPFactora.eval, exponent_inner_factor]
  rfl

/--
Truncation carries the ordered HallBasic outer-child product to the ordered
symbolic outer-child value packet.
-/
theorem truncation_inner_scaled
    {d n : ℕ}
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (z : ℤ) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.innerOuterScaled
          (tree innerWord) (tree rightWord) z) =
      ((Finset.univ.sort
          fun i j :
            HallTree.BasicIndex
              (α := FreeGenerator.{u} d) (tree innerWord).weight =>
            i ≤ j).map
        fun i =>
          ((CWord.commutator
              (.atom (basicReductionAddress i)) rightWord).eval
              PEAddres.freeLowerTruncation) ^
            (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod := by
  simp only [HallTree.innerOuterScaled,
    HallTree.innerScaledTerm]
  let indices :=
    Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j
  change
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (((indices.map fun i =>
          HallTree.indexedInnerRep
              (tree innerWord) (tree rightWord) i ^
            (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod :
          Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
            ((tree innerWord).weight + (tree rightWord).weight - 1)) :
          FreeGroup (FreeGenerator.{u} d)) =
      (indices.map fun i =>
        ((CWord.commutator
            (.atom (basicReductionAddress i)) rightWord).eval
            PEAddres.freeLowerTruncation) ^
          (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod
  induction indices with
  | nil =>
      simp
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons]
      change
        lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
            ((HallTree.indexedInnerRep
                (tree innerWord) (tree rightWord) i :
                FreeGroup (FreeGenerator.{u} d)) ^
              (HallTree.basicReductionCoordinates (tree innerWord) i * z) *
              (((indices.map fun j =>
                HallTree.indexedInnerRep
                    (tree innerWord) (tree rightWord) j ^
                  (HallTree.basicReductionCoordinates (tree innerWord) j * z)).prod :
                Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
                  ((tree innerWord).weight + (tree rightWord).weight - 1)) :
                FreeGroup (FreeGenerator.{u} d))) =
          ((CWord.commutator
              (.atom (basicReductionAddress i)) rightWord).eval
                PEAddres.freeLowerTruncation) ^
              (HallTree.basicReductionCoordinates (tree innerWord) i * z) *
            (indices.map fun j =>
              ((CWord.commutator
                  (.atom (basicReductionAddress j)) rightWord).eval
                  PEAddres.freeLowerTruncation) ^
                (HallTree.basicReductionCoordinates (tree innerWord) j * z)).prod
      rw [map_mul, map_zpow,
        truncation_indexed_rep,
        ih]

/--
The symbolic outer-child packet evaluates to the truncated HallBasic scaled
outer-child product.
-/
theorem inner_reduction_factors
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerOuterFactors factor innerWord rightWord hword) =
      lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.innerOuterScaled
          (tree innerWord) (tree rightWord) (factor.exponent q)) := by
  rw [truncation_inner_scaled]
  unfold SPFactora.listEval innerOuterFactors
  rw [List.map_map]
  induction
      (Finset.univ.sort
        fun i j :
          HallTree.BasicIndex
            (α := FreeGenerator.{u} d) (tree innerWord).weight =>
          i ≤ j) with
  | nil =>
      rfl
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [inner_reduction_eval, ih]

/--
Concrete symbolic source for the higher outer-child residual: invert the
full-weight child packet and append the original parent factor.
-/
noncomputable def innerRawSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    [factor]

/-- The raw outer-child residual source inherits physical truncation. -/
theorem truncated_inner_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerRawSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_inner_factors
          factor innerWord rightWord hword hfactor) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactor

/-- The raw outer-child residual source remains physically in the parent stratum. -/
theorem outerResidualSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerRawSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [SPFactora.inverseList] at hx
    rcases List.mem_map.mp hx with ⟨child, hchild, rfl⟩
    rw [SPFactora.word_neg]
    exact
      least_inner_factors
        factor innerWord rightWord hword child (by simpa using hchild)
  · simp only [List.mem_singleton] at hx
    subst x
    exact Nat.le_refl _

/-- The raw source evaluates to child-packet division by the parent factor. -/
theorem inner_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerRawSource
          factor innerWord rightWord hword) =
      (SPFactora.listEval q
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          factor.eval q := by
  simp [innerRawSource,
    SPFactora.list_eval_inverse]

/--
Dividing the original symbolic factor by the full-weight outer-child packet
leaves a value one lower-central stratum deeper.
-/
theorem
    inner_inv_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    (SPFactora.listEval (n := n) q
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          factor.eval q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hfree :=
    HallTree.inner_scaled_zpow
      (tree innerWord) (tree rightWord) (factor.exponent q)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword]
          simpa only [tree_weight, HallTree.weight_commutator,
            CWord.weight_commutator] using hfree))
  rw [inner_reduction_factors]
  rw [map_mul, map_inv, map_zpow,
    ← tree_commutator innerWord rightWord,
    lower_truncation_tree] at hmap
  simpa only [SPFactora.eval,
    SPFactora.wordValue, hword] using hmap

/-- The concrete raw outer-child residual evaluates one stratum deeper. -/
theorem
    inner_reduction_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerRawSource
          factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [inner_raw_source]
  exact
    inner_inv_series
      factor innerWord rightWord hword q

end HEWord
end TCTex
end Towers

-- Merged from ReductionOuterChildrenRecollection.lean

/-!
# Recollecting recipe-correct inner-reduction outer children

The full-weight outer-child packet has a physically current-stratum residual
whose value lies one lower-central stratum deeper.  A semantic coordinate
normalizer therefore recollects that residual into a source supported in the
next stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSNormalb

/--
Recollect the recipe-correct full outer-child residual into the next support
stratum.
-/
noncomputable def
    recollection_inner_raw
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteBasicCommutators.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
    (HEWord.innerRawSource
      factor innerWord rightWord hword)
    hlowerWeightPos hlowerWeightTruncated
    (HEWord.truncated_inner_source
      factor innerWord rightWord hword (by
        rw [hfactorWeight]
        exact hlowerWeightTruncated))
    (by
      rw [← hfactorWeight]
      exact
        HEWord.outerResidualSource
          factor innerWord rightWord hword)
    (fun q => by
      rw [← hfactorWeight]
      exact
        HEWord.inner_reduction_series
          factor innerWord rightWord hword q)

end TSNormalb
end TCTex
end Towers

-- Merged from ReductionOuterPoweredResidualComposition.lean

/-!
# Factoring outer residuals through powered-commutator bridges

The recipe-correct outer-child residual compares the Hall-reduced child packet
with the original powered parent bracket.  Insert the temporary Hall-Petresco
packet for `[inner ^ e, right]` between them.  The residual then splits into:

* comparison of the recipe-correct Hall children with that temporary packet;
* the powered-commutator bridge quotient from the temporary packet to the
  original parent.

This file records the exact raw-source factorization and composes semantic
recollections of its two pieces.  It is intentionally not imported by the
existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement
open HEWord
open IPBridge

namespace HEWord

/--
Compare recipe-correct full-weight Hall children with the temporary
Hall-Petresco packet collecting `[inner ^ e, right]`.
-/
noncomputable def innerPoweredComparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    (correctionPacket packet hinputWeight factor innerWord rightWord
      hrecipe).factors

/-- Evaluation of the powered comparison is child-packet division. -/
theorem powered_comparison_source
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredComparison packet hinputWeight
          factor innerWord rightWord hword hrecipe) =
      (SPFactora.listEval q
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          ⁅innerWord.eval
                (PEAddres.freeLowerTruncation
                  (n := n)) ^
              factor.exponent q,
            rightWord.eval
              (PEAddres.freeLowerTruncation
                (n := n))⁆ := by
  rw [innerPoweredComparison,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    list_packet_factors]

/--
Insert the temporary powered-commutator packet between Hall children and the
original parent factor.
-/
noncomputable def innerPoweredDecomposition
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  innerPoweredComparison packet hinputWeight factor
      innerWord rightWord hword hrecipe ++
    residualRawSource packet hinputWeight factor innerWord rightWord hrecipe

/-- Evaluation of the powered decomposition recovers the outer residual. -/
theorem
    inner_powered_decomposition
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredDecomposition packet
          hinputWeight factor innerWord rightWord hword hrecipe) =
      SPFactora.listEval q
        (innerRawSource
          factor innerWord rightWord hword) := by
  rw [innerPoweredDecomposition,
    SPFactora.listEval_append,
    powered_comparison_source,
    list_raw_source,
    inner_raw_source]
  group

end HEWord

namespace TSRecol

/--
Compose recollections of the powered comparison and powered-commutator bridge
into a recollection of the original outer residual.
-/
noncomputable def
    inner_powered_pieces
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerPoweredComparison
          packet hinputWeight factor innerWord rightWord hword hrecipe))
    (bridge :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  (comparison.append bridge).of_list_eq fun q => by
    simpa only [
      HEWord.innerPoweredDecomposition]
      using
        inner_powered_decomposition
          packet hinputWeight factor innerWord rightWord hword hrecipe q

/--
At the first nested-commutator cutoff, the powered bridge vanishes.  A
recollection of the Hall-children-to-temporary-packet comparison therefore
already recollects the original outer residual.
-/
noncomputable def
    inner_powered_comparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerPoweredComparison
          packet hinputWeight factor innerWord rightWord hword hrecipe)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  inner_powered_pieces packet
    hinputWeight factor innerWord rightWord hword hrecipe comparison
      (source_recollection_cutoff packet hinputWeight factor innerWord
        rightWord hword hrecipe hcutoff)

end TSRecol

end TCTex
end Towers

-- Merged from ReductionOuterRankedChildren.lean

/-!
# Ranked recipe-correct children for inner Hall reduction under an outer bracket

Reducing an inner Hall tree under a fixed outer-right word yields full-weight
symbolic children.  Each child is indexed by one Hall-basic inner
representative, so the classical reverse Hall-bracket rank defect attaches
directly to the finite child packet.

The resulting ranked source preserves ordinary symbolic weight and decreases
the secondary Hall-rank component.  It is the fixed-total-weight branch needed
by a lexicographic Hall collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CIChildr

/-- Attach the classical Hall-bracket rank defect to every full outer child. -/
noncomputable def rankedTasks
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d)) :
    List
      (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j).map fun i =>
    (innerOuterFactor factor innerWord rightWord hword i,
      HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged)

/-- Membership in the ranked child list exposes its Hall-basic inner index. -/
theorem index_ranked_tasks
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask : task ∈ rankedTasks factor innerWord rightWord hword unchanged) :
    ∃ i :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight,
      task =
        (innerOuterFactor factor innerWord rightWord hword i,
          HallTree.bracketRankDefect
            ((tree innerWord).weight + unchanged.weight)
            (HallTree.indexedBasicTree i) unchanged) := by
  rw [rankedTasks] at htask
  rcases List.mem_map.mp htask with ⟨i, _hi, htask⟩
  exact ⟨i, htask.symm⟩

/--
Every Hall-basic inner representative paired with the unchanged outer tree
has smaller bracket-rank defect than the original pair.
-/
theorem bracket_rank_defect
    {d : ℕ}
    (innerWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged <
      HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight := by
  apply HallTree.bracket_defect_both hRightLeft
  · apply
      HallTree.weight_add_left added originalRight
        (HallTree.indexedBasicTree i)
    rw [HallTree.indexed_tree_weight, hinnerTree]
    rfl
  · exact hRightUnchanged
  · exact HallTree.indexed_tree i
  · exact hunchangedBasic
  · rw [HallTree.indexed_tree_weight]
    exact Nat.le_add_right _ _
  · exact Nat.le_add_left _ _

/-- Every recipe-correct full outer child strictly descends at fixed weight. -/
theorem ranked_descends_tasks
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask : task ∈ rankedTasks factor innerWord rightWord hword unchanged) :
    SPFactora.HallRankedDescends n task.1 task.2 factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) := by
  rcases
      index_ranked_tasks
        factor innerWord rightWord hword unchanged htask with
    ⟨i, rfl⟩
  apply
    SPFactora.ranked_descends_defect
  · exact
      inner_outer_factor
        factor innerWord rightWord hword i
  · exact
      bracket_rank_defect innerWord added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic i

/-- Package the recipe-correct full outer children as strict Hall-ranked tasks. -/
noncomputable def rankedTaskSource
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.RCSrc
      (n := n) factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  tasks := rankedTasks factor innerWord rightWord hword unchanged
  tasks_descend := by
    intro task htask
    exact
      ranked_descends_tasks factor innerWord rightWord hword
        added originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic htask

/-- The scheduler-facing ranked source retains the concrete ranked task list. -/
@[simp]
theorem tasks_ranked_task
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic).tasks =
      rankedTasks factor innerWord rightWord hword unchanged :=
  rfl

/-- Forgetting task ranks recovers the recipe-correct full outer-child packet. -/
@[simp]
theorem factor_ranked_task
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    (rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic).factorSource =
      innerOuterFactors factor innerWord rightWord hword := by
  simp [rankedTaskSource,
    SPFactora.RCSrc.factorSource,
    rankedTasks, innerOuterFactors, List.map_map, Function.comp_def]

/-- The ranked factor source evaluates to the recipe-correct child packet. -/
theorem list_ranked_task
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (rankedTaskSource (n := n) factor innerWord rightWord hword added originalRight
          unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
            hunchangedBasic).factorSource =
      SPFactora.listEval q
        (innerOuterFactors factor innerWord rightWord hword) := by
  rw [factor_ranked_task]

/-- The ranked full outer-child source inherits parent truncation. -/
theorem truncated_ranked_task
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (rankedTaskSource (n := n) factor innerWord rightWord hword added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact
    truncated_inner_factors
      factor innerWord rightWord hword hfactorTruncated

/-- The ranked full outer-child source stays in the parent's support stratum. -/
theorem least_ranked_task
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (rankedTaskSource (n := n) factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic).factorSource := by
  rw [factor_ranked_task]
  exact
    least_inner_factors
      factor innerWord rightWord hword

end CIChildr
end TCTex
end Towers

-- Merged from ReductionOuterResidualComposition.lean

/-!
# Composing recipe-correct inner-reduction residuals

Reducing the inner word of a symbolic outer bracket produces a full-weight
child packet.  The true concrete residual of the parent splits into two
semantically deeper sources:

* comparison of the parent's canonical atomic packet with the full-weight
  child packet;
* comparison of the full-weight child packet with the parent.

This file records that exact factorization and packages recollections of the
two pieces into a concrete basic-reduction residual recollection for the
parent.  It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace HEWord

/--
Compare the parent's canonical atomic Hall packet with the recipe-correct
full-weight children obtained by reducing its inner word.
-/
noncomputable def innerComparisonSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor) ++
    innerOuterFactors factor innerWord rightWord hword

/-- The atomic-to-child comparison inherits parent truncation. -/
theorem truncated_inner_comparison
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerComparisonSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactor x hx

/-- The atomic-to-child comparison stays physically in the parent stratum. -/
theorem least_inner_comparison
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerComparisonSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (least_reduction_factors factor) x hx
  · exact
      least_inner_factors
        factor innerWord rightWord hword x hx

/-- The atomic-to-child source evaluates to canonical-packet division. -/
theorem inner_comparison_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerComparisonSource
          factor innerWord rightWord hword) =
      (SPFactora.listEval q
        (basicReductionFactors factor))⁻¹ *
          SPFactora.listEval q
            (innerOuterFactors factor innerWord rightWord hword) := by
  simp [innerComparisonSource,
    SPFactora.list_eval_inverse]

/--
Canonical atomic reduction and recipe-correct inner reduction agree in the
associated graded layer, so their comparison evaluates one stratum deeper.
-/
theorem
    inner_comparison_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerComparisonSource
          factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [inner_comparison_source]
  have hatomic :=
    reduction_inv_series
      (n := n) factor q
  have hchildren :=
    inner_inv_series
      (n := n) factor innerWord rightWord hword q
  convert Subgroup.mul_mem _ hatomic (Subgroup.inv_mem _ hchildren) using 1 ;
    group

/--
The true parent residual is exactly the product of atomic-to-child comparison
and child-to-parent comparison sources.
-/
noncomputable def innerDecompositionSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  innerComparisonSource
      factor innerWord rightWord hword ++
    innerRawSource
      factor innerWord rightWord hword

/-- Evaluation of the residual decomposition recovers the true parent residual. -/
theorem
    inner_reduction_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerDecompositionSource
          factor innerWord rightWord hword) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  rw [innerDecompositionSource,
    SPFactora.listEval_append,
    inner_comparison_source,
    inner_raw_source,
    reduction_raw_source]
  group

end HEWord

namespace
  TSRecollb

/--
Compose next-stratum recollections of the two inner-reduction pieces into a
true concrete basic-reduction residual recollection for the parent factor.
-/
noncomputable def inner_outer
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerComparisonSource
          factor innerWord rightWord hword))
    (outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerRawSource
          factor innerWord rightWord hword)) :
    TSRecollb
      (n := n) factor where
  higherSource := comparison.higherSource ++ outer.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact comparison.higher_source_truncated x hx
    · exact outer.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact comparison.higher_weight_least x hx
    · exact outer.higher_weight_least x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      comparison.list_higher_raw,
      outer.list_higher_raw,
      ←
        HEWord.inner_reduction_source
          factor innerWord rightWord hword q,
      HEWord.innerDecompositionSource,
      SPFactora.listEval_append]

end
  TSRecollb

end TCTex
end Towers

-- Merged from ReductionOuterPoweredComparisonSupport.lean

/-!
# Support of powered outer-reduction comparisons

The powered outer comparison divides the recipe-correct Hall-child packet by
the temporary Hall-Petresco packet collecting `[inner ^ e, right]`.  Both
terms are physically supported in the parent's full bracket weight, while
their quotient lies one lower-central layer deeper.

This file records those unconditional invariants for later non-circular
routing.  It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open HEWord
open IPBridge

namespace HEWord

/-- A truncated parent gives a physically truncated powered comparison source. -/
theorem truncated_powered_comparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerPoweredComparison packet hinputWeight
        factor innerWord rightWord hword hrecipe) := by
  intro x hx
  rw [innerPoweredComparison] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_inner_factors factor innerWord rightWord
          hword hfactorTruncated) x hx
  · exact
      (correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).word_weight_cutoff x hx

/-- Every powered comparison factor is supported at the parent bracket weight. -/
theorem least_powered_comparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerPoweredComparison packet hinputWeight
        factor innerWord rightWord hword hrecipe) := by
  intro x hx
  rw [innerPoweredComparison] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (least_inner_factors factor innerWord
          rightWord hword) x hx
  · have htotal :=
      packet.add_supported_factors
        hinputWeight
        (innerPowerFactor factor innerWord hrecipe)
        (rightUnitFactor (inputWeight := inputWeight) rightWord)
        (Nat.zero_le _) (Nat.zero_le _) hx
    simpa [hword, innerPowerFactor, rightUnitFactor] using htotal

/-- The powered comparison evaluates one lower-central layer above its parent. -/
theorem
    powered_comparison_series
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredComparison packet hinputWeight
          factor innerWord rightWord hword hrecipe) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight)
  let children :=
    SPFactora.listEval (n := n) q
      (innerOuterFactors factor innerWord rightWord hword)
  let temporary :=
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^
        factor.exponent q,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆
  have hchildren :
      children⁻¹ * (factor.eval (n := n) q) ∈ K := by
    exact
      inner_inv_series
        factor innerWord rightWord hword q
  have hpower :
      temporary * (factor.eval (n := n) q)⁻¹ ∈ K := by
    have hraw :=
      eval_zpow_series
        (n := n) innerWord rightWord (factor.exponent q)
    simpa [K, temporary, SPFactora.eval,
      SPFactora.wordValue, hword] using hraw
  rw [powered_comparison_source]
  change children⁻¹ * temporary ∈ K
  have hchildrenQuotient :
      QuotientGroup.mk' K children⁻¹ =
        QuotientGroup.mk' K (factor.eval (n := n) q)⁻¹ := by
    apply (mul_inv_quotient K).mp
    simpa only [inv_inv] using hchildren
  have hpowerQuotient :
      QuotientGroup.mk' K temporary =
        QuotientGroup.mk' K (factor.eval (n := n) q) :=
    (mul_inv_quotient K).mp hpower
  have htarget :
      children⁻¹ * (temporary⁻¹)⁻¹ ∈ K := by
    apply (mul_inv_quotient K).mpr
    simpa only [map_inv] using
      hchildrenQuotient.trans (congrArg Inv.inv hpowerQuotient.symm)
  simpa only [inv_inv] using htarget

/-- At the next-stratum endpoint, the powered comparison source is trivial. -/
theorem
    powered_comparison_n
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredComparison packet hinputWeight
          factor innerWord rightWord hword hrecipe) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (powered_comparison_series
      packet hinputWeight factor innerWord rightWord hword hrecipe q)

/--
At the next-stratum endpoint, the powered comparison recollects to the empty
higher source.
-/
def recollection_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerPoweredComparison packet hinputWeight
        factor innerWord rightWord hword hrecipe) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (powered_comparison_n
        packet hinputWeight factor innerWord rightWord hword hrecipe hcutoff
          q).symm

/--
A parent-stratum normalizer recollects the powered comparison one layer
higher.  This compatibility adapter isolates the current-stratum dependency
for later replacement by structural routing.
-/
noncomputable def source_recollection_normalizer
    {d n inputWeight : ℕ}
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
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerPoweredComparison packet hinputWeight
        factor innerWord rightWord hword hrecipe) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
      (innerPoweredComparison packet hinputWeight
        factor innerWord rightWord hword hrecipe)
      factor.word_weight_pos hfactorTruncated
      (truncated_powered_comparison packet
        hinputWeight factor innerWord rightWord hword hrecipe hfactorTruncated)
      (least_powered_comparison packet
        hinputWeight factor innerWord rightWord hword hrecipe)
      (powered_comparison_series
        packet hinputWeight factor innerWord rightWord hword hrecipe)

end HEWord

end TCTex
end Towers

-- Merged from ReductionOuterRankedResidualRecollection.lean

/-!
# Ranked residual recollections for full outer children

A Hall-ranked child packet rewrites one parent factor at fixed symbolic
weight.  The quotient between that packet and its parent is the genuinely
higher residual source.  This file packages those two parts of one recursive
Hall-collection step together.

The concrete constructor applies this package to the recipe-correct outer
children emitted after reducing an inner Hall tree under a fixed outer right
word.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora
namespace RCSrc

/--
The residual raw source for a ranked rewrite: invert the child packet and
append the original parent factor.
-/
def residualRawSource
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect) :
    List (SPFactora H inputWeight) :=
  SPFactora.inverseList source.factorSource ++ [parent]

/-- Evaluation of the ranked residual source is child-packet division. -/
theorem list_raw_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (q : ℕ) :
    SPFactora.listEval (n := n) q source.residualRawSource =
      (SPFactora.listEval q source.factorSource)⁻¹ *
        parent.eval q := by
  simp [residualRawSource, SPFactora.list_eval_inverse]

end RCSrc

/--
A finite strict Hall-ranked child packet together with a deeper semantic
recollection of the quotient between that packet and its parent.
-/
structure RRRecol
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) where
  source :
    RCSrc (n := n) parent parentRankDefect
  residualRecollection :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H source.residualRawSource

namespace RRRecol

/-- The one-step symbolic rewrite consists of ranked children then residual. -/
def rewriteSource
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect) :
    List (SPFactora H inputWeight) :=
  recollection.source.factorSource ++
    recollection.residualRecollection.higherSource

/-- The ranked children followed by the deeper residual reconstruct the parent. -/
theorem list_rewrite_parent
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (q : ℕ) :
    SPFactora.listEval (n := n) q recollection.rewriteSource =
      parent.eval q := by
  rw [rewriteSource, SPFactora.listEval_append,
    recollection.residualRecollection.list_higher_raw,
    recollection.source.list_raw_source]
  group

/-- Truncation of the ranked child packet extends to the one-step rewrite. -/
theorem truncated_rewrite_source
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (hsource :
      SPFactora.IsTruncated n
        recollection.source.factorSource) :
    SPFactora.IsTruncated n recollection.rewriteSource := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact hsource factor hfactor
  · exact
      recollection.residualRecollection.higher_source_truncated factor hfactor

/--
Support of the ranked child packet extends to the one-step rewrite whenever
the residual target is at least as strong as the desired bound.
-/
theorem least_rewrite_source
    {d n inputWeight lowerWeight sourceWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {parent : SPFactora H inputWeight}
    {parentRankDefect : ℕ}
    (recollection :
      RRRecol
        (n := n) (lowerWeight := lowerWeight) parent parentRankDefect)
    (hsource :
      SPFactora.WordWeightLeast sourceWeight
        recollection.source.factorSource)
    (hweight : sourceWeight ≤ lowerWeight) :
    SPFactora.WordWeightLeast
      sourceWeight recollection.rewriteSource := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact hsource factor hfactor
  · exact hweight.trans
      (recollection.residualRecollection.higher_weight_least
        factor hfactor)

end RRRecol
end SPFactora

open HEWord

namespace CIChildr

/--
Package a recipe-correct full outer-child Hall rewrite as strict same-weight
children followed by a next-stratum residual recollection.
-/
noncomputable def rankedResidualRecollection
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteBasicCommutators.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.RRRecol
      (n := n) (lowerWeight := lowerWeight + 1) factor
      (HallTree.bracketRankDefect
        ((tree innerWord).weight + unchanged.weight)
        originalLeft originalRight) where
  source :=
    rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  residualRecollection := by
    rw [SPFactora.RCSrc.residualRawSource,
      factor_ranked_task]
    exact
      normalizer.recollection_inner_raw
        hn hH factor innerWord rightWord hword hfactorWeight hlowerWeightPos
          hlowerWeightTruncated

end CIChildr
end TCTex
end Towers

-- Merged from ReductionOuterChildNormalizedResidualComposition.lean

/-!
# Parent residuals after recursively normalizing full outer children

Recipe-correct inner reduction emits finitely many full-weight outer children.
Once recursive Hall-ranked induction has recollected those children
individually, their complete packet has an exact same-stratum normalization.

The remaining parent residual then splits into:

* one atomic-to-normalized-child comparison source;
* the already identified child-to-parent residual source.

This is the local composition shape needed by a concrete ranked scheduler.  It
isolates the remaining fixed-weight atomic merge from the recursive child
normalizations.  The file is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CIChildr

/--
Recursively supplied concrete residual recollections normalize the entire
ranked full outer-child packet at the parent support stratum.
-/
noncomputable def recollection_basic_residuals
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          rankedTasks factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (innerOuterFactors factor innerWord rightWord hword) := by
  let source :=
    rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  have hsource :
      source.factorSource =
        innerOuterFactors factor innerWord rightWord hword := by
    dsimp only [source]
    exact
      factor_ranked_task factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic
  rw [← hsource]
  apply source.recollection_basic_residuals
  · rw [hsource]
    exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactorTruncated
  · rw [hsource]
    exact
      least_inner_factors
        factor innerWord rightWord hword
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end CIChildr

namespace
  TSRecollb

/--
After the full-weight children have been recursively normalized, recollecting
their atomic comparison and their outer residual recollects the parent.
-/
noncomputable def inner_child_normalization
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (comparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactora.inverseList (basicReductionFactors factor) ++
          children.higherSource))
    (outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword)) :
    TSRecollb
      (n := n) factor :=
  inner_outer factor innerWord rightWord hword
    (comparison.of_list_eq fun q => by
      rw [SPFactora.listEval_append,
        SPFactora.list_eval_inverse,
        children.list_higher_raw,
        inner_comparison_source])
    outer

/--
Specialize the parent bridge to the ranked child packet emitted by inner
reduction.  Recursive basic residuals discharge every child; only the explicit
atomic comparison source and child-to-parent residual remain as inputs.
-/
noncomputable def inner_ranked_residuals
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          CIChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1)
    (comparison :
      let children :=
        CIChildr.recollection_basic_residuals
          factor innerWord rightWord hword hfactorTruncated added originalRight
            unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
              hunchangedBasic residual
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (SPFactora.inverseList (basicReductionFactors factor) ++
          children.higherSource))
    (outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword)) :
    TSRecollb
      (n := n) factor := by
  let children :=
    CIChildr.recollection_basic_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  exact
    inner_child_normalization factor innerWord rightWord
      hword children comparison outer

end
  TSRecollb

end TCTex
end Towers

-- Merged from ReductionOuterPoweredComparisonWorklistComposition.lean

/-!
# Factoring powered outer comparisons through reconstruction worklists

The powered outer comparison divides the recipe-correct Hall-child packet by
the temporary Hall-Petresco packet for `[inner ^ e, right]`.  Insert between
them the outer-bracket worklist obtained by first reducing the powered inner
factor to its canonical atomic packet.

The resulting factorization separates two operational sources:

* comparison of recipe-correct Hall children with the atomic outer worklist;
* comparison of the atomic outer worklist with its exact reconstruction
  worklist.

Their product evaluates exactly to the original powered comparison.  This is
the source-level shape needed to route the two cancellation problems
independently.  The file is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord
open BRWork
open IPBridge

namespace HEWord

/--
Outer-bracket worklist obtained by atomically reducing the powered inner
factor before bracketing with the fixed right factor.
-/
noncomputable def innerAtomicWorklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  CBWorka.factors packet hinputWeight
    (innerPowerFactor factor innerWord hrecipe)
    (rightUnitFactor (inputWeight := inputWeight) rightWord)

/--
Exact reconstruction worklist for the powered inner factor and fixed right
factor.
-/
noncomputable def innerReconstructionWorklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  BRWork.factors packet
    hinputWeight (innerPowerFactor factor innerWord hrecipe)
      (rightUnitFactor (inputWeight := inputWeight) rightWord)

/--
The exact reconstruction worklist evaluates to the temporary Hall-Petresco
packet used in the powered comparison.
-/
theorem
    powered_reconstruction_worklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerReconstructionWorklist packet
          hinputWeight factor innerWord rightWord hrecipe) =
      SPFactora.listEval q
        (correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors := by
  exact
    list_factors_packet
      packet hinputWeight (innerPowerFactor factor innerWord hrecipe)
        (rightUnitFactor (inputWeight := inputWeight) rightWord) q

/--
First operational comparison: divide the atomic outer-bracket worklist by the
recipe-correct Hall-child packet.
-/
noncomputable def poweredAtomicWorklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    innerAtomicWorklist packet hinputWeight factor
      innerWord rightWord hrecipe

/--
Second operational comparison: divide the exact reconstruction worklist by
its atomic outer-bracket prefix.
-/
noncomputable def
    poweredReconstructionWorklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerAtomicWorklist packet hinputWeight factor
        innerWord rightWord hrecipe) ++
    innerReconstructionWorklist packet hinputWeight
      factor innerWord rightWord hrecipe

/--
The powered comparison decomposes through the atomic and reconstruction
outer-bracket worklists.
-/
noncomputable def innerPoweredWorklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  poweredAtomicWorklist packet
      hinputWeight factor innerWord rightWord hword hrecipe ++
    poweredReconstructionWorklist packet
      hinputWeight factor innerWord rightWord hrecipe

/-- Evaluation of the worklist decomposition recovers the powered comparison. -/
theorem
    powered_worklist_comparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredWorklist packet
          hinputWeight factor innerWord rightWord hword hrecipe) =
      SPFactora.listEval q
        (innerPoweredComparison packet hinputWeight
          factor innerWord rightWord hword hrecipe) := by
  simp only [innerPoweredWorklist,
    poweredAtomicWorklist,
    poweredReconstructionWorklist,
    innerPoweredComparison,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    powered_reconstruction_worklist]
  group

end HEWord

namespace TSRecol

/--
Compose independent recollections of the two worklist comparisons into a
recollection of the powered outer comparison.
-/
noncomputable def
    powered_worklist_pieces
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (atomicComparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.poweredAtomicWorklist
          packet hinputWeight factor innerWord rightWord hword hrecipe))
    (reconstructionResidual :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.poweredReconstructionWorklist
          packet hinputWeight factor innerWord rightWord hrecipe)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerPoweredComparison
        packet hinputWeight factor innerWord rightWord hword hrecipe) :=
  (atomicComparison.append reconstructionResidual).of_list_eq fun q => by
    simpa only [
      HEWord.innerPoweredWorklist]
      using
        powered_worklist_comparison
          packet hinputWeight factor innerWord rightWord hword hrecipe q

end TSRecol

end TCTex
end Towers

-- Merged from ReductionOuterChildNormalizedBasicComparison.lean

/-!
# Atomic comparison after recursively normalizing full outer children

After recursively recollecting the full-weight children emitted by inner Hall
reduction, the remaining fixed-weight comparison source consists of the
inverse canonical parent packet followed by the normalized child source.

This file names that source and records its semantic invariants.  It is the
precise input that an operational fixed-weight atomic router must recollect
into the next stratum.  The file is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace HEWord

/--
The fixed-weight comparison source remaining after recursive normalization of
the recipe-correct full outer-child packet.
-/
noncomputable def innerChildNormalized
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor) ++
    children.higherSource

/-- The post-recursion atomic comparison inherits physical truncation. -/
theorem
    truncNormalizedComparison
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerChildNormalized
        factor innerWord rightWord hword children) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · exact children.higher_source_truncated x hx

/-- The post-recursion atomic comparison remains physically in the parent layer. -/
theorem
    normalizedComparisonSource
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerChildNormalized
        factor innerWord rightWord hword children) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.least_inverse_list
        (least_reduction_factors factor) x hx
  · exact children.higher_weight_least x hx

/--
Recursive child normalization does not change the evaluated atomic comparison
source.
-/
theorem
    child_normalized_comparison
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerChildNormalized
          factor innerWord rightWord hword children) =
      SPFactora.listEval q
        (innerComparisonSource
          factor innerWord rightWord hword) := by
  rw [innerChildNormalized,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    children.list_higher_raw,
    inner_comparison_source]

/-- The post-recursion atomic comparison evaluates one stratum deeper. -/
theorem
    list_inner_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword))
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerChildNormalized
          factor innerWord rightWord hword children) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [child_normalized_comparison]
  exact
    inner_comparison_series
      factor innerWord rightWord hword q

end HEWord

namespace TSNormalb

/--
A current-stratum normalizer recollects the named post-recursion atomic
comparison into the next support layer.
-/
noncomputable def
    child_normalized_raw
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteBasicCommutators.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (children :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerOuterFactors
          factor innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerChildNormalized
        factor innerWord rightWord hword children) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
    (HEWord.innerChildNormalized
      factor innerWord rightWord hword children)
    hlowerWeightPos hlowerWeightTruncated
    (HEWord.truncNormalizedComparison
      factor innerWord rightWord hword children (by
        rw [hfactorWeight]
        exact hlowerWeightTruncated))
    (by
      rw [← hfactorWeight]
      exact
        HEWord.normalizedComparisonSource
          factor innerWord rightWord hword children)
    (fun q => by
      rw [← hfactorWeight]
      exact
        HEWord.list_inner_series
          factor innerWord rightWord hword children q)

end TSNormalb

end TCTex
end Towers

-- Merged from ReductionOuterPoweredComparisonWorklistResidualSupport.lean

/-!
# Support of reconstruction-worklist residuals in powered outer comparisons

Replacing an inner factor by its canonical atomic packet and then bracketing
with a fixed right factor produces an atomic outer worklist.  The exact
reconstruction worklist has the same outer bracket after restoring the inner
basic-reduction residual.

Their quotient lies one layer above the full outer-bracket weight.  This file
records that generic congruence estimate and specializes it to the
reconstruction residual in a powered outer comparison.  At the next-stratum
cutoff, this residual recollects to the empty source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open HEWord
open BRWork
open IPBridge

namespace BRWork

/--
Raw quotient from the atomic outer worklist to the exact reconstruction
worklist.
-/
noncomputable def residualRawSource
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (CBWorka.factors packet hinputWeight
        inner right) ++
    factors packet hinputWeight inner right

/-- Evaluation of the raw residual is outer-worklist division. -/
theorem list_raw_source
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight inner right) =
      (SPFactora.listEval q
        (CBWorka.factors packet
          hinputWeight inner right))⁻¹ *
        SPFactora.listEval q
          (factors packet hinputWeight inner right) := by
  simp [residualRawSource, SPFactora.list_eval_inverse]

/--
The reconstruction residual lies one lower-central layer above the full
outer-bracket weight.
-/
theorem raw_series_add
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) := by
  rw [list_raw_source,
    CBWorka.listEval_factors,
    listEval_factors]
  let G := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let atomic : G :=
    SPFactora.listEval (n := n) q (basicReductionFactors inner)
  let original : G := inner.eval (n := n) q
  let rightValue : G := right.eval (n := n) q
  let innerWeight := inner.word.weight PEAddres.weight
  let rightWeight := right.word.weight PEAddres.weight
  let K := Subgroup.lowerCentralSeries G (innerWeight + rightWeight)
  change ⁅atomic, rightValue⁆⁻¹ * ⁅original, rightValue⁆ ∈ K
  have hinner :
      atomic⁻¹ * original ∈ Subgroup.lowerCentralSeries G innerWeight := by
    simpa [G, atomic, original, innerWeight] using
      (reduction_inv_series
        (n := n) inner q)
  have hright :
      rightValue ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) := by
    simpa [G, rightValue, rightWeight] using
      (right.eval_lower_series (n := n) q)
  have hinnerReverse :
      atomic * original⁻¹ ∈ Subgroup.lowerCentralSeries G innerWeight := by
    let L := Subgroup.lowerCentralSeries G innerWeight
    have hconj :
        atomic * (atomic⁻¹ * original) * atomic⁻¹ ∈ L :=
      (inferInstance : L.Normal).conj_mem
        (atomic⁻¹ * original) (by simpa [L] using hinner) atomic
    have hinv := L.inv_mem hconj
    have heq :
        (atomic * (atomic⁻¹ * original) * atomic⁻¹)⁻¹ =
          atomic * original⁻¹ := by
      group
    simpa only [heq] using hinv
  have hcomm :
      ⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹ ∈
        Subgroup.lowerCentralSeries G (innerWeight + (rightWeight - 1) + 1) :=
    congr_inv_series
      hinnerReverse hright
  have hindex :
      innerWeight + (rightWeight - 1) + 1 = innerWeight + rightWeight := by
    have hrightPos := right.word_weight_pos
    simp only [rightWeight]
    omega
  have hcommK :
      ⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹ ∈ K := by
    simpa only [K, hindex] using hcomm
  have hcommInv :
      ⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹ ∈ K := by
    have hinv := K.inv_mem hcommK
    have heq :
        (⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹)⁻¹ =
          ⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹ := by
      group
    simpa only [heq] using hinv
  have hconj :
      ⁅atomic, rightValue⁆⁻¹ *
            (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) *
          (⁅atomic, rightValue⁆⁻¹)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) hcommInv
        ⁅atomic, rightValue⁆⁻¹
  have heq :
      ⁅atomic, rightValue⁆⁻¹ *
            (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) *
          (⁅atomic, rightValue⁆⁻¹)⁻¹ =
        ⁅atomic, rightValue⁆⁻¹ * ⁅original, rightValue⁆ := by
    group
  simpa only [heq] using hconj

/-- The reconstruction residual is trivial once its next layer is cut off. -/
theorem n_succ_add
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hcutoff :
      n ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight inner right) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (raw_series_add
      packet hinputWeight inner right q)

/--
At the next-stratum cutoff, the reconstruction residual recollects to the
empty source at any requested support bound.
-/
def recollection_terminal
    {d n inputWeight lowerWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hcutoff :
      n ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (residualRawSource packet hinputWeight inner right) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (n_succ_add
        packet hinputWeight inner right hcutoff q).symm

end BRWork

namespace HEWord

/--
The reconstruction half of a powered outer comparison lies one layer above
the parent bracket.
-/
theorem
    powered_reconstruction_series
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (poweredReconstructionWorklist
          packet hinputWeight factor innerWord rightWord hrecipe) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  simpa [poweredReconstructionWorklist,
    BRWork.residualRawSource,
    innerAtomicWorklist,
    innerReconstructionWorklist, innerPowerFactor,
    rightUnitFactor, hword] using
      (raw_series_add
        packet hinputWeight (innerPowerFactor factor innerWord hrecipe)
          (rightUnitFactor (inputWeight := inputWeight) rightWord) q)

/--
At the next parent-stratum endpoint, the reconstruction half of a powered
outer comparison recollects to the empty source.
-/
def
    powered_reconstruction_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (poweredReconstructionWorklist
        packet hinputWeight factor innerWord rightWord hrecipe) := by
  simpa [poweredReconstructionWorklist,
    BRWork.residualRawSource,
    innerAtomicWorklist,
    innerReconstructionWorklist, innerPowerFactor,
    rightUnitFactor, hword] using
      (BRWork.recollection_terminal
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        packet hinputWeight (innerPowerFactor factor innerWord hrecipe)
          (rightUnitFactor (inputWeight := inputWeight) rightWord)
          (by simpa [innerPowerFactor, rightUnitFactor, hword] using hcutoff))

/--
The first atomic-worklist comparison is also one layer above the parent
bracket.  This follows by dividing the full powered comparison by the already
controlled reconstruction residual.
-/
theorem
    powered_atomic_worklist
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (poweredAtomicWorklist packet
          hinputWeight factor innerWord rightWord hword hrecipe) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight)
  let atomicComparison :=
    SPFactora.listEval (n := n) q
      (poweredAtomicWorklist packet
        hinputWeight factor innerWord rightWord hword hrecipe)
  let reconstructionResidual :=
    SPFactora.listEval (n := n) q
      (poweredReconstructionWorklist packet
        hinputWeight factor innerWord rightWord hrecipe)
  let poweredComparison :=
    SPFactora.listEval (n := n) q
      (innerPoweredComparison packet hinputWeight factor
        innerWord rightWord hword hrecipe)
  have hcomparison : poweredComparison ∈ K :=
    powered_comparison_series
      packet hinputWeight factor innerWord rightWord hword hrecipe q
  have hreconstruction : reconstructionResidual ∈ K :=
    powered_reconstruction_series
      packet hinputWeight factor innerWord rightWord hword hrecipe q
  have hdecomposition :
      atomicComparison * reconstructionResidual = poweredComparison := by
    simpa only [atomicComparison, reconstructionResidual, poweredComparison,
      innerPoweredWorklist,
      SPFactora.listEval_append] using
        (powered_worklist_comparison
          packet hinputWeight factor innerWord rightWord hword hrecipe q)
  have hmul : poweredComparison * reconstructionResidual⁻¹ ∈ K :=
    K.mul_mem hcomparison (K.inv_mem hreconstruction)
  have heq :
      poweredComparison * reconstructionResidual⁻¹ = atomicComparison := by
    rw [← hdecomposition]
    group
  simpa only [heq] using hmul

/-- The first atomic-worklist comparison vanishes at the next endpoint. -/
theorem
    atomic_worklist_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (poweredAtomicWorklist packet
          hinputWeight factor innerWord rightWord hword hrecipe) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (powered_atomic_worklist
      packet hinputWeight factor innerWord rightWord hword hrecipe q)

/--
At the next parent-stratum endpoint, the first atomic-worklist comparison
recollects to the empty source.
-/
def
    powered_atomic_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (poweredAtomicWorklist packet
        hinputWeight factor innerWord rightWord hword hrecipe) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro q
    simpa using
      (atomic_worklist_terminal
        packet hinputWeight factor innerWord rightWord hword hrecipe hcutoff
          q).symm

end HEWord

namespace TSRecol

/--
At the next parent-stratum endpoint, recollecting the first atomic-worklist
comparison already recollects the full powered comparison.
-/
noncomputable def
    powered_worklist_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (atomicComparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.poweredAtomicWorklist
          packet hinputWeight factor innerWord rightWord hword hrecipe)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerPoweredComparison
        packet hinputWeight factor innerWord rightWord hword hrecipe) :=
  powered_worklist_pieces packet
    hinputWeight factor innerWord rightWord hword hrecipe atomicComparison
      (powered_reconstruction_terminal
        packet hinputWeight factor innerWord rightWord hword hrecipe hcutoff)

/--
At the next parent-stratum endpoint, recollecting the first atomic-worklist
comparison already recollects the original child-to-parent outer residual.
-/
noncomputable def
    atomic_worklist_comparison
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (atomicComparison :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (HEWord.poweredAtomicWorklist
          packet hinputWeight factor innerWord rightWord hword hrecipe)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) := by
  have hinnerPos :
      0 < innerWord.weight PEAddres.weight :=
    CWord.weight_pos PEAddres.weight
      PEAddres.weight_pos innerWord
  apply
    inner_powered_comparison
      packet hinputWeight factor innerWord rightWord hword hrecipe
  · rw [hword] at hcutoff
    simp only [CWord.weight_commutator] at hcutoff
    omega
  · exact
      powered_worklist_terminal packet
        hinputWeight factor innerWord rightWord hword hrecipe hcutoff
          atomicComparison

/--
At the next parent-stratum endpoint, the entire child-to-parent residual
recollects to the empty source through the powered worklist factorization.
-/
noncomputable def outer_raw_terminal
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  atomic_worklist_comparison packet
    hinputWeight factor innerWord rightWord hword hrecipe hcutoff
      (powered_atomic_terminal
        packet hinputWeight factor innerWord rightWord hword hrecipe hcutoff)

end TSRecol

end TCTex
end Towers

-- Merged from ReductionOuterActiveAtomicComparison.lean

/-!
# Active-atomic recollection after recursive outer-child normalization

Recursive normalization of one full-weight outer child replaces it by its
canonical atomic Hall packet followed by a strictly heavier residual.  Folding
this construction across ranked children therefore preserves a useful
invariant: every factor still in the active layer is atomic, and every other
factor is already strictly stronger.

The mixed-source sharp router recollects the resulting parent comparison using
only deeper normalizers.  In particular, this removes the current-stratum
semantic-normalizer assumption from the atomic-comparison half of inner
reduction under an outer bracket.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u v

open HEWord

/--
An upward source recollection which remembers that every factor remaining in
the active stratum is atomic.
-/
structure
    AORecol
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (rawSource : List (SPFactora H inputWeight)) where
  recollection :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H rawSource
  active_atoms_or :
    ∀ factor ∈ recollection.higherSource,
      lowerWeight <
          factor.word.weight PEAddres.weight ∨
        ∃ address : HEAddres H,
          factor.word = .atom address ∧ address.weight = lowerWeight

namespace
  AORecol

/-- The empty recollection preserves the active-atomic invariant. -/
def empty
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    AORecol
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H [] where
  recollection := .empty
  active_atoms_or := by
    intro factor hfactor
    change factor ∈ ([] : List (SPFactora H inputWeight)) at hfactor
    simp at hfactor

/-- Concatenation preserves the active-atomic invariant. -/
def append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {leftSource rightSource : List (SPFactora H inputWeight)}
    (left :
      AORecol
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      AORecol
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    AORecol
      (n := n) (lowerWeight := lowerWeight) H (leftSource ++ rightSource) where
  recollection := left.recollection.append right.recollection
  active_atoms_or := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.active_atoms_or factor hfactor
    · exact right.active_atoms_or factor hfactor

/-- Fold active-atomic recollections across a finite `flatMap` source. -/
def flatMap
    {α : Type v}
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (items : List α)
    (rawSource : α → List (SPFactora H inputWeight))
    (recollection :
      ∀ item ∈ items,
        AORecol
          (n := n) (lowerWeight := lowerWeight) H (rawSource item)) :
    AORecol
      (n := n) (lowerWeight := lowerWeight) H (items.flatMap rawSource) := by
  induction items with
  | nil =>
      exact empty
  | cons head tail ih =>
      exact
        append
          (recollection head (by simp))
          (ih fun item hitem => recollection item (by simp [hitem]))

/--
The mixed-source sharp router turns an active-atomic recollection whose value
is semantically deeper into a strictly higher recollection.
-/
noncomputable def recollectionSemanticallyHigher
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {rawSource : List (SPFactora H inputWeight)}
    (source :
      AORecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hrawSourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H rawSource := by
  let tail :=
    factory.atoms_or_higher
      hn H hH sharp nextNormalizer source.recollection.higherSource
        hlowerWeightPos hlowerWeightTruncated
          source.recollection.higher_source_truncated
            source.active_atoms_or
              (fun q => by
                rw [source.recollection.list_higher_raw]
                exact hrawSourceMem q)
  exact
    {
      higherSource := tail.higherSource
      higher_source_truncated := tail.higher_source_truncated
      higher_weight_least :=
        tail.higher_weight_least
      list_higher_raw := by
        intro q
        rw [tail.list_higher_raw,
          source.recollection.list_higher_raw]
    }

end
  AORecol

namespace
  TSRecollb

/--
Replacing one factor by its canonical atomic packet and recollected residual
preserves the active-atomic invariant at every weaker support stratum.
-/
noncomputable def atomsOrRecollection
    {d n inputWeight lowerWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (hlowerWeight :
      lowerWeight ≤ factor.word.weight PEAddres.weight) :
    AORecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) [factor] where
  recollection :=
    recollection.singletonSourceRecollection hfactorTruncated hlowerWeight
  active_atoms_or := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxWeight := word_reduction_factors factor hx
      rcases lt_or_eq_of_le hlowerWeight with hlowerWeight | hlowerWeight
      · exact Or.inl (by omega)
      · right
        rcases atom_basic_factors factor hx with
          ⟨address, hword, haddressWeight⟩
        exact ⟨address, hword, by omega⟩
    · left
      have hxWeight :=
        recollection.higher_least_succ x hx
      omega

end
  TSRecollb

namespace SPFactora
namespace RCSrc

/--
Recursively supplied concrete residual recollections preserve an active-atomic
inventory when folded over a ranked child source.
-/
noncomputable def atoms_recollect_residuals
    {d n inputWeight lowerWeight parentRankDefect : ℕ}
    {parent :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (source : RCSrc (n := n) parent parentRankDefect)
    (hsourceTruncated :
      SPFactora.IsTruncated n source.factorSource)
    (hsourceSupported :
      SPFactora.WordWeightLeast
        lowerWeight source.factorSource)
    (residual :
      ∀ task ∈ source.tasks,
        TSRecollb
          (n := n) task.1) :
    AORecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source.factorSource := by
  have hfactorSource :
      source.factorSource =
        source.tasks.flatMap
          (fun task :
              SPFactora
                  (concreteBasicCommutators.{u} d) inputWeight ×
                ℕ =>
            [task.1]) := by
    simp only [factorSource]
    induction source.tasks with
    | nil =>
        rfl
    | cons task tasks ih =>
        simp only [List.map_cons, List.flatMap_cons, List.singleton_append, ih]
  rw [hfactorSource]
  exact
    AORecol.flatMap
      (α :=
        SPFactora
            (concreteBasicCommutators.{u} d) inputWeight ×
          ℕ)
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
      (H := concreteBasicCommutators.{u} d)
      (items := source.tasks)
      (rawSource :=
        fun task :
            SPFactora
                (concreteBasicCommutators.{u} d) inputWeight ×
              ℕ =>
          [task.1])
      (recollection :=
        fun
            (task :
              SPFactora
                  (concreteBasicCommutators.{u} d) inputWeight ×
                ℕ)
            (htask : task ∈ source.tasks) =>
          (residual task htask).atomsOrRecollection
            (hsourceTruncated task.1
              (source.fst_factor_tasks htask))
            (hsourceSupported task.1
              (source.fst_factor_tasks htask)))

end RCSrc
end SPFactora

namespace CIChildr

/--
Ranked recursive normalization of the full outer-child packet preserves an
active-atomic inventory at the parent factor's Hall weight.
-/
noncomputable def
    atoms_recollect_residuals
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈ rankedTasks factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    AORecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (innerOuterFactors factor innerWord rightWord hword) := by
  let source :=
    rankedTaskSource (n := n) factor innerWord rightWord hword added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  have hsource :
      source.factorSource =
        innerOuterFactors factor innerWord rightWord hword := by
    dsimp only [source]
    exact
      factor_ranked_task factor innerWord rightWord hword added
        originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic
  rw [← hsource]
  apply source.atoms_recollect_residuals
  · rw [hsource]
    exact
      truncated_inner_factors factor innerWord rightWord hword
        hfactorTruncated
  · rw [hsource]
    exact
      least_inner_factors factor innerWord rightWord
        hword
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end CIChildr

namespace TSFtrya

/--
After recursively recollecting ranked outer children, the parent atomic
comparison recollects upward using only the sharp router and next-stratum
normalizer.
-/
noncomputable def
    child_normalized_raw
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
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (children :
      AORecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)
        (innerOuterFactors factor innerWord rightWord hword)) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerChildNormalized
        factor innerWord rightWord hword children.recollection) := by
  apply
    factory.atoms_or_higher
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer
  · exact factor.word_weight_pos
  · exact hfactorTruncated
  · exact
      truncNormalizedComparison
        factor innerWord rightWord hword children.recollection hfactorTruncated
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · right
      exact atom_reduction_factors factor hx
    · exact children.active_atoms_or x hx
  · exact fun q =>
      list_inner_series
        factor innerWord rightWord hword children.recollection q

end TSFtrya

end TCTex
end Towers

-- Merged from ReductionOuterAutomaticResidualRecollection.lean

/-!
# Automatic residual recollection after ranked inner reduction

Recipe-correct inner reduction produces strictly Hall-ranked full-weight
children.  Once recursive induction has recollected those children, a
current-stratum semantic normalizer automa removes the remaining
atomic-to-normalized-child comparison.  The ranked child-to-parent quotient
is normalized by the same current-stratum normalizer.

Together these two higher sources recollect the true canonical basic
residual of the parent factor.  This is the local nonbasic branch needed by a
Hall-ranked residual scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace
  TSRecollb

/--
Build the parent residual recollection from recursive residual recollections
for the strictly ranked full-weight children and one current-stratum
normalizer.
-/
noncomputable def
    inner_residuals_normalizer
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
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          CIChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor := by
  let children :=
    CIChildr.recollection_basic_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  let comparison :=
    normalizer.child_normalized_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
        hfactorTruncated children
  let rankedOuter :=
    CIChildr.rankedResidualRecollection
      hn hH normalizer factor innerWord rightWord hword rfl
        factor.word_weight_pos hfactorTruncated added originalRight unchanged
          originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
  have outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource
          factor innerWord rightWord hword) := by
    simpa only [rankedOuter,
      CIChildr.rankedResidualRecollection,
      SPFactora.RCSrc.residualRawSource,
      CIChildr.factor_ranked_task] using
        rankedOuter.residualRecollection
  exact
    inner_ranked_residuals factor innerWord rightWord
      hword hfactorTruncated added originalRight unchanged originalLeft
        hinnerTree hRightLeft hRightUnchanged hunchangedBasic residual
          (by
            simpa only [
              HEWord.innerChildNormalized]
              using comparison)
          outer

/-- Use a semantic normalizer family at the parent factor's Hall weight. -/
noncomputable def
    ranked_residuals_normalizer
    {d n inputWeight : ℕ}
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
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          CIChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor :=
  inner_residuals_normalizer hn hH factor
    (family.normalizer
      (factor.word.weight PEAddres.weight))
    innerWord rightWord hword hfactorTruncated added originalRight unchanged
      originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
        residual

/--
Scheduler-facing specialization: recursive residuals are supplied over the
actual `RCSrc.tasks` field consumed by well-founded induction.
-/
noncomputable def
    ranked_task_residuals
    {d n inputWeight : ℕ}
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
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          (CIChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor :=
  ranked_residuals_normalizer hn hH
    family factor innerWord rightWord hword hfactorTruncated added originalRight
      unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
        hunchangedBasic
        (fun task htask => residual task (by simpa using htask))

end
  TSRecollb

end TCTex
end Towers
