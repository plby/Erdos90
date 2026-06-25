import Submission.Group.HallBasic.ExplicitReductionScaling
import Submission.Group.Zassenhaus.TreeCompression
import Submission.Group.Zassenhaus.FactorSourceReduction

/-!
# Symbolic factors from concrete Hall-tree reduction

For the canonical concrete Hall family, explicit Hall-tree reduction can be
read as a finite packet of atomic symbolic Hall factors.  Each extracted
integer coordinate scales the coefficient of the original symbolic factor
while retaining its bounded repeated-block recipe.

The packet does not evaluate literally to the original factor.  Its inverse
followed by the original factor is a concrete symbolic source whose value lies
one lower-central stratum higher.  This is the operational input needed by a
recursive Hall collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/-- Reindexing a subgroup-family element does not change its ambient value. -/
private theorem coe_cast_family
    {G ι : Type*}
    [Group G]
    (S : ι → Subgroup G)
    {i j : ι}
    (h : i = j)
    (x : S i) :
    ((cast (congrArg (fun k => ↥(S k)) h) x : S j) : G) = x := by
  subst j
  rfl

/-- Casting a bounded recipe along a target-weight equality preserves evaluation. -/
private theorem cast_bounded_recipe
    {inputWeight r s : ℕ}
    (h : r = s)
    (recipe : BBRecipe inputWeight r)
    (q : ℕ) :
    (cast (congrArg (BBRecipe inputWeight) h) recipe).eval q =
      recipe.eval q := by
  cases h
  rfl

/-- Canonical concrete Hall address corresponding to one indexed basic tree. -/
noncomputable def basicReductionAddress
    {d r : ℕ}
    (i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r) :
    HEAddres (concreteBasicCommutators.{u} d) :=
  ⟨r, ULift.up i⟩

@[simp]
theorem basic_reduction_address
    {d r : ℕ}
    (i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r) :
    PEAddres.weight (basicReductionAddress i) = r :=
  rfl

@[simp]
theorem address_basic_reduction
    {d r : ℕ}
    (i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r) :
    evalFreeAddress (basicReductionAddress i) =
      (HallTree.indexedBasicTree i).toCWord.eval FreeGroup.of :=
  rfl

/--
Truncating the indexed basic-tree representative gives the value selected by
its canonical concrete Hall address.
-/
@[simp]
theorem
    indexed_tree_rep
    {d n r : ℕ}
    (i : HallTree.BasicIndex (α := FreeGenerator.{u} d) r) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.indexedTreeRep i) =
      PEAddres.freeLowerTruncation
        (basicReductionAddress i) := by
  rw [← lower_truncation_address]
  congr 1
  unfold HallTree.indexedTreeRep
  unfold HallTree.freeRepWeight
  exact
    coe_cast_family
      (fun k => Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) (k - 1))
      (HallTree.indexed_tree_weight i)
      (HallTree.indexedBasicTree i).freeCentralRep

/--
View a symbolic factor's bounded recipe at the weight of its expanded Hall
tree.
-/
noncomputable def basicReductionRecipe
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    BBRecipe inputWeight (tree factor.word).weight :=
  cast
    (congrArg (BBRecipe inputWeight)
      (tree_weight factor.word).symm)
    factor.recipe

@[simp]
theorem basic_reduction_recipe
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    (basicReductionRecipe factor).eval q = factor.recipe.eval q := by
  exact
    cast_bounded_recipe (tree_weight factor.word).symm
      factor.recipe q

/--
One extracted basic coordinate, carrying the original factor's repeated-block
recipe.
-/
noncomputable def basicReductionFactor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight) :
    SPFactora
      (concreteBasicCommutators.{u} d) inputWeight where
  word := .atom (basicReductionAddress i)
  coefficient :=
    HallTree.basicReductionCoordinates (tree factor.word) i *
      factor.coefficient
  recipe := basicReductionRecipe factor

@[simp]
theorem basic_reduction_exponent
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight)
    (q : ℕ) :
    (basicReductionFactor factor i).exponent q =
      HallTree.basicReductionCoordinates (tree factor.word) i *
        factor.exponent q := by
  simp [basicReductionFactor, SPFactora.exponent, mul_assoc]

@[simp]
theorem basic_reduction_factor
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight)
    (q : ℕ) :
    (basicReductionFactor factor i).eval (n := n) q =
      PEAddres.freeLowerTruncation
          (basicReductionAddress i) ^
        (HallTree.basicReductionCoordinates (tree factor.word) i *
          factor.exponent q) := by
  rw [SPFactora.eval, basic_reduction_exponent]
  rfl

/-- Ordered atomic symbolic packet extracted from one expanded Hall tree. -/
noncomputable def basicReductionFactors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree factor.word).weight =>
        i ≤ j).map
    (basicReductionFactor factor)

/-- Every extracted atomic factor remains in the original symbolic weight. -/
@[simp]
theorem basic_reduction_weight
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight) :
    (basicReductionFactor factor i).word.weight
        PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  exact tree_weight factor.word

/-- Membership in the atomic packet determines the original symbolic weight. -/
theorem word_reduction_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ basicReductionFactors factor) :
    x.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [basicReductionFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact basic_reduction_weight factor i

/-- Atomic reduction preserves physical truncation. -/
theorem truncated_reduction_factors
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n (basicReductionFactors factor) := by
  intro x hx
  rw [word_reduction_factors factor hx]
  exact hfactor

/-- Atomic reduction preserves the lower support bound of the original layer. -/
theorem least_reduction_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (basicReductionFactors factor) := by
  intro x hx
  rw [word_reduction_factors factor hx]

/--
Truncating a coordinatewise-scaled Hall-tree packet gives the corresponding
ordered product of canonical concrete Hall atoms.
-/
theorem lower_truncation_scaled
    {d n : ℕ}
    (word :
      CWord (HEAddres
        (concreteBasicCommutators.{u} d)))
    (z : ℤ) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.basicReductionScaled (tree word) z) =
      ((Finset.univ.sort
          fun i j :
            HallTree.BasicIndex
              (α := FreeGenerator.{u} d) (tree word).weight =>
            i ≤ j).map
        fun i =>
          PEAddres.freeLowerTruncation
              (n := n) (basicReductionAddress i) ^
            (HallTree.basicReductionCoordinates (tree word) i * z)).prod := by
  simp only [HallTree.basicReductionScaled,
    HallTree.basicScaledTerm]
  let indices :=
    Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree word).weight =>
        i ≤ j
  change
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (((indices.map fun i =>
          HallTree.indexedTreeRep i ^
            (HallTree.basicReductionCoordinates (tree word) i * z)).prod :
          Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
            ((tree word).weight - 1)) :
          FreeGroup (FreeGenerator.{u} d)) =
      (indices.map fun i =>
        PEAddres.freeLowerTruncation
            (n := n) (basicReductionAddress i) ^
          (HallTree.basicReductionCoordinates (tree word) i * z)).prod
  induction indices with
  | nil =>
      simp
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons]
      change
        lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
            ((HallTree.indexedTreeRep i :
                FreeGroup (FreeGenerator.{u} d)) ^
              (HallTree.basicReductionCoordinates (tree word) i * z) *
              (((indices.map fun j =>
                HallTree.indexedTreeRep j ^
                  (HallTree.basicReductionCoordinates (tree word) j * z)).prod :
                Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
                  ((tree word).weight - 1)) :
                FreeGroup (FreeGenerator.{u} d))) =
          PEAddres.freeLowerTruncation
                (n := n) (basicReductionAddress i) ^
              (HallTree.basicReductionCoordinates (tree word) i * z) *
            (indices.map fun j =>
              PEAddres.freeLowerTruncation
                  (n := n) (basicReductionAddress j) ^
                (HallTree.basicReductionCoordinates (tree word) j * z)).prod
      rw [map_mul, map_zpow,
        indexed_tree_rep,
        ih]

/--
The symbolic atomic packet evaluates to the truncated coordinatewise-scaled
Hall-tree reduction packet.
-/
theorem list_basic_factors
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicReductionFactors factor) =
      lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.basicReductionScaled (tree factor.word)
          (factor.exponent q)) := by
  rw [lower_truncation_scaled]
  unfold SPFactora.listEval basicReductionFactors
  rw [List.map_map]
  induction
      (Finset.univ.sort
        fun i j :
          HallTree.BasicIndex
            (α := FreeGenerator.{u} d) (tree factor.word).weight =>
          i ≤ j) with
  | nil =>
      rfl
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [basic_reduction_factor, ih]

/--
Dividing the original symbolic factor by its explicit atomic reduction packet
leaves a value one lower-central stratum higher.
-/
theorem reduction_inv_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    (SPFactora.listEval (n := n) q
        (basicReductionFactors factor))⁻¹ *
        factor.eval q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  have hscaledFree :=
    HallTree.scaled_zpow_series
      (tree factor.word) (factor.exponent q)
  have hscaledMap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by simpa only [tree_weight] using hscaledFree))
  have hscaled :
      (SPFactora.listEval (n := n) q
          (basicReductionFactors factor))⁻¹ *
          (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} d)) n
              (HallTree.basicReductionProduct (tree factor.word))) ^
            factor.exponent q ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight PEAddres.weight) := by
    rw [list_basic_factors]
    simpa only [map_mul, map_inv, map_zpow] using hscaledMap
  have hfactor :=
    zpow_inv_series
      (n := n) factor q
  have hmul :=
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight PEAddres.weight)).mul_mem
        hscaled hfactor
  rw [mul_assoc, mul_inv_cancel_left] at hmul
  exact hmul

/--
Concrete raw source for the higher residual: invert the explicit atomic packet
and append the original symbolic factor.
-/
noncomputable def basicRawSource
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor) ++
    [factor]

/-- A truncated factor has a physically truncated atomic residual source. -/
theorem truncated_reduction_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactor :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (basicRawSource factor) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactor

/-- The raw residual source evaluates to atomic-packet division. -/
theorem reduction_raw_source
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) =
      (SPFactora.listEval q
        (basicReductionFactors factor))⁻¹ * factor.eval q := by
  simp [basicRawSource,
    SPFactora.list_eval_inverse]

/-- The concrete raw residual source evaluates one stratum higher. -/
theorem
    list_reduction_series
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [reduction_raw_source]
  exact
    reduction_inv_series
      factor q

end HEWord

universe u

/--
Adjacent swaps cannot recollect the atomic residual source into a strictly
heavier list: the appended original factor survives every such rewrite.
-/
theorem
    TSRwa.notbasic_reduceresid_sourhighsour
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (higherSource :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight))
    (hhigherSource :
      SPFactora.WordWeightLeast
        (factor.word.weight PEAddres.weight + 1)
        higherSource) :
    ¬
    TSRwa (n := n)
      (HEWord.basicRawSource factor)
      higherSource := by
  intro hrewrites
  have hfactorMem :
      factor ∈
        HEWord.basicRawSource factor := by
    simp [HEWord.basicRawSource]
  have hfactorHigher :=
    hhigherSource factor (hrewrites.mem_of_mem hfactorMem)
  omega

/--
Semantic recollection data for the explicit atomic residual source.  A full
Hall collector must construct this package using an operation beyond adjacent
swaps.
-/
structure
    TSRecollb
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) where
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
          (HEWord.basicRawSource factor)

namespace
  TSRecollb

/-- A recollected higher source still evaluates one lower-central stratum higher. -/
theorem list_higher_series
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (q : ℕ) :
    SPFactora.listEval (n := n) q recollection.higherSource ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [recollection.list_higher_raw]
  exact
    HEWord.list_reduction_series
      factor q

end
  TSRecollb
end TCTex
end Submission
