import Towers.Group.Zassenhaus.HallTreeExpansion
import Towers.Group.Zassenhaus.SignedCorrectionSemantics
import Towers.Group.HallBasic.ExplicitScaling
import Towers.Group.HallBasic.ExplicitZeroCoordinates
import Towers.Group.HallBasic.ExplicitSwapScaling
import Towers.Group.Zassenhaus.PolynomialConcreteSemantic
import Towers.Group.HallBasic.StandardSequence
import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.HallBasic.ExplicitCoordinatePackets

/-!
# Signed polynomial factors from concrete Hall-tree reduction

For the canonical Hall family, explicit Hall-tree reduction becomes a finite
packet of atomic signed polynomial factors.  Every extracted integer
coordinate scales the original signed formula.

The packet need not evaluate literally to the original factor.  Its inverse
followed by the original factor is a concrete raw source whose value lies one
lower-central stratum higher.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

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

/-- Casting a signed formula along a target-weight equality preserves evaluation. -/
private theorem cast_binomial_formula
    {d r s : ℕ}
    {ι : Type}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (h : r = s)
    (formula : WBForm H ι r)
    (e : ι → HEFam H) :
    (cast (congrArg (WBForm H ι) h) formula).eval e =
      formula.eval e := by
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
    HEAddres.weight (basicReductionAddress i) = r :=
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
      HEAddres.freeLowerTruncation
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

/-- View a factor's signed formula at the weight of its expanded Hall tree. -/
noncomputable def basicReductionFormula
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    WBForm (concreteBasicCommutators.{u} d) ι
      (tree factor.word).weight :=
  cast
    (congrArg
      (WBForm
        (concreteBasicCommutators.{u} d) ι)
      (tree_weight factor.word).symm)
    factor.coefficient

@[simp]
theorem basic_reduction_formula
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (basicReductionFormula factor).eval e = factor.coefficient.eval e := by
  exact
    cast_binomial_formula (tree_weight factor.word).symm
      factor.coefficient e

/-- One extracted basic coordinate, carrying a scaled copy of the formula. -/
noncomputable def basicReductionFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι where
  word := .atom (basicReductionAddress i)
  coefficient :=
    (basicReductionFormula factor).scale
      (HallTree.basicReductionCoordinates (tree factor.word) i)

@[simp]
theorem basic_reduction_coefficient
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (basicReductionFactor factor i).coefficient.eval e =
      HallTree.basicReductionCoordinates (tree factor.word) i *
        factor.coefficient.eval e := by
  simp [basicReductionFactor]

@[simp]
theorem basic_reduction_factor
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (basicReductionFactor factor i).eval (n := n) e =
      HEAddres.freeLowerTruncation
          (basicReductionAddress i) ^
        (HallTree.basicReductionCoordinates (tree factor.word) i *
          factor.coefficient.eval e) := by
  rw [SPFactor.eval,
    basic_reduction_coefficient]
  rfl

/-- Ordered atomic signed-polynomial packet extracted from one expanded tree. -/
noncomputable def basicReductionFactors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree factor.word).weight =>
        i ≤ j).map
    (basicReductionFactor factor)

/-- Every extracted atomic factor remains in the original symbolic weight. -/
@[simp]
theorem basic_reduction_weight
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight) :
    (basicReductionFactor factor i).word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  exact tree_weight factor.word

/-- Membership in the atomic packet determines the original symbolic weight. -/
theorem word_reduction_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors factor) :
    x.word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  rw [basicReductionFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact basic_reduction_weight factor i

/-- Atomic reduction preserves physical truncation. -/
theorem truncated_reduction_factors
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (basicReductionFactors factor) := by
  intro x hx
  rw [word_reduction_factors factor hx]
  exact hfactor

/-- Atomic reduction preserves the support bound of the original layer. -/
theorem least_reduction_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (basicReductionFactors factor) := by
  intro x hx
  rw [word_reduction_factors factor hx]

/--
Truncating a coordinatewise-scaled Hall-tree packet gives the corresponding
ordered product of concrete Hall atoms.
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
          HEAddres.freeLowerTruncation
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
        HEAddres.freeLowerTruncation
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
          HEAddres.freeLowerTruncation
                (n := n) (basicReductionAddress i) ^
              (HallTree.basicReductionCoordinates (tree word) i * z) *
            (indices.map fun j =>
              HEAddres.freeLowerTruncation
                  (n := n) (basicReductionAddress j) ^
                (HallTree.basicReductionCoordinates (tree word) j * z)).prod
      rw [map_mul, map_zpow,
        indexed_tree_rep,
        ih]

/-- The atomic polynomial packet evaluates to the scaled Hall-tree packet. -/
theorem list_basic_factors
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.basicReductionScaled (tree factor.word)
          (factor.coefficient.eval e)) := by
  rw [lower_truncation_scaled]
  unfold SPFactor.listEval basicReductionFactors
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
Dividing the original factor by its explicit atomic reduction packet leaves a
value one lower-central stratum higher.
-/
theorem reduction_inv_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (SPFactor.listEval (n := n) e
        (basicReductionFactors factor))⁻¹ *
        factor.eval e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hscaledFree :=
    HallTree.scaled_zpow_series
      (tree factor.word) (factor.coefficient.eval e)
  have hscaledMap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by simpa only [tree_weight] using hscaledFree))
  have hscaled :
      (SPFactor.listEval (n := n) e
          (basicReductionFactors factor))⁻¹ *
          (lowerCentralTruncation
              (FreeGroup (FreeGenerator.{u} d)) n
              (HallTree.basicReductionProduct (tree factor.word))) ^
            factor.coefficient.eval e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (factor.word.weight HEAddres.weight) := by
    rw [list_basic_factors]
    simpa only [map_mul, map_inv, map_zpow] using hscaledMap
  have hfactor :=
    zpow_inv_series
      (n := n) factor e
  have hmul :=
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).mul_mem
        hscaled hfactor
  rw [mul_assoc, mul_inv_cancel_left] at hmul
  exact hmul

/--
Concrete raw source for the higher residual: invert the explicit atomic packet
and append the original factor.
-/
noncomputable def basicRawSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    [factor]

/-- A truncated factor has a physically truncated atomic residual source. -/
theorem truncated_reduction_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (basicRawSource factor) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactor) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactor

/-- The raw residual source evaluates to atomic-packet division. -/
theorem reduction_raw_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) =
      (SPFactor.listEval e
        (basicReductionFactors factor))⁻¹ * factor.eval e := by
  simp [basicRawSource,
    SPFactor.list_eval_inverse]

/-- The concrete raw residual source evaluates one stratum higher. -/
theorem
    list_reduction_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [reduction_raw_source]
  exact
    reduction_inv_series
      factor e

end CEWord

/--
Semantic recollection data for the explicit atomic residual source.  A full
Hall collector must compress this source into strictly heavier signed
polynomial factors.
-/
structure
    TRRecoll
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (CEWord.basicRawSource
            factor)

namespace
  TRRecoll

/-- A recollected higher source still evaluates one lower-central stratum higher. -/
theorem list_higher_series
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (recollection :
      TRRecoll
        (n := n) factor)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e recollection.higherSource ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [recollection.list_higher_raw]
  exact
    CEWord.list_reduction_series
        factor e

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction residuals for basic expanded trees

All-weight PBW uniqueness makes explicit reduction exact whenever a signed
polynomial factor's expanded Hall tree is already basic.  Its true concrete
reduction residual therefore recollects to the empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/--
For a factor whose expanded tree is basic, the explicit atomic Hall-tree
reduction packet evaluates literally to the original signed-polynomial
factor.
-/
theorem reduction_factors_tree
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (htreeBasic : (tree factor.word).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      factor.eval e := by
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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (htreeBasic : (tree factor.word).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_factors_tree
      factor htreeBasic e]
  simp

end CEWord

namespace
  TRRecoll

open CEWord

/--
For a factor whose expanded tree is basic, its explicit Hall-tree residual
recollects to the empty higher source.
-/
noncomputable def tree_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (htreeBasic : (CEWord.tree factor.word).IsBasic) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (reduction_raw_tree
        factor htreeBasic e).symm

end
  TRRecoll
end TCTex
end Towers

/-!
# Semantic recollection boundary for polynomial Hall-tree reduction

The explicit atomic reduction packet has a raw residual whose value lies one
lower-central stratum higher.  Pointwise Hall normal forms therefore collect
that value using coordinates supported in the higher stratum.

This remains a semantic boundary theorem: the chosen pointwise coordinates
are not asserted to be finite signed polynomial recipes.  Constructing such a
finite recollection is the remaining nonterminal symbolic task.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- Chosen pointwise Hall-normal coordinates of the atomic residual source. -/
noncomputable def basicNormalCoordinates
    {d n : ℕ}
    {ι : Type}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    HEFam (concreteBasicCommutators.{u} d) :=
  normalFormCoordinates hn (concreteBasicCommutators.{u} d) hH
    (SPFactor.listEval (n := n) e
      (basicRawSource factor))

/-- The pointwise Hall-normal coordinates collect back to the raw residual. -/
theorem collected_reduction_coordinates
    {d n : ℕ}
    {ι : Type}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    collectedHallProduct (n := n) (concreteBasicCommutators.{u} d)
        (basicNormalCoordinates hn hH factor e) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  exact
    collected_form_coordinates hn
      (concreteBasicCommutators.{u} d) hH
      (SPFactor.listEval e
        (basicRawSource factor))

/-- Every pointwise residual coordinate below the next stratum vanishes. -/
theorem basic_coordinates_below
    {d n s : ℕ}
    {ι : Type}
    (hn : 2 ≤ n)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (concreteCommutatorsWeight.{u} d t).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d))
    (hs : 1 ≤ s)
    (hsBelow :
      s < factor.word.weight HEAddres.weight + 1)
    (hsn : s < n) :
    basicNormalCoordinates hn hH factor e s = 0 := by
  apply
    imp_coordinates_below
      hn (concreteBasicCommutators.{u} d) hH
      (basicNormalCoordinates hn hH factor e)
      (r := factor.word.weight HEAddres.weight + 1)
  · rw [collected_reduction_coordinates]
    simpa using
      list_reduction_series
        factor e
  · exact hs
  · exact hsBelow
  · exact hsn

/--
Once the next residual stratum reaches the truncation cutoff, the explicit
raw residual source evaluates trivially.
-/
theorem
    reduction_raw_n
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (list_reduction_series
      factor e)

end CEWord

namespace
  TRRecoll

open CEWord

/--
At the truncation endpoint, the explicit atomic residual recollects to the
empty higher source.
-/
noncomputable def of_terminal
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (reduction_raw_n
        factor hcutoff e).symm

/--
A concrete higher-source recollection delegates directly to an existing
next-stratum semantic normalizer.
-/
theorem exists_normalizedCoordinates
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (recollection :
      TRRecoll
        (n := n) factor)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight := factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)) :
    ∃ coordinates :
        CCRecipe
          (concreteBasicCommutators.{u} d) ι,
      coordinates.NTBelow
          (factor.word.weight HEAddres.weight + 1) ∧
        ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
          SPFactor.listEval (n := n) e
              (coordinates.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (CEWord.basicRawSource
                factor) := by
  rcases normalizer.normalize recollection.higherSource
      recollection.higher_source_truncated
      recollection.higher_least_succ with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨coordinates, hcoordinates, fun e =>
      (heval e).trans (recollection.list_higher_raw e)⟩

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction residuals for expanded self-brackets

If a symbolic factor expands to a Hall-tree self-bracket, both its explicit
atomic reduction packet and its symbolic value are trivial.  Its true
concrete reduction residual therefore recollects to the empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- The explicit packet of an expanded Hall-tree self-bracket is trivial. -/
theorem reduction_tree_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = HallTree.commutator child child)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) = 1 := by
  rw [list_basic_factors, htree]
  exact
    congrArg
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (HallTree.basic_scaled_self
        child (factor.coefficient.eval e))

/-- The true reduction residual of an expanded Hall-tree self-bracket is trivial. -/
theorem
    raw_tree_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = HallTree.commutator child child)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_tree_self
      factor child htree e]
  simp only [inv_one, one_mul]
  unfold SPFactor.eval SPFactor.wordValue
  rw [← lower_truncation_tree factor.word]
  rw [htree]
  simp [CWord.eval_commutator]

end CEWord

namespace
  TRRecoll

open CEWord

/-- An expanded Hall-tree self-bracket has an empty true residual recollection. -/
noncomputable def tree_commutator_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (child : HallTree (FreeGenerator.{u} d))
    (htree : CEWord.tree factor.word =
      HallTree.commutator child child) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (raw_tree_self
        factor child htree e).symm

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction residuals for reversed basic brackets

If swapping the children of an expanded Hall-tree bracket makes it basic,
the explicit Hall-tree packet evaluates literally to the original reversed
bracket.  Its true concrete reduction residual therefore recollects to the
empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/--
For a factor whose expanded tree is a reversed basic bracket, the explicit
atomic Hall-tree reduction packet evaluates literally to the original factor.
-/
theorem reduction_tree_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      factor.eval e := by
  rw [list_basic_factors]
  rw [htree,
    HallTree.basic_scaled_swap
      left right hswapBasic]
  rw [map_zpow]
  unfold SPFactor.eval SPFactor.wordValue
  rw [← lower_truncation_tree factor.word]
  rw [htree]

/-- The true reduction residual of a reversed basic bracket is trivial. -/
theorem
    raw_tree_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_tree_swap
      factor left right htree hswapBasic e]
  simp

end CEWord

namespace
  TRRecoll

open CEWord

/-- A reversed basic bracket has an empty true residual recollection. -/
noncomputable def tree_swap_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : CEWord.tree factor.word =
      .commutator right left)
    (hswapBasic : (HallTree.commutator left right).IsBasic) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (raw_tree_swap
        factor left right htree hswapBasic e).symm

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction residuals for reversed basic brackets

If swapping the two children of an expanded Hall-tree bracket makes it basic,
all-weight PBW uniqueness and skew-symmetry make its explicit reduction packet
exact.  The corresponding true reduction residual recollects to the empty
higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator (tree left) (tree right)).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicReductionFactors factor) =
      factor.eval e := by
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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic : (HallTree.commutator (tree left) (tree right)).IsBasic)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_reversed_tree
      factor left right hword hswapBasic e]
  simp

end CEWord

namespace
  TRRecoll

open CEWord

/-- A reversed basic expanded bracket has an empty true residual recollection. -/
noncomputable def reversed_tree_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator right left)
    (hswapBasic :
      (HallTree.commutator
        (CEWord.tree left)
        (CEWord.tree right)).IsBasic) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (raw_reversed_tree
        factor left right hword hswapBasic e).symm

/-- A reversed-basic symbolic word has an empty true residual recollection. -/
noncomputable def reversed_basic
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hreversed : CEWord.IsReversedBasic factor.word) :
    TRRecoll
      (n := n) factor :=
  let left := Classical.choose hreversed
  let right := Classical.choose (Classical.choose_spec hreversed)
  let hproperties :=
    Classical.choose_spec (Classical.choose_spec hreversed)
  reversed_tree_basic factor left right hproperties.1 hproperties.2

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction residuals for self-commutators

The expanded Hall tree of a symbolic self-commutator has zero
associated-graded class.  Its explicit reduction packet and its own symbolic
value therefore both evaluate trivially, so the true reduction residual
recollects to the empty higher source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CEWord

universe u

/-- The explicit packet of a symbolic self-commutator evaluates trivially. -/
theorem reduction_factors_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
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
        (tree word) (factor.coefficient.eval e))

/-- The true reduction residual of a symbolic self-commutator is trivial. -/
theorem
    reduction_raw_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicRawSource factor) = 1 := by
  rw [reduction_raw_source,
    reduction_factors_self
      factor word hword e]
  simp [SPFactor.eval,
    SPFactor.wordValue, hword]

end CEWord

namespace
  TRRecoll

open CEWord

/-- A symbolic self-commutator has an empty true residual recollection. -/
noncomputable def word_commutator_self
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (word :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator word word) :
    TRRecoll
      (n := n) factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (reduction_raw_self
        factor word hword e).symm

end
  TRRecoll
end TCTex
end Towers

/-!
# Concrete signed-polynomial Hall-tree residual reduction in weight one

A polynomial Hall word of ordinary weight one is one address. Its expanded
Hall tree is therefore basic, so the concrete residual recollects immediately.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  TRRecoll

open CEWord

/-- A weight-one explicit Hall-tree residual recollects to the empty source. -/
noncomputable def of_weight_one
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = 1) :
    TRRecoll
      (n := n) factor :=
  tree_basic factor (by
    obtain ⟨address, hword⟩ :=
      CWord.atom_weight_one
        HEAddres.weight HEAddres.weight_pos factor.word
          hfactorWeight
    rw [hword]
    simp)

end
  TRRecoll

end TCTex
end Towers

/-!
# Comparing concrete and intrinsic signed-polynomial Hall-factor residuals

The explicit Hall-tree reduction packet and the canonical semantic active Hall
block need not be identified as lists.  Their quotient nevertheless lies one
lower-central stratum higher: both packets agree with the original factor in
the associated-graded layer.

This file packages that comparison as another concrete symbolic residual
source.  Recollecting both concrete sources upward is sufficient to produce
the intrinsic residual-source package consumed by the existing recursive
signed collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- Inverting a list preserves a common symbolic lower support bound. -/
theorem least_inverse_list
    {d lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {source : List (SPFactor H ι)}
    (hsource : WordWeightLeast lowerWeight source) :
    WordWeightLeast lowerWeight (inverseList source) := by
  intro factor hfactor
  rw [inverseList] at hfactor
  rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
  rw [word_neg]
  exact hsource sourceFactor (by simpa using hsourceFactor)

/--
The intrinsic signed-polynomial factor residual starts in the next
lower-central stratum.
-/
theorem active_block_series
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (e : ι → HEFam H) :
    factor.activeBlockValue
        (lowerWeight := lowerWeight) hn H hH e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let X := factor.signedCoordinateRecipes hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hfactorWordMem :
      factor.wordValue (n := n) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.value_lower_series (n := n)
  have hfactorMem :
      factor.eval (n := n) e ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.eval_lower_series (n := n) e
  have hXMem :
      SPFactor.listEval (n := n) e
          (X.weightFactors lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [X.list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        (X.eval e lowerWeight)
  unfold activeBlockValue
    activeNormalValue
  apply inv_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hXMem hfactorMem
  rw [X.list_weight_factors]
  have hXCoordinates :
      normalFormCoordinates hn H hH
          ((H lowerWeight).collectedWeightProduct
            (n := n) (X.eval e lowerWeight)) lowerWeight =
        X.eval e lowerWeight := by
    apply form_coordinates_next
      hn H hH hlowerWeightPos (by omega)
    · exact
        (H lowerWeight).collectedweight_productmem_lowecentseri
          (X.eval e lowerWeight)
    · simp
  rw [hXCoordinates]
  have hfactorCoordinates :
      normalFormCoordinates hn H hH
          (factor.eval (n := n) e) lowerWeight =
        X.eval e lowerWeight := by
    change
      normalFormCoordinates hn H hH
          ((factor.wordValue (n := n)) ^ factor.coefficient.eval e)
            lowerWeight =
        X.eval e lowerWeight
    rw [form_coordinates_zpow
      hn H hH hlowerWeightPos (by omega) _ hfactorWordMem]
    rw [factor.signed_coordinate_recipes
      hn H hH e lowerWeight hlowerWeightPos (by omega)]
    funext i
    simp [zscaledExponentFamily]
    ring
  exact hfactorCoordinates.symm

end SPFactor

namespace CEWord

/--
Raw symbolic comparison source: divide the canonical semantic active Hall
block by the explicit Hall-tree reduction packet.
-/
noncomputable def comparisonRawSource
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    ((factor.signedCoordinateRecipes hn
      (concreteBasicCommutators.{u} d) hH).weightFactors lowerWeight)

/-- Evaluation of the comparison source is explicit packet division. -/
theorem comparison_raw_source
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (comparisonRawSource hn hH factor
          (lowerWeight := lowerWeight)) =
      (SPFactor.listEval e
        (basicReductionFactors factor))⁻¹ *
      SPFactor.listEval e
        ((factor.signedCoordinateRecipes hn
          (concreteBasicCommutators.{u} d) hH).weightFactors
            lowerWeight) := by
  simp [comparisonRawSource,
    SPFactor.list_eval_inverse]

/--
The explicit reduction packet and the canonical semantic active block differ
only in the next lower-central stratum.
-/
theorem
    comparison_raw_series
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (comparisonRawSource hn hH factor
          (lowerWeight := lowerWeight)) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let concretePacket :=
    SPFactor.listEval (n := n) e
      (basicReductionFactors factor)
  let hallNormalPacket :=
    SPFactor.listEval (n := n) e
      ((factor.signedCoordinateRecipes hn
        (concreteBasicCommutators.{u} d) hH).weightFactors lowerWeight)
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      lowerWeight
  have hconcrete :
      concretePacket⁻¹ * factor.eval (n := n) e ∈ K := by
    simpa only [concretePacket, K, hfactorWeight] using
      reduction_inv_series
        factor e
  have hhallNormal :
      hallNormalPacket⁻¹ * factor.eval (n := n) e ∈ K := by
    simpa only [hallNormalPacket, K,
      SPFactor.activeBlockValue,
      SPFactor.activeNormalValue] using
      (factor.active_block_series
        hn (concreteBasicCommutators.{u} d) hH hfactorWeight
          hfactorTruncated e)
  rw [comparison_raw_source]
  change concretePacket⁻¹ * hallNormalPacket ∈ K
  rw [show
    concretePacket⁻¹ * hallNormalPacket =
      (concretePacket⁻¹ * factor.eval (n := n) e) *
        (hallNormalPacket⁻¹ * factor.eval (n := n) e)⁻¹ by
          group]
  exact K.mul_mem hconcrete (K.inv_mem hhallNormal)

/--
Once the next stratum reaches the truncation cutoff, the concrete-to-semantic
comparison source evaluates trivially.
-/
theorem
    comparison_n_succ
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hcutoff : n ≤ lowerWeight + 1)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (comparisonRawSource hn hH factor
          (lowerWeight := lowerWeight)) = 1 := by
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (comparison_raw_series
      hn hH factor hfactorWeight hfactorTruncated e)

end CEWord

open CEWord

/--
Semantic recollection data for the comparison between the concrete reduction
packet and the canonical semantic active Hall block.
-/
structure
    TPRecoll
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (comparisonRawSource hn hH factor
            (lowerWeight := lowerWeight))

namespace
  TPRecoll

/--
At the truncation endpoint, the concrete-to-semantic comparison residual
recollects to the empty higher source.
-/
noncomputable def of_terminal
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hcutoff : n ≤ lowerWeight + 1) :
    TPRecoll
      (lowerWeight := lowerWeight) hn hH factor where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa [SPFactor.listEval] using
      (comparison_n_succ
        hn hH factor hfactorWeight hfactorTruncated hcutoff e).symm

end
  TPRecoll

namespace
  TRRecoll

/--
Compose upward recollections of the concrete factor residual and the
concrete-to-semantic comparison residual into the intrinsic source expected by
the existing recursive signed collector.
-/
noncomputable def intrinsicResidualSource
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (recollection :
      TRRecoll
        (n := n) factor)
    (comparison :
      TPRecoll
        (lowerWeight := lowerWeight) hn hH factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight) :
    TPSrc
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH ι
        factor where
  higherSource :=
    SPFactor.inverseList comparison.higherSource ++
      recollection.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact
        SPFactor.truncated_inverse_list
          comparison.higher_source_truncated x hx
    · exact recollection.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact
        SPFactor.least_inverse_list
          comparison.higher_least_succ x hx
    · simpa only [hfactorWeight] using
        recollection.higher_least_succ x hx
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      SPFactor.list_eval_inverse,
      comparison.list_higher_raw,
      recollection.list_higher_raw,
      comparison_raw_source,
      reduction_raw_source,
      factor.active_raw_source]
    unfold SPFactor.activeBlockValue
      SPFactor.activeNormalValue
    group

end
  TRRecoll
end TCTex
end Towers

/-!
# Signed-polynomial collection from concrete Hall-tree residual sources

The recursive signed collector consumes intrinsic factor residual sources.
Concrete Hall-tree reduction splits each such residual into two operational
sources:

* the explicit atomic reduction residual; and
* the comparison residual between that packet and the semantic active Hall
  block.

This file packages recollection of those two concrete sources as a direct
input to the existing packet-backed collector.  Constructing these recollections
below the terminal cutoff remains the nonterminal symbolic Hall-collection
problem.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollections of the two concrete
Hall-tree residual sources.
-/
structure
    TSBuilde
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u} d n
  basicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) factor
  comparisonResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPRecoll
                (lowerWeight := lowerWeight) hn
                  (fun r hr hrn =>
                    concrete_forms_associated
                      d n r hr hrn)
                  factor

namespace
  TSBuilde

/--
Compose the two concrete recollections into the intrinsic residual-source
builder consumed by restricted-sharp recursion.
-/
noncomputable def restrictedSharpPacket
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TSBuilde.{u}
        (d := d) (n := n) hn) :
    SCBuilda.{u}
      (n := n) hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn) where
  packet := builder.packet
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated :=
    (builder.basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated).intrinsicResidualSource
        (builder.comparisonResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated)
        hfactorWeight

end
  TSBuilde

/--
For canonical Hall families, concrete Hall-tree residual recollections and a
cutoff Hall-Petresco packet construct product coordinate polynomials.
-/
theorem
    commutators_residual_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TSBuilde.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  restr_collect_builder
    hn e builder.restrictedSharpPacket

/--
For canonical Hall families, concrete Hall-tree residual recollections and a
cutoff Hall-Petresco packet construct inverse coordinate polynomials.
-/
theorem
    commutators_inverse_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TSBuilde.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_restr_builder
    hn e builder.restrictedSharpPacket

end TCTex
end Towers

/-!
# Automatic recollection of the concrete-to-semantic comparison source

The comparison between a concrete Hall-tree reduction packet and the
canonical semantic active Hall block is a fixed-weight list of atomic signed
Hall factors.  Restricted-sharp atomic normalization therefore recollects
that comparison into a finite source supported one stratum higher.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace CCRecipe

/-- Every factor in one signed coordinate block is an atom in that layer. -/
theorem atom_weight_factors
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coordinates : CCRecipe H ι)
    {factor : SPFactor H ι}
    (hfactor : factor ∈ coordinates.weightFactors s) :
    ∃ address : HEAddres H,
      factor.word = .atom address ∧ address.weight = s := by
  rw [CCRecipe.weightFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨i, _hi, hfactor⟩
  rcases List.mem_map.mp hfactor with ⟨formula, _hformula, rfl⟩
  exact ⟨⟨s, i⟩, rfl, rfl⟩

end CCRecipe

namespace CEWord

/-- Every factor extracted by concrete Hall-tree reduction is an atom. -/
theorem atom_basic_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors factor) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight = factor.word.weight HEAddres.weight := by
  rw [basicReductionFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact ⟨basicReductionAddress i, rfl, tree_weight factor.word⟩

/-- Inverting the concrete Hall-tree packet preserves its atomic inventory. -/
theorem atom_reduction_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx :
      x ∈
        SPFactor.inverseList
          (basicReductionFactors factor)) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight = factor.word.weight HEAddres.weight := by
  rw [SPFactor.inverseList] at hx
  rcases List.mem_map.mp hx with ⟨sourceFactor, hsourceFactor, rfl⟩
  rcases atom_basic_factors factor
      (by simpa using hsourceFactor) with
    ⟨address, hword, hweight⟩
  exact ⟨address, by simpa using hword, hweight⟩

/-- The comparison source is physically truncated with its original factor. -/
theorem truncated_comparison_source
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (comparisonRawSource hn hH factor
        (lowerWeight := lowerWeight)) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors factor hfactorTruncated) x hx
  · rw [
      (factor.signedCoordinateRecipes hn
        (concreteBasicCommutators.{u} d) hH)
          |>.word_weight_factors hx]
    omega

/-- Every factor in the comparison source is an atom of the active weight. -/
theorem atom_comparison_source
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx :
      x ∈
        comparisonRawSource hn hH factor
          (lowerWeight := lowerWeight)) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧ address.weight = lowerWeight := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases atom_reduction_factors factor hx with
      ⟨address, hword, hweight⟩
    exact ⟨address, hword, hweight.trans hfactorWeight⟩
  · exact
      (factor.signedCoordinateRecipes hn
        (concreteBasicCommutators.{u} d) hH)
        |>.atom_weight_factors hx

end CEWord

namespace
  TPRecoll

open CEWord

/--
Restricted-sharp atomic normalization constructs the finite upward
recollection of the concrete-to-semantic comparison source.
-/
noncomputable def of_atomicNorm
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d)) :
    TPRecoll
      (lowerWeight := lowerWeight) hn hH factor := by
  let source :=
    comparisonRawSource hn hH factor
      (lowerWeight := lowerWeight)
  have hhigherSource :=
    factory.higher_atoms_series
      hn (concreteBasicCommutators.{u} d) hH sharp nextNormalizer source
      (by
        have hfactorPos := factor.word_weight_pos
        omega)
      (by omega)
      (truncated_comparison_source
        hn hH factor hfactorWeight hfactorTruncated)
      (fun x hx =>
        atom_comparison_source
          hn hH factor hfactorWeight hx)
      (fun e =>
        comparison_raw_series
          hn hH factor hfactorWeight hfactorTruncated e)
  let higherSource := hhigherSource.choose
  have hhigherSourceProperties := hhigherSource.choose_spec
  exact
    { higherSource := higherSource
      higher_source_truncated := hhigherSourceProperties.1
      higher_least_succ :=
        hhigherSourceProperties.2.1
      list_higher_raw := hhigherSourceProperties.2.2 }

end
  TPRecoll

end TCTex
end Towers

/-!
# Signed-polynomial collection with automatic comparison recollection

Concrete Hall-tree reduction leaves two apparent higher-source obligations:
the true Hall-tree quotient and the comparison between its atomic packet and
the canonical semantic active Hall block.  The second source is always a
fixed-weight atomic list, so restricted-sharp routing recollects it
automa.

This file exposes the reduced constructor boundary.  A caller supplies only:

* one cutoff Hall-Petresco packet; and
* upward finite recollection of the true concrete Hall-tree residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of the true concrete
Hall-tree residual source.
-/
structure
    TPBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u} d n
  basicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TRRecoll
                (n := n) factor

namespace
  TPBuild

/-- Compile the all-integral packet to an active-stratum correction factory. -/
noncomputable def packetFactoryAt
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TPBuild.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ) :
    TSFtry
      (n := n) (concreteBasicCommutators.{u} d) lowerWeight :=
  (builder.packet.supportedWordFactory
    (WBForm.chooseNormalizerFamily
      (concreteBasicCommutators.{u} d))
    lowerWeight)
    |>.correctionPacketFactory

/--
Construct the signed semantic normalizer directly.  Recursive uses occur only
at strictly larger support weights.
-/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TPBuild.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormal.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn)
        hterminal
  else
    TSNormal.ofInsertionKernel
      { insert := by
          intro ι coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.supportedCoordinateNormalizer
              hn (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight HEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight HEAddres.weight = lowerWeight := by
              omega
            let sharp :
                TSNormala
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteBasicCommutators.{u} d) :=
              TSNormala.ofNormalizerAbove
                (lowerWeight := lowerWeight)
                (fun strongerWeight
                    (_hstronger : lowerWeight < strongerWeight) =>
                  builder.supportedCoordinateNormalizer
                    hn strongerWeight)
            let packetFactory := builder.packetFactoryAt lowerWeight
            let comparison :=
              TPRecoll.of_atomicNorm
                hn hH factor hfactorWeight hfactorTruncated packetFactory sharp
                  nextNormalizer
            let factorTail :=
              ((builder.basicResidual lowerWeight hterminal factor
                hfactorWeight hfactorTruncated).intrinsicResidualSource
                  comparison hfactorWeight).factorExpansion
            let merge :=
              (packetFactory
                |>.coord_sharp_normalizer
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              merge.activeBlockResolution factorTail hcoordinates
                hfactorWeight
            let tail :=
              (packetFactory
                |>.supported_route_normalizer
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (TPResolu.active_block_tail
                hcoordinates hfactorWeight hfactorTruncated block tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  TPBuild

/--
For canonical Hall families, a cutoff packet and true Hall-tree residual
recollections construct product coordinate polynomials.
-/
theorem
    collected_automatic_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TPBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  signed_semantic_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn 1)

/--
For canonical Hall families, a cutoff packet and true Hall-tree residual
recollections construct inverse coordinate polynomials.
-/
theorem
    automatic_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TPBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_data_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn 1)

end TCTex
end Towers

/-!
# Concrete signed-polynomial reduction packets for Jacobi brackets

A Jacobi rewrite preserves the ordinary Hall weight of a symbolic polynomial
factor and does not change its coefficient formula.  This file records the
two descendant factors and proves that the quotient of the original atomic
reduction packet by the two descendant packets lies one lower-central
stratum higher.

This is the collector-facing packet for the surviving Jacobi frontier.  It
also isolates the continuation left after that atomic correction is peeled
from the true factor residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace SPFactor

universe u

/-- Casting a weighted Hall-binomial formula along a target-weight equality preserves evaluation. -/
private theorem cast_binomial_formula
    {d r s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    {ι : Type}
    (h : r = s)
    (formula : WBForm H ι r)
    (e : ι → HEFam H) :
    (cast (congrArg (WBForm H ι) h) formula).eval e =
      formula.eval e := by
  cases h
  rfl

/-- Replace the Hall word of a symbolic factor without changing its coefficient formula. -/
noncomputable def reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight HEAddres.weight =
        factor.word.weight HEAddres.weight) :
    SPFactor H ι where
  word := word
  coefficient :=
    cast
      (congrArg (WBForm H ι) hweight.symm)
      factor.coefficient

@[simp]
theorem word_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight HEAddres.weight =
        factor.word.weight HEAddres.weight) :
    (factor.reword word hweight).word = word :=
  rfl

@[simp]
theorem coefficient_eval_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (word : CWord (HEAddres H))
    (hweight :
      word.weight HEAddres.weight =
        factor.word.weight HEAddres.weight)
    (e : ι → HEFam H) :
    (factor.reword word hweight).coefficient.eval e =
      factor.coefficient.eval e := by
  change
    (cast
      (congrArg (WBForm H ι) hweight.symm)
      factor.coefficient).eval e =
      factor.coefficient.eval e
  rw [cast_binomial_formula hweight.symm factor.coefficient e]

end SPFactor

namespace CEWord

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
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  factor.reword (.commutator (.commutator left right) middle) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)

/-- The negatively signed second Jacobi descendant of `[[left, middle], right]`. -/
noncomputable def jacobiSecondFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  (factor.reword (.commutator (.commutator middle right) left) (by
    rw [hword]
    simp only [CWord.weight_commutator]
    omega)).neg

@[simp]
theorem coefficient_jacobi_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (jacobiFirstFactor factor left middle right hword).coefficient.eval e =
      factor.coefficient.eval e := by
  rw [jacobiFirstFactor, SPFactor.coefficient_eval_reword]

@[simp]
theorem jacobi_second_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (jacobiSecondFactor factor left middle right hword).coefficient.eval e =
      -factor.coefficient.eval e := by
  rw [jacobiSecondFactor, SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem jacobi_first_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    (jacobiFirstFactor factor left middle right hword).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  change
    ((CWord.commutator
        (CWord.commutator left right) middle).weight
        HEAddres.weight) =
      factor.word.weight HEAddres.weight
  rw [hword]
  simp only [CWord.weight_commutator]
  omega

@[simp]
theorem word_jacobi_second
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    (jacobiSecondFactor factor left middle right hword).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  change
    ((CWord.commutator
        (CWord.commutator middle right) left).weight
        HEAddres.weight) =
      factor.word.weight HEAddres.weight
  rw [hword]
  simp only [CWord.weight_commutator]
  omega

/--
Atomic packet residual comparing a Jacobi bracket with its two descendants.
-/
noncomputable def jacobiReductionSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList (basicReductionFactors factor) ++
    basicReductionFactors (jacobiFirstFactor factor left middle right hword) ++
      basicReductionFactors (jacobiSecondFactor factor left middle right hword)

/--
Continuation left after peeling the atomic Jacobi packet from the true factor
residual.  Its evaluation is `A₂⁻¹ * A₁⁻¹ * factor`, where `A₁` and `A₂` are
the two descendant atomic packets.
-/
noncomputable def jacobiContinuationRaw
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
      (basicReductionFactors
        (jacobiSecondFactor factor left middle right hword)) ++
    SPFactor.inverseList
      (basicReductionFactors
        (jacobiFirstFactor factor left middle right hword)) ++
      [factor]

/-- Truncation of the original factor physically truncates its Jacobi packet. -/
theorem truncated_jacobi_reduction
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (jacobiReductionSource factor left middle right hword) := by
  intro x hx
  simp only [jacobiReductionSource, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactor.truncated_inverse_list
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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (jacobiContinuationRaw factor left middle right hword) := by
  intro x hx
  simp only [jacobiContinuationRaw, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with (hx | hx) | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_reduction_factors
          (jacobiSecondFactor factor left middle right hword)
          (by simpa only [word_jacobi_second] using hfactor))
        x hx
  · exact
      SPFactor.truncated_inverse_list
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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiReductionSource factor left middle right hword) *
      SPFactor.listEval e
        (jacobiContinuationRaw factor left middle right hword) =
      SPFactor.listEval e
        (basicRawSource factor) := by
  simp only [jacobiReductionSource, jacobiContinuationRaw,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  group

/--
The continuation is atomic-Jacobi correction division of the original true
factor residual.
-/
theorem
    jacobi_continuation_residual
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiContinuationRaw factor left middle right hword) =
      (SPFactor.listEval e
        (jacobiReductionSource factor left middle right hword))⁻¹ *
        SPFactor.listEval e
          (basicRawSource factor) := by
  rw [←
    jacobi_reduction_continuation
      factor left middle right hword e]
  group

/-- Every factor in the Jacobi packet residual is an atom in the source layer. -/
theorem atom_jacobi_source
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ jacobiReductionSource factor left middle right hword) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight HEAddres.weight := by
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
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiReductionSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.scaled_jacobi_series
      (tree left) (tree middle) (tree right) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword, CWord.weight_commutator,
            CWord.weight_commutator, ← tree_weight, ← tree_weight,
            ← tree_weight]
          exact hfree))
  rw [jacobiReductionSource, SPFactor.listEval_append,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    list_basic_factors, list_basic_factors,
    list_basic_factors]
  rw [coefficient_jacobi_factor,
    jacobi_second_factor]
  simpa only [map_mul, map_inv, tree_commutator,
    jacobiFirstFactor, jacobiSecondFactor,
    SPFactor.word_neg,
    SPFactor.word_reword,
    SPFactor.coefficient_eval_neg,
    SPFactor.coefficient_eval_reword, hword, mul_assoc] using
      hmap

/-- The remaining Jacobi continuation also evaluates one stratum higher. -/
theorem continuation_raw_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiContinuationRaw factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [
    jacobi_continuation_residual
      factor left middle right hword e]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).mul_mem
        (Subgroup.inv_mem _
          (jacobi_reduction_series
            factor left middle right hword e))
        (list_reduction_series
          factor e)

end CEWord

namespace TSFtry

open CEWord

/--
Route the finite atomic Jacobi coordinate correction into a source supported
one stratum higher.
-/
noncomputable def higher_jacobi_raw
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ higherSource :
        List
          (SPFactor
            (concreteBasicCommutators.{u} d) ι),
      SPFactor.IsTruncated n higherSource ∧
        SPFactor.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
              SPFactor.listEval (n := n) e higherSource =
                SPFactor.listEval e
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
  · intro e
    simpa only [hfactorWeight] using
      jacobi_reduction_series
        factor left middle right hword e

end TSFtry
end TCTex
end Towers
