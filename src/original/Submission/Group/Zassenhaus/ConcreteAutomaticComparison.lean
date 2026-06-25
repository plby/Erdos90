import Submission.Group.Zassenhaus.AtomicSourceNormalization
import Submission.Group.Zassenhaus.ReductionComparison

/-!
# Automatic powered concrete-to-semantic comparison recollection

The comparison between a concrete Hall-tree reduction packet and the
canonical semantic active Hall block is a fixed-weight list of atomic
symbolic Hall-power factors. Restricted-sharp atomic normalization therefore
recollects that comparison into a finite source supported one stratum higher.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/-- Every factor in one powered coordinate block is an atom in that layer. -/
theorem atom_weight_factors
    {d inputWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coordinates : CCExpans H inputWeight)
    {factor : SPFactora H inputWeight}
    (hfactor : factor ∈ coordinates.weightFactors s) :
    ∃ address : HEAddres H,
      factor.word = .atom address ∧ address.weight = s := by
  rw [CCExpans.weightFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨i, _hi, hfactor⟩
  refine ⟨⟨s, i⟩, ?_, rfl⟩
  exact
    BCExp.symbolic_power_factors
      (.atom (⟨s, i⟩ : HEAddres H))
        (coordinates.expansion s i) hfactor

end CCExpans

namespace HEWord

/-- Every factor extracted by concrete Hall-tree reduction is an atom. -/
theorem atom_basic_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ basicReductionFactors factor) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight PEAddres.weight := by
  rw [basicReductionFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact ⟨basicReductionAddress i, rfl, tree_weight factor.word⟩

/-- Inverting the concrete Hall-tree packet preserves its atomic inventory. -/
theorem atom_reduction_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx :
      x ∈
        SPFactora.inverseList
          (basicReductionFactors factor)) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧
        address.weight =
          factor.word.weight PEAddres.weight := by
  rw [SPFactora.inverseList] at hx
  rcases List.mem_map.mp hx with ⟨sourceFactor, hsourceFactor, rfl⟩
  rcases atom_basic_factors factor
      (by simpa using hsourceFactor) with
    ⟨address, hword, hweight⟩
  exact ⟨address, by simpa using hword, hweight⟩

/-- The comparison source is physically truncated with its original factor. -/
theorem truncated_comparison_source
    {d n inputWeight lowerWeight : ℕ}
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
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (comparisonRawSource
        hn hH factor lowerWeight) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactora.truncated_inverse_list
        (truncated_reduction_factors factor hfactorTruncated) x hx
  · rw [
      (factor.normalCoordinateExpansions hn
        (concreteBasicCommutators.{u} d) hH)
          |>.word_weight_factors hx]
    omega

/-- Every factor in the comparison source is an atom of the active weight. -/
theorem atom_comparison_source
    {d n inputWeight lowerWeight : ℕ}
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
      factor.word.weight PEAddres.weight = lowerWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx :
      x ∈
        comparisonRawSource
          hn hH factor lowerWeight) :
    ∃ address : HEAddres (concreteBasicCommutators.{u} d),
      x.word = .atom address ∧ address.weight = lowerWeight := by
  rcases List.mem_append.mp hx with hx | hx
  · rcases atom_reduction_factors factor hx with
      ⟨address, hword, hweight⟩
    exact ⟨address, hword, hweight.trans hfactorWeight⟩
  · exact
      (factor.normalCoordinateExpansions hn
        (concreteBasicCommutators.{u} d) hH)
        |>.atom_weight_factors hx

end HEWord

namespace
  TCRecoll

open HEWord

/--
Restricted-sharp atomic normalization constructs the finite upward
recollection of the powered concrete-to-semantic comparison source.
-/
noncomputable def of_atomicNorm
    {d n inputWeight lowerWeight : ℕ}
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
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
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
            (concreteBasicCommutators.{u} d)) :
    TCRecoll
      (lowerWeight := lowerWeight) hn hH factor := by
  let source :=
    comparisonRawSource hn hH factor lowerWeight
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
      (fun q =>
        comparison_raw_series
          hn hH factor hfactorWeight hfactorTruncated q)
  let higherSource := hhigherSource.choose
  have hhigherSourceProperties := hhigherSource.choose_spec
  exact
    { higherSource := higherSource
      higher_source_truncated := hhigherSourceProperties.1
      higher_least_succ :=
        hhigherSourceProperties.2.1
      list_higher_raw := hhigherSourceProperties.2.2 }

end
  TCRecoll

end TCTex
end Submission
