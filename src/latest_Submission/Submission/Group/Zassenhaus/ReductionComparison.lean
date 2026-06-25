import Submission.Group.Zassenhaus.ReductionRecollection

/-!
# Comparing concrete and intrinsic Hall-factor residuals

The explicit Hall-tree reduction packet and the canonical semantic active Hall
block need not be identified as lists.  Their quotient nevertheless lies one
lower-central stratum higher: both packets agree with the original factor in
the associated-graded layer.

This file packages that comparison as another concrete symbolic residual
source.  Recollecting both concrete sources upward is sufficient to produce
the intrinsic residual-source package consumed by the existing recursive
Claim 5 collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactora

/-- Inverting a list preserves a common symbolic lower support bound. -/
theorem least_inverse_list
    {d inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {source : List (SPFactora H inputWeight)}
    (hsource : WordWeightLeast lowerWeight source) :
    WordWeightLeast lowerWeight (inverseList source) := by
  intro factor hfactor
  rw [inverseList] at hfactor
  rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
  rw [word_neg]
  exact hsource sourceFactor (by simpa using hsourceFactor)

end SPFactora

namespace HEWord

open CCExpans

/--
Raw symbolic comparison source: divide the canonical semantic active Hall
block by the explicit Hall-tree reduction packet.
-/
noncomputable def comparisonRawSource
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
    (lowerWeight : ℕ) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList (basicReductionFactors factor) ++
    ((factor.normalCoordinateExpansions hn
      (concreteBasicCommutators.{u} d) hH).weightFactors lowerWeight)

/-- Evaluation of the comparison source is explicit packet division. -/
theorem comparison_raw_source
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
    (lowerWeight q : ℕ) :
    SPFactora.listEval (n := n) q
        (comparisonRawSource
          hn hH factor lowerWeight) =
      (SPFactora.listEval q
        (basicReductionFactors factor))⁻¹ *
      SPFactora.listEval q
        ((factor.normalCoordinateExpansions hn
          (concreteBasicCommutators.{u} d) hH).weightFactors
            lowerWeight) := by
  simp [comparisonRawSource,
    SPFactora.list_eval_inverse]

/--
The explicit reduction packet and the canonical semantic active block differ
only in the next lower-central stratum.
-/
theorem
    comparison_raw_series
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
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (comparisonRawSource
          hn hH factor lowerWeight) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let concretePacket :=
    SPFactora.listEval (n := n) q
      (basicReductionFactors factor)
  let hallNormalPacket :=
    SPFactora.listEval (n := n) q
      ((factor.normalCoordinateExpansions hn
        (concreteBasicCommutators.{u} d) hH).weightFactors lowerWeight)
  let K :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      lowerWeight
  have hconcrete :
      concretePacket⁻¹ * factor.eval (n := n) q ∈ K := by
    simpa only [concretePacket, K, hfactorWeight] using
      reduction_inv_series
        factor q
  have hhallNormal :
      hallNormalPacket⁻¹ * factor.eval (n := n) q ∈ K := by
    simpa only [hallNormalPacket, K,
      activeBlockValue,
      activeNormalValue] using
      (active_block_series
        hn (concreteBasicCommutators.{u} d) hH factor
          hfactorWeight hfactorTruncated q)
  rw [comparison_raw_source]
  change concretePacket⁻¹ * hallNormalPacket ∈ K
  rw [show
    concretePacket⁻¹ * hallNormalPacket =
      (concretePacket⁻¹ * factor.eval (n := n) q) *
        (hallNormalPacket⁻¹ * factor.eval (n := n) q)⁻¹ by
          group]
  exact K.mul_mem hconcrete (K.inv_mem hhallNormal)

/--
Chosen pointwise Hall-normal coordinates of the concrete-to-semantic
comparison source.
-/
noncomputable def
    basicComparisonCoordinates
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
    (lowerWeight q : ℕ) :
    HEFam (concreteBasicCommutators.{u} d) :=
  normalFormCoordinates hn (concreteBasicCommutators.{u} d) hH
    (SPFactora.listEval (n := n) q
      (comparisonRawSource
        hn hH factor lowerWeight))

/--
The chosen pointwise Hall-normal coordinates collect back to the comparison
source value.
-/
theorem
    collected_comparison_coordinates
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
    (lowerWeight q : ℕ) :
    collectedHallProduct (n := n) (concreteBasicCommutators.{u} d)
        (basicComparisonCoordinates
          hn hH factor lowerWeight q) =
      SPFactora.listEval q
        (comparisonRawSource
          hn hH factor lowerWeight) := by
  exact
    collected_form_coordinates hn
      (concreteBasicCommutators.{u} d) hH
      (SPFactora.listEval q
        (comparisonRawSource
          hn hH factor lowerWeight))

/--
Every pointwise Hall-normal coordinate of the comparison source below the next
stratum vanishes.
-/
theorem
    comparison_coordinates_below
    {d n inputWeight lowerWeight s : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (concreteCommutatorsWeight.{u} d t).FormsAssocGradedbasis
              (n := n))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ)
    (hs : 1 ≤ s)
    (hsBelow : s < lowerWeight + 1)
    (hsn : s < n) :
    basicComparisonCoordinates
        hn hH factor lowerWeight q s = 0 := by
  apply
    imp_coordinates_below
      hn (concreteBasicCommutators.{u} d) hH
      (basicComparisonCoordinates
        hn hH factor lowerWeight q)
      (r := lowerWeight + 1)
  · rw [
      collected_comparison_coordinates]
    simpa using
      (comparison_raw_series
        hn hH factor hfactorWeight hfactorTruncated q)
  · exact hs
  · exact hsBelow
  · exact hsn

/--
Once the next stratum reaches the truncation cutoff, the concrete-to-semantic
comparison source evaluates trivially.
-/
theorem
    comparison_n_succ
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
    (hcutoff : n ≤ lowerWeight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (comparisonRawSource
          hn hH factor lowerWeight) = 1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (comparison_raw_series
      hn hH factor hfactorWeight hfactorTruncated q)

end HEWord

open HEWord

/--
Semantic recollection data for the comparison between the concrete reduction
packet and the canonical semantic active Hall block.
-/
structure
    TCRecoll
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
        (concreteBasicCommutators.{u} d) inputWeight) where
  higherSource :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1)
      higherSource
  list_higher_raw :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        SPFactora.listEval q
          (comparisonRawSource
            hn hH factor lowerWeight)

namespace
  TCRecoll

/--
At the truncation endpoint, the concrete-to-semantic comparison residual
recollects to the empty higher source.
-/
noncomputable def of_terminal
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
    (hcutoff : n ≤ lowerWeight + 1) :
    TCRecoll
      (lowerWeight := lowerWeight) hn hH factor where
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
      (comparison_n_succ
        hn hH factor hfactorWeight hfactorTruncated hcutoff q).symm

/--
A concrete comparison recollection delegates directly to an existing
next-stratum semantic normalizer.
-/
theorem exists_normalizedCoordinates
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TCRecoll
        (lowerWeight := lowerWeight) hn hH factor)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight + 1)
        (concreteBasicCommutators.{u} d)) :
    ∃ coordinates :
        CCExpans
          (concreteBasicCommutators.{u} d) inputWeight,
      coordinates.NTBelow (lowerWeight + 1) ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (coordinates.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (comparisonRawSource
                hn hH factor lowerWeight) := by
  rcases normalizer.normalize recollection.higherSource
      recollection.higher_source_truncated
      recollection.higher_least_succ with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨coordinates, hcoordinates, fun q =>
      (heval q).trans (recollection.list_higher_raw q)⟩

end
  TCRecoll

namespace
  TSRecollb

/--
Compose upward recollections of the concrete factor residual and the
concrete-to-semantic comparison residual into the intrinsic source expected by
the existing recursive collector.
-/
noncomputable def intrinsicResidualSource
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (comparison :
      TCRecoll
        (lowerWeight := lowerWeight) hn hH factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight) :
    TSSrc
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor where
  higherSource :=
    SPFactora.inverseList comparison.higherSource ++
      recollection.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact
        SPFactora.truncated_inverse_list
          comparison.higher_source_truncated x hx
    · exact recollection.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact
        SPFactora.least_inverse_list
          comparison.higher_least_succ x hx
    · simpa only [hfactorWeight] using
        recollection.higher_least_succ x hx
  list_higher_raw := by
    intro q
    rw [SPFactora.listEval_append,
      SPFactora.list_eval_inverse,
      comparison.list_higher_raw,
      recollection.list_higher_raw,
      comparison_raw_source,
      reduction_raw_source,
      factor.active_raw_source]
    unfold
      CCExpans.activeBlockValue
      CCExpans.activeNormalValue
    group

end
  TSRecollb
end TCTex
end Submission
