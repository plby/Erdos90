import Submission.Group.Zassenhaus.ReductionFactors
import Submission.Group.Zassenhaus.SemanticCorrectionDelegation

/-!
# Semantic recollection boundary for concrete Hall-tree reduction

The explicit atomic reduction packet has a raw residual whose value lies one
lower-central stratum higher.  Pointwise Hall normal forms therefore collect
that value using coordinates supported in the higher stratum.

This is deliberately only a semantic boundary theorem.  The chosen pointwise
coordinates are not asserted to be bounded polynomial recipes in the power
parameter.  A universal symbolic collector must still construct that stronger
finite recollection data.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace HEWord

universe u

/--
Chosen pointwise Hall-normal coordinates of the explicit atomic residual
source.
-/
noncomputable def basicNormalCoordinates
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
    (q : ℕ) :
    HEFam (concreteBasicCommutators.{u} d) :=
  normalFormCoordinates hn (concreteBasicCommutators.{u} d) hH
    (SPFactora.listEval (n := n) q
      (basicRawSource factor))

/--
The chosen pointwise Hall-normal coordinates collect back to the explicit raw
residual value.
-/
theorem collected_reduction_coordinates
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
    (q : ℕ) :
    collectedHallProduct (n := n) (concreteBasicCommutators.{u} d)
        (basicNormalCoordinates hn hH factor q) =
      SPFactora.listEval q
        (basicRawSource factor) := by
  exact
    collected_form_coordinates hn
      (concreteBasicCommutators.{u} d) hH
      (SPFactora.listEval q
        (basicRawSource factor))

/--
Every pointwise Hall-normal coordinate of the explicit residual below the next
stratum vanishes.
-/
theorem basic_coordinates_below
    {d n inputWeight s : ℕ}
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
    (q : ℕ)
    (hs : 1 ≤ s)
    (hsBelow :
      s < factor.word.weight PEAddres.weight + 1)
    (hsn : s < n) :
    basicNormalCoordinates hn hH factor q s = 0 := by
  apply
    imp_coordinates_below
      hn (concreteBasicCommutators.{u} d) hH
      (basicNormalCoordinates hn hH factor q)
      (r := factor.word.weight PEAddres.weight + 1)
  · rw [collected_reduction_coordinates]
    simpa using
      list_reduction_series
        factor q
  · exact hs
  · exact hsBelow
  · exact hsn

/--
Once the next residual stratum reaches the truncation cutoff, the explicit raw
residual source evaluates trivially.
-/
theorem
    reduction_raw_n
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (basicRawSource factor) = 1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (list_reduction_series
      factor q)

end HEWord

universe u

namespace
  TSRecollb

open HEWord

/--
At the truncation endpoint, the explicit atomic residual recollects to the
empty higher source.
-/
noncomputable def of_terminal
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1) :
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
      (reduction_raw_n
        factor hcutoff q).symm

/--
A concrete higher-source recollection delegates directly to an existing
next-stratum semantic normalizer.
-/
theorem exists_normalizedCoordinates
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (recollection :
      TSRecollb
        (n := n) factor)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)) :
    ∃ coordinates :
        CCExpans
          (concreteBasicCommutators.{u} d) inputWeight,
      coordinates.NTBelow
          (factor.word.weight PEAddres.weight + 1) ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (coordinates.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (HEWord.basicRawSource
                factor) := by
  rcases normalizer.normalize recollection.higherSource
      recollection.higher_source_truncated
      recollection.higher_least_succ with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨coordinates, hcoordinates, fun q =>
      (heval q).trans (recollection.list_higher_raw q)⟩

end
  TSRecollb
end TCTex
end Submission
