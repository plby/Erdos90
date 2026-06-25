import Submission.Group.Zassenhaus.PolynomialOrbitVocabulary
import Submission.Group.Zassenhaus.SelectedUniformBoundary

/-!
# Claim 5 from retained-transversal occurrence schedules

The retained recipe transversal is already an ordered list of actual recipes
from the conservative finite correction closure.  An occurrence-level Hall
collection schedule proves the all-integral product law for exactly that
selected list.  Consequently it constructs the minimal supported operational
root packet directly: no closure-wide product, shape-fiber interpolation, or
recipe-chunk compression is needed.

This file threads that root packet through intrinsic residual-source
recollection to the quantified Claim 5 input and the Hall-coordinate polynomial
degree bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HACoeff
open
  CTAssigna
open
  ERTransv
open
  PTOcc
open PFSubsti

/--
An occurrence-level retained-transversal schedule is exactly the all-integral
packet law for its selected ordered recipe list.
-/
noncomputable def
    allOccurrenceSchedule
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    TAPkt.{u} d n where
  recipes :=
    recipeCoefficientRecipes n
  listEval_eq :=
    schedule.satisfiesRecipeCoefficient

@[simp]
lemma
    recipes_occurrence_schedule
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    (allOccurrenceSchedule
      schedule).recipes =
        recipeCoefficientRecipes n :=
  rfl

namespace SOPkt

/--
Compile the exact retained-transversal occurrence schedule to the selected root
packet.  Support is automatic because every selected recipe retains finite
closure provenance.
-/
noncomputable def coefficientOccurrenceSchedule
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    SOPkt.{u} d n :=
  retainedClosureRecipes
    (allOccurrenceSchedule
      schedule)
    (by
      intro recipe hrecipe
      exact
        closure_recipes_coefficient
          hrecipe)

@[simp]
lemma recipes_coefficient_occurrence
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    (coefficientOccurrenceSchedule schedule).packet.recipes =
      recipeCoefficientRecipes n :=
  rfl

/-- The selected root packet recovers the established retained-transversal
finite-index trace exactly. -/
lemma coefficient_occurrence_schedule
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    (coefficientOccurrenceSchedule schedule).finiteIndexTrace =
      retainedRecipeCoefficient n := by
  unfold finiteIndexTrace
  unfold coefficientOccurrenceSchedule
  unfold retainedClosureRecipes
  unfold allOccurrenceSchedule
  unfold
    PTRecipe.finIdxAll
  unfold retainedRecipeCoefficient
  congr

/-- Through cutoff four, the explicit class-three occurrence schedule supplies
the selected root packet without any additional support argument. -/
noncomputable def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    SOPkt.{u} d n :=
  coefficientOccurrenceSchedule
    (COSched.n_four hn)

end SOPkt

/--
One retained-transversal occurrence schedule and intrinsic residual-source
recollections for one Hall-power input weight.
-/
structure
    TOBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  schedule :
    COSched.{u} d n
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  TOBuild

/-- Compile the occurrence-schedule builder to the minimal selected-packet
residual-source builder. -/
noncomputable def selectedOccurrenceBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TOBuild
        (n := n) (inputWeight := inputWeight) hn H hH) :
    SOBuild
      (n := n) (inputWeight := inputWeight) hn H hH where
  rootPacket :=
    SOPkt.coefficientOccurrenceSchedule
      builder.schedule
  factorResidualSource :=
    builder.factorResidualSource

end
  TOBuild

namespace TSInput

/--
A supported sourced input, retained-transversal occurrence schedule, and
intrinsic residual recollections construct the Claim 5 coordinate polynomials.
-/
theorem
    transversalOccurrenceBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TOBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordCollectBuilder
    hn H hH hsourceSupported
      builder.selectedOccurrenceBuilder
      hinputWeight

end TSInput

/--
A retained-transversal occurrence schedule and weight-indexed intrinsic
residual recollections construct the complete quantified Claim 5 power input.
-/
theorem
    coord_occ_sources
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (schedule : COSched.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight :=
  forall_occ_sources
    hn H hH
      (SOPkt.coefficientOccurrenceSchedule
        schedule)
      lowWeightSource lowWeightSupported factorResidualSources

/--
A retained-transversal occurrence schedule and intrinsic residual
recollections yield the Hall-coordinate polynomial degree bound.
-/
theorem
    transversal_occurrence_sources
    {d n r s : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta.{u} d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (schedule : COSched.{u} d n)
    (lowWeightSource :
      ∀ (e : HEFam H) (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight) H e)
    (lowWeightSupported :
      ∀ (e : HEFam H) (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (factorResidualSources :
      ∀ (inputWeight : ℕ),
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              ∀ (factor : SPFactora H inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TSSrc
                      (lowerWeight := lowerWeight) hn H hH factor)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    IVMost
      (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
      (s / r) :=
  selected_occurrence_sources
    hn H hH
      (SOPkt.coefficientOccurrenceSchedule
        schedule)
      lowWeightSource lowWeightSupported factorResidualSources
      u hu hr hs hsn i

end TCTex
end Submission
