import Towers.Group.Zassenhaus.FamilyOperationalCompatible
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary

/-!
# Claim 5 from occurrence-level retained-transversal schedules

The arbitrary-cutoff retained recipe-product law is equivalent to an
occurrence-level Hall collection schedule.  The residual-aware operational
route already compiles that product law to the coordinate-polynomial package
required by Claim 5.

This file exposes the scheduler-facing composition directly.  A future
symbolic Hall collector can construct an occurrence schedule without passing
through the intermediate recipe-product proposition explicitly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace COAdapt

universe u

open
  PRPolysa
open
  SAPres
open
  CCAdapta
open
  RCAdapt
open
  ENStab
open
  ERTransv
open
  ESLift
open
  PTOcc

/--
For the repaired aggregate-presentation residual-aware route, constructing an
occurrence-level retained-transversal collector is equivalent to supplying the
natural endpoint alignment and its all-integral signed lift.
-/
theorem
    occ_alignment_lift
    {d n : ℕ}
    (kernel :
      CARecoll) :
    COSched.{u} d n ↔
      ∃ halignment :
          SatisfiesOccurrenceAlignment.{u}
            (d := d) (by simp) (by simp)
              (retainedRecipeCoefficient n),
        OccurrenceAllLift
          (shapeAggregatedSorted
            kernel)
          (retainedRecipeCoefficient n) halignment :=
  (COSched.satisfies_occ_schedule
    (d := d) (n := n)).symm.trans
    (satisfies_alignment_all
      kernel)

/--
For the smaller per-grid-cancellation facade, occurrence-level retained
collection is equivalent to the same endpoint alignment and signed lift.
-/
theorem
    occ_alignment_all
    {d n : ℕ}
    (kernel :
      OCSorted) :
    COSched.{u} d n ↔
      ∃ halignment :
          SatisfiesOccurrenceAlignment.{u}
            (d := d) (by simp) (by simp)
              (retainedRecipeCoefficient n),
        OccurrenceAllLift
          (shapeBlockSorted kernel)
          (retainedRecipeCoefficient n) halignment :=
  (COSched.satisfies_occ_schedule
    (d := d) (n := n)).symm.trans
    (alignment_all_lift
      kernel)

namespace TSInput

/--
An occurrence-level retained-transversal schedule instantiates Claim 5 through
the repaired aggregate-presentation residual-aware route.
-/
theorem
    aggregatedPresentationSorted
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      CARecoll)
    (schedule :
      COSched.{u} d n)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  RCAdapt.TSInput.coordPresentationOcc
    hn H hH kernel schedule.satisfiesRecipeCoefficient
      input hsourceSupported factorNormalization hinputWeight

/--
An occurrence-level retained-transversal schedule instantiates Claim 5 through
the smaller per-grid-cancellation facade.
-/
theorem
    sortedOccurrenceSchedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      OCSorted)
    (schedule :
      COSched.{u} d n)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  RCAdapt.TSInput.coordSortedOcc
    hn H hH kernel schedule.satisfiesRecipeCoefficient
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end COAdapt
end TCTex
end Towers
