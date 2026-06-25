import Submission.Group.Zassenhaus.SignedLeafWitt
import Submission.Group.Zassenhaus.RestrictedFullCollector

/-!
# Guarded-grid Hall-power input from unrestricted signed-leaf Hall-Witt sources

Fixed-packet generated structural restarts supply the outer residual factory.
Unrestricted signed-leaf Hall-Witt sources supply positive expanded-Jacobi
packet recollections.  The resulting normalizer families fill both endpoint
callbacks of the cutoff-aware guarded-grid collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


universe u

open
  FTOcc
open
  SOAlign
open
  CRLayer
open
  FIBridge
open
  PGSrc
open
  PGSrc.GIDecomp
open
  CCThree
open
  CPSplita

/--
Unrestricted signed-leaf Hall-Witt fixed-packet restart builders supply the
cutoff-aware guarded-grid canonical Hall-power route.
-/
theorem
    forall_restart_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {layer : NRLayer n 1 1}
    (decomposition :
      GIDecomp
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        (decomposition.selectedFullFiber
          |>.signedProfileAssignment))
    (schedule :
      OOScheda.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          LRBuild.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  occ_normalizer_families
    hn decomposition hprofileAlignment schedule lowWeightSource
      lowWeightSupported
      (fun inputWeight hinputWeight =>
        (builders inputWeight hinputWeight)
          |>.leafDirectBuilder
          |>.supportedSemanticFamily
            hn hinputWeight hrecipes)

end TCTex
end Submission
