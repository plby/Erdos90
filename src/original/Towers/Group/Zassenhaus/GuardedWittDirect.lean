import Towers.Group.Zassenhaus.RankedResidual
import Towers.Group.Zassenhaus.RestrictedFullCollector

/-!
# Guarded-grid Hall-power input from direct Hall-Witt fixed-packet restarts

Fixed-packet generated structural restarts supply the outer residual factory.
Direct higher Hall-Witt strict-trace sources supply the positive Jacobi packet
recollections.  The resulting normalizer families fill both endpoint
residual-source callbacks of the cutoff-aware guarded-grid collector.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
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
Direct Hall-Witt fixed-packet restart builders supply the cutoff-aware
guarded-grid canonical Hall-power route.
-/
theorem
    collected_restart_builders
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
          TRBuildb.{u}
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
          |>.wittDirectBuilder
          |>.supportedSemanticFamily
            hn hinputWeight hrecipes)

end TCTex
end Towers
