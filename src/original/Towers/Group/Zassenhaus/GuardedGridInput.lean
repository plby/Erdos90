import Towers.Group.Zassenhaus.RankedResidual
import Towers.Group.Zassenhaus.RestrictedFullCollector

/-!
# Guarded-grid Hall-power input from fixed-packet restarts

Fixed-packet generated structural restart routing supplies the outer
residual factory used by Jacobi-only support recursion.  This file composes
that concrete transient route with the cutoff-aware guarded-grid Hall-power
collector.

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
Fixed-packet generated structural restarts and named forward-Jacobi residuals
supply the cutoff-aware guarded-grid canonical Hall-power route.
-/
theorem
    forall_fixed_builders
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
          TFBuilda.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight :=
  forall_alignment_builders
    hn hrecipes decomposition hprofileAlignment schedule lowWeightSource
      lowWeightSupported
      (fun inputWeight hinputWeight =>
        (builders inputWeight hinputWeight)
          |>.jacobiOnlyBuilder)

end TCTex
end Towers
