import
  Submission.Group.Zassenhaus.UniformPolynomialBoundary

/-!
# Global Hall-power coordinate polynomials from an operational uniform packet

The operational uniform-packet boundary constructs the corrected fixed-packet
collection builder.  This file composes that builder with the final Claim 5
coordinate-polynomial endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open BRSpec
open HACoeff
open CSNorm
open OCKern
open SRBuilda

namespace TSInput

/--
A compatible operational uniform packet, its signed symbolic inventory, and
the remaining recursive recollection data construct the Claim 5 coordinate
polynomials directly.
-/
theorem operationalUniformPacket
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    (packet :
      UPPkt uniform d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.lift.truncatedAll)
    (pieces :
      PPFtry
        d n inputWeight packet.lift.truncatedAll hinputWeight
          (callbacks.routingOperationalUniform
            packet).fixedActiveFactory)
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect)
    (rankDefect :
      ∀ _factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight,
        ℕ) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.coordRestartBuilder
    hn hsourceSupported
      (operationalUniform
        packet hinputWeight callbacks pieces normalizerAbove cases rankDefect)
      hinputWeight

end TSInput

end TCTex
end Submission
