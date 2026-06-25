import Submission.Group.Zassenhaus.InverseTrace
import Submission.Group.Zassenhaus.RestrictedFiniteClosure

/-!
# Claim 5 from a canonical uniform signed inverse-trace packet

A genuine inverse-history scheduler that normalizes to the canonical
finite-closure recipe inventory supplies the summed signed-profile packet
consumed by the restricted-sharp Claim 5 route.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open ITSched
open ITSched.PPScheda
open
  ACAlign

namespace TSInput

/--
A canonical uniform signed inverse-trace packet, singleton recollections, and
graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem
    coordinateUniformPacket
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : PPScheda}
    (packet :
      USPkt.{u}
        kernel (canonicalRecipes n 1 1) d n)
    {signedBlockKernel :
      OCShape}
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
  coordPolyAssignment
    hn H hH (kernel := signedBlockKernel)
      (satisfies_recipe_uniform
        packet)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission
