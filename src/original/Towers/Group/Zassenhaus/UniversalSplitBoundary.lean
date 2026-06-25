import Towers.Group.Zassenhaus.SignedOrderedBoundary
import Towers.Group.Zassenhaus.Transient

/-!
# Claim 5 from a split of the retained universal raw-source vocabulary

The universal inverse vocabulary is the retained raw-source vocabulary
followed by recursively generated operational corrections.  The correction
suffix is automa a strict outer tail, so it cannot introduce another
principal `basic` recipe.

This file packages a conditional smaller symbolic obligation: an ordered
split of the retained raw-source vocabulary together with the signed lift.  It
derives the full operational principal packet and reaches the Claim 5
coordinate polynomial endpoint.  The occurrence-level raw vocabulary may
contain repeated principal recipes, so a later compression theorem must
justify this split before the adapter can become a universal constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open BRSpec
open HACoeff
open URVocabu
open CSNorm

namespace CSNorm
namespace OCKern

/--
The signed symbolic data needed above the universal operational vocabulary
after recursive operational corrections have been separated as a strict
tail.
-/
structure UUPkt
    {kernel : OCKern}
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (uniform :
      URNorm kernel
        (recipes n leftWeight rightWeight hleftWeight hrightWeight))
    (d truncation : ℕ) where
  lift :
    (uniform.truncatedNaturalPacket d truncation).AILift
  sourceSplit :
    SBSplit n leftWeight rightWeight

namespace UUPkt

/--
Extend the retained raw-source split through every recursive operational
correction.
-/
noncomputable def orderedBasicSplit
    {kernel : OCKern}
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {uniform :
      URNorm kernel
        (recipes n leftWeight rightWeight hleftWeight hrightWeight)}
    {d truncation : ℕ}
    (packet : UUPkt uniform d truncation) :
    packet.lift.truncatedAll.OBSplit :=
  packet.sourceSplit.orderedSplit rfl

/--
Compile the reduced raw-source obligation into the post-compression ordered
packet interface.
-/
noncomputable def uniformOrderedPacket
    {kernel : OCKern}
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {uniform :
      URNorm kernel
        (recipes n leftWeight rightWeight hleftWeight hrightWeight)}
    {d truncation : ℕ}
    (packet : UUPkt uniform d truncation) :
    URPkt uniform d truncation where
  lift := packet.lift
  split := packet.orderedBasicSplit

/--
Compile the reduced raw-source obligation into the full principal packet used
by structural restart.
-/
noncomputable def uniformPrincipalPacket
    {kernel : OCKern}
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {uniform :
      URNorm kernel
        (recipes n leftWeight rightWeight hleftWeight hrightWeight)}
    {d truncation : ℕ}
    (packet : UUPkt uniform d truncation) :
    UPPkt uniform d truncation :=
  packet.uniformOrderedPacket.uniformPrincipalPacket

end UUPkt
end OCKern
end CSNorm

open OCKern

namespace TSInput

/--
A signed universal operational packet and an ordered split of its retained
raw-source vocabulary construct the Claim 5 coordinate polynomials directly.
-/
theorem operationalUniversalPacket
    {d n inputWeight leftWeight rightWeight : ℕ}
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
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {uniform :
      URNorm kernel
        (recipes n leftWeight rightWeight hleftWeight hrightWeight)}
    (packet :
      UUPkt uniform d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.lift.truncatedAll)
    (pieces :
      PPFtry
        d n inputWeight packet.lift.truncatedAll hinputWeight
          (callbacks.routingOperationalUniform
            packet.uniformPrincipalPacket).fixedActiveFactory)
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
  input.operationalUniformPacket
    hn hsourceSupported packet.uniformPrincipalPacket hinputWeight
      callbacks pieces normalizerAbove cases rankDefect

end TSInput

end TCTex
end Towers
