import
  Towers.Group.Zassenhaus.UniformCoordinateData

/-!
# Claim 5 from a signed ordered fixed recipe packet

Operational collection and shape-block compression must ultimately produce a
fixed multiplicity-independent recipe list.  Transient structural restart
does not need that list to be globally duplicate-free: it needs a signed lift
and one ordered split around the principal `basic` recipe, with strict tails
on both sides.

This file records that post-compression interface and composes it with the
operational Claim 5 coordinate-polynomial endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff
open BRSpec
open CSNorm

namespace FNPkt.TNPkt

/--
A signed extension of one fixed natural packet together with the ordered
principal split consumed by transient structural restart.

Repeated nonbasic recipes are permitted on either strict tail.
-/
structure SBLift
    {d n : ℕ}
    (packet :
      FNPkt.TNPkt.{u}
        d n) where
  lift :
    packet.AILift
  split :
    lift.truncatedAll.OBSplit

namespace SBLift

/-- Forget the ordered tails while retaining principal signed inventory. -/
def principalRecipe
    {d n : ℕ}
    {naturalPacket :
      FNPkt.TNPkt.{u}
        d n}
    (packet : SBLift naturalPacket) :
    packet.lift.truncatedAll.PBRecipea :=
  packet.split.principalRecipe

/-- The ordered split contains exactly one principal `basic` occurrence. -/
def uniqueOccurrence
    {d n : ℕ}
    {naturalPacket :
      FNPkt.TNPkt.{u}
        d n}
    (packet : SBLift naturalPacket) :
    packet.lift.truncatedAll.UniqueOccurrence :=
  packet.split.uniqueOccurrence

end SBLift
end FNPkt.TNPkt

namespace CSNorm
namespace OCKern

/--
The post-compression symbolic packet above one compatible operational
normalization.
-/
abbrev URPkt
    {kernel : OCKern}
    {recipes : List BRecipe}
    (uniform : URNorm kernel recipes)
    (d n : ℕ) :=
  FNPkt.TNPkt.SBLift
    (uniform.truncatedNaturalPacket d n)

namespace URPkt

/--
Compile an ordered signed fixed recipe packet into the explicit principal
inventory interface used by existing operational structural-restart routing.
-/
def uniformPrincipalPacket
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    {d n : ℕ}
    (packet : URPkt uniform d n) :
    UPPkt uniform d n where
  lift := packet.lift
  basic_mem := packet.principalRecipe.basic_mem
  basic_bidegree_one :=
    packet.principalRecipe.basic_bidegree_one
  unique_basic_occurrence :=
    packet.uniqueOccurrence

end URPkt
end OCKern
end CSNorm

open OCKern

namespace TSInput

/--
A signed ordered fixed recipe packet and the remaining recursive recollection
data construct the Claim 5 coordinate polynomials directly.
-/
theorem coordinateOperationalPacket
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
      URPkt uniform d n)
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
