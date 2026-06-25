import Submission.Group.Zassenhaus.InverseTrace
import
  Submission.Group.Zassenhaus.NaturalLiftBoundary

/-!
# Global Hall-power polynomials from a closed inverse-trace schedule

Closed inverse-history schedules produce exact natural-multiplicity
expansions.  A uniform normalization and its signed lift expose one fixed
Hall-Petresco packet for symbolic repeated-power collection.

This file connects that genuine schedule route to the fixed-packet structural
restart boundary and hence to the final Claim 5 coordinate polynomials.  The
remaining principal-inventory and recursive recollection obligations stay
explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open ITSched
open ITSched.PPScheda

namespace
  SRCallba

/--
Compile generated restart routing from one uniform signed inverse-trace
schedule packet.
-/
noncomputable def routingDataUniform
    {d n inputWeight : ℕ}
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : USPkt.{u} kernel recipes d n)
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (callbacks :
      SRCallba
        d n inputWeight H packet.truncatedAll)
    (principal :
      (packet.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hnodup : recipes.Nodup) :
    TRRoutea
      d n inputWeight H packet.truncatedAll :=
  callbacks.routingNaturalLift packet.lift principal hnodup

end
  SRCallba

namespace
  PRRouteb

/--
Package powered one-layer recollections above one uniform signed inverse-trace
schedule packet.
-/
noncomputable def uniformPacketRouting
    {d n inputWeight : ℕ}
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : USPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.truncatedAll)
    (principal :
      (packet.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hnodup : recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight packet.truncatedAll hinputWeight
          (callbacks.routingDataUniform
            packet principal hnodup).fixedActiveFactory) :
    PRRouteb
      d n inputWeight packet.truncatedAll hinputWeight where
  activeRouting :=
    callbacks.routingDataUniform
      packet principal hnodup
  pieces := pieces

end
  PRRouteb

open
  PRRouteb

namespace
  SRBuilda

/--
Construct the corrected global Hall-power polynomial builder from one uniform
signed inverse-trace schedule packet and recursive recollection inputs.
-/
noncomputable def inverseUniformSigned
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : USPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.truncatedAll)
    (principal :
      (packet.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hnodup : recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight packet.truncatedAll hinputWeight
          (callbacks.routingDataUniform
            packet principal hnodup).fixedActiveFactory)
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
    SRBuilda
      (inputWeight := inputWeight) hn hH where
  packet := packet.truncatedAll
  hinputWeight := hinputWeight
  routing :=
    uniformPacketRouting
      packet hinputWeight callbacks principal hnodup pieces
  normalizerAbove := normalizerAbove
  cases := cases
  rankDefect := rankDefect

end
  SRBuilda

open
  SRBuilda

namespace TSInput

/--
A uniform signed inverse-trace schedule packet and recursive recollection data
construct the Claim 5 coordinate polynomials directly.
-/
theorem uniformSignedPacket
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
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : USPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.truncatedAll)
    (principal :
      (packet.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hnodup : recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight packet.truncatedAll hinputWeight
          (callbacks.routingDataUniform
            packet principal hnodup).fixedActiveFactory)
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
      (inverseUniformSigned
        packet hinputWeight callbacks principal hnodup pieces
          normalizerAbove cases rankDefect)
      hinputWeight

end TSInput

end TCTex
end Submission
