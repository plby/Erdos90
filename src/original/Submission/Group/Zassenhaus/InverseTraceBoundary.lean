import
  Submission.Group.Zassenhaus.InverseUniformBoundary
import Submission.Group.Zassenhaus.FixedUniqueRouting

/-!
# Claim 5 from an ordered signed inverse-trace schedule packet

A uniform signed inverse-trace packet need not have a globally duplicate-free
recipe list.  Transient structural restart only needs one ordered split around
the principal `basic` recipe; repeated nonbasic recipes may remain on either
strict tail.

This file records that sharper schedule-facing interface and composes it with
the fixed-packet Claim 5 endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open ITSched
open ITSched.PPScheda

namespace ITSched
namespace PPScheda

/--
A uniform signed inverse-trace packet together with the ordered principal
split consumed by transient structural restart.

Repeated nonbasic recipes are permitted on either strict tail.
-/
structure URPkt
    (kernel : PPScheda)
    (recipes : List BRecipe)
    (d n : ℕ) where
  signed :
    USPkt.{u} kernel recipes d n
  split :
    signed.truncatedAll.OBSplit

namespace URPkt

/--
Attach the sharper ordered split to a signed inverse-trace packet from the
exact unique-principal inventory condition.
-/
noncomputable def principalUniqueBasic
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (signed : USPkt.{u} kernel recipes d n)
    (principal :
      (signed.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hunique :
      signed.truncatedAll.UniqueOccurrence) :
    URPkt.{u} kernel recipes d n where
  signed := signed
  split :=
    (signed.lift.principalRecipe principal)
      |>.ordered_unique_pair hunique

/--
A duplicate-free signed inverse-trace packet supplies the ordered split as a
special case.
-/
noncomputable def principalNodup
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (signed : USPkt.{u} kernel recipes d n)
    (principal :
      (signed.uniform.truncatedNaturalPacket d n).PBRecipea)
    (hnodup : recipes.Nodup) :
    URPkt.{u} kernel recipes d n where
  signed := signed
  split :=
    signed.lift.split_principal_nodup principal hnodup

/-- The ordered split retains the signed packet's principal inventory. -/
def principalRecipe
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (packet : URPkt.{u} kernel recipes d n) :
    packet.signed.truncatedAll.PBRecipea :=
  packet.split.principalRecipe

/-- The ordered split contains exactly one principal `basic` occurrence. -/
def uniqueOccurrence
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (packet : URPkt.{u} kernel recipes d n) :
    packet.signed.truncatedAll.UniqueOccurrence :=
  packet.split.uniqueOccurrence

end URPkt
end PPScheda
end ITSched

open
  TRRoutea

namespace
  SRCallba

/--
Compile generated restart routing from one ordered signed inverse-trace
schedule packet.
-/
noncomputable def routingUniformPacket
    {d n inputWeight : ℕ}
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : URPkt.{u} kernel recipes d n)
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (callbacks :
      SRCallba
        d n inputWeight H packet.signed.truncatedAll) :
    TRRoutea
      d n inputWeight H packet.signed.truncatedAll :=
  principalUniqueBasic
    callbacks packet.principalRecipe packet.uniqueOccurrence

end
  SRCallba

namespace
  PRRouteb

/--
Package powered one-layer recollections above one ordered signed inverse-trace
schedule packet.
-/
noncomputable def inverseUniformRouting
    {d n inputWeight : ℕ}
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (packet : URPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.signed.truncatedAll)
    (pieces :
      PPFtry
        d n inputWeight packet.signed.truncatedAll
          hinputWeight
            (callbacks.routingUniformPacket
              packet).fixedActiveFactory) :
    PRRouteb
      d n inputWeight packet.signed.truncatedAll hinputWeight where
  activeRouting :=
    callbacks.routingUniformPacket packet
  pieces := pieces

end
  PRRouteb

open
  PRRouteb

namespace
  SRBuilda

/--
Construct the corrected global Hall-power polynomial builder from one ordered
signed inverse-trace schedule packet and recursive recollection inputs.
-/
noncomputable def inverseUniformPacket
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
    (packet : URPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.signed.truncatedAll)
    (pieces :
      PPFtry
        d n inputWeight packet.signed.truncatedAll
          hinputWeight
            (callbacks.routingUniformPacket
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
    SRBuilda
      (inputWeight := inputWeight) hn hH where
  packet := packet.signed.truncatedAll
  hinputWeight := hinputWeight
  routing :=
    inverseUniformRouting
      packet hinputWeight callbacks pieces
  normalizerAbove := normalizerAbove
  cases := cases
  rankDefect := rankDefect

end
  SRBuilda

open
  SRBuilda

namespace TSInput

/--
An ordered signed inverse-trace schedule packet and recursive recollection data
construct the Claim 5 coordinate polynomials directly.
-/
theorem dataUniformPacket
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
    (packet : URPkt.{u} kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          packet.signed.truncatedAll)
    (pieces :
      PPFtry
        d n inputWeight packet.signed.truncatedAll
          hinputWeight
            (callbacks.routingUniformPacket
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
      (inverseUniformPacket
        packet hinputWeight callbacks pieces normalizerAbove cases rankDefect)
      hinputWeight

end TSInput

end TCTex
end Submission
