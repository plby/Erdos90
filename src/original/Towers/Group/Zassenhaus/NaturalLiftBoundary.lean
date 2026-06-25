import Towers.Group.Zassenhaus.Polynomial
import
  Towers.Group.Zassenhaus.FixedRestartBoundary

/-!
# Global Hall-power polynomials from a signed lift of a natural packet

Claim 8 first exposes one cutoff-specific Hall-Petresco recipe list with a
uniform natural-multiplicity identity, then asks for its signed extension.
The Hall-power collector consumes the resulting all-integral packet.

This file transports principal-recipe inventory and duplicate-freeness across
that signed lift, compiles fixed-packet structural restart callbacks, and
constructs the global Claim 5 polynomial builder.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace FNPkt.TNPkt

open BRSpec

/--
A uniform natural packet contains the principal basic recipe and no other
recipe of bidegree `(1, 1)`.
-/
structure PBRecipea
    {d n : ℕ}
    (packet :
      FNPkt.TNPkt.{u}
        d n) : Prop where
  basic_mem :
    hallPair ∈ packet.recipes
  basic_bidegree_one :
    ∀ R ∈ packet.recipes,
      R.leftDegree = 1 →
        R.rightDegree = 1 →
          R = hallPair

namespace AILift

/-- Principal recipe inventory is preserved by the signed lift. -/
def principalRecipe
    {d n : ℕ}
    {packet :
      FNPkt.TNPkt.{u}
        d n}
    (lift : packet.AILift)
    (principal : packet.PBRecipea) :
    PFSubsti.TAPkt.PBRecipea
      lift.truncatedAll where
  basic_mem := principal.basic_mem
  basic_bidegree_one :=
    principal.basic_bidegree_one

/--
A duplicate-free natural packet with a signed lift supplies the ordered basic
split used by transient structural restart routing.
-/
noncomputable def split_principal_nodup
    {d n : ℕ}
    {packet :
      FNPkt.TNPkt.{u}
        d n}
    (lift : packet.AILift)
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup) :
    PFSubsti.TAPkt.OBSplit
      lift.truncatedAll :=
  (lift.principalRecipe principal).ordered_split_nodup hnodup

end AILift
end FNPkt.TNPkt

namespace
  SRCallba

/--
Compile structural restart callbacks for a signed lift of one natural packet.
The ordered split is generated from recipe-list invariants.
-/
noncomputable def routingNaturalLift
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      FNPkt.TNPkt.{u}
        d n}
    (lift : packet.AILift)
    (callbacks :
      SRCallba
        d n inputWeight H lift.truncatedAll)
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup) :
    TRRoutea
      d n inputWeight H lift.truncatedAll :=
  TRRoutea.principalNodup
    callbacks (lift.principalRecipe principal) hnodup

end
  SRCallba

namespace
  PRRouteb

/--
Package the powered one-layer recollections above structural callbacks for a
signed lift of one natural packet.
-/
noncomputable def naturalPacketLift
    {d n inputWeight : ℕ}
    {packet :
      FNPkt.TNPkt.{u}
        d n}
    (lift : packet.AILift)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          lift.truncatedAll)
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight lift.truncatedAll hinputWeight
          (callbacks.routingNaturalLift
            lift principal hnodup).fixedActiveFactory) :
    PRRouteb
      d n inputWeight lift.truncatedAll hinputWeight where
  activeRouting :=
    callbacks.routingNaturalLift lift principal hnodup
  pieces := pieces

end
  PRRouteb

namespace
  SRBuilda

/--
Construct the corrected global Hall-power polynomial builder from one uniform
natural packet, its signed lift, and fixed-packet recursive routing data.
-/
noncomputable def naturalPacketLift
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
    {packet :
      FNPkt.TNPkt.{u}
        d n}
    (lift : packet.AILift)
    (hinputWeight : 0 < inputWeight)
    (callbacks :
      SRCallba
        d n inputWeight (concreteBasicCommutators.{u} d)
          lift.truncatedAll)
    (principal : packet.PBRecipea)
    (hnodup : packet.recipes.Nodup)
    (pieces :
      PPFtry
        d n inputWeight lift.truncatedAll hinputWeight
          (callbacks.routingNaturalLift lift principal hnodup
            ).fixedActiveFactory)
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
  packet := lift.truncatedAll
  hinputWeight := hinputWeight
  routing :=
    PRRouteb.naturalPacketLift
      lift hinputWeight callbacks principal hnodup pieces
  normalizerAbove := normalizerAbove
  cases := cases
  rankDefect := rankDefect

end
  SRBuilda

end TCTex
end Towers
