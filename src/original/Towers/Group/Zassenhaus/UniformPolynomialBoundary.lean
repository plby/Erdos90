import Towers.Group.Zassenhaus.CompatiblePacketRouting
import
  Towers.Group.Zassenhaus.NaturalLiftBoundary
import Towers.Group.Zassenhaus.FixedUniqueRouting

/-!
# Global Hall-power polynomials from an operational uniform packet

The compatible operational collector produces a multiplicity-independent
natural Hall-Petresco recipe list once a uniform normalization is supplied.
The symbolic Hall-power collector additionally needs the signed extension of
that packet and the finite recipe-list inventory used by structural restart.

This file packages those remaining obligations together and connects them to
the fixed-packet Claim 5 boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open BRSpec
open HACoeff
open CSNorm
open OCKern
open TRRoutea
open
  PRRouteb

namespace CSNorm
namespace OCKern

/--
The exact symbolic data still required after compatible operational
collection has produced a uniform natural packet.

The signed extension is logically separate from natural multiplicity
counting.  Principal inventory and duplicate-freeness are recorded explicitly
because they generate the ordered basic split used by transient restart.
-/
structure UPPkt
    {kernel : OCKern}
    {recipes : List BRecipe}
    (uniform : URNorm kernel recipes)
    (d n : ℕ) : Prop where
  lift :
    (uniform.truncatedNaturalPacket d n).AILift
  basic_mem :
    hallPair ∈ recipes
  basic_bidegree_one :
    ∀ R ∈ recipes,
      R.leftDegree = 1 →
        R.rightDegree = 1 →
          R = hallPair
  unique_basic_occurrence :
    ∃ beforeBasic afterBasic : List BRecipe,
      recipes = beforeBasic ++ hallPair :: afterBasic ∧
        hallPair ∉ beforeBasic ∧
          hallPair ∉ afterBasic

namespace UPPkt

/-- The packaged recipe inventory is the principal natural-packet invariant. -/
def principalRecipe
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    {d n : ℕ}
    (packet : UPPkt uniform d n) :
    (uniform.truncatedNaturalPacket d n).PBRecipea where
  basic_mem := packet.basic_mem
  basic_bidegree_one := packet.basic_bidegree_one

/-- The packaged inventory is the unique basic occurrence of the signed lift. -/
def uniqueOccurrence
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    {d n : ℕ}
    (packet : UPPkt uniform d n) :
    packet.lift.truncatedAll.UniqueOccurrence :=
  packet.unique_basic_occurrence

/-- The packaged signed lift supplies the structural-restart ordered split. -/
noncomputable def orderedBasicSplit
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    {d n : ℕ}
    (packet : UPPkt uniform d n) :
    PFSubsti.TAPkt.OBSplit
      packet.lift.truncatedAll :=
  (packet.lift.principalRecipe packet.principalRecipe)
    |>.ordered_unique_pair packet.uniqueOccurrence

end UPPkt
end OCKern
end CSNorm

namespace
  SRCallba

/--
Compile generated restart routing from a compatible operational uniform
packet and its explicit signed symbolic obligations.
-/
noncomputable def routingOperationalUniform
    {d n inputWeight : ℕ}
    {kernel : OCKern}
    {recipes : List BRecipe}
    {uniform : URNorm kernel recipes}
    (packet :
      UPPkt uniform d n)
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (callbacks :
      SRCallba
        d n inputWeight H packet.lift.truncatedAll) :
    TRRoutea
      d n inputWeight H packet.lift.truncatedAll :=
  principalUniqueBasic
    callbacks
      (packet.lift.principalRecipe packet.principalRecipe)
        packet.uniqueOccurrence

end
  SRCallba

namespace
  PRRouteb

/--
Package powered one-layer recollections above the operational uniform packet
restart route.
-/
noncomputable def ofUniformPacket
    {d n inputWeight : ℕ}
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
            packet).fixedActiveFactory) :
    PRRouteb
      d n inputWeight packet.lift.truncatedAll hinputWeight where
  activeRouting :=
    callbacks.routingOperationalUniform packet
  pieces := pieces

end
  PRRouteb

namespace
  SRBuilda

/--
Construct the corrected global Hall-power polynomial builder from a compatible
operational uniform packet and the remaining recursive recollection inputs.
-/
noncomputable def operationalUniform
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n)}
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
    SRBuilda
      (inputWeight := inputWeight) hn hH where
  packet := packet.lift.truncatedAll
  hinputWeight := hinputWeight
  routing :=
    ofUniformPacket
      packet hinputWeight callbacks pieces
  normalizerAbove := normalizerAbove
  cases := cases
  rankDefect := rankDefect

end
  SRBuilda

end TCTex
end Towers
