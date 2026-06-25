import Submission.Group.Zassenhaus.CorrectionClosureVocabulary
import Submission.Group.Zassenhaus.RestrictedSharp

/-!
# Claim 5 from finite-correction-closure signed-block stabilization

The conservative finite correction closure gives an unconditional finite
support universe for every truncated concrete operational packet.  Once one
ordered closure-supported packet is shown to stabilize those local packets
and receives its all-integral lift, the existing restricted-sharp singleton
collector constructs the Claim 5 coordinate polynomials.

This file exposes that direct corrected boundary.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open CCTrunc
open UNPkt
open
  UCSuppor
open
  UCAll

namespace
  SSBuilda

/--
A closure-supported stabilized ordered packet supplies the generic concrete
stabilization builder consumed by the existing signed-block Claim 5 route.
-/
def closureStabilizedPacket
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {kernel : OCShape}
    (packet :
      SBPkt.{u} kernel d n 1 1)
    (lift :
      packet.truncNaturalPacket.AILift)
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
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH kernel packet.packets where
  stabilization :=
    packet.truncatedNaturalStabilization
  lift :=
    lift
  factorNormalization :=
    factorNormalization

end
  SSBuilda

namespace TSInput

open
  SSBuilda

/--
Finite correction-closure stabilization, its signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    coordinateClosureStabilization
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (packet :
      SBPkt.{u} kernel d n 1 1)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (lift :
      packet.truncNaturalPacket.AILift)
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
  input.sharpStabilizationBuilder
    hn H hH hsourceSupported
      (closureStabilizedPacket
        packet lift factorNormalization)
      hinputWeight

/--
The primary all-integral closure-supported packet boundary constructs Claim 5
data directly; its natural stabilization and signed lift are automatic.
-/
theorem
    coordinateAllPacket
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (packet :
      TAPkta.{u} d n 1 1)
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
  input.coordinateClosureStabilization
    hn H hH
      (packet.stabilizedBlockPacket kernel)
      hsourceSupported (packet.allIntegralLift kernel)
      factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from explicit class-three finite-closure packets

At cutoff at most four, the finite-correction-closure signed-block packet is
explicit.  Its raw inverse-trace triple words evaluate to the conventional
class-three Hall-Petresco corrections, so the corrected restricted-sharp
collector constructs the Claim 5 coordinate polynomials without a separate
stabilization input.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open CTPacket

namespace TSInput

/--
For cutoff at most four, the explicit finite-correction-closure packet,
singleton recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem coordinateClosureThree
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel) (n_four (d := d) hn4)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from finite-correction-closure signed-block stabilization

The finite correction closure gives an unconditional support universe for
every concrete operational packet.  The remaining global combinatorial law is
stabilization: choose one fixed ordered packet in that universe whose
evaluations agree with all multiplicity-dependent concrete packets.

This file feeds such a stabilized closure packet into the powered
restricted-sharp Claim 5 adapter.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open
  CSAggreg
open
  CCTrunc
open
  CFSubsti
open
  UCOrdere

namespace
  SSBuilda

/--
Closure-supported stabilization supplies the generic concrete signed-block
builder consumed by powered restricted-sharp recollection.
-/
def stabilizedClosurePacket
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {kernel : OCShape}
    (packet :
      SCPkt.{u}
        kernel d n 1 1)
    (lift :
      packet.truncNaturalPacket.AILift)
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
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH kernel packet.packets where
  stabilization :=
    packet.truncatedNaturalStabilization
  lift :=
    lift
  factorNormalization :=
    factorNormalization

end
  SSBuilda

namespace TSInput

open
  SSBuilda

/--
An explicitly ordered closure-supported cutoff stabilization, its signed
extension, singleton recollections, and graded Hall bases construct the
integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    sharpStabilizedPacket
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (packet :
      SCPkt.{u}
        kernel d n 1 1)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (lift :
      packet.truncNaturalPacket.AILift)
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
  input.sharpStabilizationBuilder
    hn H hH hsourceSupported
      (stabilizedClosurePacket
        packet lift factorNormalization)
      hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from explicit low-cutoff finite-closure packets

At cutoff at most three, the finite-correction-closure signed-block packet is
explicit.  Feeding that packet into the corrected restricted-sharp collector
constructs the Claim 5 coordinate polynomials without a separate stabilization
input.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open CLPacket

namespace TSInput

/--
For cutoff at most three, the explicit finite-correction-closure packet,
singleton recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem coordinateLowCutoff
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn3 : n ≤ 3)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel) (n_three (d := d) hn3)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from a finite-closure recipe packet

An all-integral ordered recipe packet is a particularly concrete way to
construct the closure-supported signed-profile packet.  When every recipe in
the packet lies in the conservative finite correction closure, the positive
signed-block adapter supplies the corrected Claim 5 boundary directly.

This file exposes that recipe-level constructor path.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open UCSuppor
open UCVocabu
open
  UCAdapt

namespace TSInput

/--
A closure-supported all-integral recipe packet, singleton recollections, and
graded Hall bases construct the Claim 5 coordinate polynomials.
-/
theorem coordinateClosurePacket
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hsupport :
      ∀ recipe ∈ packet.recipes,
        recipe ∈ correctionClosureRecipes n 1 1)
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel)
      (truncAllPacket
        packet (by simp) (by simp)
          (fun recipe hrecipe =>
            shape_vocabulary_recipes
              (hsupport recipe hrecipe)))
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from a universal finite-closure profile assignment

The conservative finite correction closure contains every below-cutoff word
emitted by the genuine operational collector.  A universal signed-profile
assignment on that finite skeleton compiles to the all-integral ordered packet
required by the corrected Claim 5 boundary.

This file exposes the resulting direct constructor path.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open
  FCAssign

namespace TSInput

/--
A universal signed-profile assignment on the finite correction closure,
singleton recollections, and graded Hall bases construct the Claim 5
coordinate polynomials.
-/
theorem
    closureProfileAssignment
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (assignment :
      UPAssign.{u} n 1 1)
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel)
      (assignment.truncAllPacket d
        (by simp) (by simp))
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from recursive finite-closure profile builders

A recursive finite-closure profile kernel removes the need to assign formulas
globally by hand: source formulas and binary correction builders construct the
profile assignment by weighted Hall-degree induction.  Once the ordered
all-integral product law is supplied, the existing finite-closure adapter
constructs the Claim 5 coordinate polynomials.

This file exposes that direct constructor path.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open CSAggreg
open
  CRAssign
open
  FCAssign

namespace TSInput

/--
Recursive source and correction profile builders, their remaining ordered
product identity, singleton recollections, and graded Hall bases construct the
Claim 5 coordinate polynomials.
-/
theorem
    recursiveProfileAssignment
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (recursiveKernel :
      RPKern n 1 1)
    (listEval_eq :
      ∀ {G : Type u} [Group G]
        (left right : G)
        (leftExponent rightExponent : ℤ),
          (((recursiveKernel.signedProfileAssignment
              (by simp) (by simp)).toPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
            ⁅left ^ leftExponent, right ^ rightExponent⁆)
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
  input.closureProfileAssignment
    hn H hH (kernel := kernel)
      (recursiveKernel.universalProfileAssignment
        (by simp) (by simp) listEval_eq)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

/-!
# Claim 5 from a truncated finite-closure profile assignment

A symbolic Hall collector naturally produces finite sums of signed binomial
profiles, one packet for each retained erased Hall word.  Its cutoff-specific
product law is enough to construct the all-integral ordered packet consumed by
the restricted-sharp Claim 5 route.

This file exposes that direct constructor without requiring an all-groups
universal assignment or a singleton recipe transversal.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open CSAggreg
open
  FCAssign
open
  UTAssign

open SPAssign

namespace TSInput

/--
A root-weight summed profile assignment, its fixed-truncation product law,
singleton recollections, and graded Hall bases construct the Claim 5
coordinate polynomials.
-/
theorem
    coordinateProfileAssignment
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (assignment :
      SPAssign n 1 1)
    (hlistEval :
      SatisfiesTruncEval.{u} (d := d) assignment)
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
  input.coordinateAllPacket
    hn H hH (kernel := kernel)
      (truncAllPacket
        assignment (by simp) (by simp) hlistEval)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission
