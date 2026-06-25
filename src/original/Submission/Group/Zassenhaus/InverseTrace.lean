import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.FormulaChooseSubstitution
import Submission.Group.Zassenhaus.InverseUniversalClosure

/-!
# Block-family expansions from closed inverse traces

A closed inverse-oriented history schedule is already an exact ordered list of
complete block families.  This file packages that genuine operational endpoint
as the `BFam.Expansion` consumed by natural Hall-Petresco polynomial
specialization.

No cutoff deletion and no factor permutation are used.
This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ITSched

open scoped commutatorElement

open HACoeff
open RNCompre
open BRSpec
open ITEvalua
open PPColl.RCColl.RPAggreg

export RNCompre.BFam.Expansion
  (recipe_cast_pow)

namespace CHSched

/--
An exact closed inverse-history schedule is a canonical counted block-family
expansion at its generating natural multiplicities.
-/
def blockExpansion
    {M N : ℕ}
    (schedule : CHSched M N) :
    BFam.Expansion M N where
  families := schedule.families
  collapsed_eval_eq := by
    simpa [collapsedListEval,
      BFTrunc.collapsedList] using
        (schedule.collapsed_realization_source
          universalLeft universalRight).trans
            (collapsed_commutator_pow
              universalLeft universalRight)

/--
The recipe list read from a closed inverse-history schedule satisfies the
natural powered-commutator law in every group.
-/
lemma recipe_cast_pow
    {M N : ℕ}
    (schedule : CHSched M N)
    {G : Type*}
    [Group G]
    (left right : G) :
    (((schedule.families.map BFam.recipe).map fun recipe =>
      recipe.erasedShape.eval (HPAtom.eval left right) ^
        coefficientValue recipe (M : ℤ) (N : ℤ)).prod) =
      ⁅left ^ M, right ^ N⁆ :=
  ITSched.recipe_cast_pow
    (M := M) (N := N) schedule.blockExpansion left right

end CHSched

namespace PPScheda

/--
A positive-positive inverse-history scheduler, together with its checked zero
branches, constructs exact counted block-family expansions for every natural
multiplicity pair.
-/
noncomputable def resolveAllExpansion
    (kernel : PPScheda)
    (M N : ℕ) :
    BFam.Expansion M N :=
  (kernel.resolveAll M N).blockExpansion

/--
The expansions resolved by one positive scheduling kernel satisfy the natural
powered-commutator recipe law in every group.
-/
lemma recipe_cast_pow
    (kernel : PPScheda)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    (((kernel.resolveAllExpansion M N).families.map
      BFam.recipe).map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ :=
  (kernel.resolveAll M N).recipe_cast_pow left right

end PPScheda

/-- The explicit first positive-positive inverse trace gives one exact
counted block-family expansion. -/
def blockFamilyExpansion :
    BFam.Expansion 1 1 :=
  oneOne.blockExpansion

/-- The explicit first positive-positive inverse trace satisfies the natural
recipe-product law. -/
lemma recipe_cast_commutator
    {G : Type*}
    [Group G]
    (left right : G) :
    (((blockFamilyExpansion.families.map BFam.recipe).map
      fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe (1 : ℤ) (1 : ℤ)).prod) =
      ⁅left, right⁆ := by
  simpa using
    (oneOne.recipe_cast_pow left right)

end ITSched
end TCTex
end Submission

/-!
# Uniform natural packets from closed inverse traces

The genuine inverse-history scheduler produces one exact counted-family
expansion for each pair of natural source multiplicities.  Symbolic
Hall-Petresco collection needs one recipe list independent of those
multiplicities.

This file isolates that normalization boundary directly over closed schedules.
A fixed recipe list only has to agree semantically with each resolved schedule
at its generating natural pair.  Literal stabilization of the scheduled recipe
lists is a sufficient special case.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ITSched
namespace PPScheda

open scoped commutatorElement

open HACoeff
open BRSpec
open FNPkt

/--
A fixed recipe list uniformly normalizes the genuine closed inverse-history
schedules at every natural multiplicity pair.
-/
structure URNorm
    (kernel : PPScheda)
    (recipes : List BRecipe) :
    Prop where
  recipe_prod_schedule :
    ∀ (M N : ℕ)
      {G : Type*}
      [Group G]
      (left right : G),
        ((recipes.map fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe (M : ℤ) (N : ℤ)).prod) =
          ((((kernel.resolveAll M N).families.map BFam.recipe).map
            fun recipe =>
              recipe.erasedShape.eval (HPAtom.eval left right) ^
                coefficientValue recipe (M : ℤ) (N : ℤ)).prod)

namespace URNorm

/--
Literal stabilization of the recipe lists read from the resolved schedules is
a sufficient uniform normalization witness.
-/
def of_recipes_eq
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (hrecipes :
      ∀ M N : ℕ,
        (kernel.resolveAll M N).recipes = recipes) :
    URNorm kernel recipes where
  recipe_prod_schedule M N _ _ left right := by
    rw [← hrecipes M N]
    rfl

/--
Uniform schedule normalization is exactly the natural Hall-Petresco packet
available before proving the all-integral signed extension theorem.
-/
noncomputable def truncatedNaturalPacket
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (uniform : URNorm kernel recipes)
    (d n : ℕ) :
    TNPkt.{u} d n where
  recipes := recipes
  list_nat_cast left right M N :=
    (uniform.recipe_prod_schedule M N left right).trans
      ((kernel.resolveAll M N).recipe_cast_pow
        left right)

@[simp]
lemma recipes_natural_packet
    {kernel : PPScheda}
    {recipes : List BRecipe}
    (uniform : URNorm kernel recipes)
    (d n : ℕ) :
    (uniform.truncatedNaturalPacket d n).recipes = recipes :=
  rfl

end URNorm
end PPScheda
end ITSched
end TCTex
end Submission

/-!
# Uniform signed packets from closed inverse traces

Closed inverse-history schedules and uniform natural normalization reach the
natural Hall-Petresco packet boundary.  Symbolic recollection additionally
needs the signed extension of that one fixed packet.

This file packages the remaining signed obligation directly over the genuine
schedule route and exposes the correction factories consumed by polynomial and
repeated-power collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace ITSched
namespace PPScheda

universe u

open HACoeff
open FNPkt
open PFSubsti

/--
One multiplicity-independent recipe list that normalizes every closed
inverse-history schedule, together with its all-integral signed extension in
one free lower-central truncation.
-/
structure USPkt
    (kernel : PPScheda)
    (recipes : List BRecipe)
    (d n : ℕ) where
  uniform :
    URNorm.{u} kernel recipes
  lift :
    (URNorm.truncatedNaturalPacket.{u}
      uniform d n).AILift

namespace USPkt

/--
Attach genuine schedule provenance to an independently proved all-integral
packet with the same fixed recipe list.
-/
def truncatedIntegralPacket
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (uniform : URNorm.{u} kernel recipes)
    (packet : TAPkt.{u} d n)
    (hrecipes : packet.recipes = recipes) :
    USPkt.{u} kernel recipes d n where
  uniform := uniform
  lift := {
    listEval_eq := by
      intro left right leftExponent rightExponent
      simpa only [URNorm.truncatedNaturalPacket,
        hrecipes] using
          packet.listEval_eq left right leftExponent rightExponent }

/-- Forget the schedule provenance and expose the all-integral packet consumed
by polynomial substitution. -/
def truncatedAll
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (packet : USPkt kernel recipes d n) :
    TAPkt.{u} d n :=
  packet.lift.truncatedAll

@[simp]
lemma recipes_all_packet
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    (packet : USPkt kernel recipes d n) :
    packet.truncatedAll.recipes = recipes :=
  rfl

/-- Attach the fixed signed schedule packet to two arbitrary symbolic Hall
parents. -/
def toCorrectionExpansion
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : USPkt kernel recipes d n)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) :
    SCExp (n := n) left right :=
  packet.truncatedAll.toCorrectionExpansion
    normalizer left right

/-- The fixed signed schedule packet supplies arbitrary-parent polynomial
corrections at every supported stratum. -/
def supportedWordFactory
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : USPkt kernel recipes d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    SSFtrya
      (n := n) H lowerWeight :=
  packet.truncatedAll
    |>.supportedWordFactory normalizers lowerWeight

/-- The same fixed signed schedule packet supplies powered correction
expansions at every supported stratum. -/
noncomputable def powerSupportedFactory
    {kernel : PPScheda}
    {recipes : List BRecipe}
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : USPkt kernel recipes d n)
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  packet.truncatedAll
    |>.powerSupportedFactory
      hinputWeight lowerWeight

end USPkt
end PPScheda
end ITSched
end TCTex
end Submission

/-!
# Canonical uniform signed packets from inverse traces

A genuine inverse-history scheduler may normalize to the fixed canonical
finite-closure recipe inventory.  Once its natural normalization has an
all-integral signed lift, the canonical flattened-recipe law and the canonical
summed-profile law follow immediately.

This file isolates the exact schedule-facing endpoint for the arbitrary-cutoff
collector.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ITSched
namespace PPScheda

universe u

open
  CPSplit
open
  CTAssign
open
  ACAlign
open
  UTAssign

/--
A genuine uniform signed schedule packet whose fixed recipe list is the
canonical finite-closure inventory proves the canonical recipe-product law.
-/
lemma satisfies_recipe_uniform
    {kernel : PPScheda}
    {d n : ℕ}
    (packet :
      USPkt.{u}
        kernel (canonicalRecipes n 1 1) d n) :
    SatisfiesRecipeTruncated.{u} d n :=
  packet.truncatedAll.listEval_eq

/--
The same canonical uniform signed schedule packet proves the fixed-truncation
summed-profile product law directly.
-/
lemma
    satisfies_assignment_uniform
    {kernel : PPScheda}
    {d n : ℕ}
    (packet :
      USPkt.{u}
        kernel (canonicalRecipes n 1 1) d n) :
    SatisfiesTruncEval.{u} (d := d)
      (canonicalProfileAssignment n 1 1) :=
  satisfies_profile_assignment
    (satisfies_recipe_uniform
      packet)

/--
An arbitrary fixed schedule recipe list may be identified with the canonical
inventory after the signed packet has been constructed.
-/
lemma satisfies_truncated_uniform
    {kernel : PPScheda}
    {recipes : List HACoeff.BRecipe}
    {d n : ℕ}
    (packet : USPkt.{u} kernel recipes d n)
    (hrecipes : recipes = canonicalRecipes n 1 1) :
    SatisfiesRecipeTruncated.{u} d n := by
  subst recipes
  exact
    satisfies_recipe_uniform
      packet

end PPScheda
end ITSched
end TCTex
end Submission

/-!
# Global canonical symbolic recollection polynomials from inverse traces

A uniform inverse-trace normalization compares one fixed canonical recipe list
with every genuine resolved schedule at natural source multiplicities.  The
canonical recipe-chunk alignment then compares the aggregated same-word packet
with that fixed recipe list without reordering factors.

Combining those equalities with the genuine concrete-packet theorem constructs
the order-aware canonical stabilization certificate.  A uniform signed recipe
packet additionally supplies the all-integral lift, and therefore the global
canonical symbolic recollection-polynomial law.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  GCPolyno

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open CSAggreg
open
  CCTrunc
open ITSched
open ITSched.PPScheda
open
  GRPolys
open
  RPStab
open
  ACAlign

/--
A canonical natural inverse-trace normalization constructs the order-aware
stabilization certificate for the aggregated canonical packet.
-/
noncomputable def
    stabilization_uniform_normalization
    {inverseTraceKernel : PPScheda}
    {signedBlockKernel : OCShape}
    {d n : ℕ}
    (uniform :
      URNorm.{u}
        inverseTraceKernel (canonicalRecipes n 1 1)) :
    SatisfiesNaturalStabilization.{u}
      signedBlockKernel d n where
  leftWeight_pos := by
    simp
  rightWeight_pos := by
    simp
  packet_prod_concrete M N left right hleft hright := by
    calc
      ((globalProfilePackets n 1 1).map
          fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value (M : ℤ) (N : ℤ)).prod =
          ((canonicalRecipes n 1 1).map fun recipe =>
            recipe.erasedShape.eval (HPAtom.eval left right) ^
              coefficientValue recipe (M : ℤ) (N : ℤ)).prod := by
        simpa only [globalProfilePackets] using
          (canonicalChunkAlignment n 1 1).list_recipe_factors
            left right (M : ℤ) (N : ℤ)
      _ =
          ((((inverseTraceKernel.resolveAll M N).families.map
              BFam.recipe).map fun recipe =>
                recipe.erasedShape.eval (HPAtom.eval left right) ^
                  coefficientValue recipe (M : ℤ) (N : ℤ)).prod) :=
        uniform.recipe_prod_schedule M N left right
      _ = ⁅left ^ M, right ^ N⁆ :=
        (inverseTraceKernel.resolveAll M N)
          |>.recipe_cast_pow left right
      _ =
          ((truncatedConcretePackets
              signedBlockKernel n 1 1 M N).map fun packet =>
                packet.word.eval (HPAtom.eval left right) ^
                  packet.profiles.value (M : ℤ) (N : ℤ)).prod :=
        (concrete_packets_pow
          (by simp) (by simp) signedBlockKernel M N left right
            hleft hright).symm

/--
A canonical uniform signed inverse-trace packet supplies the all-integral lift
of its order-aware aggregated stabilization certificate.
-/
noncomputable def
    global_all_uniform
    {inverseTraceKernel : PPScheda}
    {signedBlockKernel : OCShape}
    {d n : ℕ}
    (packet :
      USPkt.{u}
        inverseTraceKernel (canonicalRecipes n 1 1) d n) :
    GlobalAllLift
      (kernel := signedBlockKernel)
      (d := d)
      (n := n)
      (stabilization_uniform_normalization
        (signedBlockKernel := signedBlockKernel)
        (d := d) (n := n) packet.uniform) :=
  global_all_satisfies
    (stabilization_uniform_normalization
      (signedBlockKernel := signedBlockKernel)
      (d := d) (n := n) packet.uniform)
    (satisfies_recipe_uniform
      packet)

/--
A canonical uniform signed inverse-trace packet proves the powered-commutator
law directly in the global aggregated symbolic language.
-/
lemma
    global_uniform_packet
    {inverseTraceKernel : PPScheda}
    {signedBlockKernel : OCShape}
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      USPkt.{u}
        inverseTraceKernel (canonicalRecipes n 1 1) d n)
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalRecollectionFactors normalizer
          n 1 1 left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  global_all_lift
    (stabilization_uniform_normalization
      (signedBlockKernel := signedBlockKernel)
      (d := d) (n := n) packet.uniform)
    (global_all_uniform
      (signedBlockKernel := signedBlockKernel) packet)
    normalizer e left right

end
  GCPolyno
end TCTex
end Submission

/-!
# Raw canonical finite-closure inventory cannot normalize inverse traces

The conservative canonical finite-closure inventory is useful as a finite
support universe, but it is not the multiplicity-independent packet produced
by a normalized inverse-history schedule.  The distinction is already forced
at cutoff three: the raw inventory repeats the basic Hall-pair contribution
when both source multiplicities are one.

This file transports the class-two semantic obstruction to the genuine
inverse-trace normalization API.  It is intentionally not imported by the
existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ITSched
namespace PPScheda

universe u

open
  CPSplit
open
  CSObstru
open
  ACAlign

/--
No positive closed inverse-history scheduler can normalize uniformly to the
raw cutoff-three canonical finite-closure inventory.
-/
theorem uniform_normalization_recipes
    (kernel : PPScheda) :
    ¬ URNorm.{u} kernel (canonicalRecipes 3 1 1) := by
  intro uniform
  apply not_satisfies_three
  intro left right
  simpa using
    (uniform.truncatedNaturalPacket 2 3).list_nat_cast
      left right 1 1

/--
Consequently, the raw cutoff-three canonical inventory cannot underlie a
uniform signed inverse-trace packet in any truncation.
-/
theorem not_uniform_recipes
    (kernel : PPScheda)
    (d n : ℕ) :
    ¬ USPkt.{u}
      kernel (canonicalRecipes 3 1 1) d n := by
  intro packet
  exact
    uniform_normalization_recipes
      kernel packet.uniform

end PPScheda
end ITSched
end TCTex
end Submission
