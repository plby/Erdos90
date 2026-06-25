import Submission.Group.Zassenhaus.CanonicalPacketAlignment
import Submission.Group.Zassenhaus.ClassEndpointFibers
import Submission.Group.Zassenhaus.PolynomialOrbitVocabulary
import Submission.Group.Zassenhaus.RetainedHistoryFibers
import Submission.Group.Zassenhaus.FiniteIndexProfiles
import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.FamilyOperationalCompatible
import Submission.Group.Zassenhaus.OneSourcedInput
import Submission.Group.Zassenhaus.InverseUniversalOrbit

/-!
# Ordered retained-transversal signed law through cutoff four

Through cutoff four, the sorted retained-transversal packet has its signed
recollection law even when its order differs from the finite-closure
enumeration: the class-three factors commute pairwise, so the existing
permutation argument applies.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open
  SOAlign
open
  FUClass

/--
The sorted retained-transversal signed law holds through cutoff four by the
class-three permutation-and-commutation argument.
-/
theorem
    satisfies_n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  exact
    coefficient_assignment_four
      hn left right leftExponent rightExponent

end TCTex
end Submission

/-!
# Ordered occurrence schedules for the retained transversal

The retained recipe transversal keeps the inherited finite-closure order,
while cutoff-full interpolation attaches the same retained profiles in sorted
More3 vocabulary order.  Literal equality of those lists is stronger than the
required theorem.  What Claim 5 needs is equality of their ordered products.

This file isolates that order-aware transport semantically and
operationally.  An occurrence-level transport rewrites the retained list into
the sorted list.  Composing it with the retained parent-pair schedule gives a
single ordered occurrence schedule whose target is exactly the sorted packet
consumed by cutoff-full interpolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  OOSched

universe u

open scoped commutatorElement

open
  SOAlign
open
  CCThree
open
  PTOcc

/--
Evaluate the retained singleton profiles in sorted cutoff-full vocabulary
order.
-/
def orderedEvaluatedFactors
    {G : Type*}
    [Group G]
    (n : ℕ)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    List G :=
  (profileRecollectionPackets n).map
    fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent

/--
Semantic order-aware transport from the sorted retained packet product to
the occurrence-preserving retained recipe product.
-/
def RetainedRecipeTransport
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      (orderedEvaluatedFactors
          n left right leftExponent rightExponent).prod =
        (coefficientEvaluatedFactors
          n left right leftExponent rightExponent).prod

/--
An occurrence-level order-aware transport recollects the inherited retained
factor list into the sorted retained packet list.
-/
structure COTrans
    (d n : ℕ) :
    Prop where
  rewrites :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
      CORw
        (coefficientEvaluatedFactors
          n left right leftExponent rightExponent)
        (orderedEvaluatedFactors
          n left right leftExponent rightExponent)

namespace COTrans

/--
Every occurrence-level ordered transport supplies its semantic product
transport.
-/
theorem retainedRecipeTransport
    {d n : ℕ}
    (transport :
      COTrans.{u} d n) :
    RetainedRecipeTransport.{u} d n := by
  intro left right leftExponent rightExponent
  exact
    (transport.rewrites left right leftExponent rightExponent).list_prod_eq

end COTrans

/--
A semantic order-aware transport carries the inherited retained recipe law
to the sorted retained packet law.
-/
theorem
    satisfies_coeff_trunc
    {d n : ℕ}
    (transport :
      RetainedRecipeTransport.{u} d n)
    (hlistEval :
      SatisfiesRecipeCoefficient.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  change
    (orderedEvaluatedFactors
      n left right leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆
  exact
    (transport left right leftExponent rightExponent).trans
      (hlistEval left right leftExponent rightExponent)

/--
Under the inherited retained recipe law, semantic ordered transport is
equivalent to the sorted retained packet law.
-/
theorem
    recipe_coeff_trunc
    {d n : ℕ}
    (hlistEval :
      SatisfiesRecipeCoefficient.{u} d n) :
    RetainedRecipeTransport.{u} d n ↔
      SatisfiesCoefficientTruncated.{u} d n := by
  constructor
  · intro transport
    exact
      satisfies_coeff_trunc
        transport hlistEval
  · intro hordered left right leftExponent rightExponent
    exact
      (hordered left right leftExponent rightExponent).trans
        (hlistEval left right leftExponent rightExponent).symm

/--
An occurrence-level ordered transport and the inherited retained recipe law
supply the sorted retained packet law.
-/
theorem
    satisfies_coeff_occ
    {d n : ℕ}
    (transport :
      COTrans.{u} d n)
    (hlistEval :
      SatisfiesRecipeCoefficient.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_coeff_trunc
    transport.retainedRecipeTransport hlistEval

/--
An occurrence-level ordered transport and the inherited retained parent-pair
schedule supply the sorted retained packet law.
-/
theorem
    occ_transport_schedule
    {d n : ℕ}
    (transport :
      COTrans.{u} d n)
    (schedule :
      COSched.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_coeff_occ
    transport schedule.satisfiesRecipeCoefficient

/--
A single occurrence-aware schedule from the powered parent pair to the
sorted retained packet followed by the swapped powered parents.
-/
structure COScheda
    (d n : ℕ) :
    Prop where
  rewrites :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
      CORw
        [left ^ leftExponent, right ^ rightExponent]
        (orderedEvaluatedFactors
            n left right leftExponent rightExponent ++
          [right ^ rightExponent, left ^ leftExponent])

namespace COScheda

/--
Composing the inherited parent-pair schedule with an ordered transport gives
the ordered parent-pair schedule consumed by cutoff-full interpolation.
-/
def occ_schedule_transport
    {d n : ℕ}
    (schedule :
      COSched.{u} d n)
    (transport :
      COTrans.{u} d n) :
    COScheda.{u} d n where
  rewrites left right leftExponent rightExponent := by
    apply
      (schedule.rewrites left right leftExponent rightExponent).trans
    simpa using
      (transport.rewrites left right leftExponent rightExponent).context
        [] [right ^ rightExponent, left ^ leftExponent]

/--
An ordered occurrence schedule gives the adjacent-swap equation before
cancellation.
-/
lemma evaluated_factors_swap
    {d n : ℕ}
    (schedule :
      COScheda.{u} d n)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod *
          right ^ rightExponent * left ^ leftExponent =
      left ^ leftExponent * right ^ rightExponent := by
  simpa [List.prod_append, mul_assoc] using
    (schedule.rewrites left right leftExponent rightExponent).list_prod_eq

/--
Cancellation of the swapped powered parents turns an ordered occurrence
schedule into the sorted retained packet law.
-/
theorem satisfiesCoefficientTruncated
    {d n : ℕ}
    (schedule :
      COScheda.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  change
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod =
      ⁅left ^ leftExponent, right ^ rightExponent⁆
  have hswap :=
    schedule.evaluated_factors_swap
      left right leftExponent rightExponent
  calc
    (orderedEvaluatedFactors
          n left right leftExponent rightExponent).prod =
        (orderedEvaluatedFactors
              n left right leftExponent rightExponent).prod *
            right ^ rightExponent * left ^ leftExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      group
    _ =
        left ^ leftExponent * right ^ rightExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      rw [hswap]
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
      rfl

/--
The sorted retained packet law itself supplies a one-step ordered occurrence
schedule.  This packages existing shallow laws under the ordered scheduler
interface.
-/
noncomputable def satisfies_ordered_trunc
    {d n : ℕ}
    (hlistEval :
      SatisfiesCoefficientTruncated.{u} d n) :
    COScheda.{u} d n where
  rewrites left right leftExponent rightExponent := by
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] [] (left ^ leftExponent) (right ^ rightExponent)
        (orderedEvaluatedFactors
          n left right leftExponent rightExponent)
        (by
          unfold orderedEvaluatedFactors
          rw [hlistEval left right leftExponent rightExponent]
          simp [commutatorElement_def, mul_assoc]))

/--
The sorted retained packet law is equivalent to constructing an
occurrence-aware parent-pair schedule with the sorted packet as target.
-/
theorem
    satisfies_coefficient_occurrence
    {d n : ℕ} :
    SatisfiesCoefficientTruncated.{u} d n ↔
      COScheda.{u} d n := by
  constructor
  · exact satisfies_ordered_trunc
  · exact satisfiesCoefficientTruncated

end COScheda

end
  OOSched
end TCTex
end Submission

/-!
# Ordered retained occurrence schedules through cutoff four

Through cutoff four, the shallow permutation-and-commutation theorem supplies
an ordered occurrence schedule for the retained-transversal packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open
  OOSched

namespace OOSched
namespace COScheda

/--
Through cutoff four, the shallow permutation-and-commutation theorem supplies
an ordered occurrence schedule.
-/
noncomputable def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    COScheda.{u} d n :=
  satisfies_ordered_trunc
    (satisfies_n_four
      hn)

end COScheda
end OOSched
end TCTex
end Submission

/-!
# Cutoff-aware ordered occurrence schedules for the retained transversal

The cutoff-full collector natively emits occurrence runs that combine Hall
swaps with certified erasures of factors already equal to the identity at the
nilpotent cutoff.  Pure retained occurrence rewrites remain useful as a
semantic facade, but the native operational target for an arbitrary-cutoff
symbolic collector is the richer cutoff-aware relation.

This file packages the corresponding ordered transport and combined
parent-pair schedule.  Every cutoff-aware schedule still supplies the sorted
retained signed law consumed by Claim 5.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  FTOcc

universe u


open scoped commutatorElement

open
  OOSched
open
  SOAlign
open
  CCThree
open
  PTOcc
open
  PCBridge

/--
A cutoff-aware ordered transport recollects the inherited retained factor
list into the sorted retained packet list, allowing certified identity
erasures at the nilpotent cutoff.
-/
structure TOTransa
    (d n : ℕ) :
    Prop where
  rewrites :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
      TORwa
        (coefficientEvaluatedFactors
          n left right leftExponent rightExponent)
        (orderedEvaluatedFactors
          n left right leftExponent rightExponent)

namespace COTrans

/--
Every pure ordered occurrence transport embeds into the cutoff-aware
transport relation.
-/
def occTransport
    {d n : ℕ}
    (transport :
      COTrans.{u} d n) :
    TOTransa.{u} d n where
  rewrites left right leftExponent rightExponent :=
    TORwa.ofOccurrenceRewrites
      (transport.rewrites left right leftExponent rightExponent)

end COTrans

namespace TOTransa

/--
Every cutoff-aware ordered transport supplies its semantic product
transport.
-/
theorem retainedRecipeTransport
    {d n : ℕ}
    (transport :
      TOTransa.{u} d n) :
    RetainedRecipeTransport.{u} d n := by
  intro left right leftExponent rightExponent
  exact
    (transport.rewrites left right leftExponent rightExponent).list_prod_eq

end TOTransa

/--
A cutoff-aware ordered transport and the inherited retained recipe law supply
the sorted retained packet law.
-/
theorem
    satisfies_trunc_occ
    {d n : ℕ}
    (transport :
      TOTransa.{u} d n)
    (hlistEval :
      SatisfiesRecipeCoefficient.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_coeff_trunc
    transport.retainedRecipeTransport hlistEval

/--
A cutoff-aware ordered transport and the inherited retained parent-pair
schedule supply the sorted retained packet law.
-/
theorem
    satisfies_occ_transport
    {d n : ℕ}
    (transport :
      TOTransa.{u} d n)
    (schedule :
      COSched.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_trunc_occ
    transport schedule.satisfiesRecipeCoefficient

/--
A single cutoff-aware schedule from the powered parent pair to the sorted
retained packet followed by the swapped powered parents.
-/
structure OOScheda
    (d n : ℕ) :
    Prop where
  rewrites :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
      TORwa
        [left ^ leftExponent, right ^ rightExponent]
        (orderedEvaluatedFactors
            n left right leftExponent rightExponent ++
          [right ^ rightExponent, left ^ leftExponent])

namespace OOScheda

/--
Compose an inherited parent-pair schedule with a cutoff-aware ordered
transport.
-/
def occ_trunc_transport
    {d n : ℕ}
    (schedule :
      COSched.{u} d n)
    (transport :
      TOTransa.{u} d n) :
    OOScheda.{u} d n where
  rewrites left right leftExponent rightExponent := by
    apply
      (TORwa.ofOccurrenceRewrites
        (schedule.rewrites left right leftExponent rightExponent)).trans
    simpa using
      (transport.rewrites left right leftExponent rightExponent).context
        [] [right ^ rightExponent, left ^ leftExponent]

/--
Every pure ordered parent-pair schedule embeds into the cutoff-aware schedule
relation.
-/
def orderedOccurrenceSchedule
    {d n : ℕ}
    (schedule :
      COScheda.{u} d n) :
    OOScheda.{u} d n where
  rewrites left right leftExponent rightExponent :=
    TORwa.ofOccurrenceRewrites
      (schedule.rewrites left right leftExponent rightExponent)

/--
A cutoff-aware ordered occurrence schedule gives the adjacent-swap equation
before cancellation.
-/
lemma evaluated_factors_swap
    {d n : ℕ}
    (schedule :
      OOScheda.{u} d n)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod *
          right ^ rightExponent * left ^ leftExponent =
      left ^ leftExponent * right ^ rightExponent := by
  simpa [List.prod_append, mul_assoc] using
    (schedule.rewrites left right leftExponent rightExponent).list_prod_eq

/--
Cancellation of the swapped powered parents turns a cutoff-aware ordered
occurrence schedule into the sorted retained packet law.
-/
theorem satisfiesCoefficientTruncated
    {d n : ℕ}
    (schedule :
      OOScheda.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  change
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod =
      ⁅left ^ leftExponent, right ^ rightExponent⁆
  have hswap :=
    schedule.evaluated_factors_swap
      left right leftExponent rightExponent
  calc
    (orderedEvaluatedFactors
          n left right leftExponent rightExponent).prod =
        (orderedEvaluatedFactors
              n left right leftExponent rightExponent).prod *
            right ^ rightExponent * left ^ leftExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      group
    _ =
        left ^ leftExponent * right ^ rightExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      rw [hswap]
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
      rfl

/--
The sorted retained packet law itself supplies a one-step cutoff-aware
ordered schedule.
-/
noncomputable def satisfies_ordered_trunc
    {d n : ℕ}
    (hlistEval :
      SatisfiesCoefficientTruncated.{u} d n) :
    OOScheda.{u} d n :=
  orderedOccurrenceSchedule
    (COScheda.satisfies_ordered_trunc
      hlistEval)

/--
A cutoff-aware ordered schedule can be consumed by the existing pure ordered
schedule facade after forgetting its operational erasures semantically.
-/
noncomputable def occurrenceSchedule
    {d n : ℕ}
    (schedule :
      OOScheda.{u} d n) :
    COScheda.{u} d n :=
  COScheda.satisfies_ordered_trunc
    schedule.satisfiesCoefficientTruncated

/--
The sorted retained packet law is equivalent to constructing a cutoff-aware
ordered parent-pair schedule.
-/
theorem
    satisfies_occurrence_schedule
    {d n : ℕ} :
    SatisfiesCoefficientTruncated.{u} d n ↔
      OOScheda.{u} d n := by
  constructor
  · exact satisfies_ordered_trunc
  · exact satisfiesCoefficientTruncated

end OOScheda

end
  FTOcc
end TCTex
end Submission

/-!
# Natural endpoint cutoff-aware occurrence schedules

The terminating cutoff-full collector already produces a literal rewrite run
from the inverse-raw family trace to its selected sorted endpoint.  This file
adjoins the powered parent pair and packages the resulting natural-exponent
schedule.  It also records that fixed-slot interpolation packets and the
literal endpoint list have the same product at natural casts.

The remaining arbitrary-cutoff problem is therefore an all-integral symbolic
extension of this natural endpoint schedule, not construction of a terminating
concrete collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  NTOcc

universe u


open scoped commutatorElement

open
  HACoeff
open
  CFCollec
open
  CFCollec.DFTerm
open
  FCEnd
open
  FCEnd.IDTerms
open
  FSInterp
open
  FPInterp
open
  CRLayer
open
  CFSubsti
open
  PTOcc
open
  PCBridge

namespace NRLayer

/--
At natural exponents, the powered parent pair rewrites to the literal selected
cutoff-full endpoint followed by the swapped powered parents.  The tail of the
run is the terminating collector's actual sequence of Hall swaps and certified
identity erasures.
-/
lemma parent_endpoint_rewrites
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) := by
  have hendpoint :=
    PCBridge.NRLayer.endpoint_occurrence_rewrites
      layer M N x y hleftWeight hrightWeight hx hy hbot
  have hrawProd :
      (collapsedEvaluatedFactors x y
        (inverseDecoratedTerms M N)).prod =
          ⁅x ^ M, y ^ N⁆ := by
    calc
      (collapsedEvaluatedFactors x y
            (inverseDecoratedTerms M N)).prod =
          (collapsedEvaluatedFactors x y
            (layer.endpoint M N).factors).prod :=
        hendpoint.list_prod_eq.symm
      _ = ⁅x ^ M, y ^ N⁆ := by
        simpa [collapsedEvaluatedFactors, collapsedList] using
          (layer.endpoint M N).collapsed_list_pow
            x y hleftWeight hrightWeight hx hy hbot
  have hparents :
      CORw
        [x ^ M, y ^ N]
        (collapsedEvaluatedFactors x y
            (inverseDecoratedTerms M N) ++
          [y ^ N, x ^ M]) := by
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] [] (x ^ M) (y ^ N)
        (collapsedEvaluatedFactors x y
          (inverseDecoratedTerms M N))
        (by
          rw [hrawProd]
          simp [commutatorElement_def, mul_assoc]))
  apply
    (TORwa.ofOccurrenceRewrites hparents).trans
  simpa using
    hendpoint.context [] [y ^ N, x ^ M]

/--
At root weights in the free lower-central truncation, the support and
terminal-vanishing hypotheses for the natural endpoint schedule are automatic.
-/
lemma parentEndpointTrunc
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    TORwa
      [x ^ M, y ^ N]
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
        [y ^ N, x ^ M]) := by
  exact
    parent_endpoint_rewrites layer
      M N x y (by omega) (by omega) (by simp) (by simp)
        SCFactor.trunc_last_bot

end NRLayer

/--
A selected natural recollection layer carries a cutoff-aware parent-pair
schedule at every natural exponent pair.
-/
structure NOSched
    (d n : ℕ)
    (layer : NRLayer n 1 1) :
    Prop where
  rewrites :
    ∀ (M N : ℕ)
      (x y :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n),
      TORwa
        [x ^ M, y ^ N]
        (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
          [y ^ N, x ^ M])

namespace NOSched

/--
The terminating cutoff-full collector constructs the natural endpoint
schedule unconditionally.
-/
noncomputable def natural_recollect_layer
    {d n : ℕ}
    (layer : NRLayer n 1 1) :
    NOSched.{u} d n layer where
  rewrites M N x y :=
    NRLayer.parentEndpointTrunc
      layer
      M N x y

end NOSched

namespace EFInterp

/--
At natural casts, endpoint shape-fiber interpolation packets have the same
ordered product as the literal selected cutoff-full endpoint factors.
-/
lemma endpoint_evaluated_factors
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval x y) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod := by
  calc
    (packets.map fun packet =>
        packet.word.eval (HPAtom.eval x y) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        ⁅x ^ M, y ^ N⁆ :=
      (interpolation.naturalFixedInterpolation
        hleftWeight hrightWeight)
          |>.packet_cast_pow
            M N x y hx hy hbot
    _ =
        (collapsedEvaluatedFactors x y
          (layer.endpoint M N).factors).prod := by
      simpa [collapsedEvaluatedFactors, collapsedList] using
        ((layer.endpoint M N).collapsed_list_pow
          x y hleftWeight hrightWeight hx hy hbot).symm

end EFInterp

end
  NTOcc
end TCTex
end Submission

/-!
# Cutoff-aware ordered retained occurrence schedules through cutoff four

Through cutoff four, the shallow ordered occurrence schedule also supplies
the richer cutoff-aware interface.  This lift uses no identity erasures, but
it lets downstream Claim 5 reductions depend uniformly on the operational
schedule type needed at arbitrary cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open
  OOSched
open
  FTOcc

namespace FTOcc
namespace OOScheda

/--
Through cutoff four, the shallow permutation-and-commutation theorem supplies
a cutoff-aware ordered occurrence schedule.
-/
noncomputable def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    OOScheda.{u} d n :=
  orderedOccurrenceSchedule
    (COScheda.n_four
      (d := d) hn)

end OOScheda
end FTOcc
end TCTex
end Submission

/-!
# Adjacent power compression for natural cutoff-full endpoints

The cutoff-full collector emits one evaluated group factor for every retained
decorated-family occurrence.  The natural recollection layer consumes one
powered group factor for every maximal adjacent erased-shape run.

This file records the missing operational bridge.  A local compression move
merges one factor followed by a power of the same factor.  Every maximal
same-shape endpoint block compresses by a finite sequence of such adjacent
moves, and the blockwise schedules concatenate to the natural recollection
packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  NACompre

universe u

open scoped commutatorElement

open
  HACoeff
open
  CFCollec
open
  CFCollec.DFTerm
open
  CRLayer
open
  PCBridge

/--
One adjacent power-compression move.  The factor retained on the left is
absorbed into the following power of the same factor.
-/
inductive ACStep
    {G : Type*}
    [Group G] :
    List G → List G → Prop where
  | merge
      (front back : List G)
      (factor : G)
      (exponent : ℕ) :
      ACStep
        (front ++ [factor, factor ^ exponent] ++ back)
        (front ++ [factor ^ (exponent + 1)] ++ back)

/-- Finite runs of adjacent power-compression moves. -/
abbrev ACRw
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  Relation.ReflTransGen
    (@ACStep G _) source target

namespace ACStep

/-- One adjacent merge preserves the ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : ACStep source target) :
    target.prod = source.prod := by
  cases step with
  | merge front back factor exponent =>
      simp [List.prod_append, pow_succ', mul_assoc]

/-- One adjacent merge remains valid in a list context. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : ACStep source target)
    (front back : List G) :
    ACStep
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  cases step with
  | merge innerFront innerBack factor exponent =>
      simpa [List.append_assoc] using
        (ACStep.merge
          (front ++ innerFront) (innerBack ++ back) factor exponent)

end ACStep

namespace ACRw

/-- Every finite adjacent-compression run preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : ACRw source target) :
    target.prod = source.prod := by
  induction rewrites with
  | refl =>
      rfl
  | tail _ step ih =>
      exact step.list_prod_eq.trans ih

/-- Adjacent-compression runs remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : ACRw source target)
    (front back : List G) :
    ACRw
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih (step.context front back)

/-- Independently constructed compression runs compose under concatenation. -/
lemma append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left :
      ACRw leftSource leftTarget)
    (right :
      ACRw rightSource rightTarget) :
    ACRw
      (leftSource ++ rightSource)
      (leftTarget ++ rightTarget) := by
  have hleft :
      ACRw
        (leftSource ++ rightSource)
        (leftTarget ++ rightSource) := by
    simpa using left.context [] rightSource
  have hright :
      ACRw
        (leftTarget ++ rightSource)
        (leftTarget ++ rightTarget) := by
    simpa using right.context leftTarget []
  exact hleft.trans hright

/-- A nonempty repeated block compresses to one power of its repeated factor. -/
lemma replicate_succ
    {G : Type*}
    [Group G]
    (factor : G) :
    ∀ exponent : ℕ,
      ACRw
        (List.replicate (exponent + 1) factor)
        [factor ^ (exponent + 1)] := by
  intro exponent
  induction exponent with
  | zero =>
      simpa using
        (Relation.ReflTransGen.refl :
          ACRw [factor] [factor])
  | succ exponent ih =>
      have htail :
          ACRw
            (factor :: List.replicate (exponent + 1) factor)
            [factor, factor ^ (exponent + 1)] := by
        simpa using ih.context [factor] []
      have hmerge :
          ACRw
            [factor, factor ^ (exponent + 1)]
            [factor ^ ((exponent + 1) + 1)] :=
        Relation.ReflTransGen.single
          (ACStep.merge [] [] factor (exponent + 1))
      simpa [List.replicate_succ] using htail.trans hmerge

end ACRw

namespace DFTerm

/--
The evaluated occurrence list of a same-shape block is literally a repetition
of the common erased-shape evaluation.
-/
lemma collapsed_evaluated_replicate
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (block : List (DFTerm M N K))
    (shape : CWord HPAtom)
    (hsame : ∀ term ∈ block, term.erasedShape = shape) :
    collapsedEvaluatedFactors x y block =
      List.replicate block.length
        (shape.eval (HPAtom.eval x y)) := by
  unfold collapsedEvaluatedFactors
  calc
    block.map (fun term => collapsedEvalAt x y term) =
        List.replicate
          (block.map fun term => collapsedEvalAt x y term).length
          (shape.eval (HPAtom.eval x y)) := by
      apply List.eq_replicate_length.mpr
      intro factor hfactor
      rcases List.mem_map.mp hfactor with ⟨term, hterm, rfl⟩
      change term.erasedShape.eval (HPAtom.eval x y) =
        shape.eval (HPAtom.eval x y)
      rw [hsame term hterm]
    _ =
        List.replicate block.length
          (shape.eval (HPAtom.eval x y)) := by
      rw [List.length_map]

/-- One nonempty same-shape block compresses to its natural run factor. -/
lemma adjacent_rewrites_run
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (block : List (DFTerm M N K))
    (hsame : SameErasedBlock block)
    (hne : block ≠ []) :
    ACRw
      (collapsedEvaluatedFactors x y block)
      [(naturalRunFactor block).evalAt x y] := by
  rcases hsame with ⟨shape, hshape⟩
  rw [collapsed_evaluated_replicate
    x y block shape hshape]
  cases block with
  | nil =>
      contradiction
  | cons term terms =>
      simpa [naturalRunFactor, firstErasedShape,
        NRFactor.evalAt, hshape term (by simp)] using
          (ACRw.replicate_succ
            (shape.eval (HPAtom.eval x y)) terms.length)

/--
Compress a finite ordered list of nonempty same-shape blocks without changing
their order.
-/
lemma adjacent_compression_rewrites
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (blocks : List (List (DFTerm M N K)))
    (hsame :
      ∀ block ∈ blocks, SameErasedBlock block)
    (hne :
      ∀ block ∈ blocks, block ≠ []) :
    ACRw
      (collapsedEvaluatedFactors x y blocks.flatten)
      ((naturalShapeFactors blocks).map fun factor =>
        factor.evalAt x y) := by
  induction blocks with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons block blocks ih =>
      have hblock :=
        adjacent_rewrites_run
          x y block (hsame block (by simp)) (hne block (by simp))
      have htail :=
        ih
          (fun next hnext => hsame next (by simp [hnext]))
          (fun next hnext => hne next (by simp [hnext]))
      simpa [collapsedEvaluatedFactors, naturalShapeFactors,
        List.map_append] using hblock.append htail

/--
Every decorated-family occurrence list compresses, run by run, to its natural
shape packet.
-/
lemma adjacent_compression_run
    {M N K : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (terms : List (DFTerm M N K)) :
    ACRw
      (collapsedEvaluatedFactors x y terms)
      ((naturalRunFactors terms).map fun factor =>
        factor.evalAt x y) := by
  simpa [naturalRunFactors, flatten_same_blocks] using
    adjacent_compression_rewrites
      x y (sameErasedBlocks terms)
      (same_erased_blocks terms)
      (by
        intro block hblock
        apply List.ne_nil_of_mem_splitBy
        simpa [sameErasedBlocks] using hblock)

end DFTerm

namespace NRLayer

/--
The selected natural cutoff-full endpoint compresses operationally to the
natural run packet consumed by interpolation.
-/
lemma endpoint_adjacent_rewrites
    {n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (x y : G) :
    ACRw
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors)
      ((layer.factors M N).map fun factor => factor.evalAt x y) := by
  exact
    DFTerm.adjacent_compression_run
      x y (layer.endpoint M N).factors

end NRLayer

/--
At root weights, the natural endpoint collector and adjacent block compressor
form an explicit two-phase operational schedule.  The first phase records Hall
swaps and cutoff erasures.  The second phase compresses the selected endpoint
occurrences to the natural shape-run powers consumed by interpolation.
-/
structure NPCompre
    (d n : ℕ)
    (layer : NRLayer n 1 1) :
    Prop where
  truncatedOccurrenceRewrites :
    ∀ (M N : ℕ)
      (x y :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n),
      TORwa
        [x ^ M, y ^ N]
        (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
          [y ^ N, x ^ M])
  adjacentCompressionRewrites :
    ∀ (M N : ℕ)
      (x y :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n),
      ACRw
        (collapsedEvaluatedFactors x y (layer.endpoint M N).factors ++
          [y ^ N, x ^ M])
        (((layer.factors M N).map fun factor => factor.evalAt x y) ++
          [y ^ N, x ^ M])

namespace NPCompre

/-- The terminating cutoff-full collector constructs the two-phase schedule. -/
noncomputable def natural_recollect_layer
    {d n : ℕ}
    (layer : NRLayer n 1 1) :
    NPCompre.{u}
      d n layer where
  truncatedOccurrenceRewrites M N x y :=
    NTOcc.NRLayer.parentEndpointTrunc
      layer M N x y
  adjacentCompressionRewrites M N x y := by
    simpa using
      (NRLayer.endpoint_adjacent_rewrites
        layer M N x y).context [] [y ^ N, x ^ M]

/--
The two operational phases expose the swap equation for the compressed natural
shape-run packet before cancellation of the powered parents.
-/
lemma compressed_factors_swap
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      NPCompre.{u}
        d n layer)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    ((layer.factors M N).map fun factor => factor.evalAt x y).prod *
          y ^ N * x ^ M =
      x ^ M * y ^ N := by
  simpa [List.prod_append, mul_assoc] using
    (schedule.adjacentCompressionRewrites M N x y).list_prod_eq.trans
      (schedule.truncatedOccurrenceRewrites M N x y).list_prod_eq

/--
Cancellation of the swapped powered parents recovers the natural commutator
law directly from the explicit two-phase operational schedule.
-/
lemma compressed_factors_pow
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      NPCompre.{u}
        d n layer)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    ((layer.factors M N).map fun factor => factor.evalAt x y).prod =
      ⁅x ^ M, y ^ N⁆ := by
  have hswap :=
    schedule.compressed_factors_swap M N x y
  calc
    ((layer.factors M N).map fun factor => factor.evalAt x y).prod =
        ((layer.factors M N).map fun factor => factor.evalAt x y).prod *
            y ^ N * x ^ M * (x ^ M)⁻¹ * (y ^ N)⁻¹ := by
      group
    _ = x ^ M * y ^ N * (x ^ M)⁻¹ * (y ^ N)⁻¹ := by
      rw [hswap]
    _ = ⁅x ^ M, y ^ N⁆ := by
      rfl

end NPCompre

end
  NACompre
end TCTex
end Submission

/-!
# Natural endpoint alignment with the ordered retained packet

The finite-index endpoint kernel interpolates the selected cutoff-full
collector's concrete shape fibers.  When those word-local profiles agree with
the retained transversal, the sorted retained packet product is exactly the
literal selected endpoint product at every natural specialization.

This isolates the remaining arbitrary-cutoff theorem sharply: extend this
natural-cast identity to arbitrary integer exponents while preserving the
weight-controlled signed profiles.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  EOAlign

universe u


open scoped commutatorElement

open
  CFCollec
open
  CFCollec.DFTerm
open
  FCEnd
open
  FCEnd.IDTerms
open
  OOSched
open
  SOAlign
open
  CRLayer
open
  PCBridge
open
  FIBridge

/--
Word-local endpoint-profile agreement with the retained transversal identifies
the sorted retained packet product with the literal cutoff-full endpoint
product at every natural specialization.
-/
lemma
    ordered_coeff_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    (orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ)).prod =
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod := by
  unfold orderedEvaluatedFactors
  rw [←
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    NTOcc.EFInterp.endpoint_evaluated_factors
      kernel.fiberProfileInterpolation
        M N x y (by simp) (by simp) (by simp) (by simp)
          SCFactor.trunc_last_bot

/--
Consequently, word-local endpoint-profile agreement proves the sorted retained
packet law on the natural quadrant.
-/
lemma
    ordered_profile_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    (orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ)).prod =
      ⁅x ^ M, y ^ N⁆ := by
  calc
    (orderedEvaluatedFactors
          n x y (M : ℤ) (N : ℤ)).prod =
        (collapsedEvaluatedFactors x y
          (layer.endpoint M N).factors).prod :=
      ordered_coeff_alignment
        kernel hprofileAlignment M N x y
    _ = ⁅x ^ M, y ^ N⁆ := by
      simpa [collapsedEvaluatedFactors, collapsedList] using
        (layer.endpoint M N).collapsed_list_pow
          x y (by simp) (by simp) (by simp) (by simp)
            SCFactor.trunc_last_bot

end
  EOAlign
end TCTex
end Submission

/-!
# Operational identity padding for natural cutoff-full fixed slots

The natural cutoff-full endpoint compresses to one power for every retained
shape run.  Interpolation uses a fixed finite erased-shape vocabulary, so absent
run positions are padded with multiplicity zero.

This file turns that padding into a literal operational schedule.  A local step
inserts one identity factor.  Induction on `FSAlign` compiles every
zero-multiplicity slot into one such insertion while preserving all retained
factor positions.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  NIPaddin

universe u

open scoped commutatorElement

open
  NACompre
open
  CRLayer
open
  NRCoordi
open
  PCBridge

/-- One contextual insertion of an identity factor. -/
inductive IPStep
    {G : Type*}
    [Group G] :
    List G → List G → Prop where
  | insert
      (front back : List G) :
      IPStep
        (front ++ back)
        (front ++ [1] ++ back)

/-- Finite contextual identity-padding runs. -/
abbrev IPRw
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  Relation.ReflTransGen
    (@IPStep G _) source target

namespace IPStep

/-- Inserting one identity preserves the ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : IPStep source target) :
    target.prod = source.prod := by
  cases step with
  | insert front back =>
      simp [List.prod_append]

/-- Identity insertion remains valid in a list context. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : IPStep source target)
    (front back : List G) :
    IPStep
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  cases step with
  | insert innerFront innerBack =>
      simpa [List.append_assoc] using
        (IPStep.insert
          (front ++ innerFront) (innerBack ++ back))

end IPStep

namespace IPRw

/-- Every finite identity-padding run preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : IPRw source target) :
    target.prod = source.prod := by
  induction rewrites with
  | refl =>
      rfl
  | tail _ step ih =>
      exact step.list_prod_eq.trans ih

/-- Identity-padding runs remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : IPRw source target)
    (front back : List G) :
    IPRw
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih (step.context front back)

/-- Independently constructed padding runs compose under concatenation. -/
lemma append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left :
      IPRw leftSource leftTarget)
    (right :
      IPRw rightSource rightTarget) :
    IPRw
      (leftSource ++ rightSource)
      (leftTarget ++ rightTarget) := by
  have hleft :
      IPRw
        (leftSource ++ rightSource)
        (leftTarget ++ rightSource) := by
    simpa using left.context [] rightSource
  have hright :
      IPRw
        (leftTarget ++ rightSource)
        (leftTarget ++ rightTarget) := by
    simpa using right.context leftTarget []
  exact hleft.trans hright

end IPRw

namespace FSAlign

/--
Every fixed-slot alignment compiles to a finite identity-padding run after
evaluation in an arbitrary group.
-/
lemma identity_padding_rewrites :
    ∀ {factors skeleton slots}
      {G : Type*}
      [Group G]
      (x y : G)
      (_alignment : FSAlign factors skeleton slots),
        IPRw
          (factors.map fun factor => factor.evalAt x y)
          (slots.map fun factor => factor.evalAt x y) := by
  intro factors skeleton slots G _ x y alignment
  induction alignment with
  | nil =>
      exact Relation.ReflTransGen.refl
  | skip word _alignment ih =>
      apply ih.trans
      apply Relation.ReflTransGen.single
      simpa [NRFactor.evalAt] using
        (IPStep.insert (G := G) [] _)
  | keep factor alignment ih =>
      simpa using
        ih.context [factor.evalAt x y] []

end FSAlign

namespace NSCoordi

/-- Chosen natural fixed-slot coordinates inherit the literal padding run. -/
lemma identity_padding_rewrites
    {n leftWeight rightWeight M N : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    (coordinates : NSCoordi layer M N)
    {G : Type*}
    [Group G]
    (x y : G) :
    IPRw
      ((layer.factors M N).map fun factor => factor.evalAt x y)
      (coordinates.slots.map fun factor => factor.evalAt x y) :=
  FSAlign.identity_padding_rewrites
    x y coordinates.alignment

end NSCoordi

/-- Root-weight fixed-slot coordinates with their positivity proofs discharged. -/
noncomputable def naturalSlotCoordinates
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ) :
    NSCoordi layer M N :=
  fixedSlotCoordinates layer (by simp) (by simp) M N

/--
The natural root-weight collector, run compressor, and fixed-slot padder form
an explicit three-phase operational schedule.
-/
structure
    PSPaddin
    (d n : ℕ)
    (layer : NRLayer n 1 1) :
    Prop where
  compressionSchedule :
    NPCompre.{u}
      d n layer
  identityPaddingRewrites :
    ∀ (M N : ℕ)
      (x y :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n),
      IPRw
        (((layer.factors M N).map fun factor => factor.evalAt x y) ++
          [y ^ N, x ^ M])
        (((naturalSlotCoordinates layer M N).slots.map fun factor =>
            factor.evalAt x y) ++
          [y ^ N, x ^ M])

namespace
  PSPaddin

/-- The terminating cutoff-full collector constructs the three-phase schedule. -/
noncomputable def natural_recollect_layer
    {d n : ℕ}
    (layer : NRLayer n 1 1) :
    PSPaddin.{u}
      d n layer where
  compressionSchedule :=
    NPCompre.natural_recollect_layer
      layer
  identityPaddingRewrites M N x y := by
    simpa using
      NSCoordi.identity_padding_rewrites
        (naturalSlotCoordinates layer M N) x y
        |>.context [] [y ^ N, x ^ M]

/--
The three operational phases expose the swap equation for the padded
fixed-length natural packet before cancellation of the powered parents.
-/
lemma fixed_slot_swap
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      PSPaddin.{u}
        d n layer)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    ((naturalSlotCoordinates layer M N).slots.map fun factor =>
          factor.evalAt x y).prod *
          y ^ N * x ^ M =
      x ^ M * y ^ N := by
  calc
    ((naturalSlotCoordinates layer M N).slots.map fun factor =>
          factor.evalAt x y).prod *
          y ^ N * x ^ M =
        (((naturalSlotCoordinates layer M N).slots.map fun factor =>
            factor.evalAt x y) ++ [y ^ N, x ^ M]).prod := by
      simp [List.prod_append, mul_assoc]
    _ =
        (((layer.factors M N).map fun factor => factor.evalAt x y) ++
          [y ^ N, x ^ M]).prod :=
      (schedule.identityPaddingRewrites M N x y).list_prod_eq
    _ =
        ((layer.factors M N).map fun factor => factor.evalAt x y).prod *
          y ^ N * x ^ M := by
      simp [List.prod_append, mul_assoc]
    _ = x ^ M * y ^ N :=
      schedule.compressionSchedule.compressed_factors_swap M N x y

/--
Cancellation of the swapped powered parents recovers the natural commutator
law directly from the explicit three-phase operational schedule.
-/
lemma fixed_slot_pow
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      PSPaddin.{u}
        d n layer)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    ((naturalSlotCoordinates layer M N).slots.map fun factor =>
      factor.evalAt x y).prod =
        ⁅x ^ M, y ^ N⁆ := by
  have hswap :=
    schedule.fixed_slot_swap M N x y
  calc
    ((naturalSlotCoordinates layer M N).slots.map fun factor =>
        factor.evalAt x y).prod =
        ((naturalSlotCoordinates layer M N).slots.map fun factor =>
            factor.evalAt x y).prod *
          y ^ N * x ^ M * (x ^ M)⁻¹ * (y ^ N)⁻¹ := by
      group
    _ = x ^ M * y ^ N * (x ^ M)⁻¹ * (y ^ N)⁻¹ := by
      rw [hswap]
    _ = ⁅x ^ M, y ^ N⁆ := by
      rfl

end
  PSPaddin

end
  NIPaddin
end TCTex
end Submission

/-!
# Negative-quadrant boundary for the retained cutoff-full endpoint packet

Finite-index profile alignment and the concrete cutoff-full collector prove
the sorted retained packet law on the natural-natural quadrant.  The generic
integer-quadrant reduction therefore identifies the remaining arbitrary-cutoff
signed theorem with three explicit negative sign quadrants.

This file also packages those three laws as the all-integral endpoint
interpolation lift consumed by the Claim 5 route.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  OQBounda

universe u

open
  FPInterp
open
  OOSched
open
  SOAlign
open
  EOAlign
open
  CRLayer
open
  UNPkt
open
  FIBridge

/--
The sorted retained packet, equipped with its natural-natural law from the
selected cutoff-full endpoint collector.
-/
noncomputable def
    naturalProfileAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TBPkt.{u} d n where
  packets :=
    profileRecollectionPackets n
  list_nat_cast left right leftExponent rightExponent := by
    simpa only [orderedEvaluatedFactors] using
      ordered_profile_alignment
        kernel hprofileAlignment leftExponent rightExponent left right

@[simp]
lemma packets_natural_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    (naturalProfileAlignment
      (d := d) kernel hprofileAlignment).packets =
        profileRecollectionPackets n :=
  rfl

/--
For the endpoint-aligned sorted retained packet, the remaining signed theorem
is precisely the conjunction of its three negative sign-quadrant laws.
-/
abbrev OrderedQuadrantLaws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    Prop :=
  TBPkt.NegativeQuadrantLaws.{u}
    (naturalProfileAlignment
      (d := d) kernel hprofileAlignment)

/--
The three negative quadrants complete the sorted retained packet law at
arbitrary integer exponents.
-/
def
    satisfies_quadrant_laws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      OrderedQuadrantLaws.{u}
        (d := d) kernel hprofileAlignment) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allQuadrantLaws
    laws).listEval_eq

/--
At the selected cutoff-full endpoint, the sorted retained all-integral law is
equivalent to its three negative sign-quadrant laws.
-/
theorem
    quadrant_laws_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    SatisfiesCoefficientTruncated.{u} d n ↔
      OrderedQuadrantLaws.{u}
        (d := d) kernel hprofileAlignment := by
  constructor
  · intro hlistEval
    exact
      TBPkt.AILift.negativeQuadrantLaws
        (packet :=
          naturalProfileAlignment
            (d := d) kernel hprofileAlignment)
        {
          listEval_eq := by
            intro left right leftExponent rightExponent
            exact hlistEval left right leftExponent rightExponent
        }
  · exact
      satisfies_quadrant_laws
        kernel hprofileAlignment

/--
The three negative quadrants provide the all-integral endpoint interpolation
lift consumed by the signed-profile Claim 5 adapter.
-/
noncomputable def
    fiberQuadrantLaws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      OrderedQuadrantLaws.{u}
        (d := d) kernel hprofileAlignment) :
    EFInterp.AILift.{u}
      (d := d)
        kernel.fiberProfileInterpolation := by
  apply
    allLiftAlignment
  · exact
      coeff_profile_alignment
        kernel.signedProfileAssignment hprofileAlignment
  · exact
      satisfies_quadrant_laws
        kernel hprofileAlignment laws

namespace TSInput

/--
Finite-index endpoint profiles, retained-transversal profile alignment, and
the three negative sign quadrants instantiate the Claim 5 coordinate
polynomials.
-/
theorem
    selectedQuadrantLaws
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      OrderedQuadrantLaws.{u}
        (d := d) kernel hprofileAlignment)
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
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      (fiberQuadrantLaws
        kernel hprofileAlignment laws)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  OQBounda
end TCTex
end Submission

/-!
# Semantic alignment with the ordered retained packet

Literal equality of signed-profile records is stronger than cutoff-full
collection needs.  Distinct profile lists may denote the same bivariate
integer-valued coefficient function.  This file replaces literal alignment by
word-local equality of evaluated coefficients.

The integral extensionality theorem for homogeneous signed-block packets
shows that it is enough to compare profile values on the natural quadrant.
Consequently, two assignments which count the same concrete endpoint
shape-fibers are semantically aligned at every integral exponent pair.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  SABounda

universe u


open scoped commutatorElement

open
  CFCollec
open
  CFCollec.DFTerm
open
  FCEnd
open
  FCEnd.IDTerms
open
  FPInterp
open
  OOSched
open
  SOAlign
open
  NTOcc
open
  CRLayer
open
  NRSubinv
open
  CFSubsti
open
  CTAssigna
open
  RPThree
open
  FCAssign
open
  UCSuppor
open
  PCBridge
open
  FIBridge

/--
An assignment is semantically aligned with the retained transversal when its
profile value agrees word by word on the sorted cutoff-full vocabulary at
every pair of integral source exponents.
-/
def SemanticProfileAlignment
    {n : ℕ}
    (assignment : SPAssign n 1 1) :
    Prop :=
  ∀ (word : CWord HPAtom)
    (hword : word ∈ orderedErasedVocabulary n 1 1)
    (leftExponent rightExponent : ℤ),
      (assignment.profiles word
        (ordered_erased_vocabulary.mp hword)).value
          leftExponent rightExponent =
        ((blockProfileAssignment n)
          |>.toSPAssign.profiles word
            (ordered_erased_vocabulary.mp hword)).value
              leftExponent rightExponent

/--
Literal retained-profile alignment implies semantic alignment.
-/
lemma
    recipe_coeff_alignment
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (halignment :
      RetainedProfileAlignment assignment) :
    SemanticProfileAlignment assignment := by
  intro word hword leftExponent rightExponent
  rw [halignment word (ordered_erased_vocabulary.mp hword)]

/--
Two root-weight assignments which count the same concrete endpoint
shape-fibers on natural inputs agree semantically at every integral exponent
pair.
-/
lemma
    values_counts_fibers
    {n : ℕ}
    {layer : NRLayer n 1 1}
    (first second : SPAssign n 1 1)
    (hfirst :
      first.CountsFibersCast layer)
    (hsecond :
      second.CountsFibersCast layer) :
    ∀ (word : CWord HPAtom)
      (hword : word ∈ orderedErasedVocabulary n 1 1)
      (leftExponent rightExponent : ℤ),
        (first.profiles word
          (ordered_erased_vocabulary.mp hword)).value
            leftExponent rightExponent =
          (second.profiles word
            (ordered_erased_vocabulary.mp hword)).value
              leftExponent rightExponent := by
  intro word hword leftExponent rightExponent
  apply HFPkt.value_cast
  intro left right
  rw [hfirst left right word hword, hsecond left right word hword]

/--
If the retained transversal counts the selected natural endpoint fibers, any
other assignment counting those fibers is semantically aligned with it.
-/
lemma
    fibers_nat_cast
    {n : ℕ}
    {layer : NRLayer n 1 1}
    (assignment : SPAssign n 1 1)
    (hassignment :
      assignment.CountsFibersCast layer)
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer) :
    SemanticProfileAlignment assignment :=
  values_counts_fibers
    assignment
      ((blockProfileAssignment n)
        |>.toSPAssign)
    hassignment hretained

/--
Semantic profile alignment identifies the evaluated sorted packet lists,
without requiring equality of their profile syntax.
-/
lemma
    evaluated_semantic_alignment
    {G : Type*}
    [Group G]
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (halignment :
      SemanticProfileAlignment assignment)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    (assignment.erasedVocabPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent) =
      (profileRecollectionPackets n).map
        fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent := by
  classical
  unfold
    profileRecollectionPackets
  unfold SPAssign.erasedVocabPackets
  simp only [List.map_map]
  apply List.map_congr_left
  intro word _hword
  change
    word.1.eval (HPAtom.eval left right) ^
          (assignment.profiles word.1
            (ordered_erased_vocabulary.mp word.2)).value
              leftExponent rightExponent =
      word.1.eval (HPAtom.eval left right) ^
          ((blockProfileAssignment n)
            |>.toSPAssign.profiles word.1
              (ordered_erased_vocabulary.mp word.2)).value
                leftExponent rightExponent
  rw [halignment word.1 word.2 leftExponent rightExponent]

/--
Semantic retained-profile alignment transports the sorted retained packet law
to an arbitrary aligned profile assignment.
-/
lemma
    satisfies_trunc_coeff
    {d n : ℕ}
    (assignment : SPAssign n 1 1)
    (halignment :
      SemanticProfileAlignment assignment)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n) :
    ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (assignment.erasedVocabPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  intro left right leftExponent rightExponent
  rw [
    evaluated_semantic_alignment
      assignment halignment]
  exact hordered left right leftExponent rightExponent

/--
Semantic profile alignment identifies the retained sorted packet product with
the literal selected endpoint product at every natural specialization.
-/
lemma
    coeff_semantic_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (assignment : SPAssign n 1 1)
    (hcounts :
      assignment.CountsFibersCast layer)
    (halignment :
      SemanticProfileAlignment assignment)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    (orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ)).prod =
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod := by
  unfold orderedEvaluatedFactors
  calc
    ((profileRecollectionPackets n).map
          fun packet =>
            packet.word.eval (HPAtom.eval x y) ^
              packet.profiles.value (M : ℤ) (N : ℤ)).prod =
        (assignment.erasedVocabPackets.map fun packet =>
          packet.word.eval (HPAtom.eval x y) ^
            packet.profiles.value (M : ℤ) (N : ℤ)).prod := by
      rw [
        evaluated_semantic_alignment
          assignment halignment]
    _ =
        (collapsedEvaluatedFactors x y
          (layer.endpoint M N).factors).prod :=
      EFInterp.endpoint_evaluated_factors
        (assignment.fiberProfileInterpolation
          hcounts)
        M N x y (by simp) (by simp) (by simp) (by simp)
          SCFactor.trunc_last_bot

namespace
  EIFiber

/--
The selected endpoint kernel is semantically aligned with the retained
transversal as soon as the retained transversal counts its concrete endpoint
shape-fibers on natural inputs.
-/
lemma coeff_fibers_cast
    {n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer) :
    SemanticProfileAlignment
      kernel.signedProfileAssignment :=
  fibers_nat_cast
    kernel.signedProfileAssignment
      kernel.counts_fibers_assignment
        hretained

/--
Retained endpoint-fiber counting and the sorted retained packet law give the
selected endpoint kernel its all-integral signed list-evaluation law.
-/
def
    satisfiesFibersCoeff
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  satisfies_trunc_coeff
    kernel.signedProfileAssignment
      (coeff_fibers_cast
        kernel hretained)
      hordered

/--
The same semantic hypotheses package the signed lift consumed by the selected
endpoint interpolation route.
-/
def
    allCoeffTrunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n) :
    EIFiber.AILift.{u}
      (d := d) kernel :=
  kernel.allLiftSatisfies
    (satisfiesFibersCoeff
      kernel hretained hordered)

end
  EIFiber

namespace TSInput

/--
Retained endpoint-fiber counting on natural inputs and the sorted retained
packet law instantiate the Claim 5 coordinate polynomials.  Literal equality
between selected endpoint profile records and retained profile records is not
required.
-/
theorem
    coordPolyCounts
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n)
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
  _root_.Submission.TCTex.TSInput.coordTruncEval
    hn H hH kernel
      (EIFiber.satisfiesFibersCoeff
        kernel hretained hordered)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  SABounda
end TCTex
end Submission

/-!
# Natural-cast operational alignment with fixed-slot signed profiles

The natural cutoff-full collector now reaches a fixed-length padded coordinate
list by explicit Hall swaps, cutoff erasures, adjacent power merges, and
identity insertions.  Signed-profile interpolation evaluates to that same list
at natural casts.

This file proves the literal list equality, not merely equality of ordered
products, and transports the operational swap law to the interpolating packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  SPAlign

universe u

open scoped commutatorElement

open
  FSInterp
open
  NIPaddin
open
  CRLayer
open
  NRCoordi
open
  NRSubinv
open
  CFSubsti

/-- Evaluate signed-profile packets without changing their list order. -/
def signedEvaluatedFactors
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ)
    (packets : List RFPkt) :
    List G :=
  packets.map fun packet =>
    packet.word.eval (HPAtom.eval left right) ^
      packet.profiles.value leftExponent rightExponent

/-- Packet evaluation is the zip of the packet words and profile values. -/
lemma evaluated_zip_value
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ∀ packets : List RFPkt,
      signedEvaluatedFactors
          left right leftExponent rightExponent packets =
        List.zipWith
          (fun word exponent =>
            word.eval (HPAtom.eval left right) ^ exponent)
          (packets.map RFPkt.word)
          (packets.map fun packet =>
            packet.profiles.value leftExponent rightExponent)
  | [] =>
      rfl
  | packet :: packets => by
      simp only [signedEvaluatedFactors, List.map_cons,
        List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨True.intro,
        evaluated_zip_value
          left right leftExponent rightExponent packets⟩

/-- Slot evaluation is the zip of slot words and natural multiplicities. -/
lemma eval_zip_multiplicity
    {G : Type*}
    [Group G]
    (left right : G) :
    ∀ slots : List NRFactor,
      (slots.map fun factor => factor.evalAt left right) =
        List.zipWith
          (fun word multiplicity =>
            word.eval (HPAtom.eval left right) ^ multiplicity)
          (slots.map NRFactor.word)
          (slots.map NRFactor.multiplicity)
  | [] =>
      rfl
  | factor :: slots => by
      simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨rfl,
        eval_zip_multiplicity left right slots⟩

namespace NSInterp

/--
At natural casts, interpolating packet evaluation is literally the evaluated
padded coordinate list.
-/
lemma evaluated_slot_coordinates
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer hleftWeight hrightWeight packets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    signedEvaluatedFactors left right (M : ℤ) (N : ℤ) packets =
      ((fixedSlotCoordinates
        layer hleftWeight hrightWeight M N).slots.map fun factor =>
          factor.evalAt left right) := by
  calc
    signedEvaluatedFactors left right (M : ℤ) (N : ℤ) packets =
        List.zipWith
          (fun word exponent =>
            word.eval (HPAtom.eval left right) ^ exponent)
          (packets.map RFPkt.word)
          (packets.map fun packet =>
            packet.profiles.value (M : ℤ) (N : ℤ)) :=
      evaluated_zip_value
        left right (M : ℤ) (N : ℤ) packets
    _ =
        List.zipWith
          (fun word exponent =>
            word.eval (HPAtom.eval left right) ^ exponent)
          (orderedErasedVocabulary n leftWeight rightWeight)
          ((naturalSlotVector
            layer hleftWeight hrightWeight M N).map fun
              (multiplicity : ℕ) => (multiplicity : ℤ)) := by
      rw [interpolation.map_word_packets,
        interpolation.map_nat_cast]
    _ =
        List.zipWith
          (fun word multiplicity =>
            word.eval (HPAtom.eval left right) ^ multiplicity)
          (orderedErasedVocabulary n leftWeight rightWeight)
          (naturalSlotVector
            layer hleftWeight hrightWeight M N) :=
      zip_zpow_cast
        (orderedErasedVocabulary n leftWeight rightWeight)
        (naturalSlotVector
          layer hleftWeight hrightWeight M N)
        left right
    _ =
        List.zipWith
          (fun word multiplicity =>
            word.eval (HPAtom.eval left right) ^ multiplicity)
          ((fixedSlotCoordinates
            layer hleftWeight hrightWeight M N).slots.map
              NRFactor.word)
          ((fixedSlotCoordinates
            layer hleftWeight hrightWeight M N).slots.map
              NRFactor.multiplicity) := by
      rw [naturalSlotVector,
        (fixedSlotCoordinates layer hleftWeight hrightWeight M N)
          |>.slots_erased_vocabulary]
    _ =
        ((fixedSlotCoordinates
          layer hleftWeight hrightWeight M N).slots.map fun factor =>
            factor.evalAt left right) :=
      (eval_zip_multiplicity left right
        (fixedSlotCoordinates
          layer hleftWeight hrightWeight M N).slots).symm

/--
At root weights, the interpolating packet evaluates literally to the selected
root fixed-slot coordinate list.
-/
lemma evaluated_slot_coords
    {n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer (by simp) (by simp) packets)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (left right : G) :
    signedEvaluatedFactors left right (M : ℤ) (N : ℤ) packets =
      ((naturalSlotCoordinates layer M N).slots.map fun factor =>
        factor.evalAt left right) := by
  exact
    evaluated_slot_coordinates
      interpolation M N left right

end NSInterp

namespace
  PSPaddin

/--
At natural casts, the explicit three-phase schedule exposes the swap equation
for the interpolating fixed-slot signed-profile packet.
-/
lemma signed_profile_swap
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      PSPaddin.{u}
        d n layer)
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer (by simp) (by simp) packets)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    (signedEvaluatedFactors x y (M : ℤ) (N : ℤ)
        packets).prod *
          y ^ N * x ^ M =
      x ^ M * y ^ N := by
  rw [
    NSInterp.evaluated_slot_coords
      interpolation]
  exact schedule.fixed_slot_swap M N x y

/--
Cancellation of the swapped powered parents recovers the natural commutator
law for the interpolating packet from the explicit operational schedule.
-/
lemma signed_profile_pow
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (schedule :
      PSPaddin.{u}
        d n layer)
    {packets : List RFPkt}
    (interpolation :
      NSInterp
        layer (by simp) (by simp) packets)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    (signedEvaluatedFactors x y (M : ℤ) (N : ℤ)
      packets).prod =
        ⁅x ^ M, y ^ N⁆ := by
  rw [
    NSInterp.evaluated_slot_coords
      interpolation]
  exact schedule.fixed_slot_pow M N x y

end
  PSPaddin

end
  SPAlign
end TCTex
end Submission

/-!
# Inverted-base recollection boundary for the retained cutoff-full endpoint

The selected cutoff-full endpoint collector proves the sorted retained packet
law at natural source multiplicities.  Its remaining signed extension can be
stated concretely as compatibility with replacing a negative source exponent
by a positive natural magnitude at an inverted group base.

This file transports that generic naturalization boundary through the retained
endpoint profile alignment and exposes the resulting Claim 5 adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  NINatura

universe u

open
  FPInterp
open
  SOAlign
open
  OQBounda
open
  CRLayer
open
  UNPkt
open
  FIBridge

/--
The three inverted-base recollection laws for the endpoint-aligned sorted
retained packet.
-/
abbrev InputNaturalizationLaws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    Prop :=
  TBPkt.NegativeNaturalizationLaws.{u}
    (naturalProfileAlignment
      (d := d) kernel hprofileAlignment)

/--
Inverted-base recollection supplies the three negative sign quadrants for the
sorted retained packet.
-/
def
    quadrantLawsNaturalization
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      InputNaturalizationLaws.{u}
        (d := d) kernel hprofileAlignment) :
    OrderedQuadrantLaws.{u}
      (d := d) kernel hprofileAlignment :=
  TBPkt.quadrantInputNaturalization
    laws

/--
At the selected cutoff-full endpoint, the full sorted retained signed law is
equivalent to its three inverted-base recollection laws.
-/
theorem
    satisfies_laws_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    SatisfiesCoefficientTruncated.{u} d n ↔
      InputNaturalizationLaws.{u}
        (d := d) kernel hprofileAlignment := by
  constructor
  · intro hlistEval
    exact
      TBPkt.AILift.negativeNaturalizationLaws
          (packet :=
            naturalProfileAlignment
              (d := d) kernel hprofileAlignment)
          {
            listEval_eq := by
              intro left right leftExponent rightExponent
              exact hlistEval left right leftExponent rightExponent
          }
  · intro laws
    exact
      satisfies_quadrant_laws
        kernel hprofileAlignment
          (quadrantLawsNaturalization
            kernel hprofileAlignment laws)

/--
The three inverted-base recollection laws provide the all-integral endpoint
interpolation lift consumed by Claim 5.
-/
noncomputable def
    inputNaturalizationLaws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      InputNaturalizationLaws.{u}
        (d := d) kernel hprofileAlignment) :
    EFInterp.AILift.{u}
      (d := d)
        kernel.fiberProfileInterpolation :=
  fiberQuadrantLaws
    kernel hprofileAlignment
      (quadrantLawsNaturalization
        kernel hprofileAlignment laws)

namespace TSInput

/--
Finite-index endpoint profiles, retained-transversal profile alignment, and
the three inverted-base recollection laws instantiate the Claim 5 coordinate
polynomials.
-/
theorem
    coordNaturalizationLaws
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      InputNaturalizationLaws.{u}
        (d := d) kernel hprofileAlignment)
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
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      (inputNaturalizationLaws
        kernel hprofileAlignment laws)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  NINatura
end TCTex
end Submission

/-!
# Fixed-slot operational alignment for the ordered retained packet

The selected finite-index endpoint kernel interpolates the sorted retained
recipe-coefficient packet whenever its word-local profiles agree with the
retained transversal.  The cutoff-full collector now reaches that same packet
by an explicit sequence of swaps, cutoff erasures, adjacent power merges, and
identity insertions.

This file specializes the generic fixed-slot operational bridge to the exact
ordered retained packet used by the Claim 5 boundary.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  FSBounda

universe u

open scoped commutatorElement

open
  FSInterp
open
  FPInterp
open
  OOSched
open
  SOAlign
open
  NIPaddin
open
  SPAlign
open
  CRLayer
open
  NRSubinv
open
  FIBridge

/--
At natural casts, the exact sorted retained recipe-coefficient packet is
literally the evaluated fixed-slot coordinate list reached by the collector.
-/
lemma
    coeff_coords_alignment
    {n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (M N : ℕ)
    {G : Type*}
    [Group G]
    (x y : G) :
    orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ) =
      ((naturalSlotCoordinates layer M N).slots.map fun factor =>
        factor.evalAt x y) := by
  unfold orderedEvaluatedFactors
  rw [←
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    NSInterp.evaluated_slot_coords
      (kernel.fiberProfileInterpolation
        |>.naturalFixedInterpolation (by simp) (by simp))
      M N x y

/--
The explicit collector exposes the pre-cancellation swap equation for the
exact sorted retained recipe-coefficient packet.
-/
lemma
    recipe_profile_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    (orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ)).prod *
          y ^ N * x ^ M =
      x ^ M * y ^ N := by
  rw [
    coeff_coords_alignment
      kernel hprofileAlignment]
  exact
    (PSPaddin.natural_recollect_layer
      layer).fixed_slot_swap M N x y

/--
After cancellation, the exact sorted retained recipe-coefficient packet
computes the commutator of the naturally powered parents.
-/
lemma
    ordered_profile_alignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n) :
    (orderedEvaluatedFactors
        n x y (M : ℤ) (N : ℤ)).prod =
      ⁅x ^ M, y ^ N⁆ := by
  rw [
    coeff_coords_alignment
      kernel hprofileAlignment]
  exact
    (PSPaddin.natural_recollect_layer
      layer).fixed_slot_pow M N x y

end
  FSBounda
end TCTex
end Submission

/-!
# Cutoff-aware negative-input transports for the retained endpoint packet

The selected cutoff-full endpoint already supplies the sorted retained packet
law at natural source multiplicities.  The remaining all-integral theorem can
be constructed operationally by recollecting each negative-input packet list
into its natural-magnitude packet list at inverted group bases.

This file packages those three cutoff-aware occurrence transports and proves
that they supply the negative-input naturalization laws consumed by Claim 5.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  TOTrans

universe u

open
  FPInterp
open
  OOSched
open
  SOAlign
open
  OQBounda
open
  NINatura
open
  CRLayer
open
  UNPkt
open
  PCBridge
open
  FIBridge

/--
Cutoff-aware recollection transports from the three negative-input sorted
packet lists to their positive-magnitude lists at inverted group bases.
-/
structure
    IOTransp
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      TORwa
        (orderedEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (orderedEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      TORwa
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (orderedEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      TORwa
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
        (orderedEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  IOTransp

/--
The three cutoff-aware negative-input transports supply the semantic
inverted-base naturalization laws for the endpoint-aligned packet.
-/
def naturalizationLawsAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    InputNaturalizationLaws.{u}
      (d := d) kernel hprofileAlignment where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packets_natural_alignment]
        using
        (transports.rightNegative
          left right leftExponent rightMagnitude).list_prod_eq.symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packets_natural_alignment]
        using
        (transports.leftNegative
          left right leftMagnitude rightExponent).list_prod_eq.symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packets_natural_alignment]
        using
        (transports.bothNegative
          left right leftMagnitude rightMagnitude).list_prod_eq.symm

/--
The three cutoff-aware negative-input transports complete the sorted retained
packet law at arbitrary integral exponents.
-/
def satisfiesProfileAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfies_quadrant_laws
    kernel hprofileAlignment
      (quadrantLawsNaturalization
        kernel hprofileAlignment
          (naturalizationLawsAlignment
            kernel hprofileAlignment transports))

/--
The three cutoff-aware negative-input transports provide the all-integral
endpoint interpolation lift consumed by Claim 5.
-/
noncomputable def
    endpointFiberAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    EFInterp.AILift.{u}
      (d := d)
        kernel.fiberProfileInterpolation :=
  inputNaturalizationLaws
    kernel hprofileAlignment
      (naturalizationLawsAlignment
        kernel hprofileAlignment transports)

namespace TSInput

/--
Finite-index endpoint profiles, retained-transversal profile alignment, and
the three cutoff-aware negative-input transports instantiate the Claim 5
coordinate polynomials.
-/
theorem
    alignmentOccTransports
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n)
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
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      (endpointFiberAlignment
        kernel hprofileAlignment transports)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  IOTransp

end
  TOTrans
end TCTex
end Submission

/-!
# Operational signed obstruction for the ordered retained endpoint packet

The explicit cutoff-full collector proves the sorted retained packet law on the
natural quadrant by swaps, cutoff erasures, adjacent power merges, and identity
insertions.  The remaining signed extension is exactly the family of three
negative-input occurrence transports.

This file feeds that operational presentation into the selected finite-index
endpoint profile kernel consumed by the Claim 5 polynomial constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  FTTrans

universe u

open scoped commutatorElement

open
  OOSched
open
  SOAlign
open
  FSBounda
open
  TOTrans
open
  CRLayer
open
  UNPkt
open
  FIBridge

/--
The sorted retained packet with its natural-quadrant law supplied by the
explicit fixed-slot collector.
-/
noncomputable def
    coeffProfileAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TBPkt.{u} d n where
  packets :=
    profileRecollectionPackets n
  list_nat_cast left right leftExponent rightExponent := by
    simpa only [orderedEvaluatedFactors] using
      ordered_profile_alignment
        kernel hprofileAlignment leftExponent rightExponent left right

@[simp]
lemma
    packetsProfileAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    (coeffProfileAlignment
      (d := d) kernel hprofileAlignment).packets =
        profileRecollectionPackets n :=
  rfl

/--
The existing occurrence transports naturalize all three negative-input
quadrants of the operationally justified retained packet.
-/
def
    naturalizationLawsTransports
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    TBPkt.NegativeNaturalizationLaws.{u}
      (coeffProfileAlignment
        (d := d) kernel hprofileAlignment) where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (transports.rightNegative
          left right leftExponent rightMagnitude).list_prod_eq.symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (transports.leftNegative
          left right leftMagnitude rightExponent).list_prod_eq.symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (transports.bothNegative
          left right leftMagnitude rightMagnitude).list_prod_eq.symm

/--
The explicit natural collector and the three negative-input occurrence
transports prove the all-integral sorted retained packet law.
-/
def
    satisfiesOperationalAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allNaturalizationLaws
    (naturalizationLawsTransports
      kernel hprofileAlignment transports)).listEval_eq

/--
The operational retained-packet law transports across profile alignment to the
selected endpoint finite-index kernel.
-/
def
    satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  rw [
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    satisfiesOperationalAlignment
      kernel hprofileAlignment transports left right leftExponent rightExponent

namespace TSInput

/--
The explicit natural collector, retained-profile alignment, and the three
negative-input occurrence transports instantiate the Claim 5 coordinate
polynomials.
-/
theorem
    inputOccTransports
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      IOTransp.{u}
        d n)
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
  input.coordTruncEval
    hn H hH kernel
      (satisfiesTruncAlignment
        kernel hprofileAlignment transports)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  FTTrans
end TCTex
end Submission

/-!
# Root-swap mirrored negative-input transports for the retained endpoint packet

Reverse root-swap gives a symbolic packet presentation of inverse ordered
products.  The mirrored cutoff-aware Hall collector from the imported boundary
therefore provides an equivalent orientation for the three negative-input
transports consumed by Claim 5.

This file packages that orientation and converts it to the existing endpoint
transport interface.  It is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  RTTrans

universe u

open
  FPInterp
open
  OOSched
open
  SOAlign
open
  TOTrans
open
  CRLayer
open
  FRSwap
open
  TOMirror
open
  PCBridge
open
  FIBridge

/--
Evaluate the reverse root-swapped retained endpoint packet.
-/
def swapEvaluatedFactors
    {G : Type*}
    [Group G]
    (n : ℕ)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    List G :=
  packetEvaluatedFactors
    (rootSwapPackets
      (profileRecollectionPackets n))
    left right leftExponent rightExponent

/--
The reverse root-swapped retained endpoint packet evaluates to the
reverse-inverse transport of the original factor list.
-/
lemma swap_evaluated_factors
    {G : Type*}
    [Group G]
    (n : ℕ)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    swapEvaluatedFactors
        n left right leftExponent rightExponent =
      reverseInverseFactors
        (orderedEvaluatedFactors
          n left right leftExponent rightExponent) := by
  rw [swapEvaluatedFactors,
    evaluated_swap_packets]
  rfl

/--
Mirrored cutoff-aware recollection transports between reverse root-swapped
negative-input packet lists and their positive-magnitude counterparts.
-/
structure
    TOTransp
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      TORw
        (swapEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (swapEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      TORw
        (swapEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (swapEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      TORw
        (swapEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
        (swapEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  TOTransp

/--
The mirrored root-swap orientation converts to the ordinary negative-input
transport interface by reverse-inverse involutivity.
-/
def inputOccurrenceTransports
    {d n : ℕ}
    (transports :
      TOTransp.{u}
        d n) :
    IOTransp.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    rw [←
      trailing_rewrites_reverse]
    simpa only [
      swap_evaluated_factors] using
        transports.rightNegative left right leftExponent rightMagnitude
  leftNegative left right leftMagnitude rightExponent := by
    rw [←
      trailing_rewrites_reverse]
    simpa only [
      swap_evaluated_factors] using
        transports.leftNegative left right leftMagnitude rightExponent
  bothNegative left right leftMagnitude rightMagnitude := by
    rw [←
      trailing_rewrites_reverse]
    simpa only [
      swap_evaluated_factors] using
        transports.bothNegative left right leftMagnitude rightMagnitude

/--
The mirrored root-swap transports supply the all-integral endpoint
interpolation lift consumed by Claim 5.
-/
noncomputable def
    endpointFiberAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      TOTransp.{u}
        d n) :
    EFInterp.AILift.{u}
      (d := d)
        kernel.fiberProfileInterpolation :=
  IOTransp.endpointFiberAlignment
    kernel hprofileAlignment
      transports.inputOccurrenceTransports

namespace TSInput

/--
Mirrored root-swap negative-input transports instantiate the Claim 5
coordinate polynomials after conversion to the ordinary occurrence
orientation.
-/
theorem
    trailingOccTransports
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transports :
      TOTransp.{u}
        d n)
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
  input.fiberInterpolationLift
    hn H hH kernel.fiberProfileInterpolation
      (endpointFiberAlignment
        kernel hprofileAlignment transports)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  TOTransp

end
  RTTrans
end TCTex
end Submission


/-!
# Negative-input parent-pair schedules for the fixed-slot packet

The natural endpoint collector already proves the positive-magnitude branch
after replacing every negative input by an inverted base.  A signed collector
therefore does not need to recollect both packet lists from a common source.
It is enough to construct one directed run from the naturalized powered parent
pair to the negative-input fixed-slot packet followed by the swapped parents.

This file packages that smaller collector-native obligation and records the
corresponding Claim 5 adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  TOSched

universe u

open
  OOSched
open
  SOAlign
open
  FSBounda
open
  FTTrans
open
  CRLayer
open
  UNPkt
open
  PTOcc
open
  PCBridge
open
  FIBridge

/--
Directed negative-input recollection runs from naturalized powered parent
pairs to the negative fixed-slot packet followed by the swapped parents.
-/
structure
    TOSchedu
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      TORwa
        [left ^ leftExponent, right⁻¹ ^ (rightMagnitude + 1)]
        (orderedEvaluatedFactors
            n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude) ++
          [right⁻¹ ^ (rightMagnitude + 1), left ^ leftExponent])
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      TORwa
        [left⁻¹ ^ (leftMagnitude + 1), right ^ rightExponent]
        (orderedEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ) ++
          [right ^ rightExponent, left⁻¹ ^ (leftMagnitude + 1)])
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      TORwa
        [left⁻¹ ^ (leftMagnitude + 1), right⁻¹ ^ (rightMagnitude + 1)]
        (orderedEvaluatedFactors
            n left right (Int.negSucc leftMagnitude)
              (Int.negSucc rightMagnitude) ++
          [right⁻¹ ^ (rightMagnitude + 1), left⁻¹ ^ (leftMagnitude + 1)])

namespace
  TOSchedu

/--
An all-integral ordered parent-pair occurrence schedule specializes directly
to the three directed negative-input schedules.
-/
def coeff_occ_schedule
    {d n : ℕ}
    (schedule :
      COScheda.{u} d n) :
    TOSchedu.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    apply TORwa.ofOccurrenceRewrites
    simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
      schedule.rewrites
        left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)
  leftNegative left right leftMagnitude rightExponent := by
    apply TORwa.ofOccurrenceRewrites
    simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
      schedule.rewrites
        left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)
  bothNegative left right leftMagnitude rightMagnitude := by
    apply TORwa.ofOccurrenceRewrites
    simpa only [zpow_negSucc, ← inv_pow] using
      schedule.rewrites
        left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)

/--
The right-negative schedule and the positive inverse-base endpoint schedule
have the same trailing swapped parents, so their packet products agree.
-/
lemma right_negative_prod
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightMagnitude : ℕ) :
    (orderedEvaluatedFactors
        n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)).prod =
      (orderedEvaluatedFactors
        n left right⁻¹ (leftExponent : ℤ)
          ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
  apply mul_right_cancel
  calc
    (orderedEvaluatedFactors
          n left right (leftExponent : ℤ)
            (Int.negSucc rightMagnitude)).prod *
        (right⁻¹ ^ (rightMagnitude + 1) * left ^ leftExponent) =
      left ^ leftExponent * right⁻¹ ^ (rightMagnitude + 1) := by
        simpa [List.prod_append, mul_assoc] using
          (schedules.rightNegative
            left right leftExponent rightMagnitude).list_prod_eq
    _ =
      (orderedEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ)).prod *
        (right⁻¹ ^ (rightMagnitude + 1) * left ^ leftExponent) := by
      simpa [mul_assoc] using
        (recipe_profile_alignment
          kernel hprofileAlignment leftExponent (rightMagnitude + 1)
            left right⁻¹).symm

/--
The left-negative schedule and the positive inverse-base endpoint schedule
have the same trailing swapped parents, so their packet products agree.
-/
lemma left_negative_prod
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftMagnitude rightExponent : ℕ) :
    (orderedEvaluatedFactors
        n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)).prod =
      (orderedEvaluatedFactors
        n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
          (rightExponent : ℤ)).prod := by
  apply mul_right_cancel
  calc
    (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude)
            (rightExponent : ℤ)).prod *
        (right ^ rightExponent * left⁻¹ ^ (leftMagnitude + 1)) =
      left⁻¹ ^ (leftMagnitude + 1) * right ^ rightExponent := by
        simpa [List.prod_append, mul_assoc] using
          (schedules.leftNegative
            left right leftMagnitude rightExponent).list_prod_eq
    _ =
      (orderedEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ)).prod *
        (right ^ rightExponent * left⁻¹ ^ (leftMagnitude + 1)) := by
      simpa [mul_assoc] using
        (recipe_profile_alignment
          kernel hprofileAlignment (leftMagnitude + 1) rightExponent
            left⁻¹ right).symm

/--
The both-negative schedule and the positive inverse-base endpoint schedule
have the same trailing swapped parents, so their packet products agree.
-/
lemma both_negative_prod
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftMagnitude rightMagnitude : ℕ) :
    (orderedEvaluatedFactors
        n left right (Int.negSucc leftMagnitude)
          (Int.negSucc rightMagnitude)).prod =
      (orderedEvaluatedFactors
        n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
          ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
  apply mul_right_cancel
  calc
    (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude)
            (Int.negSucc rightMagnitude)).prod *
        (right⁻¹ ^ (rightMagnitude + 1) * left⁻¹ ^ (leftMagnitude + 1)) =
      left⁻¹ ^ (leftMagnitude + 1) * right⁻¹ ^ (rightMagnitude + 1) := by
        simpa [List.prod_append, mul_assoc] using
          (schedules.bothNegative
            left right leftMagnitude rightMagnitude).list_prod_eq
    _ =
      (orderedEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ)).prod *
        (right⁻¹ ^ (rightMagnitude + 1) *
          left⁻¹ ^ (leftMagnitude + 1)) := by
      simpa [mul_assoc] using
        (recipe_profile_alignment
          kernel hprofileAlignment (leftMagnitude + 1) (rightMagnitude + 1)
            left⁻¹ right⁻¹).symm

/--
Negative parent-pair schedules naturalize the three signed quadrants of the
operationally justified fixed-slot packet.
-/
def negativeInputNaturalization
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n) :
    TBPkt.NegativeNaturalizationLaws.{u}
      (coeffProfileAlignment
        (d := d) kernel hprofileAlignment) where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        schedules.right_negative_prod
          kernel hprofileAlignment left right leftExponent rightMagnitude
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        schedules.left_negative_prod
          kernel hprofileAlignment left right leftMagnitude rightExponent
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        schedules.both_negative_prod
          kernel hprofileAlignment left right leftMagnitude rightMagnitude

/--
Conversely, the three semantic naturalization laws produce one-step
parent-pair schedules.  The single obstruction step exposes the packet as the
correction block for the naturalized powered parent pair.
-/
def negative_naturalization_laws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (laws :
      TBPkt.NegativeNaturalizationLaws.{u}
        (coeffProfileAlignment
          (d := d) kernel hprofileAlignment)) :
    TOSchedu.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    apply TORwa.ofOccurrenceRewrites
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] []
        (left ^ leftExponent)
        (right⁻¹ ^ (rightMagnitude + 1))
        (orderedEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (by
          have hnaturalization :
              (orderedEvaluatedFactors
                  n left right (leftExponent : ℤ)
                    (Int.negSucc rightMagnitude)).prod =
                (orderedEvaluatedFactors
                  n left right⁻¹ (leftExponent : ℤ)
                    ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
            simpa only [
              orderedEvaluatedFactors,
              packetsProfileAlignment] using
                laws.rightNegative left right leftExponent rightMagnitude
          rw [hnaturalization]
          exact
            recipe_profile_alignment
              kernel hprofileAlignment leftExponent (rightMagnitude + 1)
                left right⁻¹))
  leftNegative left right leftMagnitude rightExponent := by
    apply TORwa.ofOccurrenceRewrites
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] []
        (left⁻¹ ^ (leftMagnitude + 1))
        (right ^ rightExponent)
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (by
          have hnaturalization :
              (orderedEvaluatedFactors
                  n left right (Int.negSucc leftMagnitude)
                    (rightExponent : ℤ)).prod =
                (orderedEvaluatedFactors
                  n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                    (rightExponent : ℤ)).prod := by
            simpa only [
              orderedEvaluatedFactors,
              packetsProfileAlignment] using
                laws.leftNegative left right leftMagnitude rightExponent
          rw [hnaturalization]
          exact
            recipe_profile_alignment
              kernel hprofileAlignment (leftMagnitude + 1) rightExponent
                left⁻¹ right))
  bothNegative left right leftMagnitude rightMagnitude := by
    apply TORwa.ofOccurrenceRewrites
    apply Relation.ReflTransGen.single
    simpa using
      (COStep.obstruction
        [] []
        (left⁻¹ ^ (leftMagnitude + 1))
        (right⁻¹ ^ (rightMagnitude + 1))
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude)
            (Int.negSucc rightMagnitude))
        (by
          have hnaturalization :
              (orderedEvaluatedFactors
                  n left right (Int.negSucc leftMagnitude)
                    (Int.negSucc rightMagnitude)).prod =
                (orderedEvaluatedFactors
                  n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                    ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
            simpa only [
              orderedEvaluatedFactors,
              packetsProfileAlignment] using
                laws.bothNegative left right leftMagnitude rightMagnitude
          rw [hnaturalization]
          exact
            recipe_profile_alignment
              kernel hprofileAlignment (leftMagnitude + 1)
                (rightMagnitude + 1) left⁻¹ right⁻¹))

/--
For the operational fixed-slot packet, constructing negative parent-pair
schedules is exactly equivalent to proving the three negative-input
naturalization laws.
-/
theorem
    parent_naturalization_laws
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TOSchedu.{u}
        d n ↔
      TBPkt.NegativeNaturalizationLaws.{u}
        (coeffProfileAlignment
          (d := d) kernel hprofileAlignment) :=
  ⟨negativeInputNaturalization kernel hprofileAlignment,
    negative_naturalization_laws kernel hprofileAlignment⟩

/--
Any semantic all-integral law for the sorted retained packet gives explicit
negative parent-pair schedules by first exposing its all-integral ordered
parent-pair occurrence schedule.
-/
def satisfies_ordered_trunc
    {d n : ℕ}
    (hlistEval :
      SatisfiesCoefficientTruncated.{u} d n) :
    TOSchedu.{u}
      d n :=
  coeff_occ_schedule
    (COScheda.satisfies_ordered_trunc
      hlistEval)

/--
The explicit natural collector and negative parent-pair schedules prove the
all-integral sorted retained packet law.
-/
def satisfiesOperationalAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allNaturalizationLaws
    (negativeInputNaturalization
      kernel hprofileAlignment schedules)).listEval_eq

/--
For an operationally aligned endpoint kernel, explicit negative parent-pair
schedules are equivalent to the semantic all-integral sorted retained-packet
law.
-/
theorem
    negative_input_parent
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TOSchedu.{u}
        d n ↔
      SatisfiesCoefficientTruncated.{u} d n :=
  ⟨satisfiesOperationalAlignment
      kernel hprofileAlignment,
    satisfies_ordered_trunc⟩

/--
The operational retained-packet law transports across profile alignment to
the selected endpoint finite-index kernel.
-/
def satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  rw [
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    satisfiesOperationalAlignment
      kernel hprofileAlignment schedules
        left right leftExponent rightExponent

namespace TSInput

/--
Negative-input parent-pair schedules instantiate the Claim 5 coordinate
polynomials.
-/
theorem
    coordOccSchedules
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      TOSchedu.{u}
        d n)
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
  input.coordTruncEval
    hn H hH kernel
      (satisfiesTruncAlignment
        kernel hprofileAlignment schedules)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  TOSchedu

end
  TOSched
end TCTex
end Submission

/-!
# Symmetric cutoff-aware occurrence spans for negative inputs

The cutoff-full collector is directed: one raw occurrence list recollects
forward to one endpoint list.  Comparing two endpoints naturally gives a
zigzag through their common source rather than a directed recollection from one
endpoint to the other.

This file records the equivalence closure of cutoff-aware Hall steps, proves
that it preserves ordered products, and packages common-source spans for the
three negative-input substitutions.  These spans are sufficient for the signed
list law and therefore for the Claim 5 coordinate-polynomial constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  TOEquivb

universe u

open
  OOSched
open
  SOAlign
open
  FTTrans
open
  TOTrans
open
  CRLayer
open
  UNPkt
open
  PCBridge
open
  FIBridge

/--
The symmetric transitive closure of cutoff-aware Hall collection steps.
-/
abbrev TOEquivc
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  Relation.EqvGen (@TOStepa G _) source target

namespace TOEquivc

/-- Every directed cutoff-aware run is a cutoff-aware zigzag. -/
lemma ofRewrites
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORwa source target) :
    TOEquivc source target := by
  induction rewrites with
  | refl =>
      exact Relation.EqvGen.refl _
  | tail _ step ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.rel _ _ step)

/-- Every cutoff-aware zigzag preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquivc source target) :
    target.prod = source.prod := by
  induction equivalence with
  | rel source target step =>
      exact step.list_prod_eq
  | refl source =>
      rfl
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ ihLeft ihRight =>
      exact ihRight.trans ihLeft

/-- Cutoff-aware zigzags remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquivc source target)
    (front back : List G) :
    TOEquivc
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _ (step.context front back)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

/--
Two directed collections from a common source give a cutoff-aware zigzag
between their endpoints.
-/
lemma ofCommonSource
    {G : Type*}
    [Group G]
    {origin left right : List G}
    (leftRewrites : TORwa origin left)
    (rightRewrites : TORwa origin right) :
    TOEquivc left right :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (ofRewrites leftRewrites))
    (ofRewrites rightRewrites)

/--
Two directed collections to a common target also give a cutoff-aware zigzag.
-/
lemma ofCommonTarget
    {G : Type*}
    [Group G]
    {left right target : List G}
    (leftRewrites : TORwa left target)
    (rightRewrites : TORwa right target) :
    TOEquivc left right :=
  Relation.EqvGen.trans _ _ _
    (ofRewrites leftRewrites)
    (Relation.EqvGen.symm _ _ (ofRewrites rightRewrites))

end TOEquivc

/--
Symmetric cutoff-aware recollection witnesses for the three negative-input
substitutions.
-/
structure
    IOEquiva
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      TOEquivc
        (orderedEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (orderedEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      TOEquivc
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (orderedEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      TOEquivc
        (orderedEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
        (orderedEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  IOEquiva

/-- Directed negative-input transports embed into symmetric zigzags. -/
def truncatedOccurrenceTransports
    {d n : ℕ}
    (transports :
      IOTransp.{u}
        d n) :
    IOEquiva.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude :=
    TOEquivc.ofRewrites
      (transports.rightNegative left right leftExponent rightMagnitude)
  leftNegative left right leftMagnitude rightExponent :=
    TOEquivc.ofRewrites
      (transports.leftNegative left right leftMagnitude rightExponent)
  bothNegative left right leftMagnitude rightMagnitude :=
    TOEquivc.ofRewrites
      (transports.bothNegative left right leftMagnitude rightMagnitude)

/--
Symmetric negative-input zigzags naturalize the three signed quadrants of the
operationally justified retained packet.
-/
def negativeInputNaturalization
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (equivalences :
      IOEquiva.{u}
        d n) :
    TBPkt.NegativeNaturalizationLaws.{u}
      (coeffProfileAlignment
        (d := d) kernel hprofileAlignment) where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (equivalences.rightNegative
          left right leftExponent rightMagnitude).list_prod_eq.symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (equivalences.leftNegative
          left right leftMagnitude rightExponent).list_prod_eq.symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        (equivalences.bothNegative
          left right leftMagnitude rightMagnitude).list_prod_eq.symm

/--
The explicit natural collector and symmetric negative-input zigzags prove the
all-integral sorted retained packet law.
-/
def
    satisfiesOperationalAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (equivalences :
      IOEquiva.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allNaturalizationLaws
    (negativeInputNaturalization
      kernel hprofileAlignment equivalences)).listEval_eq

/--
The operational retained-packet law transports across profile alignment to the
selected endpoint finite-index kernel.
-/
def
    satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (equivalences :
      IOEquiva.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  rw [
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    satisfiesOperationalAlignment
      kernel hprofileAlignment equivalences left right
        leftExponent rightExponent

end
  IOEquiva

/--
Concrete common-source spans for the three negative-input substitutions.
-/
structure
    OCSpans
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      ∃ origin,
        TORwa origin
          (orderedEvaluatedFactors
            n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)) ∧
        TORwa origin
          (orderedEvaluatedFactors
            n left right⁻¹ (leftExponent : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      ∃ origin,
        TORwa origin
          (orderedEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)) ∧
        TORwa origin
          (orderedEvaluatedFactors
            n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
              (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      ∃ origin,
        TORwa origin
          (orderedEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)) ∧
        TORwa origin
          (orderedEvaluatedFactors
            n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  OCSpans

/-- Every common-source span supplies a symmetric negative-input zigzag. -/
def toEquivalences
    {d n : ℕ}
    (spans :
      OCSpans.{u}
        d n) :
    IOEquiva.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    rcases spans.rightNegative left right leftExponent rightMagnitude with
      ⟨origin, hleft, hright⟩
    exact TOEquivc.ofCommonSource hleft hright
  leftNegative left right leftMagnitude rightExponent := by
    rcases spans.leftNegative left right leftMagnitude rightExponent with
      ⟨origin, hleft, hright⟩
    exact TOEquivc.ofCommonSource hleft hright
  bothNegative left right leftMagnitude rightMagnitude := by
    rcases spans.bothNegative left right leftMagnitude rightMagnitude with
      ⟨origin, hleft, hright⟩
    exact TOEquivc.ofCommonSource hleft hright

namespace TSInput

/--
The explicit natural collector, retained-profile alignment, and three
common-source negative-input spans instantiate the Claim 5 coordinate
polynomials.
-/
theorem
    coordCommonSpans
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (spans :
      OCSpans.{u}
        d n)
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
  input.coordTruncEval
    hn H hH kernel
      (IOEquiva.satisfiesTruncAlignment
        kernel hprofileAlignment spans.toEquivalences)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  OCSpans

end
  TOEquivb
end TCTex
end Submission

/-!
# Phase-aware all-integral parent-pair schedules

The positive natural branch of the cutoff-full collector has three literal
operational phases: cutoff-aware occurrence rewrites, adjacent compression of
equal factors into powers, and insertion of identity factors for absent fixed
slots.  The final padding phase is intentionally not hidden inside the
cutoff-aware occurrence relation, whose native identity move points in the
opposite direction.

This file packages that honest positive branch together with the three direct
negative-input occurrence schedules.  Consequently an arbitrary-cutoff signed
collector has one remaining obligation: construct the directed negative-input
runs.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  PPSched

universe u

open scoped commutatorElement

open
  OOSched
open
  SOAlign
open
  NACompre
open
  NIPaddin
open
  FSBounda
open
  TOSched
open
  CRLayer
open
  PCBridge
open
  FIBridge

/--
A literal three-phase run: collect occurrences with cutoff erasures, compress
adjacent equal factors into powers, then insert identity padding.
-/
def CPRw
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  ∃ occurrenceTarget compressionTarget : List G,
    TORwa source occurrenceTarget ∧
      ACRw occurrenceTarget compressionTarget ∧
        IPRw compressionTarget target

namespace CPRw

/-- Every three-phase run preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites :
      CPRw
        source target) :
    target.prod = source.prod := by
  rcases rewrites with
    ⟨occurrenceTarget, compressionTarget, hoccurrence, hcompression,
      hpadding⟩
  exact
    hpadding.list_prod_eq.trans
      (hcompression.list_prod_eq.trans hoccurrence.list_prod_eq)

end CPRw

/--
A signed parent-pair run is either a direct cutoff-aware occurrence run or
the positive natural branch's three-phase run.
-/
inductive PPRw
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop where
  | truncated
      (rewrites : TORwa source target) :
      PPRw source target
  | positiveNatural
      (rewrites :
        CPRw
          source target) :
      PPRw source target

namespace PPRw

/-- Every signed parent-pair phase run preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : PPRw source target) :
    target.prod = source.prod := by
  cases rewrites with
  | truncated rewrites =>
      exact rewrites.list_prod_eq
  | positiveNatural rewrites =>
      exact rewrites.list_prod_eq

end PPRw

/--
After retained-profile alignment, the natural cutoff-full collector reaches
the exact sorted retained fixed-slot packet by its three native phases.
-/
noncomputable def
    parentPhaseRewrites
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℕ) :
    CPRw
      [left ^ leftExponent, right ^ rightExponent]
      (orderedEvaluatedFactors
          n left right (leftExponent : ℤ) (rightExponent : ℤ) ++
        [right ^ rightExponent, left ^ leftExponent]) := by
  let schedule :=
    PSPaddin.natural_recollect_layer
      (d := d) layer
  refine
    ⟨
        collapsedEvaluatedFactors
            left right (layer.endpoint leftExponent rightExponent).factors ++
          [right ^ rightExponent, left ^ leftExponent],
        ((layer.factors leftExponent rightExponent).map fun factor =>
            factor.evalAt left right) ++
          [right ^ rightExponent, left ^ leftExponent],
        schedule.compressionSchedule.truncatedOccurrenceRewrites
          leftExponent rightExponent left right,
        schedule.compressionSchedule.adjacentCompressionRewrites
          leftExponent rightExponent left right,
        ?_⟩
  rw [
    coeff_coords_alignment
      kernel hprofileAlignment]
  exact schedule.identityPaddingRewrites
    leftExponent rightExponent left right

/--
The honest operational data for every sign quadrant: the automa
constructed three-phase natural branch and direct cutoff-aware occurrence
runs for the other three branches.
-/
structure PPSchedu
    (d n : ℕ)
    (layer : NRLayer n 1 1)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    Prop where
  positiveNatural :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℕ),
      CPRw
        [left ^ leftExponent, right ^ rightExponent]
        (orderedEvaluatedFactors
            n left right (leftExponent : ℤ) (rightExponent : ℤ) ++
          [right ^ rightExponent, left ^ leftExponent])
  negativeInput :
    TOSchedu.{u}
      d n

namespace PPSchedu

/--
The explicit natural collector fills the positive branch automa, so
the three directed negative schedules construct the all-integral phase
package.
-/
noncomputable def parent_occ_schedules
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (negativeInput :
      TOSchedu.{u}
        d n) :
    PPSchedu.{u}
      d n layer kernel hprofileAlignment where
  positiveNatural :=
    parentPhaseRewrites
      kernel hprofileAlignment
  negativeInput := negativeInput

/--
For an aligned operational endpoint, all-integral phase schedules are exactly
the three directed negative-input schedules.
-/
theorem
    phase_schedules_occurrence
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    PPSchedu.{u}
        d n layer kernel hprofileAlignment ↔
      TOSchedu.{u}
        d n :=
  ⟨negativeInput,
    parent_occ_schedules
      kernel hprofileAlignment⟩

/--
Case analysis on the two integer exponents presents every signed parent-pair
run through one phase-aware interface.
-/
def rewrites
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {kernel :
      EIFiber
        layer (by simp) (by simp)}
    {hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment}
    (schedules :
      PPSchedu.{u}
        d n layer kernel hprofileAlignment)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    PPRw
      [left ^ leftExponent, right ^ rightExponent]
      (orderedEvaluatedFactors
          n left right leftExponent rightExponent ++
        [right ^ rightExponent, left ^ leftExponent]) := by
  cases leftExponent with
  | ofNat leftExponent =>
      cases rightExponent with
      | ofNat rightExponent =>
          apply PPRw.positiveNatural
          simpa only [zpow_natCast] using
            schedules.positiveNatural
              left right leftExponent rightExponent
      | negSucc rightMagnitude =>
          apply PPRw.truncated
          simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
            schedules.negativeInput.rightNegative
              left right leftExponent rightMagnitude
  | negSucc leftMagnitude =>
      cases rightExponent with
      | ofNat rightExponent =>
          apply PPRw.truncated
          simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
            schedules.negativeInput.leftNegative
              left right leftMagnitude rightExponent
      | negSucc rightMagnitude =>
          apply PPRw.truncated
          simpa only [zpow_negSucc, ← inv_pow] using
            schedules.negativeInput.bothNegative
              left right leftMagnitude rightMagnitude

/--
Every signed phase run exposes the swap equation before cancellation of the
powered parents.
-/
lemma evaluated_factors_swap
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {kernel :
      EIFiber
        layer (by simp) (by simp)}
    {hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment}
    (schedules :
      PPSchedu.{u}
        d n layer kernel hprofileAlignment)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod *
          right ^ rightExponent * left ^ leftExponent =
      left ^ leftExponent * right ^ rightExponent := by
  simpa [List.prod_append, mul_assoc] using
    (schedules.rewrites left right leftExponent rightExponent).list_prod_eq

/--
Every all-integral phase package supplies the semantic sorted retained packet
law consumed by Claim 5.
-/
def satisfiesCoefficientTruncated
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {kernel :
      EIFiber
        layer (by simp) (by simp)}
    {hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment}
    (schedules :
      PPSchedu.{u}
        d n layer kernel hprofileAlignment) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  change
    (orderedEvaluatedFactors
        n left right leftExponent rightExponent).prod =
      ⁅left ^ leftExponent, right ^ rightExponent⁆
  have hswap :=
    schedules.evaluated_factors_swap
      left right leftExponent rightExponent
  calc
    (orderedEvaluatedFactors
          n left right leftExponent rightExponent).prod =
        (orderedEvaluatedFactors
              n left right leftExponent rightExponent).prod *
            right ^ rightExponent * left ^ leftExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      group
    _ =
        left ^ leftExponent * right ^ rightExponent *
          (left ^ leftExponent)⁻¹ * (right ^ rightExponent)⁻¹ := by
      rw [hswap]
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
      rfl

/--
For an aligned endpoint, the phase-aware operational package is equivalent to
the semantic all-integral sorted retained-packet law.
-/
theorem
    all_parent_trunc
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    PPSchedu.{u}
        d n layer kernel hprofileAlignment ↔
      SatisfiesCoefficientTruncated.{u} d n :=
  ⟨satisfiesCoefficientTruncated,
    fun hlistEval =>
      parent_occ_schedules
        kernel hprofileAlignment
          (TOSchedu.satisfies_ordered_trunc
              hlistEval)⟩

/--
The phase-aware sorted retained-packet law transports across profile alignment
to the selected endpoint finite-index kernel.
-/
def satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {kernel :
      EIFiber
        layer (by simp) (by simp)}
    {hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment}
    (schedules :
      PPSchedu.{u}
        d n layer kernel hprofileAlignment) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  rw [
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    schedules.satisfiesCoefficientTruncated
      left right leftExponent rightExponent

namespace TSInput

/--
Phase-aware all-integral parent-pair schedules instantiate the Claim 5
coordinate polynomials.
-/
theorem
    parentPhaseSchedules
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedules :
      PPSchedu.{u}
        d n layer kernel hprofileAlignment)
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
  input.coordTruncEval
    hn H hH kernel
      schedules.satisfiesTruncAlignment
      hsourceSupported factorNormalization hinputWeight

end TSInput

end PPSchedu

end
  PPSched
end TCTex
end Submission

/-!
# Negative-input parent-pair schedules through cutoff four

Through cutoff four, the sorted retained-transversal packet already has its
semantic signed recollection law.  Its all-integral ordered occurrence
schedule therefore produces explicit directed negative-input parent-pair
runs.  The retained singleton profiles also count the selected endpoint trace
exactly, so they give an aligned operational profile kernel for the Claim 5
adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  CTBounda

universe u

open
  FFCard
open
  OOSched
open
  SOAlign
open
  TOSched
open
  CRLayer
open
  NRSubinv
open
  FUClass
open
  CTAssigna
open
  UCSuppor
open
  RITrace
open
  FIBridge

/--
Through cutoff four, the shallow all-integral ordered occurrence schedule
specializes to the three directed negative-input parent-pair schedules.
-/
noncomputable def input_parent_schedules
    {d n : ℕ}
    (hn : n ≤ 4) :
    TOSchedu.{u}
      d n :=
  TOSchedu.coeff_occ_schedule
    (COScheda.n_four hn)

/--
Through cutoff four, the retained singleton profiles themselves form a
selected endpoint finite-index trace profile kernel.
-/
noncomputable def
    idxNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    EIFiber
      layer (by simp) (by simp) where
  profiles word hword :=
    retainedRecipeProfiles ⟨word, hword⟩
  profiles_nat_trace M N word hword := by
    calc
      (retainedRecipeProfiles ⟨word, hword⟩).value
          (M : ℤ) (N : ℤ) =
        (endpointRecipeMultiplicity layer M N word : ℤ) := by
          exact
            signed_n_four
              layer hn M N word
                (ordered_erased_vocabulary.mpr hword)
      _ =
        (((selectedFullEndpoint
          layer M N (by simp) (by simp)).filter fun index =>
            decide
              ((retainedOrbitKey index).erasedShape =
                word)).length : ℤ) := by
          exact_mod_cast
            (filter_key_mult
              layer M N (by simp) (by simp) word).symm

/--
The retained-profile selected endpoint kernel is definitionally aligned with
the sorted retained-transversal packet.
-/
lemma
    coeffNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    RetainedProfileAlignment
      (idxNFour
        layer hn).signedProfileAssignment := by
  intro word hword
  rfl

/--
The explicit negative-input schedules and retained-profile alignment give the
selected endpoint kernel its full signed list-evaluation law.
-/
def
    idxSatisfiesTrunc
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (hn : n ≤ 4) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d)
      (idxNFour
        layer hn) :=
  TOSchedu.satisfiesTruncAlignment
    (idxNFour
      layer hn)
    (coeffNFour
      layer hn)
    (input_parent_schedules hn)

namespace TSInput

/--
Through cutoff four, the retained-profile selected endpoint kernel and the
explicit directed negative-input schedules construct the Claim 5 coordinate
polynomials.
-/
theorem
    coordPolyFour
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
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
  TOSched.TOSchedu.TSInput.coordOccSchedules
    hn H hH
      (idxNFour
        layer hn4)
      (coeffNFour
        layer hn4)
      (input_parent_schedules hn4)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

/--
Through cutoff four, local factor normalizations promote the explicit
negative-input parent-pair scheduler route to the complete quantified Claim 5
power input.
-/
theorem
    schedules_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (factorNormalization :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          ∀ lowerWeight : ℕ,
            ¬n ≤ 2 * lowerWeight →
              TSNormalb
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight + 1) H →
                ∀ (factor : SPFactora H inputWeight),
                  factor.word.weight PEAddres.weight =
                      lowerWeight →
                    factor.word.weight PEAddres.weight < n →
              TANorm
                (n := n) (lowerWeight := lowerWeight) H factor) :
    ∀ (e : HEFam H) (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) H e inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hOne : inputWeight = 1
  · subst inputWeight
    exact
      TSInput.coordPolyFour
        (layer := layer) hn hn4 H hH
          (TSInput.classThreeSource
            hn4 e)
          (TSInput.word_least_source
            hn4 e)
          (factorNormalization 1 (by omega)) (by omega)
  · exact
      collected_profiles_below
        hn H hH hinputWeight (by omega)
          (idxNFour
            layer hn4)
          (idxSatisfiesTrunc
            layer hn4)
          (factorNormalization inputWeight hinputWeight)

end
  CTBounda
end TCTex
end Submission

/-!
# Mirrored symmetric occurrence spans for negative inputs

Reverse root-swap transports leading-correction cutoff collection to the
trailing-correction orientation.  Completed endpoints are compared most
naturally by symmetric zigzags through a common raw source.

This file lifts reverse-inverse transport from directed runs to equivalence
closures, specializes it to the retained endpoint packet, and supplies a Claim
5 coordinate-polynomial adapter from mirrored common-source spans.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  RTEquiv

universe u

open
  SOAlign
open
  TOEquivb
open
  RTTrans
open
  CRLayer
open
  TOMirror
open
  PCBridge
open
  FIBridge

/--
The symmetric transitive closure of mirrored trailing-correction cutoff-aware
Hall collection steps.
-/
abbrev TOEquiv
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  Relation.EqvGen (@TTOccur G _) source target

namespace TOEquiv

/-- Every directed mirrored run is a mirrored cutoff-aware zigzag. -/
lemma ofRewrites
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORw source target) :
    TOEquiv source target := by
  induction rewrites with
  | refl =>
      exact Relation.EqvGen.refl _
  | tail _ step ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.rel _ _ step)

/-- Every mirrored cutoff-aware zigzag preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquiv source target) :
    target.prod = source.prod := by
  induction equivalence with
  | rel source target step =>
      exact step.list_prod_eq
  | refl source =>
      rfl
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ ihLeft ihRight =>
      exact ihRight.trans ihLeft

/-- Mirrored cutoff-aware zigzags remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquiv source target)
    (front back : List G) :
    TOEquiv
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _ (step.context front back)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

/-- Two mirrored collections from a common source give an endpoint zigzag. -/
lemma ofCommonSource
    {G : Type*}
    [Group G]
    {origin left right : List G}
    (leftRewrites : TORw origin left)
    (rightRewrites : TORw origin right) :
    TOEquiv left right :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (ofRewrites leftRewrites))
    (ofRewrites rightRewrites)

end TOEquiv

/--
Reverse-inverse transport carries ordinary cutoff-aware zigzags to mirrored
trailing-correction zigzags.
-/
lemma equivalence_trailing_reverse
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquivc source target) :
    TOEquiv
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _
        (trailing_reverse_factors step)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

/--
Reverse-inverse transport carries mirrored zigzags back to ordinary
leading-correction zigzags.
-/
lemma trailing_equivalence_leading
    {G : Type*}
    [Group G]
    {source target : List G}
    (equivalence : TOEquiv source target) :
    TOEquivc
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _
        (trailing_occurrence_leading step)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

/--
Ordinary cutoff-aware zigzags are exactly mirrored zigzags after
reverse-inverse transport.
-/
theorem trailing_equivalence_reverse
    {G : Type*}
    [Group G]
    {source target : List G} :
    TOEquiv
        (reverseInverseFactors source) (reverseInverseFactors target) ↔
      TOEquivc source target := by
  constructor
  · intro equivalence
    simpa using
      trailing_equivalence_leading
        equivalence
  · exact equivalence_trailing_reverse

/--
Mirrored symmetric recollection witnesses for the reverse root-swapped
negative-input retained packets.
-/
structure
    TOEquiva
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      TOEquiv
        (swapEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (swapEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      TOEquiv
        (swapEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (swapEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      TOEquiv
        (swapEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
        (swapEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  TOEquiva

/--
Mirrored reverse root-swap zigzags convert to ordinary negative-input
zigzags by reverse-inverse involutivity.
-/
def inputOccurrenceEquivalences
    {d n : ℕ}
    (equivalences :
      TOEquiva.{u}
        d n) :
    IOEquiva.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    rw [←
      trailing_equivalence_reverse]
    simpa only [
      swap_evaluated_factors] using
        equivalences.rightNegative left right leftExponent rightMagnitude
  leftNegative left right leftMagnitude rightExponent := by
    rw [←
      trailing_equivalence_reverse]
    simpa only [
      swap_evaluated_factors] using
        equivalences.leftNegative left right leftMagnitude rightExponent
  bothNegative left right leftMagnitude rightMagnitude := by
    rw [←
      trailing_equivalence_reverse]
    simpa only [
      swap_evaluated_factors] using
        equivalences.bothNegative left right leftMagnitude rightMagnitude

namespace TSInput

/--
Mirrored reverse root-swap zigzags instantiate the Claim 5 coordinate
polynomials after conversion to ordinary cutoff-aware zigzags.
-/
theorem
    trailingOccEquivalences
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (equivalences :
      TOEquiva.{u}
        d n)
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
  input.coordTruncEval
    hn H hH kernel
      (IOEquiva.satisfiesTruncAlignment
        kernel hprofileAlignment
          equivalences.inputOccurrenceEquivalences)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  TOEquiva

/--
Mirrored common-source spans for the reverse root-swapped negative-input
retained packet lists.
-/
structure
    SOSpans
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      ∃ origin,
        TORw origin
          (swapEvaluatedFactors
            n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)) ∧
        TORw origin
          (swapEvaluatedFactors
            n left right⁻¹ (leftExponent : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      ∃ origin,
        TORw origin
          (swapEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)) ∧
        TORw origin
          (swapEvaluatedFactors
            n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
              (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      ∃ origin,
        TORw origin
          (swapEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude)) ∧
        TORw origin
          (swapEvaluatedFactors
            n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  SOSpans

/-- Every mirrored common-source span supplies a mirrored zigzag. -/
def toEquivalences
    {d n : ℕ}
    (spans :
      SOSpans.{u}
        d n) :
    TOEquiva.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    rcases spans.rightNegative left right leftExponent rightMagnitude with
      ⟨origin, hleft, hright⟩
    exact TOEquiv.ofCommonSource hleft hright
  leftNegative left right leftMagnitude rightExponent := by
    rcases spans.leftNegative left right leftMagnitude rightExponent with
      ⟨origin, hleft, hright⟩
    exact TOEquiv.ofCommonSource hleft hright
  bothNegative left right leftMagnitude rightMagnitude := by
    rcases spans.bothNegative left right leftMagnitude rightMagnitude with
      ⟨origin, hleft, hright⟩
    exact TOEquiv.ofCommonSource hleft hright

/--
Reverse-inverse involutivity converts mirrored common-source spans to ordinary
leading-correction common-source spans while preserving their paired-forward
collection presentation.
-/
def occurrenceCommonSpans
    {d n : ℕ}
    (spans :
      SOSpans.{u}
        d n) :
    OCSpans.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    rcases spans.rightNegative left right leftExponent rightMagnitude with
      ⟨origin, hleft, hright⟩
    refine ⟨reverseInverseFactors origin, ?_, ?_⟩
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hleft
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hright
  leftNegative left right leftMagnitude rightExponent := by
    rcases spans.leftNegative left right leftMagnitude rightExponent with
      ⟨origin, hleft, hright⟩
    refine ⟨reverseInverseFactors origin, ?_, ?_⟩
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hleft
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hright
  bothNegative left right leftMagnitude rightMagnitude := by
    rcases spans.bothNegative left right leftMagnitude rightMagnitude with
      ⟨origin, hleft, hright⟩
    refine ⟨reverseInverseFactors origin, ?_, ?_⟩
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hleft
    · simpa only [
        swap_evaluated_factors,
        reverse_inverse_factors] using
          trailing_rewrites_leading
            hright

namespace TSInput

/--
Mirrored reverse root-swap common-source spans instantiate the Claim 5
coordinate polynomials.
-/
theorem
    coordOccSpans
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (spans :
      SOSpans.{u}
        d n)
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
  TOEquiva.TSInput.trailingOccEquivalences
    hn H hH kernel hprofileAlignment spans.toEquivalences input
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  SOSpans

end
  RTEquiv
end TCTex
end Submission


/-!
# Homomorphic naturality of cutoff-aware occurrence collection

Universal Hall collection schedules should be constructed once and then
specialized to a target group.  This file proves that the leading-correction
and trailing-correction occurrence relations, their finite runs, and their
symmetric zigzag closures all transport through an arbitrary group
homomorphism.

Reverse-inverse factor transport also commutes with homomorphic mapping.  Thus
the ordinary and mirrored collectors may both be specialized after symbolic
collection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  OHNat

open
  PTOcc
open
  PCBridge
open
  TOMirror
open
  TOEquivb
open
  RTEquiv

/-- Ordered list products commute with group homomorphisms. -/
lemma list_prod_hom
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    (factors : List G) :
    (factors.map f).prod = f factors.prod := by
  induction factors with
  | nil =>
      simp
  | cons factor factors ih =>
      simp [ih]

/-- Leading-correction adjacent swaps transport through group homomorphisms. -/
lemma coefficient_occurrence_step
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (step : COStep source target) :
    COStep
      (source.map f) (target.map f) := by
  cases step with
  | obstruction front back left right corrections hswap =>
      simpa [List.map_append] using
        (COStep.obstruction
          (front.map f) (back.map f)
          (f left) (f right) (corrections.map f)
          (by simpa [list_prod_hom] using congrArg f hswap))

/-- Finite leading-correction runs transport through group homomorphisms. -/
lemma coefficient_occurrence_rewrites
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (rewrites : CORw source target) :
    CORw
      (source.map f) (target.map f) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih
        (coefficient_occurrence_step f step)

/-- Leading-correction cutoff-aware steps transport through group homomorphisms. -/
lemma truncated_occurrence_step
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (step : TOStepa source target) :
    TOStepa (source.map f) (target.map f) := by
  cases step with
  | swap step =>
      exact TOStepa.swap
        (coefficient_occurrence_step f step)
  | erase front back factor hfactor =>
      simpa [List.map_append] using
        (TOStepa.erase
          (front.map f) (back.map f) (f factor)
          (by simp [hfactor]))

/-- Finite leading-correction cutoff-aware runs transport through group homomorphisms. -/
lemma occurrence_rewrites
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (rewrites : TORwa source target) :
    TORwa (source.map f) (target.map f) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih (truncated_occurrence_step f step)

/-- Leading-correction cutoff-aware zigzags transport through group homomorphisms. -/
lemma truncated_occurrence_equivalence
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (equivalence : TOEquivc source target) :
    TOEquivc (source.map f) (target.map f) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _ (truncated_occurrence_step f step)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

/-- Reverse-inverse factor transport commutes with homomorphic mapping. -/
lemma reverse_factors
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    (factors : List G) :
    reverseInverseFactors (factors.map f) =
      (reverseInverseFactors factors).map f := by
  simp [reverseInverseFactors, List.map_reverse, List.map_map]

/-- Trailing-correction adjacent swaps transport through group homomorphisms. -/
lemma trailing_occurrence_step
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (step :
      TOStep source target) :
    TOStep
      (source.map f) (target.map f) := by
  cases step with
  | obstruction front back left right corrections hswap =>
      simpa [List.map_append] using
        (TOStep.obstruction
          (front.map f) (back.map f)
          (f left) (f right) (corrections.map f)
          (by simpa [list_prod_hom] using congrArg f hswap))

/-- Trailing-correction cutoff-aware steps transport through group homomorphisms. -/
lemma trailing_truncated_occurrence
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (step : TTOccur source target) :
    TTOccur (source.map f) (target.map f) := by
  cases step with
  | swap step =>
      exact TTOccur.swap
        (trailing_occurrence_step f step)
  | erase front back factor hfactor =>
      simpa [List.map_append] using
        (TTOccur.erase
          (front.map f) (back.map f) (f factor)
          (by simp [hfactor]))

/-- Finite trailing-correction cutoff-aware runs transport through group homomorphisms. -/
lemma trailing_occurrence_rewrites
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (rewrites : TORw source target) :
    TORw
      (source.map f) (target.map f) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih
        (trailing_truncated_occurrence f step)

/-- Trailing-correction cutoff-aware zigzags transport through group homomorphisms. -/
lemma trailing_occurrence_equivalence
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {source target : List G}
    (equivalence : TOEquiv source target) :
    TOEquiv
      (source.map f) (target.map f) := by
  induction equivalence with
  | rel source target step =>
      exact Relation.EqvGen.rel _ _
        (trailing_truncated_occurrence f step)
  | refl source =>
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans source middle target _ _ ihLeft ihRight =>
      exact Relation.EqvGen.trans _ _ _ ihLeft ihRight

end
  OHNat
end TCTex
end Submission

/-!
# Uniform support-avoidance profile families

The homogeneous support-avoidance compiler is recursively closed under
same-shape concatenation and Cartesian correction grids.  This file packages
that recursion uniformly over the two natural source multiplicities.

Two such uniform parent families, together with one compatible witness pair
at each multiplicity, directly provide the profile-family input consumed by
the compatible-grid selected-correction compiler.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  AAProf

open HACoeff
open CCAggreg
open CCGrida
open CFAlg
open CFSubsti
open SEComp
open SFAppend
open SFSpec
open HSPacket
open
  CCGrid

/--
A multiplicity-independent homogeneous support-avoidance packet family
specialized by concrete decorated parent terms at every natural multiplicity
pair.  The witness records that the concrete list is uniformly nonempty.
-/
structure USAvoida
    (K : ℕ)
    (shape : CWord HPAtom) where
  terms :
    ∀ M N : ℕ, List (DFTerm M N K)
  packets :
    ∀ _slots : Finset (Fin K),
      HFPkt
        shape.pairLeftDegree shape.pairRightDegree
  expressions :
    ∀ (M N : ℕ) (slots : Finset (Fin K)),
      SAExpr
        (terms M N) slots
        shape.pairLeftDegree shape.pairRightDegree
  specialization :
    ∀ M N : ℕ,
      SASpec
        (terms M N) packets (expressions M N)
  shape_eq :
    ∀ (M N : ℕ) term,
      term ∈ terms M N →
        term.erasedShape = shape
  witness :
    ∀ M N : ℕ, DFTerm M N K
  witness_mem :
    ∀ M N : ℕ, witness M N ∈ terms M N

namespace USAvoida

/--
Concatenate two uniform support-avoidance families carrying the same erased
shape.  Their fixed homogeneous formula packets add pointwise.
-/
def append
    {K : ℕ}
    {shape : CWord HPAtom}
    (left right : USAvoida K shape) :
    USAvoida K shape where
  terms M N :=
    left.terms M N ++ right.terms M N
  packets slots :=
    FPkt.add (left.packets slots) (right.packets slots)
  expressions M N slots :=
    appendExpression
      (left.expressions M N slots) (right.expressions M N slots)
  specialization M N :=
    appendSpecialization
      (left.specialization M N) (right.specialization M N)
  shape_eq M N term hterm := by
    rcases List.mem_append.mp hterm with hterm | hterm
    · exact left.shape_eq M N term hterm
    · exact right.shape_eq M N term hterm
  witness M N :=
    left.witness M N
  witness_mem M N :=
    List.mem_append_left _ (left.witness_mem M N)

/--
Cartesian correction of two uniform support-avoidance families.  The concrete
term lists form a correction grid and their fixed homogeneous formula packets
multiply pointwise.
-/
noncomputable def correctionGrid
    {K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (left : USAvoida K leftShape)
    (right : USAvoida K rightShape) :
    USAvoida K
      (CWord.commutator leftShape rightShape) where
  terms M N :=
    DFTerm.correctionGrid (left.terms M N) (right.terms M N)
  packets slots := by
    simpa only [CWord.pair_left_commutator,
      CWord.pair_degree_commutator] using
        FPkt.multiply (left.packets slots) (right.packets slots)
  expressions M N slots := by
    simpa only [CWord.pair_left_commutator,
      CWord.pair_degree_commutator] using
        SAExpr.correctionGrid
          (left.expressions M N slots) (right.expressions M N slots)
  specialization M N := by
    simpa only [CWord.pair_left_commutator,
      CWord.pair_degree_commutator] using
        SASpec.correctionGrid
          (left.specialization M N) (right.specialization M N)
  shape_eq M N term hterm := by
    rcases List.mem_flatMap.mp hterm with ⟨leftTerm, hleftTerm, hterm⟩
    rcases List.mem_map.mp hterm with ⟨rightTerm, hrightTerm, rfl⟩
    rw [DFTerm.erasedShape_corr,
      left.shape_eq M N leftTerm hleftTerm,
      right.shape_eq M N rightTerm hrightTerm]
  witness M N :=
    (left.witness M N).correction (right.witness M N)
  witness_mem M N := by
    apply List.mem_flatMap.mpr
    exact
      ⟨left.witness M N, left.witness_mem M N,
        List.mem_map.mpr
          ⟨right.witness M N, right.witness_mem M N, rfl⟩⟩

/--
Package two uniform parent families as the compatible-grid profile-family
input expected by the selected-correction polynomial compiler.
-/
noncomputable def compatibleGridFamily
    {K : ℕ}
    {leftShape rightShape : CWord HPAtom}
    (left : USAvoida K leftShape)
    (right : USAvoida K rightShape)
    (hcompatible :
      ∀ M N : ℕ,
        correctionPairCompatible (left.witness M N) (right.witness M N)) :
    CGFam K leftShape rightShape where
  leftTerms :=
    left.terms
  rightTerms :=
    right.terms
  leftPackets :=
    left.packets
  rightPackets :=
    right.packets
  leftExpressions :=
    left.expressions
  rightExpressions :=
    right.expressions
  leftSpecialization :=
    left.specialization
  rightSpecialization :=
    right.specialization
  leftShape_eq :=
    left.shape_eq
  rightShape_eq :=
    right.shape_eq
  leftWitness :=
    left.witness
  rightWitness :=
    right.witness
  leftWitness_mem :=
    left.witness_mem
  rightWitness_mem :=
    right.witness_mem
  witness_compatible :=
    hcompatible

end USAvoida

end
  AAProf
end TCTex
end Submission


/-!
# Natural common-source spans for cutoff-aware occurrence collection

Two forward Hall collections from a common raw factor list are the operational
form needed by the signed negative-input collector.  This file packages that
presentation independently of the particular retained packet, proves that it
specializes through group homomorphisms, and relates its leading-correction and
trailing-correction forms by reverse-inverse transport.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CSNat

open
  PCBridge
open
  TOMirror
open
  TOEquivb
open
  RTEquiv
open
  OHNat

/--
A paired-forward leading-correction collection from one common raw factor
list.
-/
abbrev OCSpan
    {G : Type*}
    [Group G]
    (left right : List G) :
    Prop :=
  ∃ origin,
    TORwa origin left ∧
      TORwa origin right

/-- Leading-correction common-source spans specialize through group homomorphisms. -/
lemma occurrence_common_span
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {left right : List G}
    (span : OCSpan left right) :
    OCSpan (left.map f) (right.map f) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨origin.map f,
      occurrence_rewrites f hleft,
      occurrence_rewrites f hright⟩

/-- A paired-forward leading-correction collection supplies a symmetric zigzag. -/
lemma occurrence_common_equivalence
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : OCSpan left right) :
    TOEquivc left right := by
  rcases span with ⟨origin, hleft, hright⟩
  exact TOEquivc.ofCommonSource hleft hright

/--
A paired-forward trailing-correction collection from one common raw factor
list.
-/
abbrev TrailingOccurrenceCommon
    {G : Type*}
    [Group G]
    (left right : List G) :
    Prop :=
  ∃ origin,
    TORw origin left ∧
      TORw origin right

/-- Trailing-correction common-source spans specialize through group homomorphisms. -/
lemma trailing_occurrence_common
    {G H : Type*}
    [Group G]
    [Group H]
    (f : G →* H)
    {left right : List G}
    (span : TrailingOccurrenceCommon left right) :
    TrailingOccurrenceCommon
      (left.map f) (right.map f) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨origin.map f,
      trailing_occurrence_rewrites f hleft,
      trailing_occurrence_rewrites f hright⟩

/-- A paired-forward trailing-correction collection supplies a symmetric zigzag. -/
lemma trailing_common_equivalence
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : TrailingOccurrenceCommon left right) :
    TOEquiv left right := by
  rcases span with ⟨origin, hleft, hright⟩
  exact TOEquiv.ofCommonSource hleft hright

/--
Reverse-inverse transport sends paired-forward leading-correction collections
to paired-forward trailing-correction collections.
-/
lemma common_trailing_reverse
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : OCSpan left right) :
    TrailingOccurrenceCommon
      (reverseInverseFactors left) (reverseInverseFactors right) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨reverseInverseFactors origin,
      rewrites_trailing_reverse hleft,
      rewrites_trailing_reverse hright⟩

/--
Reverse-inverse transport sends paired-forward trailing-correction collections
back to paired-forward leading-correction collections.
-/
lemma trailing_common_leading
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : TrailingOccurrenceCommon left right) :
    OCSpan
      (reverseInverseFactors left) (reverseInverseFactors right) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨reverseInverseFactors origin,
      trailing_rewrites_leading hleft,
      trailing_rewrites_leading
        hright⟩

/--
Leading and trailing paired-forward collection presentations are exactly
equivalent after reverse-inverse factor transport.
-/
theorem trailing_common_reverse
    {G : Type*}
    [Group G]
    {left right : List G} :
    TrailingOccurrenceCommon
        (reverseInverseFactors left) (reverseInverseFactors right) ↔
      OCSpan left right := by
  constructor
  · intro span
    simpa using
      trailing_common_leading
        span
  · exact
      common_trailing_reverse

end
  CSNat
end TCTex
end Submission


/-!
# Transport signed common-source spans from the retained transversal

The inherited retained transversal and the sorted fixed-slot packet use the
same retained occurrences in different operational presentations.  A signed
collector should therefore be allowed to construct paired-forward spans in
the inherited transversal order.  The existing cutoff-aware ordered transport
can postcompose both legs into the sorted packet order consumed by Claim 5.

This file isolates that reduction and records the corresponding Claim 5
adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  CSTrans

universe u

open
  PTOcc
open
  PCBridge
open
  TOMirror
open
  OOSched
open
  FTOcc
open
  TOEquivb
open
  CSNat
open
  CRLayer
open
  FIBridge
open
  SOAlign

/--
Postcompose both legs of a paired-forward collection with independently
constructed cutoff-aware runs.
-/
lemma OCSpan.postcompose
    {G : Type*}
    [Group G]
    {left right leftTarget rightTarget : List G}
    (span : OCSpan left right)
    (leftRewrites : TORwa left leftTarget)
    (rightRewrites : TORwa right rightTarget) :
    OCSpan leftTarget rightTarget := by
  rcases span with ⟨origin, hleft, hright⟩
  exact ⟨origin, hleft.trans leftRewrites, hright.trans rightRewrites⟩

/--
Independently constructed cutoff-aware runs compose under concatenation.
-/
lemma occurrence_rewrites_append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left : TORwa leftSource leftTarget)
    (right : TORwa rightSource rightTarget) :
    TORwa
      (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  have hleft :
      TORwa
        (leftSource ++ rightSource) (leftTarget ++ rightSource) := by
    simpa using left.context [] rightSource
  have hright :
      TORwa
        (leftTarget ++ rightSource) (leftTarget ++ rightTarget) := by
    simpa using right.context leftTarget []
  exact hleft.trans hright

/--
Pointwise cutoff-aware runs assemble over a list of symbolic blocks.
-/
lemma occurrence_rewrites_flat
    {G ι : Type*}
    [Group G]
    (indices : List ι)
    {source target : ι → List G}
    (rewrites :
      ∀ index ∈ indices,
        TORwa (source index) (target index)) :
    TORwa
      (indices.flatMap source) (indices.flatMap target) := by
  induction indices with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons index indices ih =>
      simpa only [List.flatMap_cons] using
        occurrence_rewrites_append
          (rewrites index (by simp))
          (ih fun next hnext => rewrites next (by simp [hnext]))

/-- Paired-forward cutoff-aware collections remain valid in list contexts. -/
lemma occurrence_common_context
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : OCSpan left right)
    (front back : List G) :
    OCSpan
      (front ++ left ++ back) (front ++ right ++ back) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨front ++ origin ++ back,
      hleft.context front back,
      hright.context front back⟩

/-- Independently constructed paired-forward collections compose by concatenation. -/
lemma occurrence_common_append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left : OCSpan leftSource leftTarget)
    (right : OCSpan rightSource rightTarget) :
    OCSpan
      (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  rcases left with ⟨leftOrigin, hleftSource, hleftTarget⟩
  rcases right with ⟨rightOrigin, hrightSource, hrightTarget⟩
  exact
    ⟨leftOrigin ++ rightOrigin,
      occurrence_rewrites_append hleftSource hrightSource,
      occurrence_rewrites_append hleftTarget hrightTarget⟩

/-- Every collected word is a paired-forward common source for itself. -/
lemma occurrence_common_refl
    {G : Type*}
    [Group G]
    (source : List G) :
    OCSpan source source :=
  ⟨source, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/--
Pointwise paired-forward collections assemble over a list of symbolic blocks.
-/
lemma occurrence_common_flat
    {G ι : Type*}
    [Group G]
    (indices : List ι)
    {left right : ι → List G}
    (spans :
      ∀ index ∈ indices,
        OCSpan (left index) (right index)) :
    OCSpan
      (indices.flatMap left) (indices.flatMap right) := by
  induction indices with
  | nil =>
      simpa using occurrence_common_refl ([] : List G)
  | cons index indices ih =>
      simpa only [List.flatMap_cons] using
        occurrence_common_append
          (spans index (by simp))
          (ih fun next hnext => spans next (by simp [hnext]))

/--
Postcompose both legs of a mirrored paired-forward collection with
independently constructed cutoff-aware runs.
-/
lemma trailing_common_postcompose
    {G : Type*}
    [Group G]
    {left right leftTarget rightTarget : List G}
    (span : TrailingOccurrenceCommon left right)
    (leftRewrites : TORw left leftTarget)
    (rightRewrites : TORw right rightTarget) :
    TrailingOccurrenceCommon leftTarget rightTarget := by
  rcases span with ⟨origin, hleft, hright⟩
  exact ⟨origin, hleft.trans leftRewrites, hright.trans rightRewrites⟩

/--
Independently constructed mirrored cutoff-aware runs compose under
concatenation.
-/
lemma trailing_rewrites_append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left : TORw leftSource leftTarget)
    (right : TORw rightSource rightTarget) :
    TORw
      (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  have hleft :
      TORw
        (leftSource ++ rightSource) (leftTarget ++ rightSource) := by
    simpa using left.context [] rightSource
  have hright :
      TORw
        (leftTarget ++ rightSource) (leftTarget ++ rightTarget) := by
    simpa using right.context leftTarget []
  exact hleft.trans hright

/--
Pointwise mirrored cutoff-aware runs assemble over a list of symbolic blocks.
-/
lemma trailing_rewrites_flat
    {G ι : Type*}
    [Group G]
    (indices : List ι)
    {source target : ι → List G}
    (rewrites :
      ∀ index ∈ indices,
        TORw (source index) (target index)) :
    TORw
      (indices.flatMap source) (indices.flatMap target) := by
  induction indices with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons index indices ih =>
      simpa only [List.flatMap_cons] using
        trailing_rewrites_append
          (rewrites index (by simp))
          (ih fun next hnext => rewrites next (by simp [hnext]))

/-- Mirrored paired-forward collections remain valid in list contexts. -/
lemma trailing_common_context
    {G : Type*}
    [Group G]
    {left right : List G}
    (span : TrailingOccurrenceCommon left right)
    (front back : List G) :
    TrailingOccurrenceCommon
      (front ++ left ++ back) (front ++ right ++ back) := by
  rcases span with ⟨origin, hleft, hright⟩
  exact
    ⟨front ++ origin ++ back,
      hleft.context front back,
      hright.context front back⟩

/--
Independently constructed mirrored paired-forward collections compose by
concatenation.
-/
lemma trailing_common_append
    {G : Type*}
    [Group G]
    {leftSource leftTarget rightSource rightTarget : List G}
    (left :
      TrailingOccurrenceCommon leftSource leftTarget)
    (right :
      TrailingOccurrenceCommon rightSource rightTarget) :
    TrailingOccurrenceCommon
      (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  rcases left with ⟨leftOrigin, hleftSource, hleftTarget⟩
  rcases right with ⟨rightOrigin, hrightSource, hrightTarget⟩
  exact
    ⟨leftOrigin ++ rightOrigin,
      trailing_rewrites_append hleftSource hrightSource,
      trailing_rewrites_append hleftTarget hrightTarget⟩

/-- Every mirrored collected word is a paired-forward common source for itself. -/
lemma trailing_common_refl
    {G : Type*}
    [Group G]
    (source : List G) :
    TrailingOccurrenceCommon source source :=
  ⟨source, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/--
Pointwise mirrored paired-forward collections assemble over a list of
symbolic blocks.
-/
lemma trailing_common_flat
    {G ι : Type*}
    [Group G]
    (indices : List ι)
    {left right : ι → List G}
    (spans :
      ∀ index ∈ indices,
        TrailingOccurrenceCommon
          (left index) (right index)) :
    TrailingOccurrenceCommon
      (indices.flatMap left) (indices.flatMap right) := by
  induction indices with
  | nil =>
      simpa using
        trailing_common_refl ([] : List G)
  | cons index indices ih =>
      simpa only [List.flatMap_cons] using
        trailing_common_append
          (spans index (by simp))
          (ih fun next hnext => spans next (by simp [hnext]))

/--
Concrete common-source spans for the three negative-input substitutions in
the inherited retained-transversal order.
-/
structure
    ICSpans
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
          n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
        (coefficientEvaluatedFactors
          n left right⁻¹ (leftExponent : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
        (coefficientEvaluatedFactors
          n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
            (rightExponent : ℤ))
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
          n left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
        (coefficientEvaluatedFactors
          n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
            ((rightMagnitude + 1 : ℕ) : ℤ))

namespace
  ICSpans

/--
The cutoff-aware ordered transport postcomposes inherited-transversal spans
into sorted retained-packet spans.
-/
def inputCommonSpans
    {d n : ℕ}
    (spans :
      ICSpans.{u}
        d n)
    (transport :
      TOTransa.{u} d n) :
    OCSpans.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude :=
    OCSpan.postcompose
      (spans.rightNegative left right leftExponent rightMagnitude)
      (transport.rewrites
        left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
      (transport.rewrites
        left right⁻¹ (leftExponent : ℤ) ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative left right leftMagnitude rightExponent :=
    OCSpan.postcompose
      (spans.leftNegative left right leftMagnitude rightExponent)
      (transport.rewrites
        left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
      (transport.rewrites
        left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ) (rightExponent : ℤ))
  bothNegative left right leftMagnitude rightMagnitude :=
    OCSpan.postcompose
      (spans.bothNegative left right leftMagnitude rightMagnitude)
      (transport.rewrites
        left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
      (transport.rewrites
        left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
          ((rightMagnitude + 1 : ℕ) : ℤ))

namespace TSInput

/--
Inherited-transversal negative-input spans and an ordered cutoff-aware
transport instantiate the Claim 5 coordinate polynomials.
-/
theorem
    occCommonSpans
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      ICSpans.{u}
        d n)
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
  TOEquivb.OCSpans.TSInput.coordCommonSpans
    hn H hH kernel hprofileAlignment
      (spans.inputCommonSpans
        transport)
      input
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  ICSpans

end
  CSTrans
end TCTex
end Submission


/-!
# Cancel trailing parents from retained-transversal signed spans

The cutoff-full collector naturally produces endpoints consisting of retained
correction factors followed by the swapped powered parents.  A signed
collector should therefore be allowed to compare those full endpoints through
a common raw source.  After negative powers are naturalized by inverted bases,
the trailing parent lists agree literally and can be cancelled semantically.

This file packages that weaker collector-facing obligation, transports its
retained-factor product laws into sorted fixed-slot order, and records the
corresponding Claim 5 adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  NCCommon

universe u

open
  OOSched
open
  SOAlign
open
  FTOcc
open
  CSTrans
open
  CSNat
open
  FTTrans
open
  CRLayer
open
  UNPkt
open
  PTOcc
open
  FIBridge

/--
A paired-forward span between lists with equal trailing contexts identifies
the products of their prefixes.
-/
lemma OCSpan.prefixlist_prodeq_suffixeq
    {G : Type*}
    [Group G]
    {left right leftSuffix rightSuffix : List G}
    (span :
      OCSpan
        (left ++ leftSuffix) (right ++ rightSuffix))
    (hsuffix : leftSuffix = rightSuffix) :
    right.prod = left.prod := by
  subst rightSuffix
  have hprod :
      right.prod * leftSuffix.prod =
        left.prod * leftSuffix.prod := by
    simpa only [List.prod_append] using
      (occurrence_common_equivalence span).list_prod_eq
  exact mul_right_cancel hprod

/--
Collector-native common-source spans for the three negative substitutions.
Each endpoint retains the swapped powered parents emitted by Hall collection.
-/
structure
    CCSpans
    (d n : ℕ) :
    Prop where
  rightNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightMagnitude : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
            n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude) ++
          [right ^ Int.negSucc rightMagnitude, left ^ (leftExponent : ℤ)])
        (coefficientEvaluatedFactors
            n left right⁻¹ (leftExponent : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ) ++
          [right⁻¹ ^ ((rightMagnitude + 1 : ℕ) : ℤ),
            left ^ (leftExponent : ℤ)])
  leftNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightExponent : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
            n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ) ++
          [right ^ (rightExponent : ℤ), left ^ Int.negSucc leftMagnitude])
        (coefficientEvaluatedFactors
            n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
              (rightExponent : ℤ) ++
          [right ^ (rightExponent : ℤ),
            left⁻¹ ^ ((leftMagnitude + 1 : ℕ) : ℤ)])
  bothNegative :
    ∀ (left right :
        LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
      (leftMagnitude rightMagnitude : ℕ),
      OCSpan
        (coefficientEvaluatedFactors
            n left right (Int.negSucc leftMagnitude)
              (Int.negSucc rightMagnitude) ++
          [right ^ Int.negSucc rightMagnitude,
            left ^ Int.negSucc leftMagnitude])
        (coefficientEvaluatedFactors
            n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ) ++
          [right⁻¹ ^ ((rightMagnitude + 1 : ℕ) : ℤ),
            left⁻¹ ^ ((leftMagnitude + 1 : ℕ) : ℤ)])

namespace
  CCSpans

/-- Cancel the naturalized trailing parent pair in the right-negative span. -/
lemma right_negative_prod
    {d n : ℕ}
    (spans :
      CCSpans.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightMagnitude : ℕ) :
    (coefficientEvaluatedFactors
        n left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)).prod =
      (coefficientEvaluatedFactors
        n left right⁻¹ (leftExponent : ℤ)
          ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
  exact
    (OCSpan.prefixlist_prodeq_suffixeq
      (spans.rightNegative left right leftExponent rightMagnitude)
      (by simp only [zpow_natCast, zpow_negSucc, ← inv_pow])).symm

/-- Cancel the naturalized trailing parent pair in the left-negative span. -/
lemma left_negative_prod
    {d n : ℕ}
    (spans :
      CCSpans.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftMagnitude rightExponent : ℕ) :
    (coefficientEvaluatedFactors
        n left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)).prod =
      (coefficientEvaluatedFactors
        n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
          (rightExponent : ℤ)).prod := by
  exact
    (OCSpan.prefixlist_prodeq_suffixeq
      (spans.leftNegative left right leftMagnitude rightExponent)
      (by simp only [zpow_natCast, zpow_negSucc, ← inv_pow])).symm

/-- Cancel the naturalized trailing parent pair in the both-negative span. -/
lemma both_negative_prod
    {d n : ℕ}
    (spans :
      CCSpans.{u}
        d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftMagnitude rightMagnitude : ℕ) :
    (coefficientEvaluatedFactors
        n left right (Int.negSucc leftMagnitude)
          (Int.negSucc rightMagnitude)).prod =
      (coefficientEvaluatedFactors
        n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
          ((rightMagnitude + 1 : ℕ) : ℤ)).prod := by
  exact
    (OCSpan.prefixlist_prodeq_suffixeq
      (spans.bothNegative left right leftMagnitude rightMagnitude)
      (by simp only [zpow_natCast, zpow_negSucc, ← inv_pow])).symm

/--
Trailing-context common-source spans and retained-order normalization
naturalize the three negative quadrants of the operational fixed-slot packet.
-/
def negativeInputNaturalization
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    TBPkt.NegativeNaturalizationLaws.{u}
      (coeffProfileAlignment
        (d := d) kernel hprofileAlignment) where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (leftExponent : ℤ)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (leftExponent : ℤ)
                  (Int.negSucc rightMagnitude)).prod :=
            (transport.rewrites
              left right (leftExponent : ℤ)
                (Int.negSucc rightMagnitude)).list_prod_eq
          _ =
              (coefficientEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            spans.right_negative_prod
              left right leftExponent rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (transport.rewrites
              left right⁻¹ (leftExponent : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).list_prod_eq.symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (rightExponent : ℤ)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (rightExponent : ℤ)).prod :=
            (transport.rewrites
              left right (Int.negSucc leftMagnitude)
                (rightExponent : ℤ)).list_prod_eq
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            spans.left_negative_prod
              left right leftMagnitude rightExponent
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            (transport.rewrites
              left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                (rightExponent : ℤ)).list_prod_eq.symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (Int.negSucc rightMagnitude)).prod :=
            (transport.rewrites
              left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)).list_prod_eq
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            spans.both_negative_prod
              left right leftMagnitude rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (transport.rewrites
              left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).list_prod_eq.symm

/--
The natural collector and collector-native trailing-context spans prove the
all-integral sorted retained packet law.
-/
def satisfiesOperationalAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allNaturalizationLaws
    (negativeInputNaturalization
      kernel hprofileAlignment transport spans)).listEval_eq

/--
The operational retained-packet law transports across profile alignment to
the selected endpoint finite-index kernel.
-/
def satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel := by
  intro left right leftExponent rightExponent
  rw [
    coeff_profile_alignment
      kernel.signedProfileAssignment hprofileAlignment]
  exact
    satisfiesOperationalAlignment
      kernel hprofileAlignment transport spans
        left right leftExponent rightExponent

namespace TSInput

/--
Collector-native trailing-context spans instantiate the Claim 5 coordinate
polynomials after semantic cancellation of the swapped powered parents.
-/
theorem
    contextCommonSpans
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n)
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
  input.coordTruncEval
    hn H hH kernel
      (satisfiesTruncAlignment
        kernel hprofileAlignment transport spans)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  CCSpans

end
  NCCommon
end TCTex
end Submission

/-!
# Phase-aware signed schedules from retained-transversal trailing spans

The collector-facing signed obligation is naturally weaker than a directed
run from a powered parent pair to the final fixed-slot packet.  It is enough
to collect two retained-transversal endpoints from one common raw source while
keeping the swapped powered parents as a shared trailing context.

Semantic cancellation of that context naturalizes the three negative
quadrants.  This file promotes those native spans into the phase-aware
all-integral parent-pair interface and records the corresponding Claim 5
adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  ACCommon

universe u

open
  SOAlign
open
  FTOcc
open
  PPSched
open
  TOSched
open
  NCCommon
open
  CRLayer
open
  FIBridge

/--
Trailing-context common-source spans and retained-order normalization supply
the directed negative parent-pair facade.
-/
def
    parentContextSpans
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    TOSchedu.{u}
      d n :=
  TOSchedu.negative_naturalization_laws
    kernel hprofileAlignment
      (CCSpans.negativeInputNaturalization
        kernel hprofileAlignment transport spans)

/--
The natural positive branch and retained-transversal trailing-context spans
assemble into the phase-aware all-integral parent-pair schedule.
-/
noncomputable def
    phaseSchedulesSpans
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    PPSchedu.{u}
      d n layer kernel hprofileAlignment :=
  PPSchedu.parent_occ_schedules
    kernel hprofileAlignment
      (parentContextSpans
        kernel hprofileAlignment transport spans)

/--
Trailing-context common-source spans therefore supply the semantic sorted
retained-packet law through the phase-aware all-integral interface.
-/
def
    satisfiesContextSpans
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (phaseSchedulesSpans
    kernel hprofileAlignment transport spans)
      |>.satisfiesCoefficientTruncated

/--
Trailing-context common-source spans give the selected endpoint finite-index
kernel its signed list-evaluation law through the phase-aware interface.
-/
def
    satisfiesCommonSpans
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (phaseSchedulesSpans
    kernel hprofileAlignment transport spans)
      |>.satisfiesTruncAlignment

namespace TSInput

/--
Collector-native retained-transversal trailing-context spans instantiate the
Claim 5 coordinate polynomials through the phase-aware signed schedule.
-/
theorem
    coordContextSpans
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (transport :
      TOTransa.{u} d n)
    (spans :
      CCSpans.{u}
        d n)
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
  PPSched.PPSchedu.TSInput.parentPhaseSchedules
    hn H hH kernel hprofileAlignment
      (phaseSchedulesSpans
        kernel hprofileAlignment transport spans)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  ACCommon
end TCTex
end Submission

/-!
# Signed trailing-context collector kernel

After the natural positive branch has been compiled into its explicit
collection, compression, and padding phases, the retained-transversal signed
collector has two independent operational obligations:

* normalize inherited retained-transversal order into sorted fixed-slot order;
* collect the three negative-input endpoint pairs from common raw sources,
  retaining the swapped powered parents as cancellable trailing contexts.

This file packages exactly that pair as a reusable arbitrary-cutoff kernel and
feeds it into the phase-aware Claim 5 route.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  CCKern

universe u

open
  SOAlign
open
  FTOcc
open
  PPSched
open
  ACCommon
open
  NCCommon
open
  CRLayer
open
  FIBridge

/--
The remaining operational signed-collector kernel after the positive natural
quadrant has been discharged automa.
-/
structure TCCollec
    (d n : ℕ) :
    Prop where
  orderedTransport :
    TOTransa.{u} d n
  negativeInputSpans :
    CCSpans.{u}
      d n

namespace TCCollec

/--
Every signed trailing-context collector kernel promotes to the phase-aware
all-integral parent-pair schedule.
-/
noncomputable def allPhaseSchedules
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      TCCollec.{u} d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    PPSchedu.{u}
      d n layer kernel hprofileAlignment :=
  phaseSchedulesSpans
    kernel hprofileAlignment collector.orderedTransport
      collector.negativeInputSpans

/--
A signed trailing-context collector kernel proves the semantic all-integral
sorted retained-packet law.
-/
def satisfiesCoefficientTruncated
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      TCCollec.{u} d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (collector.allPhaseSchedules kernel hprofileAlignment)
    |>.satisfiesCoefficientTruncated

/--
A signed trailing-context collector kernel gives the selected endpoint
finite-index kernel its full signed list-evaluation law.
-/
def satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      TCCollec.{u} d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (collector.allPhaseSchedules kernel hprofileAlignment)
    |>.satisfiesTruncAlignment

namespace TSInput

/--
A signed trailing-context collector kernel instantiates the Claim 5
coordinate polynomials.
-/
theorem
    trailingContextCollector
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (collector :
      TCCollec.{u} d n)
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
  PPSched.PPSchedu.TSInput.parentPhaseSchedules
    hn H hH kernel hprofileAlignment
      (collector.allPhaseSchedules
        kernel hprofileAlignment)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end TCCollec

end
  CCKern
end TCTex
end Submission

/-!
# Signed trailing-context collector kernels from retained occurrence schedules

An all-integral retained-transversal occurrence schedule already collects the
same powered parent pair to both presentations of each negative-input
substitution.  After rewriting negative powers as positive powers of inverted
bases, those two runs have a literal common source and retain the same swapped
parent suffix.

This file constructs the three trailing-context spans from that observation.
Together with retained-order normalization, it yields the signed
trailing-context collector kernel.  The construction is useful both as a
low-cutoff instantiation and as a compatibility theorem for any future
arbitrary-cutoff symbolic Hall scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  SOSched

universe u

open
  OOSched
open
  FTOcc
open
  NCCommon
open
  CSNat
open
  CCKern
open
  PTOcc
open
  PCBridge

namespace COSched

/--
An all-integral retained occurrence schedule gives common-source spans between
every negative-input endpoint and its positive-magnitude inverted-base
presentation.
-/
def trailingContextSpans
    {d n : ℕ}
    (schedule : COSched.{u} d n) :
    CCSpans.{u}
      d n where
  rightNegative left right leftExponent rightMagnitude := by
    refine ⟨[left ^ leftExponent, right⁻¹ ^ (rightMagnitude + 1)], ?_, ?_⟩
    · simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left right (leftExponent : ℤ) (Int.negSucc rightMagnitude))
    · simpa only [zpow_natCast] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left right⁻¹ (leftExponent : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))
  leftNegative left right leftMagnitude rightExponent := by
    refine ⟨[left⁻¹ ^ (leftMagnitude + 1), right ^ rightExponent], ?_, ?_⟩
    · simpa only [zpow_natCast, zpow_negSucc, ← inv_pow] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left right (Int.negSucc leftMagnitude) (rightExponent : ℤ))
    · simpa only [zpow_natCast] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
              (rightExponent : ℤ))
  bothNegative left right leftMagnitude rightMagnitude := by
    refine
      ⟨[left⁻¹ ^ (leftMagnitude + 1), right⁻¹ ^ (rightMagnitude + 1)],
        ?_, ?_⟩
    · simpa only [zpow_negSucc, ← inv_pow] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left right (Int.negSucc leftMagnitude) (Int.negSucc rightMagnitude))
    · simpa only [zpow_natCast] using
        TORwa.ofOccurrenceRewrites
          (schedule.rewrites
            left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
              ((rightMagnitude + 1 : ℕ) : ℤ))

end COSched

namespace TCCollec

/--
A retained occurrence schedule and an ordered occurrence transport construct
the signed trailing-context collector kernel.
-/
def occ_schedule_transport
    {d n : ℕ}
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    TCCollec.{u} d n where
  orderedTransport :=
    FTOcc.COTrans.occTransport
      orderedTransport
  negativeInputSpans :=
    SOSched.COSched.trailingContextSpans
      schedule

end TCCollec

end
  SOSched
end TCTex
end Submission

/-!
# Phase-aware signed schedules from retained occurrence schedules

The terminating cutoff-full collector constructs the positive natural branch
through literal collection, adjacent power compression, and identity padding.
An all-integral retained-transversal occurrence schedule supplies the three
negative branches by collecting each negative-input endpoint and its
positive-magnitude inverted-base endpoint from the same powered parent pair.

This file exposes the resulting local-to-global compiler directly.  It retains
the phase-aware rewrite relation before passing to its list-evaluation
consequence and the Claim 5 coordinate-polynomial constructor.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  AOSched

universe u

open
  OOSched
open
  SOAlign
open
  PPSched
open
  CCKern
open
  SOSched
open
  CRLayer
open
  PTOcc
open
  FIBridge

/--
The explicit positive natural collector, an all-integral retained occurrence
schedule, and operational retained-order transport assemble into the complete
phase-aware signed parent-pair scheduler.
-/
noncomputable def
    schedulesOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    PPSchedu.{u}
      d n layer kernel hprofileAlignment :=
  (TCCollec.occ_schedule_transport
      schedule orderedTransport).allPhaseSchedules
    kernel hprofileAlignment

/--
Before semantic cancellation, the compiled scheduler retains an explicit
phase-aware rewrite run for every pair of integer exponents.
-/
noncomputable def
    rewritesOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
    (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    PPRw
      [left ^ leftExponent, right ^ rightExponent]
      (orderedEvaluatedFactors
          n left right leftExponent rightExponent ++
        [right ^ rightExponent, left ^ leftExponent]) :=
  (schedulesOccTransport
      kernel hprofileAlignment schedule orderedTransport).rewrites
    left right leftExponent rightExponent

/--
The phase-aware compiler supplies the selected endpoint finite-index kernel
with its full all-integral list-evaluation law.
-/
def
    satisfiesOccurrenceTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (schedulesOccTransport
      kernel hprofileAlignment schedule orderedTransport)
    |>.satisfiesTruncAlignment

namespace TSInput

/--
The local-to-global operational compiler instantiates the Claim 5 coordinate
polynomials from a retained occurrence schedule and retained-order transport.
-/
theorem
    polyOccTransport
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      COTrans.{u} d n)
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
  input.coordTruncEval
    hn H hH kernel
      (satisfiesOccurrenceTransport
        kernel hprofileAlignment schedule orderedTransport)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  AOSched
end TCTex
end Submission

/-!
# Signed trailing-context collector kernels with semantic order transport

The retained-transversal trailing-context collector only uses retained-order
normalization through equality of ordered products.  A directed cutoff-aware
rewrite from inherited retained order to sorted fixed-slot order is therefore
stronger than the Claim 5 route requires.

This file packages the sharp product-level order hypothesis together with the
genuinely collector-native common-source spans.  The resulting kernel still
promotes to the phase-aware all-integral parent-pair schedule and hence to the
Claim 5 coordinate polynomials.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section


namespace Submission
namespace TCTex
namespace
  OCKerna

universe u

open
  OOSched
open
  SOAlign
open
  PPSched
open
  TOSched
open
  NCCommon
open
  FTTrans
open
  CCKern
open
  SOSched
open
  CRLayer
open
  UNPkt
open
  CCThree
open
  PTOcc
open
  FIBridge

/--
The sharp signed collector kernel: semantic retained-order normalization and
three collector-native trailing-context common-source spans.
-/
structure CSCollec
    (d n : ℕ) :
    Prop where
  orderedProductTransport :
    RetainedRecipeTransport.{u} d n
  negativeInputSpans :
    CCSpans.{u}
      d n

namespace
  CSCollec

/--
The stronger operational order-transport kernel forgets to the sharp
product-level order kernel.
-/
def signedContextCollector
    {d n : ℕ}
    (collector :
      TCCollec.{u} d n) :
    CSCollec.{u}
      d n where
  orderedProductTransport :=
    collector.orderedTransport.retainedRecipeTransport
  negativeInputSpans :=
    collector.negativeInputSpans

/--
A retained occurrence schedule and the sorted retained-packet law construct
the sharp signed collector kernel.
-/
def occ_coeff_trunc
    {d n : ℕ}
    (schedule : COSched.{u} d n)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n) :
    CSCollec.{u}
      d n where
  orderedProductTransport :=
    (recipe_coeff_trunc
      schedule.satisfiesRecipeCoefficient).mpr hordered
  negativeInputSpans :=
    COSched.trailingContextSpans
      schedule

/--
The two universal retained-packet list laws construct the sharp signed
collector kernel directly.
-/
def
    satisfies_trunc_eval
    {d n : ℕ}
    (hretained :
      SatisfiesRecipeCoefficient.{u} d n)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n) :
    CSCollec.{u}
      d n :=
  occ_coeff_trunc
    (COSched.satisfies_recipe_coeff
      hretained)
    hordered

/--
The sharp collector kernel naturalizes the three signed quadrants of the
operational fixed-slot packet.
-/
def negativeInputNaturalization
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      CSCollec.{u}
        d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TBPkt.NegativeNaturalizationLaws.{u}
      (coeffProfileAlignment
        (d := d) kernel hprofileAlignment) where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (leftExponent : ℤ)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (leftExponent : ℤ)
                  (Int.negSucc rightMagnitude)).prod :=
            collector.orderedProductTransport
              left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)
          _ =
              (coefficientEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            collector.negativeInputSpans.right_negative_prod
              left right leftExponent rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (collector.orderedProductTransport
              left right⁻¹ (leftExponent : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (rightExponent : ℤ)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (rightExponent : ℤ)).prod :=
            collector.orderedProductTransport
              left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            collector.negativeInputSpans.left_negative_prod
              left right leftMagnitude rightExponent
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            (collector.orderedProductTransport
              left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                (rightExponent : ℤ)).symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      orderedEvaluatedFactors,
      packetsProfileAlignment] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (Int.negSucc rightMagnitude)).prod :=
            collector.orderedProductTransport
              left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            collector.negativeInputSpans.both_negative_prod
              left right leftMagnitude rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (collector.orderedProductTransport
              left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).symm

/--
The sharp collector kernel supplies the directed negative parent-pair facade.
-/
def inputParentSchedules
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      CSCollec.{u}
        d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    TOSchedu.{u}
      d n :=
  TOSchedu.negative_naturalization_laws
    kernel hprofileAlignment
      (collector.negativeInputNaturalization
        kernel hprofileAlignment)

/--
The natural positive branch and the sharp signed collector kernel assemble
into the phase-aware all-integral parent-pair schedule.
-/
noncomputable def allPhaseSchedules
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      CSCollec.{u}
        d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    PPSchedu.{u}
      d n layer kernel hprofileAlignment :=
  PPSchedu.parent_occ_schedules
    kernel hprofileAlignment
      (collector.inputParentSchedules
        kernel hprofileAlignment)

/--
The sharp signed collector kernel gives the selected endpoint finite-index
kernel its full signed list-evaluation law.
-/
def satisfiesTruncAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (collector :
      CSCollec.{u}
        d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (collector.allPhaseSchedules kernel hprofileAlignment)
    |>.satisfiesTruncAlignment

/--
The two universal retained-packet list laws give an aligned selected endpoint
kernel its full signed list-evaluation law.
-/
def
    satisfiesTruncCoeff
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (hretained :
      SatisfiesRecipeCoefficient.{u} d n)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n)
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  (satisfies_trunc_eval
      hretained hordered).satisfiesTruncAlignment
    kernel hprofileAlignment

namespace TSInput

/--
The sharp signed trailing-context collector kernel instantiates the Claim 5
coordinate polynomials.
-/
theorem
    coordAlignmentCollector
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (collector :
      CSCollec.{u}
        d n)
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
  PPSched.PPSchedu.TSInput.parentPhaseSchedules
    hn H hH kernel hprofileAlignment
      (collector.allPhaseSchedules
        kernel hprofileAlignment)
      input hsourceSupported factorNormalization hinputWeight

/--
The two universal retained-packet list laws instantiate the Claim 5
coordinate polynomials directly.
-/
theorem
    coordTruncCoeff
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hprofileAlignment :
      RetainedProfileAlignment
        kernel.signedProfileAssignment)
    (hretained :
      SatisfiesRecipeCoefficient.{u} d n)
    (hordered :
      SatisfiesCoefficientTruncated.{u} d n)
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
  coordAlignmentCollector
    hn H hH kernel hprofileAlignment
      (satisfies_trunc_eval
        hretained hordered)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  CSCollec

end
  OCKerna
end TCTex
end Submission

/-!
# Semantic fiber counts and signed trailing-context collection

The retained recipe-coefficient profile assignment need not agree literally
with a selected endpoint profile kernel.  It is enough for the retained
assignment to count the concrete endpoint shape fibers on natural inputs.
Those counts make the sorted retained packet a natural Hall-Petresco packet.

Semantic retained-order transport and the collector-native trailing-context
spans then naturalize the three negative input quadrants.  Consequently the
sorted retained packet satisfies its all-integral law, and the semantic
profile-alignment adapter supplies the Claim 5 coordinate polynomials without
literal equality of profile records.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  TCBounda

universe u


open scoped commutatorElement

open
  CFCollec.DFTerm
open
  FCEnd
open
  OOSched
open
  FTOcc
open
  SOAlign
open
  NCCommon
open
  OCKerna
open
  SOSched
open
  SABounda
open
  CRLayer
open
  UNPkt
open
  CTAssigna
open
  FCAssign
open
  PTOcc
open
  PCBridge
open
  FIBridge

/--
The retained assignment is semantically aligned with itself.  This elementary
fact lets retained endpoint-fiber counts feed the natural packet constructor
without any selected-profile syntax theorem.
-/
lemma
    coeffProfileAssignment
    {n : ℕ} :
    SemanticProfileAlignment
      ((blockProfileAssignment n)
        |>.toSPAssign) := by
  intro word hword leftExponent rightExponent
  rfl

namespace
  CSCollec

/--
An all-integral retained occurrence schedule supplies the three signed
common-source spans.  Together with semantic retained-order normalization this
constructs the sharp signed collector kernel directly.
-/
def occurrenceScheduleTransport
    {d n : ℕ}
    (schedule : COSched.{u} d n)
    (orderedProductTransport :
      RetainedRecipeTransport.{u} d n) :
    CSCollec.{u}
      d n where
  orderedProductTransport :=
    orderedProductTransport
  negativeInputSpans :=
    SOSched.COSched.trailingContextSpans
      schedule

/--
A concrete cutoff-aware order transport supplies the semantic normalization
used by the sharp collector constructor.
-/
def occ_trunc_transport
    {d n : ℕ}
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n) :
    CSCollec.{u}
      d n :=
  occurrenceScheduleTransport schedule
    orderedTransport.retainedRecipeTransport

end
  CSCollec

/--
If the retained assignment counts the concrete natural endpoint fibers, its
sorted packet is a natural signed Hall-Petresco packet.
-/
noncomputable def
    coeffFibersCast
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer) :
    TBPkt.{u} d n where
  packets :=
    profileRecollectionPackets n
  list_nat_cast left right leftExponent rightExponent := by
    calc
      (orderedEvaluatedFactors
          n left right (leftExponent : ℤ) (rightExponent : ℤ)).prod =
          (collapsedEvaluatedFactors left right
            (layer.endpoint leftExponent rightExponent).factors).prod :=
        coeff_semantic_alignment
          ((blockProfileAssignment n)
            |>.toSPAssign)
          hretained
          coeffProfileAssignment
          leftExponent rightExponent left right
      _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
        simpa [collapsedEvaluatedFactors, collapsedList] using
          (layer.endpoint leftExponent rightExponent)
            |>.collapsed_list_pow
              left right (by simp) (by simp) (by simp) (by simp)
                SCFactor.trunc_last_bot

/--
Semantic retained-order transport and collector-native common-source spans
naturalize every negative input quadrant of the retained sorted packet.
-/
def
    naturalizationLawsCollector
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (collector :
      CSCollec.{u}
        d n) :
    (coeffFibersCast.{u}
      (d := d) hretained).NegativeNaturalizationLaws where
  rightNegative left right leftExponent rightMagnitude := by
    simpa only [
      coeffFibersCast,
      orderedEvaluatedFactors] using
        calc
          (orderedEvaluatedFactors
              n left right (leftExponent : ℤ)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (leftExponent : ℤ)
                  (Int.negSucc rightMagnitude)).prod :=
            collector.orderedProductTransport
              left right (leftExponent : ℤ) (Int.negSucc rightMagnitude)
          _ =
              (coefficientEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            collector.negativeInputSpans.right_negative_prod
              left right leftExponent rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left right⁻¹ (leftExponent : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (collector.orderedProductTransport
              left right⁻¹ (leftExponent : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).symm
  leftNegative left right leftMagnitude rightExponent := by
    simpa only [
      coeffFibersCast,
      orderedEvaluatedFactors] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (rightExponent : ℤ)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (rightExponent : ℤ)).prod :=
            collector.orderedProductTransport
              left right (Int.negSucc leftMagnitude) (rightExponent : ℤ)
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            collector.negativeInputSpans.left_negative_prod
              left right leftMagnitude rightExponent
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                  (rightExponent : ℤ)).prod :=
            (collector.orderedProductTransport
              left⁻¹ right ((leftMagnitude + 1 : ℕ) : ℤ)
                (rightExponent : ℤ)).symm
  bothNegative left right leftMagnitude rightMagnitude := by
    simpa only [
      coeffFibersCast,
      orderedEvaluatedFactors] using
        calc
          (orderedEvaluatedFactors
              n left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)).prod =
              (coefficientEvaluatedFactors
                n left right (Int.negSucc leftMagnitude)
                  (Int.negSucc rightMagnitude)).prod :=
            collector.orderedProductTransport
              left right (Int.negSucc leftMagnitude)
                (Int.negSucc rightMagnitude)
          _ =
              (coefficientEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            collector.negativeInputSpans.both_negative_prod
              left right leftMagnitude rightMagnitude
          _ =
              (orderedEvaluatedFactors
                n left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                  ((rightMagnitude + 1 : ℕ) : ℤ)).prod :=
            (collector.orderedProductTransport
              left⁻¹ right⁻¹ ((leftMagnitude + 1 : ℕ) : ℤ)
                ((rightMagnitude + 1 : ℕ) : ℤ)).symm

/--
Retained natural endpoint-fiber counts and the sharp signed collector kernel
prove the all-integral sorted retained-packet law.
-/
def
    satisfiesSemanticCollector
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (collector :
      CSCollec.{u}
        d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  (TBPkt.allNaturalizationLaws
    (naturalizationLawsCollector
      hretained collector)).listEval_eq

/--
Retained endpoint-fiber counts, an all-integral retained occurrence schedule,
and cutoff-aware order transport prove the sorted retained-packet law.
-/
def
    satisfiesOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n :=
  satisfiesSemanticCollector
    hretained
      (CSCollec.occ_trunc_transport
        schedule orderedTransport)

namespace
  EIFiber

/--
The same semantic hypotheses give every selected finite-index endpoint kernel
its signed list-evaluation law, without literal profile-record alignment.
-/
def
    satisfiesTruncCollector
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (collector :
      CSCollec.{u}
        d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  SABounda.EIFiber.satisfiesFibersCoeff
    kernel
    hretained
      (satisfiesSemanticCollector
        hretained collector)

/--
The concrete operational schedule inputs give every selected finite-index
endpoint kernel its signed list-evaluation law.
-/
def
    truncOccTransport
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n) :
    EIFiber.SatisfiesTruncEval.{u}
      (d := d) kernel :=
  satisfiesTruncCollector
    kernel hretained
      (CSCollec.occ_trunc_transport
        schedule orderedTransport)

end
  EIFiber

namespace TSInput

/--
Retained natural endpoint-fiber counts and the sharp signed trailing-context
collector kernel instantiate the Claim 5 coordinate polynomials without a
literal selected-profile alignment theorem.
-/
theorem
    coordSemanticCollector
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (collector :
      CSCollec.{u}
        d n)
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
  _root_.Submission.TCTex.TSInput.coordTruncEval
    hn H hH kernel
      (EIFiber.satisfiesTruncCollector
        kernel hretained collector)
      input hsourceSupported factorNormalization hinputWeight

/--
The concrete arbitrary-cutoff scheduler interfaces instantiate the Claim 5
coordinate polynomials directly.  The remaining operational construction
problem is now exposed as endpoint-fiber counting, retained occurrence
scheduling, and cutoff-aware retained-order transport.
-/
theorem
    coordOccTransport
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (kernel :
      EIFiber
        layer (by simp) (by simp))
    (hretained :
      (blockProfileAssignment n)
        |>.toSPAssign
        |>.CountsFibersCast layer)
    (schedule : COSched.{u} d n)
    (orderedTransport :
      TOTransa.{u} d n)
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
  coordSemanticCollector
    hn H hH kernel hretained
      (CSCollec.occ_trunc_transport
        schedule orderedTransport)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  TCBounda
end TCTex
end Submission
