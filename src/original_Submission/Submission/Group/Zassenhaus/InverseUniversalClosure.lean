import Submission.Group.Zassenhaus.BlockRecipe
import Submission.Group.Zassenhaus.CorrectionClosureVocabulary
import Submission.Group.Zassenhaus.FamilyOperationalSupport
import Submission.Group.Zassenhaus.Inverse
import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.Transient
import Submission.Group.HallBasic.StandardSequence
import Submission.Group.Zassenhaus.WordExpansions
import Submission.Group.Zassenhaus.SignedBlockStabilization
import Submission.Group.Zassenhaus.SignedProfilePackets

/-!
# Polynomial-orbit packets supported in the finite correction closure

The retained finite correction closure canonically supplies one homogeneous
signed-profile packet for each polynomial orbit.  This file packages those
packets in the existing ordered cutoff-support interface and exposes their
recipe-free packet count.

The conservative closure is a finite support universe, not yet a semantic
noncommutative schedule.  The root all-integral recollection identity is
therefore named explicitly as the remaining obligation.  Once that identity
is proved, the orbit packet immediately supplies the all-integral cutoff
packet consumed by the signed polynomial collection route.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UFClos

universe u

open scoped commutatorElement

open ROAggreg
open RFPacket
open ROTransi
open
  CFSubsti
open
  UCAll
open
  UCSuppor
open UCVocabu

/-- Every retained polynomial-orbit packet word lies in the retained erased-word
support vocabulary. -/
lemma erased_vocabulary_packets
    {n leftWeight rightWeight : ℕ}
    {packet : RFPkt}
    (hpacket :
      packet ∈ closureOrbitPackets
        n leftWeight rightWeight) :
    packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
  rcases List.mem_map.mp hpacket with ⟨key, _hkey, rfl⟩
  change
    (recipePolynomialOrbit
      (correctionClosureRecipes n leftWeight rightWeight)
      key).erasedShape ∈ erasedShapeVocabulary n leftWeight rightWeight
  apply shape_vocabulary_recipes
  exact recipes_polynomial_orbit
    (recipe_polynomial_orbit _ key)

/-- The retained polynomial-orbit packet list as one ordered cutoff-supported
packet. -/
noncomputable def closureBlockPacket
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    OBPkt n leftWeight rightWeight where
  leftWeight_pos :=
    hleftWeight
  rightWeight_pos :=
    hrightWeight
  packets :=
    closureOrbitPackets
      n leftWeight rightWeight
  word_erased_vocabulary _packet hpacket :=
    erased_vocabulary_packets
      hpacket

@[simp]
lemma packets_closure_packet
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (closureBlockPacket
      n leftWeight rightWeight hleftWeight hrightWeight).packets =
        closureOrbitPackets
          n leftWeight rightWeight :=
  rfl

/-- The recipe-free retained orbit vocabulary counts the canonical retained
orbit packets exactly. -/
lemma length_closure_packets
    (n leftWeight rightWeight : ℕ) :
    (closureOrbitPackets
      n leftWeight rightWeight).length =
        (retainedOrbitVocabulary
          n leftWeight rightWeight).length := by
  unfold closureOrbitPackets polynomialOrbitPackets
  rw [retained_orbit_vocabulary]
  simp

/--
The remaining semantic scheduling obligation for the retained root orbit
packets: their ordered list evaluation must be the powered commutator for all
integral source exponents.
-/
def SatisfiesClosureOrbit
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((closureOrbitPackets n 1 1).map
        fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
Once the root scheduling identity is available, the retained orbit packets
instantiate the all-integral ordered cutoff interface directly.
-/
noncomputable def
    allIntegralPacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesClosureOrbit.{u}
        d n) :
    TAPkta.{u} d n 1 1 where
  toOBPkt :=
    closureBlockPacket
      n 1 1 (by simp) (by simp)
  listEval_eq :=
    hlistEval

@[simp]
lemma
    packets_all_integral
    {d n : ℕ}
    (hlistEval :
      SatisfiesClosureOrbit.{u}
        d n) :
    (allIntegralPacket
      hlistEval).packets =
        closureOrbitPackets n 1 1 :=
  rfl

end UFClos
end TCTex
end Submission

/-!
# Canonical recipe inventory for the finite correction closure

The canonical recipe chunks partition the retained finite correction closure
by erased Hall word.  This file proves that flattening those chunks preserves
the complete retained recipe inventory, including repeated recipes.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ACAlign

open HACoeff
open BRSpec
open OCPartit
open
  UCSuppor
open UCVocabu

private lemma flat_attach_val
    {α β : Type*}
    (keys : List α)
    (f : α → List β) :
    keys.attach.flatMap (fun key => f key.1) =
      keys.flatMap f := by
  simpa only [List.flatMap_map, Function.comp_apply] using
    congrArg (fun nextKeys => nextKeys.flatMap f)
      (List.attach_map_subtype_val keys)

private lemma flat_key_perm
    {α β : Type*}
    [DecidableEq β]
    (key : α → β) :
    ∀ (keys : List β) (values : List α),
      keys.Nodup →
        (∀ value ∈ values, key value ∈ keys) →
          List.Perm
            (keys.flatMap fun target =>
              values.filter fun value => key value = target)
            values
  | [], values, _hnodup, hcover => by
      have hvalues : values = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value hvalue
        simpa using hcover value hvalue
      subst values
      exact .nil
  | target :: keys, values, hnodup, hcover => by
      let matching :=
        values.filter fun value => key value = target
      let rest :=
        values.filter fun value => key value ≠ target
      have hrestCover :
          ∀ value ∈ rest, key value ∈ keys := by
        intro value hvalue
        have hvalueMem : value ∈ values :=
          List.mem_of_mem_filter hvalue
        have hvalueNe : key value ≠ target :=
          of_decide_eq_true (List.mem_filter.mp hvalue).2
        have hkeyMem := hcover value hvalueMem
        simpa [hvalueNe] using hkeyMem
      have hfilter :
          ∀ nextTarget ∈ keys,
            values.filter (fun value => key value = nextTarget) =
              rest.filter (fun value => key value = nextTarget) := by
        intro nextTarget hnextTarget
        simp only [rest, List.filter_filter]
        apply List.filter_congr
        intro value _hvalue
        have htargetNotMem : target ∉ keys :=
          (List.nodup_cons.mp hnodup).1
        have hnextNe : nextTarget ≠ target := by
          intro hnextEq
          subst nextTarget
          exact htargetNotMem hnextTarget
        by_cases hvalueEq : key value = nextTarget
        · simp [hvalueEq, hnextNe]
        · simp [hvalueEq]
      have htail :
          List.Perm
            (keys.flatMap fun nextTarget =>
              rest.filter fun value => key value = nextTarget)
            rest :=
        flat_key_perm key keys rest
          (List.nodup_cons.mp hnodup).2 hrestCover
      have htailEq :
          (keys.flatMap fun nextTarget =>
              values.filter fun value => key value = nextTarget) =
            keys.flatMap fun nextTarget =>
              rest.filter fun value => key value = nextTarget := by
        apply List.flatMap_congr
        exact hfilter
      simp only [List.flatMap_cons]
      rw [htailEq]
      exact
        (List.Perm.append_left matching htail).trans
          (by
            simpa [matching, rest] using
              (List.perm_filterappend_filternot
                (fun value => decide (key value = target)) values).symm)

/--
Every word retained by the finite closure has a nonempty canonical recipe
chunk.
-/
lemma recipes_nil_vocabulary
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    recipesForWord n leftWeight rightWeight word ≠ [] := by
  rcases recipe_erased_vocabulary hword with
    ⟨recipe, hrecipe, hshape⟩
  apply List.ne_nil_of_mem (a := recipe)
  classical
  unfold recipesForWord
  rw [List.mem_filter]
  exact ⟨hrecipe, by simp [hshape]⟩

/--
Flattening canonical same-word chunks preserves the retained finite closure
inventory up to permutation.
-/
lemma recipes_perm_closure
    (n leftWeight rightWeight : ℕ) :
    List.Perm
      (canonicalRecipes n leftWeight rightWeight)
      (correctionClosureRecipes n leftWeight rightWeight) := by
  classical
  unfold canonicalRecipes canonicalRecipeChunks erasedShapeVocabulary
  unfold recipesForWord
  let values :=
    correctionClosureRecipes n leftWeight rightWeight
  let keys :=
    ((values.map BRecipe.erasedShape).dedup)
  change
    List.Perm
      ((keys.attach.map fun word =>
        values.filter fun recipe => recipe.erasedShape = word.1).flatten)
      values
  rw [show
      (keys.attach.map fun word =>
        values.filter fun recipe => recipe.erasedShape = word.1).flatten =
          keys.flatMap fun target =>
            values.filter fun recipe => recipe.erasedShape = target by
    change
      keys.attach.flatMap (fun word =>
        values.filter fun recipe => recipe.erasedShape = word.1) =
          keys.flatMap fun target =>
            values.filter fun recipe => recipe.erasedShape = target
    exact flat_attach_val keys fun target =>
      values.filter fun recipe => recipe.erasedShape = target]
  exact
    flat_key_perm BRecipe.erasedShape
      keys
      values
      (List.nodup_dedup _)
      (fun recipe hrecipe => by
        rw [List.mem_dedup]
        exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩)

/-- Canonical flattening retains exactly the recipes in the finite closure. -/
lemma mem_canonicalRecipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe} :
    recipe ∈ canonicalRecipes n leftWeight rightWeight ↔
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight :=
  (recipes_perm_closure
    n leftWeight rightWeight).mem_iff

/-- Every recipe in the flattened canonical inventory remains below cutoff. -/
lemma weighted_canonical_recipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ canonicalRecipes n leftWeight rightWeight) :
    weightedWordWeight leftWeight rightWeight recipe < n :=
  weighted_closure_recipes
    (mem_canonicalRecipes.mp hrecipe)

end
  ACAlign
end TCTex
end Submission

/-!
# Ordered principal packets from finite-closure profile assignments

At root weights above the first surviving bracket cutoff, a profile assignment
on the deduplicated finite correction closure produces an ordered packet with
exactly one literal principal Hall-pair occurrence.  Universal assignments
inherit the same predicate after compilation to all-integral packets.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  APWord

universe u

open
  UCAll
open
  CPWord
open
  FCAssign

namespace SPAssign

/--
At root weights above cutoff two, attaching assigned profiles turns the
deduplicated skeleton split into the ordered-packet uniqueness predicate.
-/
lemma unique_occurrence_packet
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (hn : 2 < n) :
    OBPkt.UniqueBaseOccurrence
      (assignment.orderedBlockPacket (by simp) (by simp)) := by
  exact unique_split_packets assignment hn

end SPAssign

namespace UPAssign

/--
A universal root-weight profile assignment compiles to an all-integral packet
with exactly one literal principal Hall-pair occurrence.
-/
lemma
    unique_occurrence_all
    {n : ℕ}
    (assignment : UPAssign.{u} n 1 1)
    (d : ℕ)
    (hn : 2 < n) :
    OBPkt.UniqueBaseOccurrence
      (assignment.truncAllPacket
        d (by simp) (by simp)).toOBPkt := by
  exact
    SPAssign.unique_occurrence_packet
      assignment.toSPAssign hn

end UPAssign

end
  APWord
end TCTex
end Submission

/-!
# Principal factor splits for finite correction-closure factories

An ordered finite-closure correction packet with one principal Hall-pair
occurrence compiles to one principal symbolic polynomial factor surrounded by
two strict higher-weight tails.  This is the recursive shape needed by a
symbolic Hall collector: the principal bracket is explicit, while every
remaining factor belongs to a strictly later weight stratum.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCFtry

universe u

open CFExp
open CFSubsti
open
  UCAll
open
  CPWord
open
  UCSuppor

namespace TAPkta

/--
The symbolic factors emitted by one closure-supported correction packet split
into a strict higher prefix, one principal Hall-pair factor, and a strict
higher suffix.
-/
structure PHSplit
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι) where
  beforeFactors :
    List (SPFactor H ι)
  principalFactor :
    SPFactor H ι
  afterFactors :
    List (SPFactor H ι)
  factors_eq :
    symbolicFactors normalizer packet.packets left right =
      beforeFactors ++ principalFactor :: afterFactors
  principal_word_eq :
    principalFactor.word =
      CWord.hallPairBind
        left.word right.word CWord.hallPairBase
  principal_word_weight :
    principalFactor.word.weight HEAddres.weight =
      leftWeight + rightWeight
  before_weight_least :
    SPFactor.WordWeightLeast
      (leftWeight + rightWeight + 1) beforeFactors
  after_weight_least :
    SPFactor.WordWeightLeast
      (leftWeight + rightWeight + 1) afterFactors

namespace SBSplita

/--
Compile a packet-level principal split into the factor-level shape consumed by
recursive symbolic collection.
-/
noncomputable def principalTailSplit
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer :
      WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split :
      SBSplita packet normalizer left right)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    PHSplit
      packet normalizer left right where
  beforeFactors :=
    symbolicFactors normalizer split.beforePackets left right
  principalFactor :=
    split.principalPacket.symbolicFactor normalizer left right
  afterFactors :=
    symbolicFactors normalizer split.afterPackets left right
  factors_eq := by
    rw [split.packets_eq]
    simp [symbolicFactors]
  principal_word_eq := by
    exact split.word_principal_factor
  principal_word_weight := by
    exact split.princi_symbo_facto hleft hright
  before_weight_least := by
    exact split.least_before_factors hleft hright
  after_weight_least := by
    exact split.least_after_factors hleft hright

end SBSplita

/--
The unique principal Hall-pair occurrence produces a principal factor split
with strict higher tails.
-/
noncomputable def higher_split_unique
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (hunique :
      OBPkt.UniqueBaseOccurrence
        packet.toOBPkt)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    PHSplit
      packet normalizer left right :=
  SBSplita.principalTailSplit
    (symbolic_split_unique
      packet normalizer left right hunique) hleft hright

namespace PHSplit

/--
Evaluation of the full correction packet factors through its strict higher
prefix, principal factor, and strict higher suffix.
-/
lemma list_eval_factors
    {d n leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizer :
      WBForm.RCNormal H ι}
    {left right : SPFactor H ι}
    (split :
      PHSplit
        packet normalizer left right)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
          (symbolicFactors normalizer packet.packets left right) =
      SPFactor.listEval e split.beforeFactors *
        (split.principalFactor.eval e *
          SPFactor.listEval e split.afterFactors) := by
  rw [split.factors_eq, SPFactor.listEval_append,
    SPFactor.listEval_cons]

/--
Physical routing preserves the principal-factor split because every attached
closure factor already lies below cutoff.
-/
lemma factor_suppo_facto
    {d n leftWeight rightWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizers :
      WBForm.PositiveChooseNormalizer H}
    {left right : SPFactor H ι}
    (split :
      PHSplit
        packet (normalizers.normalizer ι) left right)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    ((supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported).factors =
      split.beforeFactors ++ split.principalFactor :: split.afterFactors := by
  rw [supported_factory_symbolic
    packet normalizers left right hleftSupported hrightSupported hleft hright,
    split.factors_eq]

/--
The routed correction packet evaluates as its strict higher prefix, principal
factor, and strict higher suffix.
-/
lemma list_supported_factory
    {d n leftWeight rightWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      TAPkta.{u}
        d n leftWeight rightWeight}
    {normalizers :
      WBForm.PositiveChooseNormalizer H}
    {left right : SPFactor H ι}
    (split :
      PHSplit
        packet (normalizers.normalizer ι) left right)
    (e : ι → HEFam H)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.listEval (n := n) e
        (((supportedPacketFactory
          packet normalizers lowerWeight).packet
            left right hleftSupported hrightSupported).factors) =
      SPFactor.listEval e split.beforeFactors *
        (split.principalFactor.eval e *
          SPFactor.listEval e split.afterFactors) := by
  rw [split.factor_suppo_facto
      hleftSupported hrightSupported hleft hright,
    SPFactor.listEval_append,
    SPFactor.listEval_cons]

end PHSplit

end TAPkta

end UCFtry
end TCTex
end Submission

/-!
# Truncated principal splits for finite correction-closure factories

At parents of the declared weights, physical truncation removes no factor
from a closure-supported polynomial correction packet.  The raw principal
factor split therefore descends unchanged to the packet consumed by signed
semantic routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open
  UCAll
open
  CPWord

namespace TSPkt

/--
A physically truncated correction packet split around one selected principal
factor, with strict higher tails on both sides.
-/
structure PTSplit
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (principalWord : CWord (HEAddres H))
    (principalWeight : ℕ)
    (higherWeight : ℕ) where
  beforeFactors : List (SPFactor H ι)
  principalFactor : SPFactor H ι
  afterFactors : List (SPFactor H ι)
  factors_eq :
    C.factors = beforeFactors ++ principalFactor :: afterFactors
  principal_word_eq :
    principalFactor.word = principalWord
  principal_word_weight :
    principalFactor.word.weight HEAddres.weight =
      principalWeight
  before_weight_least :
    SPFactor.WordWeightLeast
      higherWeight beforeFactors
  after_weight_least :
    SPFactor.WordWeightLeast
      higherWeight afterFactors

namespace PTSplit

/-- Every selected prefix factor belongs to the physical correction packet. -/
lemma before_factors_subset
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight)
    {factor : SPFactor H ι}
    (hfactor : factor ∈ split.beforeFactors) :
    factor ∈ C.factors := by
  rw [split.factors_eq]
  exact List.mem_append_left _ hfactor

/-- The selected principal factor belongs to the physical correction packet. -/
lemma principal_factor_factors
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight) :
    split.principalFactor ∈ C.factors := by
  rw [split.factors_eq]
  simp

/-- Every selected suffix factor belongs to the physical correction packet. -/
lemma after_factors_subset
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight)
    {factor : SPFactor H ι}
    (hfactor : factor ∈ split.afterFactors) :
    factor ∈ C.factors := by
  rw [split.factors_eq]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hfactor)

/-- The selected strict higher prefix remains physically truncated. -/
lemma truncated_before_factors
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight) :
    SPFactor.IsTruncated n split.beforeFactors := by
  intro factor hfactor
  exact
    C.word_weight_cutoff factor
      (split.before_factors_subset hfactor)

/-- The selected strict higher suffix remains physically truncated. -/
lemma truncated_after_factors
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight) :
    SPFactor.IsTruncated n split.afterFactors := by
  intro factor hfactor
  exact
    C.word_weight_cutoff factor
      (split.after_factors_subset hfactor)

/-- The selected principal factor remains physically below cutoff. -/
lemma principal_factor_cutoff
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight) :
    split.principalFactor.word.weight HEAddres.weight < n :=
  C.word_weight_cutoff split.principalFactor
    split.principal_factor_factors

/-- The selected principal weight is physically below cutoff. -/
lemma principal_weight_cutoff
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight) :
    principalWeight < n := by
  rw [← split.principal_word_weight]
  exact split.principal_factor_cutoff

/-- The selected principal factor lies strictly before its declared tail
stratum whenever the declared principal weight does. -/
lemma principal_factor_higher
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight)
    (hweight : principalWeight < higherWeight) :
    split.principalFactor.word.weight HEAddres.weight <
      higherWeight := by
  rw [split.principal_word_weight]
  exact hweight

/--
Evaluation of the physical correction packet factors through its strict
higher prefix, selected principal factor, and strict higher suffix.
-/
lemma eval_factors
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e C.factors =
      SPFactor.listEval e split.beforeFactors *
        (split.principalFactor.eval e *
          SPFactor.listEval e split.afterFactors) := by
  rw [split.factors_eq, SPFactor.listEval_append,
    SPFactor.listEval_cons]

/--
The split product is the commutator correction required by the adjacent
parent swap.
-/
lemma list_split_commutator
    {d n principalWeight higherWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    {principalWord : CWord (HEAddres H)}
    (split :
      C.PTSplit principalWord principalWeight higherWeight)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅B.eval (n := n) e, A.eval (n := n) e⁆ := by
  rw [← split.eval_factors e]
  exact C.listEval_eq e

end PTSplit

end TSPkt

namespace
  UCFtry

namespace TAPkta

/--
At parents of the declared weights, a unique literal Hall-pair occurrence in
the closure packet descends to a principal split of the physically truncated
factory packet.
-/
noncomputable def
    factory_split_unique
    {d n leftWeight rightWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      TAPkta.{u}
        d n leftWeight rightWeight)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hunique :
      OBPkt.UniqueBaseOccurrence
        packet.toOBPkt)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (leftWeight + rightWeight)
      (leftWeight + rightWeight + 1) := by
  let split :=
    higher_split_unique packet
      (normalizers.normalizer ι) left right hunique hleft hright
  refine
    { beforeFactors := split.beforeFactors
      principalFactor := split.principalFactor
      afterFactors := split.afterFactors
      factors_eq := ?_
      principal_word_eq := split.principal_word_eq
      principal_word_weight := split.principal_word_weight
      before_weight_least := split.before_weight_least
      after_weight_least := split.after_weight_least }
  rw [supported_factory_symbolic
    packet normalizers left right hleftSupported hrightSupported hleft hright]
  exact split.factors_eq

end TAPkta

end
  UCFtry
end TCTex
end Submission

/-!
# Principal factor splits from recursive profile assignments

A recursive finite-closure profile kernel compiles to the ordered packet
support used by the symbolic correction factory.  At root weights, the
closure's unique principal Hall-pair occurrence therefore supplies the
principal-factor split automa once the universal product identity is
known.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace UCFtry

universe u

open scoped commutatorElement

open CFSubsti
open
  CPWord
open
  PWSep
open
  APWord
open
  CRAssign
open
  FCAssign

namespace TAPkta

/--
The root-weight profile-assignment packet inherits the closure skeleton's
unique principal Hall-pair occurrence.
-/
lemma unique_occurrence_assignment
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (hn : 2 < n) :
    OBPkt.UniqueBaseOccurrence
      (assignment.orderedBlockPacket (by simp) (by simp)) := by
  change
    ∃ beforeBasic afterBasic : List (CWord HPAtom),
      assignment.toPackets.map RFPkt.word =
          beforeBasic ++ CWord.hallPairBase :: afterBasic ∧
        CWord.hallPairBase ∉ beforeBasic ∧
          CWord.hallPairBase ∉ afterBasic
  rw [assignment.word_packets]
  exact unique_split_vocabulary hn

/--
The ordered packet compiled from a recursive root-weight profile kernel has
one principal Hall-pair occurrence.
-/
lemma unique_occurrence_recursive
    {n : ℕ}
    (kernel : RPKern n 1 1)
    (hn : 2 < n) :
    OBPkt.UniqueBaseOccurrence
      ((kernel.signedProfileAssignment (by simp) (by simp))
        |>.orderedBlockPacket (by simp) (by simp)) := by
  exact
    unique_occurrence_assignment
      _ hn

/--
Once its universal product identity is supplied, a recursive root-weight
profile kernel produces the symbolic principal-factor split with strict
higher-weight tails.
-/
noncomputable def higher_split_recursive
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (kernel : RPKern n 1 1)
    (listEval_eq :
      ∀ {G : Type u} [Group G]
        (left right : G)
        (leftExponent rightExponent : ℤ),
          (((kernel.signedProfileAssignment
              (by simp) (by simp)).toPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
            ⁅left ^ leftExponent, right ^ rightExponent⁆)
    (hn : 2 < n)
    (normalizer :
      WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    PHSplit
      ((kernel.universalProfileAssignment
        (by simp) (by simp) listEval_eq)
        |>.truncAllPacket d
          (by simp) (by simp))
      normalizer left right :=
  higher_split_unique
    ((kernel.universalProfileAssignment
      (by simp) (by simp) listEval_eq)
      |>.truncAllPacket d
        (by simp) (by simp))
    normalizer left right
    (unique_occurrence_recursive
      kernel hn)
    hleft hright

end TAPkta

end UCFtry
end TCTex
end Submission

/-!
# Polynomial principal splits from finite-closure profile assignments

A universal root-weight profile assignment compiles all the way to a
physically truncated polynomial correction packet with one principal
weight-two factor and strict weight-three-or-higher tails.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  APWord

universe u

open
  UCFtry
open TAPkta
open
  FCAssign

namespace UPAssign

/--
Above cutoff two, a universal root-weight closure assignment supplies the
physical principal-factor split required by polynomial residual routing.
-/
noncomputable def factoryPrincipalSplit
    {n lowerWeight d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (assignment : UPAssign.{u} n 1 1)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      assignment.truncAllPacket
        d (by simp) (by simp)
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factory_split_unique
      (assignment.truncAllPacket
        d (by simp) (by simp))
      normalizers left right hleftSupported hrightSupported
      (unique_occurrence_all
        assignment d hn)
      hleft hright

end UPAssign

end
  APWord
end TCTex
end Submission

/-!
# Polynomial principal splits from recipe-chunk alignment

An ordered cutoff-specific recipe packet, grouped into the same-word chunks of
a finite-closure profile assignment, supplies the physically truncated
principal-factor split used by polynomial residual routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ACAlign

universe u

open
  UCFtry
open TAPkta
open
  CPWord
open
  APWord
open
  FCAssign

set_option linter.style.longLine false in
private lemma assignment_unique_occurrence
    {n : ℕ}
    (assignment : SPAssign n 1 1)
    (hn : 2 < n) :
    OBPkt.UniqueBaseOccurrence
      (assignment.orderedBlockPacket (by simp) (by simp)) := by
  exact
    SPAssign.unique_occurrence_packet
      assignment hn

namespace SPAssign

/--
Recipe-chunk alignment routes a cutoff-specific root-weight recollection to one
weight-two principal polynomial factor and strict weight-three-or-higher tails.
-/
noncomputable def
    factoryChunkAlignment
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (assignment : SPAssign n 1 1)
    (recipePacket :
      PFSubsti.TAPkt.{u}
        d n)
    (alignment : RCAlign assignment recipePacket.recipes)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      allChunkAlignment
        assignment recipePacket (by simp) (by simp) alignment
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factory_split_unique
      (allChunkAlignment
        assignment recipePacket (by simp) (by simp) alignment)
      normalizers left right hleftSupported hrightSupported
      (assignment_unique_occurrence assignment hn)
      hleft hright

end SPAssign

end
  ACAlign
end TCTex
end Submission

/-!
# Polynomial principal splits from recursive finite-closure profiles

A recursive root-weight profile kernel compiles to the physically truncated
polynomial correction packet used by residual routing once its remaining
ordered semantic product identity is supplied.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CRAssign

universe u

open scoped commutatorElement

open
  UCFtry
open TAPkta
open
  APWord
open
  FCAssign
open UPAssign

namespace RPKern

/--
The ordered semantic product identity is the only extra input needed to route
a recursively generated root-weight closure packet into one weight-two
principal polynomial factor and strict weight-three-or-higher tails.
-/
noncomputable def supportedFactorySplit
    {n lowerWeight d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (kernel : RPKern n 1 1)
    (listEval_eq :
      ∀ {G : Type u} [Group G]
        (left right : G)
        (leftExponent rightExponent : ℤ),
          (((kernel.signedProfileAssignment
              (by simp) (by simp)).toPackets).map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
            ⁅left ^ leftExponent, right ^ rightExponent⁆)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let assignment :=
      kernel.universalProfileAssignment
        (by simp) (by simp) listEval_eq
    let packet :=
      assignment.truncAllPacket
        d (by simp) (by simp)
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryPrincipalSplit
        (kernel.universalProfileAssignment
          (by simp) (by simp) listEval_eq)
        normalizers left right hn hleftSupported hrightSupported hleft hright

end RPKern

end
  CRAssign
end TCTex
end Submission

/-!
# Canonical finite-closure recipe principal split

The canonical recipe inventory gives an explicit finite ordered list of
same-word chunks.  Its remaining cutoff-specific recollection law compiles to
the physically truncated principal split consumed by polynomial residual
routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CPSplit

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  UCAll
open
  UCFtry
open
  ACAlign
open
  FCAssign
open SPAssign
open TAPkta
open TSPkt

/--
The explicit remaining collection theorem for the canonical finite recipe
inventory at one lower-central cutoff.
-/
def SatisfiesRecipeTruncated
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((canonicalRecipes n 1 1).map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
A canonical recipe recollection law is a cutoff-specific all-integral
Hall-Petresco packet.
-/
noncomputable def canonicalAllPacket
    {d n : ℕ}
    (hlistEval : SatisfiesRecipeTruncated d n) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes :=
    canonicalRecipes n 1 1
  listEval_eq :=
    hlistEval

/--
The canonical assignment and its chunk alignment compile the canonical recipe
law to an ordered closure-supported signed packet.
-/
noncomputable def canonicalRecipePacket
    {d n : ℕ}
    (hlistEval : SatisfiesRecipeTruncated d n) :
    TAPkta.{u} d n 1 1 :=
  allChunkAlignment
    (canonicalProfileAssignment n 1 1)
    (canonicalAllPacket hlistEval)
    (by simp)
    (by simp)
    (canonicalChunkAlignment n 1 1)

/--
At root-weight parents and cutoff above two, the canonical recipe law supplies
one physical weight-two principal factor and strict weight-three-or-higher
tails.
-/
noncomputable def canonicalHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval : SatisfiesRecipeTruncated d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      canonicalRecipePacket hlistEval
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryChunkAlignment
      (canonicalProfileAssignment n 1 1)
      (canonicalAllPacket hlistEval)
      (canonicalChunkAlignment n 1 1)
      normalizers left right hn hleftSupported hrightSupported hleft hright

/--
The canonical physical principal split evaluates to the root commutator
correction.
-/
lemma principal_higher_commutator
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval : SatisfiesRecipeTruncated d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      canonicalHigherSplit
        hlistEval normalizers left right hn hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (canonicalHigherSplit
      hlistEval normalizers left right hn hleftSupported hrightSupported
        hleft hright).list_split_commutator e

end
  CPSplit
end TCTex
end Submission

namespace Submission
namespace TCTex
namespace
  CAAlign

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open CFSubsti
open
  UCAll
open
  UCFtry
open
  ACAlign
open
  RASem
open
  FCAssign
open SPAssign
open TAPkta
open TSPkt

lemma singleton_chunk_alignment
    (packet : RFPkt)
    (hpacket : RecipeProfile packet.word packet.profiles) :
    ∃ recipe : BRecipe,
      RFPkt.RCAlign
        packet [recipe] := by
  rcases hpacket with ⟨recipe, hshape, hvalue⟩
  refine ⟨recipe, ?_⟩
  refine
    { erased_shape_word := ?_
      profiles_value_sum := ?_ }
  · intro nextRecipe hnextRecipe
    simp only [List.mem_singleton] at hnextRecipe
    subst nextRecipe
    exact hshape
  · intro leftExponent rightExponent
    simpa using hvalue leftExponent rightExponent

private theorem exists_chunks_forall₂_of_exists_recipeChunkAlignment :
    ∀ packets : List RFPkt,
      (∀ packet ∈ packets,
        ∃ recipes : List BRecipe,
          RFPkt.RCAlign
            packet recipes) →
      ∃ chunks : List (List BRecipe),
        List.Forall₂
          RFPkt.RCAlign
          packets chunks
  | [], _ =>
      ⟨[], .nil⟩
  | packet :: packets, hexists => by
      rcases hexists packet (by simp) with ⟨recipes, hrecipes⟩
      rcases
          exists_chunks_forall₂_of_exists_recipeChunkAlignment packets
            (fun nextPacket hnextPacket =>
              hexists nextPacket (by simp [hnextPacket])) with
        ⟨chunks, hchunks⟩
      exact ⟨recipes :: chunks, .cons hrecipes hchunks⟩

theorem chunk_profiles_motive
    {n leftWeight rightWeight : ℕ}
    (assignment :
      PAMotive
        n leftWeight rightWeight RecipeProfile) :
    Nonempty (Σ recipes : List BRecipe,
      SPAssign.RCAlign
        assignment.toSPAssign recipes) := by
  have hexists :
      ∀ packet ∈ assignment.toSPAssign.toPackets,
        ∃ recipes : List BRecipe,
          RFPkt.RCAlign
            packet recipes := by
    intro packet hpacket
    rcases
        singleton_chunk_alignment
          packet (assignment.profile_motive_packets hpacket) with
      ⟨recipe, hrecipe⟩
    exact ⟨[recipe], hrecipe⟩
  rcases
      exists_chunks_forall₂_of_exists_recipeChunkAlignment
        assignment.toSPAssign.toPackets hexists with
    ⟨chunks, hchunks⟩
  exact
    ⟨⟨chunks.flatten,
        { chunks := chunks
          packets_chunks := hchunks
          flatten_chunks := rfl }⟩⟩

noncomputable def positiveChunkAlignment
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :=
  Classical.choice
    (chunk_profiles_motive
      (positiveProfileAssignment
        n leftWeight rightWeight hleftWeight hrightWeight))

noncomputable def positiveCoefficientRecipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (positiveChunkAlignment
    n leftWeight rightWeight hleftWeight hrightWeight).1

noncomputable def positiveCoefficientChunk
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SPAssign.RCAlign
      ((positiveProfileAssignment
        n leftWeight rightWeight hleftWeight hrightWeight)
        |>.toSPAssign)
      (positiveCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight) :=
  (positiveChunkAlignment
    n leftWeight rightWeight hleftWeight hrightWeight).2

lemma positive_assignment_recipes
    {G : Type*}
    [Group G]
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((((positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.toSPAssign.toPackets).map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod) =
      ((positiveCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight).map fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe leftExponent rightExponent).prod := by
  exact
    (positiveCoefficientChunk
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.list_recipe_factors
        left right leftExponent rightExponent

/--
The remaining cutoff-specific collection law after automatic recipe-chunk
alignment: the selected ordered recipe product recollects the root
commutator.
-/
def SatisfiesPositiveRecipe
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((positiveCoefficientRecipes n 1 1 (by simp) (by simp)).map
        fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
A proof of the selected ordered recipe-product identity is precisely the
cutoff-specific all-integral packet required by the polynomial collector.
-/
noncomputable def positiveAllPacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesPositiveRecipe d n) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes :=
    positiveCoefficientRecipes n 1 1 (by simp) (by simp)
  listEval_eq :=
    hlistEval

/--
Automatic chunk alignment compiles the selected recipe-product law to the
ordered root-weight signed packet required by correction stabilization.
-/
noncomputable def
    positiveRecipePacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesPositiveRecipe d n) :
    TAPkta.{u} d n 1 1 :=
  allChunkAlignment
      ((positiveProfileAssignment
        n 1 1 (by simp) (by simp)).toSPAssign)
      (positiveAllPacket hlistEval)
      (by simp)
      (by simp)
      (positiveCoefficientChunk
        n 1 1 (by simp) (by simp))

/--
At root-weight parents and cutoff above two, the selected recipe collection
law supplies one physical weight-two principal factor and strict
weight-three-or-higher tails.
-/
noncomputable def
    positiveHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesPositiveRecipe d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      positiveRecipePacket
        hlistEval
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryChunkAlignment
        ((positiveProfileAssignment
          n 1 1 (by simp) (by simp)).toSPAssign)
        (positiveAllPacket hlistEval)
        (positiveCoefficientChunk
          n 1 1 (by simp) (by simp))
        normalizers left right hn hleftSupported hrightSupported hleft hright

/--
The physical principal split assembled from the selected recipe-product law
evaluates to the root commutator correction.
-/
lemma higher_split_commutator
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesPositiveRecipe d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      positiveHigherSplit
        hlistEval normalizers left right hn hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (positiveHigherSplit
      hlistEval normalizers left right hn hleftSupported hrightSupported
        hleft hright).list_split_commutator e

end
  CAAlign
end TCTex
end Submission

/-!
# Canonical finite-correction recipes at the first cutoffs

This file records the first semantic instances for the canonical recipe list.
Below cutoff three the inventory is empty.  At cutoff at most three, every
surviving recipe has the basic Hall-pair erased shape.
-/

namespace Submission
namespace TCTex
namespace
  CPSplit

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  UCAll
open CLPacket
open
  ACAlign
open
  CPSep
open
  PWSep
open
  UCSuppor
open UCVocabu

lemma recipes_nil_n
    {n : ℕ}
    (hn : n ≤ 2) :
    canonicalRecipes n 1 1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro recipe hrecipe
  have hlt :
      weightedWordWeight 1 1 recipe < n :=
    weighted_canonical_recipes hrecipe
  have hbasic :
      weightedWordWeight 1 1 hallPair ≤
        weightedWordWeight 1 1 recipe :=
    weighted_weight_basic 1 1 recipe
  simp only [weighted_word_pair] at hbasic
  omega

lemma satisfies_n_two
    {d n : ℕ}
    (hn : n ≤ 2) :
    SatisfiesRecipeTruncated d n := by
  intro left right leftExponent rightExponent
  rw [recipes_nil_n hn]
  exact
    (empty_n_two (d := d) hn).listEval_eq
      left right leftExponent rightExponent

noncomputable def
    canonical_n_two
    {d n : ℕ}
    (hn : n ≤ 2) :
    TAPkta.{u} d n 1 1 :=
  canonicalRecipePacket
    (satisfies_n_two hn)

lemma erased_recipes_n
    {n : ℕ}
    (hn : n ≤ 3)
    {recipe : BRecipe}
    (hrecipe : recipe ∈ canonicalRecipes n 1 1) :
    recipe.erasedShape = CWord.hallPairBase := by
  have hretained :
      recipe ∈ correctionClosureRecipes n 1 1 :=
    mem_canonicalRecipes.mp hrecipe
  have hlt :
      weightedWordWeight 1 1 recipe < n :=
    weighted_closure_recipes
      hretained
  have hbasic :
      weightedWordWeight 1 1 hallPair ≤
        weightedWordWeight 1 1 recipe :=
    weighted_weight_basic 1 1 recipe
  have hweight :
      weightedWordWeight 1 1 recipe = 2 := by
    simp only [weighted_word_pair] at hbasic
    omega
  have hdegrees :
      recipe.leftDegree + recipe.rightDegree = 2 := by
    simpa [weighted_word_weight] using hweight
  have hleftPositive := leftDegree_pos recipe
  have hrightPositive := rightDegree_pos recipe
  have hleftDegree :
      recipe.leftDegree = 1 := by
    omega
  have hrightDegree :
      recipe.rightDegree = 1 := by
    omega
  exact
    base_recipes_bidegree
      (recipes_closure_bidegree
        hretained hleftDegree hrightDegree)
      hleftDegree hrightDegree

lemma erased_vocabulary_singleton
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    erasedShapeVocabulary n 1 1 =
      [CWord.hallPairBase] := by
  have hallPairBase_of_mem :
      ∀ word ∈ erasedShapeVocabulary n 1 1,
        word = CWord.hallPairBase := by
    intro word hword
    have hlt :
        word.weight (HPAtom.weight 1 1) < n :=
      erased_shape_vocabulary hword
    rw [CWord.pair_atom_degree] at hlt
    simp only [Nat.mul_one] at hlt
    have hpositive :
        word.PBPos :=
      bidegree_positive_vocabulary hword
    have hleftPositive :
        0 < word.pairLeftDegree :=
      hpositive.1
    have hrightPositive :
        0 < word.pairRightDegree :=
      hpositive.2
    have hleftDegree :
        word.pairLeftDegree = 1 := by
      omega
    have hrightDegree :
        word.pairRightDegree = 1 := by
      omega
    exact
      erased_vocabulary_bidegree
        hword hleftDegree hrightDegree
  rcases unique_split_vocabulary hlow with
    ⟨beforeBasic, afterBasic, hsplit, hbeforeBasic, hafterBasic⟩
  have hbeforeBasicNil :
      beforeBasic = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro word hword
    apply hbeforeBasic
    rw [← hallPairBase_of_mem word]
    · exact hword
    · rw [hsplit]
      simp [hword]
  have hafterBasicNil :
      afterBasic = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro word hword
    apply hafterBasic
    rw [← hallPairBase_of_mem word]
    · exact hword
    · rw [hsplit]
      simp [hword]
  rw [hsplit, hbeforeBasicNil, hafterBasicNil]
  simp

lemma chunks_singleton_chunk
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    canonicalRecipeChunks n 1 1 =
      [recipesForWord n 1 1 CWord.hallPairBase] := by
  unfold canonicalRecipeChunks
  rw [
    erased_vocabulary_singleton
      hlow hhigh]
  rfl

lemma recipes_chunk_n
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    canonicalRecipes n 1 1 =
      recipesForWord n 1 1 CWord.hallPairBase := by
  unfold canonicalRecipes
  rw [
    chunks_singleton_chunk
      hlow hhigh]
  simp

lemma
    length_packets_assignment
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    (canonicalProfileAssignment n 1 1).toPackets.length = 1 := by
  rw [packets_profile_assignment]
  simp only [List.length_map, List.length_attach]
  rw [
    erased_vocabulary_singleton
      hlow hhigh]
  rfl

end
  CPSplit
end TCTex
end Submission

/-!
# Canonical truncated signed-profile assignment

The canonical finite-closure recipe inventory is grouped into same-word
chunks.  Its flattened recipe-product law is therefore equivalent to the
fixed-truncation product law for the corresponding summed signed-profile
assignment.

This identifies the precise arbitrary-cutoff semantic obligation for Claim 5
without replacing coefficient sums by a singleton recipe transversal.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CTAssign

universe u

open
  CPSplit
open
  ACAlign
open
  UTAssign

/--
The canonical recipe-product law implies the summed-profile product law in
the fixed free lower-central truncation.
-/
lemma satisfies_profile_assignment
    {d n : ℕ}
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n) :
    SatisfiesTruncEval.{u} (d := d)
      (canonicalProfileAssignment n 1 1) := by
  intro left right leftExponent rightExponent
  exact
    ((canonicalChunkAlignment n 1 1).list_recipe_factors
      left right leftExponent rightExponent).trans
        (hlistEval left right leftExponent rightExponent)

/--
Conversely, the summed-profile product law recovers the flattened canonical
recipe-product law.
-/
lemma satisfies_canonical_recipe
    {d n : ℕ}
    (hlistEval :
      SatisfiesTruncEval.{u} (d := d)
        (canonicalProfileAssignment n 1 1)) :
    SatisfiesRecipeTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  exact
    ((canonicalChunkAlignment n 1 1).list_recipe_factors
      left right leftExponent rightExponent).symm.trans
        (hlistEval left right leftExponent rightExponent)

/--
For the canonical finite-closure collector, the recipe law and the
summed-profile law are equivalent.
-/
theorem satisfies_recipe_truncated
    {d n : ℕ} :
    SatisfiesRecipeTruncated.{u} d n ↔
      SatisfiesTruncEval.{u} (d := d)
        (canonicalProfileAssignment n 1 1) :=
  ⟨satisfies_profile_assignment,
    satisfies_canonical_recipe⟩

end
  CTAssign
end TCTex
end Submission

/-!
# Global canonical aggregated symbolic recollection polynomials

The finite correction closure carries a canonical same-word chunking.  Each
chunk contributes one homogeneous signed-profile formula whose value is the
sum of the generalized-binomial recipe coefficients in that chunk.

This file substitutes arbitrary symbolic Hall parents into those canonical
packets.  The resulting factor list has one entry per erased Hall word, is
stable under physical cutoff truncation, and evaluates exactly as the
flattened canonical recipe inventory.  The remaining global semantic theorem
is intentionally exposed as `SatisfiesRecipeTruncated`: the
finite correction closure is a conservative support universe, not by itself
an operational collection schedule.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  GRPolys

universe u

open scoped commutatorElement

open
  CFExp
open
  CFSubsti
open
  CPSplit
open
  UCFtry
open
  ACAlign
open
  FCAssign
open
  UCSuppor
open TAPkta

/-- Canonical coefficient-sum packets attached to the deduplicated erased-word
skeleton. -/
noncomputable def globalProfilePackets
    (n leftWeight rightWeight : ℕ) :
    List RFPkt :=
  (canonicalProfileAssignment n leftWeight rightWeight).toPackets

/-- Substitute arbitrary symbolic Hall parents into the fixed canonical
coefficient-sum packet list. -/
noncomputable def globalRecollectionFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (left right : SPFactor H ι) :
    List (SPFactor H ι) :=
  symbolicFactors normalizer
    (globalProfilePackets
      n leftWeight rightWeight)
    left right

/-- Forgetting canonical coefficient sums recovers the deduplicated erased-word
skeleton. -/
@[simp]
lemma global_recollection_packets
    (n leftWeight rightWeight : ℕ) :
    (globalProfilePackets
      n leftWeight rightWeight).map
        RFPkt.word =
      erasedShapeVocabulary n leftWeight rightWeight := by
  unfold globalProfilePackets
  exact SPAssign.word_packets _

/-- There is exactly one canonical coefficient-sum packet per skeleton word. -/
lemma length_recollection_packets
    (n leftWeight rightWeight : ℕ) :
    (globalProfilePackets
      n leftWeight rightWeight).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  rw [← List.length_map,
    global_recollection_packets]

/-- The substituted canonical factor list still has fixed skeleton
cardinality. -/
lemma length_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (left right : SPFactor H ι) :
    (globalRecollectionFactors normalizer
      n leftWeight rightWeight left right).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  unfold globalRecollectionFactors
  unfold symbolicFactors
  rw [List.length_map,
    length_recollection_packets]

/-- Canonical symbolic-factor words are exactly the substituted skeleton
words. -/
lemma global_profile_recollection
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (left right : SPFactor H ι) :
    (globalRecollectionFactors normalizer
      n leftWeight rightWeight left right).map
        SPFactor.word =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
  unfold globalRecollectionFactors
  unfold symbolicFactors
  rw [List.map_map]
  calc
    _ =
      (globalProfilePackets
        n leftWeight rightWeight).map
          (fun packet =>
            CWord.hallPairBind
              left.word right.word packet.word) := by
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      ((globalProfilePackets
        n leftWeight rightWeight).map
          RFPkt.word).map
            (fun word =>
              CWord.hallPairBind left.word right.word word) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
      rw [global_recollection_packets]

/-- Every canonical substituted factor lies below cutoff at symbolic parents
of the declared weights. -/
lemma
    global_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈
        globalRecollectionFactors normalizer
          n leftWeight rightWeight left right) :
    factor.word.weight HEAddres.weight < n := by
  unfold globalRecollectionFactors at hfactor
  rcases packet_symbolic_factors hfactor with
    ⟨packet, hpacket, rfl⟩
  have hword :
      packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
    unfold globalProfilePackets at hpacket
    exact
      SPAssign.word_vocabulary_packets
        _ hpacket
  rw [packet.word_symbolicFactor, packet.weight_boundWord, hleft, hright]
  simpa [HPAtom.weight] using
    erased_shape_vocabulary hword

/-- Physical truncation removes no canonical symbolic recollection factor. -/
@[simp]
lemma truncate_global_self
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (left right : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.truncate n
        (globalRecollectionFactors normalizer
          n leftWeight rightWeight left right) =
      globalRecollectionFactors normalizer
        n leftWeight rightWeight left right := by
  apply List.filter_eq_self.2
  intro factor hfactor
  simpa only [decide_eq_true_eq] using
    global_recollection_factors
      normalizer left right factor hleft hright hfactor

/--
After arbitrary symbolic substitution, canonical coefficient-sum factors
evaluate exactly as the flattened canonical recipe inventory.
-/
lemma
    global_recollection_recipes
    {d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (n leftWeight rightWeight : ℕ)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := truncation) e
        (globalRecollectionFactors normalizer
          n leftWeight rightWeight left right) =
      ((canonicalRecipes n leftWeight rightWeight).map fun recipe =>
          recipe.erasedShape.eval
            (HPAtom.eval
              (left.wordValue (n := truncation))
              (right.wordValue (n := truncation))) ^
          BRSpec.coefficientValue recipe
            (left.coefficient.eval e) (right.coefficient.eval e)).prod := by
  unfold globalRecollectionFactors
  rw [listSymbolicFactors]
  unfold globalProfilePackets
  exact
    (canonicalChunkAlignment n leftWeight rightWeight)
      |>.list_recipe_factors
        (left.wordValue (n := truncation))
        (right.wordValue (n := truncation))
        (left.coefficient.eval e)
        (right.coefficient.eval e)

/--
At root weights, the remaining canonical-inventory semantic law gives the
powered commutator equation directly in the global aggregated symbolic
language.
-/
lemma
    global_recollection_commutator
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hlistEval : SatisfiesRecipeTruncated.{u} d n)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalRecollectionFactors normalizer
          n 1 1 left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ := by
  rw [
    global_recollection_recipes]
  exact
    hlistEval
      (left.wordValue (n := n))
      (right.wordValue (n := n))
      (left.coefficient.eval e)
      (right.coefficient.eval e)

/--
The canonical all-integral packet exposes exactly the global canonical packet
list.
-/
@[simp]
lemma packets_truncated_packet
    {d n : ℕ}
    (hlistEval : SatisfiesRecipeTruncated.{u} d n) :
    (canonicalRecipePacket hlistEval).packets =
      globalProfilePackets n 1 1 :=
  rfl

/--
At supported root-weight parents, physical routing emits literally the fixed
global canonical aggregated factor list.
-/
lemma supported_factory_canonical
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval : SatisfiesRecipeTruncated.{u} d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    ((supportedPacketFactory
        (canonicalRecipePacket hlistEval)
        normalizers lowerWeight).packet
          left right hleftSupported hrightSupported).factors =
      globalRecollectionFactors
        (normalizers.normalizer ι) n 1 1 left right := by
  rw [
    supported_factory_symbolic
      (canonicalRecipePacket hlistEval)
      normalizers left right hleftSupported hrightSupported hleft hright]
  rfl

end
  GRPolys
end TCTex
end Submission

/-!
# Explicit recipe-coefficient transversals

The recursive recipe-coefficient assignment chooses one coefficient formula
for every erased Hall word in the finite correction-closure skeleton.  This
file chooses the witnessing recipe word by word, in skeleton order.  The
resulting recipe list is an explicit transversal: its erased shapes are
exactly the deduplicated vocabulary, with no conservative closure
multiplicities.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CETransv

open HACoeff
open BRSpec
open CFSubsti
open
  ACAlign
open
  RASem
open
  FCAssign
open
  UCSuppor

/--
The recursively selected coefficient profile for one vocabulary word has a
shape-equivalent recipe witness.
-/
private theorem explicit_recipe_witness
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    ∃ recipe : BRecipe,
      recipe.erasedShape = word.1 ∧
        ∀ leftExponent rightExponent : ℤ,
          ((positiveProfileAssignment
              n leftWeight rightWeight hleftWeight hrightWeight)
            |>.toSPAssign.profiles word.1 word.2).value
              leftExponent rightExponent =
            coefficientValue recipe leftExponent rightExponent := by
  exact
    recipe_profiles_assignment
      hleftWeight hrightWeight word.1 word.2

/-- One recursively selected recipe witness for a retained erased Hall word. -/
noncomputable def explicitRecipeWord
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    BRecipe :=
  Classical.choose
    (explicit_recipe_witness hleftWeight hrightWeight word)

/-- The explicit recipe witness has the requested erased Hall word. -/
lemma erased_shape_explicit
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    (explicitRecipeWord hleftWeight hrightWeight word).erasedShape =
      word.1 :=
  (Classical.choose_spec
    (explicit_recipe_witness hleftWeight hrightWeight word)).1

/--
The recursively selected profile value is the coefficient value of its
explicit recipe witness.
-/
lemma value_profiles_explicit
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight })
    (leftExponent rightExponent : ℤ) :
    ((positiveProfileAssignment
        n leftWeight rightWeight hleftWeight hrightWeight)
      |>.toSPAssign.profiles word.1 word.2).value
        leftExponent rightExponent =
      coefficientValue
        (explicitRecipeWord hleftWeight hrightWeight word)
        leftExponent rightExponent :=
  (Classical.choose_spec
    (explicit_recipe_witness hleftWeight hrightWeight word)).2
      leftExponent rightExponent

/-- Singleton chunks of explicit recipe witnesses, in skeleton order. -/
noncomputable def explicitCoefficientChunks
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (List BRecipe) :=
  (erasedShapeVocabulary n leftWeight rightWeight).attach.map fun word =>
    [explicitRecipeWord hleftWeight hrightWeight word]

/-- Flatten the singleton chunks to the explicit selected recipe transversal. -/
noncomputable def explicitCoefficientRecipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (erasedShapeVocabulary n leftWeight rightWeight).attach.map fun word =>
    explicitRecipeWord hleftWeight hrightWeight word

/-- Each explicit recipe witness is aligned with its selected profile packet. -/
noncomputable def explicitChunkAlignment
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    RFPkt.RCAlign
      {
        word := word.1
        positive :=
          bidegree_positive_vocabulary word.2
        profiles :=
          (positiveProfileAssignment
            n leftWeight rightWeight hleftWeight hrightWeight)
            |>.toSPAssign.profiles word.1 word.2
      }
      [explicitRecipeWord hleftWeight hrightWeight word] where
  erased_shape_word := by
    intro recipe hrecipe
    simp only [List.mem_singleton] at hrecipe
    subst recipe
    exact erased_shape_explicit hleftWeight hrightWeight word
  profiles_value_sum := by
    intro leftExponent rightExponent
    simpa using
      value_profiles_explicit
        hleftWeight hrightWeight word leftExponent rightExponent

/--
The recursive recipe-coefficient assignment is aligned with the explicit
singleton recipe transversal.
-/
noncomputable def coefficientChunkAlignment
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SPAssign.RCAlign
      ((positiveProfileAssignment
        n leftWeight rightWeight hleftWeight hrightWeight)
        |>.toSPAssign)
      (explicitCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight) where
  chunks :=
    explicitCoefficientChunks
      n leftWeight rightWeight hleftWeight hrightWeight
  packets_chunks := by
    unfold SPAssign.toPackets
    unfold explicitCoefficientChunks
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro word _hword
    exact
      explicitChunkAlignment
        hleftWeight hrightWeight word
  flatten_chunks := by
    unfold explicitCoefficientChunks
    unfold explicitCoefficientRecipes
    induction (erasedShapeVocabulary n leftWeight rightWeight).attach with
    | nil =>
        rfl
    | cons word words ih =>
        simp [ih]

/--
Erasing the explicit recipe transversal recovers the finite skeleton in its
original deduplicated order.
-/
lemma erased_explicit_recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (explicitCoefficientRecipes
      n leftWeight rightWeight hleftWeight hrightWeight).map
        BRecipe.erasedShape =
      erasedShapeVocabulary n leftWeight rightWeight := by
  unfold explicitCoefficientRecipes
  rw [List.map_map]
  calc
    (erasedShapeVocabulary n leftWeight rightWeight).attach.map
          (BRecipe.erasedShape ∘
            explicitRecipeWord hleftWeight hrightWeight) =
        (erasedShapeVocabulary n leftWeight rightWeight).attach.map
          Subtype.val := by
      apply List.map_congr_left
      intro word _hword
      exact erased_shape_explicit hleftWeight hrightWeight word
    _ = erasedShapeVocabulary n leftWeight rightWeight :=
      List.attach_map_subtype_val _

/-- The explicit transversal contains one recipe for each skeleton word. -/
lemma length_explicit_recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (explicitCoefficientRecipes
      n leftWeight rightWeight hleftWeight hrightWeight).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  simpa only [List.length_map] using
    congrArg List.length
      (erased_explicit_recipes
        n leftWeight rightWeight hleftWeight hrightWeight)

/-- No two explicit selected recipes have the same erased Hall word. -/
lemma nodup_explicit_recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ((explicitCoefficientRecipes
      n leftWeight rightWeight hleftWeight hrightWeight).map
        BRecipe.erasedShape).Nodup := by
  rw [
    erased_explicit_recipes
      n leftWeight rightWeight hleftWeight hrightWeight]
  exact List.nodup_dedup _

/-- In particular, the explicit selected recipe transversal has no repeats. -/
lemma nodup_coefficient_recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (explicitCoefficientRecipes
      n leftWeight rightWeight hleftWeight hrightWeight).Nodup :=
  (nodup_explicit_recipes
    n leftWeight rightWeight hleftWeight hrightWeight).of_map
      BRecipe.erasedShape

/-- Every explicit selected recipe remains strictly below the cutoff. -/
lemma weighted_explicit_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈
        explicitCoefficientRecipes
          n leftWeight rightWeight hleftWeight hrightWeight) :
    weightedWordWeight leftWeight rightWeight recipe < n := by
  have hshape :
      recipe.erasedShape ∈ erasedShapeVocabulary n leftWeight rightWeight := by
    rw [←
      erased_explicit_recipes
        n leftWeight rightWeight hleftWeight hrightWeight]
    exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩
  simpa only [weightedWordWeight] using
    erased_shape_vocabulary hshape

/--
Every skeleton word has exactly one erased-shape occurrence in the explicit
recipe transversal.
-/
lemma unique_explicit_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃! recipe : BRecipe,
      recipe ∈
          explicitCoefficientRecipes
            n leftWeight rightWeight hleftWeight hrightWeight ∧
        recipe.erasedShape = word := by
  have hword' :
      word ∈
        (explicitCoefficientRecipes
          n leftWeight rightWeight hleftWeight hrightWeight).map
            BRecipe.erasedShape := by
    rwa [
      erased_explicit_recipes
        n leftWeight rightWeight hleftWeight hrightWeight]
  rcases List.mem_map.mp hword' with ⟨recipe, hrecipe, hshape⟩
  refine ⟨recipe, ⟨hrecipe, hshape⟩, ?_⟩
  intro nextRecipe hnextRecipe
  exact (
    List.inj_on_of_nodup_map
      (nodup_explicit_recipes
        n leftWeight rightWeight hleftWeight hrightWeight)
        hrecipe hnextRecipe.1 (hshape.trans hnextRecipe.2.symm)).symm

/--
Evaluation of the recursive profile assignment is evaluation of the explicit
ordered recipe transversal.
-/
lemma assignment_explicit_recipes
    {G : Type*}
    [Group G]
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((((positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.toSPAssign.toPackets).map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value leftExponent rightExponent).prod) =
      ((explicitCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight).map fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe leftExponent rightExponent).prod := by
  exact
    (coefficientChunkAlignment
      n leftWeight rightWeight hleftWeight hrightWeight)
      |>.list_recipe_factors
        left right leftExponent rightExponent

end
  CETransv
end TCTex
end Submission

/-!
# Low-cutoff canonical aggregated symbolic recollection polynomials

At cutoff at most two the canonical finite-closure inventory is empty, and
the corresponding fixed aggregated symbolic factor list evaluates
unconditionally to the powered commutator.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CRPolys

universe u

open scoped commutatorElement

open
  CPSplit
open
  GRPolys

/--
Through cutoff two, the fixed canonical aggregated symbolic list evaluates
unconditionally to the powered commutator.
-/
lemma
    recollection_n_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hn : n ≤ 2)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalRecollectionFactors normalizer
          n 1 1 left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  global_recollection_commutator
    normalizer e
      (satisfies_n_two hn)
      left right

end
  CRPolys
end TCTex
end Submission

/-!
# Stabilization boundary for global canonical recollection polynomials

The genuine operational collector produces a multiplicity-dependent ordered
signed-profile packet.  The canonical global polynomial endpoint produces one
fixed packet list, with one coefficient-sum formula per erased Hall word.

This file states the exact order-aware comparison between those two lists.
Such a stabilization certificate immediately proves the canonical packet law
at every natural source multiplicity.  The remaining signed extension is
isolated as the existing `AILift` interface, and is equivalent to the
canonical recipe-product law consumed by the polynomial correction factory.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  RPStab

universe u

open scoped commutatorElement

open
  CSAggreg
open
  CCPkt
open
  CCTrunc
open
  CFExp
open
  CFSubsti
open
  UNPkt
open
  UCAll
open
  CPSplit
open
  GRPolys
open
  ACAlign

/--
The order-aware natural stabilization obligation for the fixed canonical
root-weight packet.  No permutation or commutative regrouping is allowed: the
fixed packet product is compared directly with each truncated concrete
operational packet product.
-/
def SatisfiesNaturalStabilization
    (kernel : OCShape)
    (d n : ℕ) :
    Prop :=
  TNStab.{u}
    kernel d n 1 1
      (globalProfilePackets n 1 1)

/-- A canonical stabilization certificate is the natural signed-block packet
consumed by the existing signed-lift interface. -/
noncomputable def canonicalNaturalPacket
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n) :
    TBPkt.{u} d n :=
  stabilization.truncNaturalPacket

@[simp]
lemma packets_natural_packet
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n) :
    (canonicalNaturalPacket stabilization).packets =
      globalProfilePackets n 1 1 :=
  rfl

/--
Order-aware stabilization proves the fixed canonical packet law at all
natural source multiplicities.
-/
lemma
    recollection_packets_cast
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n)
    (M N : ℕ)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ((globalProfilePackets n 1 1).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      ⁅left ^ M, right ^ N⁆ := by
  exact
    stabilization.nat_cast_pow
      M N left right (by simp) (by simp)

/--
After symbolic parent substitution, canonical global factors satisfy the
powered-commutator identity whenever the evaluated parent coefficients are
natural casts.
-/
lemma
    global_nat_cast
    {kernel : OCShape}
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n)
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (M N : ℕ)
    (left right : SPFactor H ι)
    (hleftCoefficient :
      left.coefficient.eval e = (M : ℤ))
    (hrightCoefficient :
      right.coefficient.eval e = (N : ℤ)) :
    SPFactor.listEval (n := n) e
        (globalRecollectionFactors normalizer
          n 1 1 left right) =
      ⁅left.wordValue (n := n) ^ M, right.wordValue (n := n) ^ N⁆ := by
  unfold globalRecollectionFactors
  rw [listSymbolicFactors, hleftCoefficient, hrightCoefficient]
  exact
    recollection_packets_cast
      stabilization M N
        (left.wordValue (n := n))
        (right.wordValue (n := n))

/--
The remaining signed extension after order-aware stabilization.
-/
abbrev GlobalAllLift
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n) :
    Prop :=
  (canonicalNaturalPacket stabilization).AILift

/--
Conversely, the canonical recipe-product law automa stabilizes its
aggregated packet against every genuine truncated concrete packet.
-/
noncomputable def
    satisfies_natural_stabilization
    (kernel : OCShape)
    {d n : ℕ}
    (hlistEval : SatisfiesRecipeTruncated.{u} d n) :
    SatisfiesNaturalStabilization.{u} kernel d n := by
  simpa only [
    packets_truncated_packet] using
      ((canonicalRecipePacket hlistEval)
        |>.stabilizedBlockPacket kernel
        |>.truncatedNaturalStabilization)

/--
A signed lift of the stabilized canonical packet discharges the flattened
canonical recipe-product law.
-/
lemma satisfies_global_all
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n)
    (lift : GlobalAllLift stabilization) :
    SatisfiesRecipeTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  rw [←
    (canonicalChunkAlignment n 1 1).list_recipe_factors
      left right leftExponent rightExponent]
  exact lift.listEval_eq left right leftExponent rightExponent

/--
Conversely, the canonical recipe-product law supplies the signed lift of an
already stabilized canonical packet.
-/
def global_all_satisfies
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n)
    (hlistEval : SatisfiesRecipeTruncated.{u} d n) :
    GlobalAllLift stabilization where
  listEval_eq := by
    intro left right leftExponent rightExponent
    exact
      ((canonicalChunkAlignment n 1 1).list_recipe_factors
        left right leftExponent rightExponent).trans
          (hlistEval left right leftExponent rightExponent)

/--
After natural stabilization, the remaining signed lift is exactly the
canonical recipe-product theorem.
-/
theorem satisfies_global_lift
    {kernel : OCShape}
    {d n : ℕ}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n) :
    SatisfiesRecipeTruncated.{u} d n ↔
      GlobalAllLift stabilization :=
  ⟨global_all_satisfies
      stabilization,
    satisfies_global_all
      stabilization⟩

/--
The canonical recipe-product law is equivalent to the existence of an
order-aware canonical natural stabilization together with its signed lift.
-/
theorem
    satisfies_stabilization_lift
    (kernel : OCShape)
    {d n : ℕ} :
    SatisfiesRecipeTruncated.{u} d n ↔
      ∃ stabilization :
          SatisfiesNaturalStabilization.{u} kernel d n,
        GlobalAllLift stabilization := by
  constructor
  · intro hlistEval
    let stabilization :=
      satisfies_natural_stabilization
        kernel hlistEval
    exact
      ⟨stabilization,
        global_all_satisfies
          stabilization hlistEval⟩
  · rintro ⟨stabilization, lift⟩
    exact
      satisfies_global_all
        stabilization lift

/--
Natural stabilization plus its signed extension proves the powered
commutator law in the global canonical symbolic language.
-/
lemma
    global_all_lift
    {kernel : OCShape}
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (stabilization :
      SatisfiesNaturalStabilization.{u} kernel d n)
    (lift : GlobalAllLift stabilization)
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalRecollectionFactors normalizer
          n 1 1 left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  global_recollection_commutator
    normalizer e
      (satisfies_global_all
        stabilization lift)
      left right

end
  RPStab
end TCTex
end Submission

/-!
# Principal splits from explicit recipe-coefficient transversals

The explicit recipe-coefficient transversal removes conservative closure
multiplicities from the remaining semantic problem.  This file states that
problem as one cutoff-specific ordered recipe-product identity and compiles
any proof of it into the closure-supported signed packet and polynomial
principal split consumed by residual routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace EPSplit

universe u

open scoped commutatorElement

open BRSpec
open
  UCAll
open
  UCFtry
open
  ACAlign
open
  CETransv
open
  RASem
open
  FCAssign
open SPAssign
open TAPkta
open TSPkt

/--
The remaining cutoff-specific collection law after selecting one recursive
recipe-coefficient witness for each retained erased Hall word.
-/
def SatisfiesExplicitRecipe
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((explicitCoefficientRecipes n 1 1 (by simp) (by simp)).map
        fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The explicit recipe-product law is equivalent to the ordered signed-profile
product law for the recursively selected assignment.
-/
lemma satisfies_explicit_assignment
    {d n : ℕ} :
    SatisfiesExplicitRecipe.{u} d n ↔
      ∀ (left right :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftExponent rightExponent : ℤ),
          (((((positiveProfileAssignment
            n 1 1 (by simp) (by simp))
            |>.toSPAssign.toPackets).map fun packet =>
              packet.word.eval (HPAtom.eval left right) ^
                packet.profiles.value leftExponent rightExponent).prod) =
            ⁅left ^ leftExponent, right ^ rightExponent⁆) := by
  constructor
  · intro hlistEval left right leftExponent rightExponent
    rw [
      assignment_explicit_recipes
        (n := n) (by simp) (by simp)
        left right leftExponent rightExponent]
    exact hlistEval left right leftExponent rightExponent
  · intro hlistEval left right leftExponent rightExponent
    rw [←
      assignment_explicit_recipes
        (n := n) (by simp) (by simp)
        left right leftExponent rightExponent]
    exact hlistEval left right leftExponent rightExponent

/-- The explicit recipe-product law is a cutoff-specific all-integral packet. -/
noncomputable def explicitAllPacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesExplicitRecipe d n) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes :=
    explicitCoefficientRecipes n 1 1 (by simp) (by simp)
  listEval_eq :=
    hlistEval

/--
The explicit singleton chunk alignment compiles the recipe-product law to the
ordered root-weight signed packet required by correction stabilization.
-/
noncomputable def
    explicitRecipePacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesExplicitRecipe d n) :
    TAPkta.{u} d n 1 1 :=
  allChunkAlignment
      ((positiveProfileAssignment
        n 1 1 (by simp) (by simp)).toSPAssign)
      (explicitAllPacket hlistEval)
      (by simp)
      (by simp)
      (coefficientChunkAlignment
        n 1 1 (by simp) (by simp))

/--
At root-weight parents and cutoff above two, an explicit transversal
collection law supplies one physical weight-two principal factor and strict
weight-three-or-higher tails.
-/
noncomputable def explicitHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesExplicitRecipe d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      explicitRecipePacket
        hlistEval
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryChunkAlignment
        ((positiveProfileAssignment
          n 1 1 (by simp) (by simp)).toSPAssign)
        (explicitAllPacket hlistEval)
        (coefficientChunkAlignment
          n 1 1 (by simp) (by simp))
        normalizers left right hn hleftSupported hrightSupported hleft hright

/--
The physical principal split assembled from the explicit transversal law
evaluates to the root commutator correction.
-/
lemma explicit_higher_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesExplicitRecipe d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      explicitHigherSplit
        hlistEval normalizers left right hn hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (explicitHigherSplit
      hlistEval normalizers left right hn hleftSupported hrightSupported
        hleft hright).list_split_commutator e

end EPSplit
end TCTex
end Submission

/-!
# Recursive decomposition of the explicit recipe transversal

The explicit recipe-coefficient transversal contains one selected recipe for
each erased Hall word in the deduplicated finite correction-closure skeleton.
This file transfers the skeleton recursion to that exact selected list.

Every selected recipe is either source-shaped or has selected parent recipes
of strictly smaller weighted Hall degree.  The resulting well-founded
induction principle is the recursion interface needed by an explicit symbolic
collector.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  ECTransv

open HACoeff
open BRSpec
open
  CETransv
open
  CRDecomp
open
  UCSuppor
open URVocabu

/--
The explicit witness selected for one skeleton word occurs in the complete
explicit transversal.
-/
lemma explicit_coefficient_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight }) :
    explicitRecipeWord hleftWeight hrightWeight word ∈
      explicitCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight := by
  unfold explicitCoefficientRecipes
  exact List.mem_map.mpr ⟨word, List.mem_attach _ _, rfl⟩

/--
Every skeleton word has a selected explicit-transversal recipe with exactly
that erased shape.
-/
lemma explicit_recipes_shape
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {word : CWord HPAtom}
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    ∃ recipe ∈
        explicitCoefficientRecipes
          n leftWeight rightWeight hleftWeight hrightWeight,
      recipe.erasedShape = word := by
  let word' :
      { word //
        word ∈ erasedShapeVocabulary n leftWeight rightWeight } :=
    ⟨word, hword⟩
  exact
    ⟨explicitRecipeWord hleftWeight hrightWeight word',
      explicit_coefficient_recipes
        hleftWeight hrightWeight word',
      erased_shape_explicit hleftWeight hrightWeight word'⟩

/--
Every explicit selected recipe is either source-shaped or a commutator of two
selected explicit recipes of strictly smaller weighted Hall degree.
-/
lemma
    selected_parent_explicit
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈
        explicitCoefficientRecipes
          n leftWeight rightWeight hleftWeight hrightWeight) :
    (∃ sourceRecipe ∈ sourceRecipes n leftWeight rightWeight,
      sourceRecipe.erasedShape = recipe.erasedShape) ∨
      ∃ leftRecipe ∈
          explicitCoefficientRecipes
            n leftWeight rightWeight hleftWeight hrightWeight,
        ∃ rightRecipe ∈
            explicitCoefficientRecipes
              n leftWeight rightWeight hleftWeight hrightWeight,
          recipe.erasedShape =
              .commutator leftRecipe.erasedShape rightRecipe.erasedShape ∧
            weightedWordWeight leftWeight rightWeight leftRecipe <
                weightedWordWeight leftWeight rightWeight recipe ∧
              weightedWordWeight leftWeight rightWeight rightRecipe <
                weightedWordWeight leftWeight rightWeight recipe := by
  have hshape :
      recipe.erasedShape ∈
        erasedShapeVocabulary n leftWeight rightWeight := by
    rw [←
      erased_explicit_recipes
        n leftWeight rightWeight hleftWeight hrightWeight]
    exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩
  rcases
      parent_words_vocabulary
        hleftWeight hrightWeight hshape with
    hsource |
      ⟨leftWord, hleftWord, rightWord, hrightWord, hword, hleftLt,
        hrightLt⟩
  · exact Or.inl hsource
  · rcases
        explicit_recipes_shape
          hleftWeight hrightWeight hleftWord with
      ⟨leftRecipe, hleftRecipe, hleftShape⟩
    rcases
        explicit_recipes_shape
          hleftWeight hrightWeight hrightWord with
      ⟨rightRecipe, hrightRecipe, hrightShape⟩
    refine
      Or.inr
        ⟨leftRecipe, hleftRecipe, rightRecipe, hrightRecipe, ?_, ?_, ?_⟩
    · simpa only [hleftShape, hrightShape] using hword
    · simpa only [weightedWordWeight, hleftShape] using hleftLt
    · simpa only [weightedWordWeight, hrightShape] using hrightLt

/--
Well-founded induction over the exact selected transversal.  The correction
case receives selected parents already known to satisfy the motive.
-/
theorem explicit_recipes_induction
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {motive : BRecipe → Prop}
    (source :
      ∀ recipe ∈
          explicitCoefficientRecipes
            n leftWeight rightWeight hleftWeight hrightWeight,
        (∃ sourceRecipe ∈ sourceRecipes n leftWeight rightWeight,
          sourceRecipe.erasedShape = recipe.erasedShape) →
          motive recipe)
    (correction :
      ∀ recipe leftRecipe rightRecipe,
        recipe ∈
            explicitCoefficientRecipes
              n leftWeight rightWeight hleftWeight hrightWeight →
          leftRecipe ∈
              explicitCoefficientRecipes
                n leftWeight rightWeight hleftWeight hrightWeight →
            rightRecipe ∈
                explicitCoefficientRecipes
                  n leftWeight rightWeight hleftWeight hrightWeight →
              recipe.erasedShape =
                  .commutator
                    leftRecipe.erasedShape rightRecipe.erasedShape →
                motive leftRecipe →
                  motive rightRecipe →
                    motive recipe) :
    ∀ recipe ∈
        explicitCoefficientRecipes
          n leftWeight rightWeight hleftWeight hrightWeight,
      motive recipe := by
  intro recipe hrecipe
  refine
    (InvImage.wf
      (fun nextRecipe : BRecipe =>
        weightedWordWeight leftWeight rightWeight nextRecipe)
      Nat.lt_wfRel.wf).induction
        (C := fun nextRecipe =>
          nextRecipe ∈
              explicitCoefficientRecipes
                n leftWeight rightWeight hleftWeight hrightWeight →
            motive nextRecipe)
        recipe ?_ hrecipe
  intro nextRecipe ih hnextRecipe
  rcases
      selected_parent_explicit
        hleftWeight hrightWeight hnextRecipe with
    hsource |
      ⟨leftRecipe, hleftRecipe, rightRecipe, hrightRecipe, hshape, hleftLt,
        hrightLt⟩
  · exact source nextRecipe hnextRecipe hsource
  · exact correction nextRecipe leftRecipe rightRecipe
      hnextRecipe hleftRecipe hrightRecipe hshape
      (ih leftRecipe hleftLt hleftRecipe)
      (ih rightRecipe hrightLt hrightRecipe)

end
  ECTransv
end TCTex
end Submission

/-!
# Global symbolic recollection polynomials from the explicit transversal

The finite correction closure supplies a deduplicated erased-word skeleton.
The explicit recipe-coefficient transversal chooses one coefficient formula
for each skeleton word, in skeleton order.  Substituting two arbitrary
symbolic Hall parents therefore gives one multiplicity-independent ordered
list of global symbolic recollection factors.

This file packages that list directly and proves its basic endpoint facts:

* its length is the size of the finite erased-word skeleton;
* its words are exactly the skeleton words after Hall-pair substitution;
* every emitted word lies below cutoff at parents of the declared weights;
* its ordered evaluation is the explicit selected recipe-polynomial product;
* at root weights, the remaining transversal semantic law turns that product
  into the powered commutator.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CRPolyno

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open PFSubsti
open
  EPSplit
open
  CETransv
open
  UCSuppor

/--
The fixed explicit recipe transversal, renamed at the global symbolic
recollection boundary.
-/
noncomputable def globalRecollectionRecipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  explicitCoefficientRecipes
    n leftWeight rightWeight hleftWeight hrightWeight

/--
Substitute two arbitrary symbolic Hall parents into the fixed explicit
recollection transversal.
-/
noncomputable def globalSymbolicFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    List (SPFactor H ι) :=
  symbolicFactors normalizer
    (globalRecollectionRecipes
      n leftWeight rightWeight hleftWeight hrightWeight)
    left right

/-- The global recipe transversal has one entry for each erased Hall word. -/
lemma length_recollection_recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (globalRecollectionRecipes
      n leftWeight rightWeight hleftWeight hrightWeight).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  unfold globalRecollectionRecipes
  exact
    length_explicit_recipes
      n leftWeight rightWeight hleftWeight hrightWeight

/-- The global symbolic factor list has the fixed skeleton cardinality. -/
lemma length_symbolic_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    (globalSymbolicFactors normalizer
      n leftWeight rightWeight hleftWeight hrightWeight left right).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  unfold globalSymbolicFactors
  unfold PFSubsti.symbolicFactors
  rw [List.length_map,
    length_recollection_recipes]

/--
The words of the global symbolic factors are exactly the deduplicated
skeleton words after substituting the two symbolic Hall parents.
-/
lemma global_symbolic_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    (globalSymbolicFactors normalizer
      n leftWeight rightWeight hleftWeight hrightWeight left right).map
        SPFactor.word =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
  unfold globalSymbolicFactors
  unfold globalRecollectionRecipes
  unfold PFSubsti.symbolicFactors
  rw [List.map_map]
  calc
    _ =
      (explicitCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight).map
          (fun recipe =>
            CWord.hallPairBind
              left.word right.word recipe.erasedShape) := by
      apply List.map_congr_left
      intro recipe _hrecipe
      rfl
    _ =
      ((explicitCoefficientRecipes
        n leftWeight rightWeight hleftWeight hrightWeight).map
          BRecipe.erasedShape).map
            (fun word =>
              CWord.hallPairBind left.word right.word word) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro recipe _hrecipe
      rfl
    _ =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
      rw [
        erased_explicit_recipes
          n leftWeight rightWeight hleftWeight hrightWeight]

/--
Every global symbolic recollection factor lies physically below cutoff when
its two symbolic parents have the declared weights.
-/
lemma symbolic_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈
        globalSymbolicFactors normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) :
    factor.word.weight HEAddres.weight < n := by
  unfold globalSymbolicFactors at hfactor
  unfold globalRecollectionRecipes at hfactor
  rcases recipe_factors hfactor with
    ⟨recipe, hrecipe, rfl⟩
  rw [PFSubsti.word_symbolic_factor,
    hleft, hright, ← weighted_word_weight]
  exact
    weighted_explicit_recipes
      hleftWeight hrightWeight hrecipe

/-- Physical truncation removes no global symbolic recollection factor. -/
@[simp]
lemma truncate_global_recollection
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.truncate n
        (globalSymbolicFactors normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) =
      globalSymbolicFactors normalizer
        n leftWeight rightWeight hleftWeight hrightWeight left right := by
  apply List.filter_eq_self.2
  intro factor hfactor
  simpa only [decide_eq_true_eq] using
    symbolic_recollection_factors
      normalizer hleftWeight hrightWeight left right factor
        hleft hright hfactor

/--
Ordered evaluation of the global symbolic list is exactly evaluation of the
fixed selected recipe-polynomial transversal.
-/
lemma recollection_explicit_recipes
    {d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := truncation) e
        (globalSymbolicFactors normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) =
      ((globalRecollectionRecipes
        n leftWeight rightWeight hleftWeight hrightWeight).map fun recipe =>
          recipe.erasedShape.eval
              (HPAtom.eval
                (left.wordValue (n := truncation))
                (right.wordValue (n := truncation))) ^
            coefficientValue recipe
              (left.coefficient.eval e) (right.coefficient.eval e)).prod := by
  unfold globalSymbolicFactors
  exact listSymbolicFactors normalizer e _ left right

/--
At root weights, the remaining explicit-transversal semantic law turns the
fixed symbolic recollection-polynomial list into the powered commutator.
-/
lemma global_symbolic_recollection
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hlistEval :
      SatisfiesExplicitRecipe.{u} d n)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalSymbolicFactors normalizer
          n 1 1 (by simp) (by simp) left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ := by
  rw [
    recollection_explicit_recipes]
  unfold globalRecollectionRecipes
  exact
    hlistEval
      (left.wordValue (n := n))
      (right.wordValue (n := n))
      (left.coefficient.eval e)
      (right.coefficient.eval e)

end
  CRPolyno
end TCTex
end Submission

/-!
# Explicit recipe-coefficient transversals at the first cutoffs

At cutoff at most two the explicit recipe transversal is empty.  Above weight
two and through cutoff three it is a singleton.  Its unique recipe has
bidegree `(1, 1)`, so its generalized-binomial coefficient is the ordinary
product of the two source exponents.  This proves the first nontrivial
instances of the explicit transversal collection law.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ECLow

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  EPSplit
open
  UCAll
open
  CPSplit
open
  CLPacket
open
  CETransv
open
  UCSuppor

/--
A generalized-binomial product indexed by degrees of total degree one is the
original exponent.
-/
lemma prod_choose_self
    (degrees : List ℕ)
    (hdegrees : degrees.sum = 1)
    (exponent : ℤ) :
    (degrees.map fun degree => Ring.choose exponent degree).prod =
      exponent := by
  induction degrees with
  | nil =>
      simp at hdegrees
  | cons degree degrees ih =>
      have hdegreeLe : degree ≤ 1 := by
        simp only [List.sum_cons] at hdegrees
        omega
      interval_cases degree
      · simp only [List.sum_cons, zero_add] at hdegrees
        simp [ih hdegrees]
      · have hdegreesZero :
            degrees.sum = 0 := by
          simp only [List.sum_cons] at hdegrees
          omega
        have hprod :
            ∀ nextDegrees : List ℕ,
              nextDegrees.sum = 0 →
                (nextDegrees.map fun nextDegree =>
                  Ring.choose exponent nextDegree).prod = 1 := by
          intro nextDegrees hnextDegrees
          induction nextDegrees with
          | nil =>
              rfl
          | cons nextDegree nextDegrees ih =>
              simp only [List.sum_cons] at hnextDegrees
              have hnextDegreeZero :
                  nextDegree = 0 := by
                omega
              have htailZero :
                  nextDegrees.sum = 0 := by
                omega
              subst nextDegree
              simp [ih htailZero]
        simp only [List.map_cons, List.prod_cons, Ring.choose_one_right,
          hprod degrees hdegreesZero, mul_one]

/--
Every block recipe of principal bidegree `(1, 1)` has the basic coefficient
value, independently of its internal labels.
-/
lemma coefficient_value_bidegree
    (recipe : BRecipe)
    (hleftDegree : recipe.leftDegree = 1)
    (hrightDegree : recipe.rightDegree = 1)
    (leftExponent rightExponent : ℤ) :
    coefficientValue recipe leftExponent rightExponent =
      leftExponent * rightExponent := by
  unfold coefficientValue
  rw [
    prod_choose_self
      recipe.leftBlocks (by simpa [BRecipe.leftDegree] using hleftDegree),
    prod_choose_self
      recipe.rightBlocks
        (by simpa [BRecipe.rightDegree] using hrightDegree)]

/-- Below the first bracket weight, the explicit transversal is empty. -/
lemma explicit_recipes_nil
    {n : ℕ}
    (hn : n ≤ 2) :
    explicitCoefficientRecipes n 1 1 (by simp) (by simp) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro recipe hrecipe
  have hlt :
      weightedWordWeight 1 1 recipe < n :=
    weighted_explicit_recipes
      (by simp) (by simp) hrecipe
  have hbasic :
      weightedWordWeight 1 1 hallPair ≤
        weightedWordWeight 1 1 recipe :=
    weighted_weight_basic 1 1 recipe
  simp only [weighted_word_pair] at hbasic
  omega

/--
Through cutoff three and above the basic bracket weight, the explicit
transversal consists of one recipe with basic erased shape and coefficient.
-/
lemma explicit_recipes_singleton
    {n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    ∃ recipe : BRecipe,
      explicitCoefficientRecipes n 1 1 (by simp) (by simp) =
          [recipe] ∧
        recipe.erasedShape = CWord.hallPairBase ∧
          ∀ leftExponent rightExponent : ℤ,
            coefficientValue recipe leftExponent rightExponent =
              leftExponent * rightExponent := by
  have hlength :
      (explicitCoefficientRecipes n 1 1
        (by simp) (by simp)).length = 1 := by
    calc
      (explicitCoefficientRecipes n 1 1
          (by simp) (by simp)).length =
          (erasedShapeVocabulary n 1 1).length :=
        length_explicit_recipes n 1 1 (by simp) (by simp)
      _ = 1 := by
        rw [
          erased_vocabulary_singleton
            hlow hhigh]
        rfl
  rcases List.length_eq_one_iff.mp hlength with
    ⟨recipe, hrecipes⟩
  have hshape :
      recipe.erasedShape = CWord.hallPairBase := by
    have hmap :=
      erased_explicit_recipes
        n 1 1 (by simp) (by simp)
    rw [hrecipes,
      erased_vocabulary_singleton
        hlow hhigh] at hmap
    simpa using hmap
  have hleftDegree :
      recipe.leftDegree = 1 := by
    rw [← recipe.erased_left_degree, hshape]
    rfl
  have hrightDegree :
      recipe.rightDegree = 1 := by
    rw [← recipe.erased_shape_degree, hshape]
    rfl
  exact
    ⟨recipe, hrecipes, hshape,
      coefficient_value_bidegree
        recipe hleftDegree hrightDegree⟩

/-- The explicit transversal collection law holds below the first bracket. -/
lemma satisfies_explicit_two
    {d n : ℕ}
    (hn : n ≤ 2) :
    SatisfiesExplicitRecipe.{u} d n := by
  intro left right leftExponent rightExponent
  rw [explicit_recipes_nil hn]
  exact
    (empty_n_two (d := d) hn).listEval_eq
      left right leftExponent rightExponent

/-- The explicit transversal collection law holds in nilpotency class two. -/
lemma
    satisfies_explicit_n
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3) :
    SatisfiesExplicitRecipe.{u} d n := by
  intro left right leftExponent rightExponent
  rcases
      explicit_recipes_singleton
        hlow hhigh with
    ⟨recipe, hrecipes, hshape, hcoefficient⟩
  rw [hrecipes]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, hshape, hcoefficient, CWord.eval_pair_base]
  have hcommutes :=
    PFSubsti.TAPkt.commute_n_three
      hhigh left right
  have hpullLeft :
      ⁅left ^ leftExponent, right⁆ =
        ⁅left, right⁆ ^ leftExponent :=
    commutator_zpow_commute
      hcommutes.1 leftExponent
  have hcommuteRight :
      Commute right ⁅left ^ leftExponent, right⁆ := by
    rw [hpullLeft]
    exact hcommutes.2.zpow_right leftExponent
  rw [zpow_commute_collection
    hcommuteRight, hpullLeft, zpow_mul]

/-- Uniform explicit-transversal collection law through cutoff three. -/
lemma satisfies_explicit_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    SatisfiesExplicitRecipe.{u} d n := by
  by_cases hlow : n ≤ 2
  · exact
      satisfies_explicit_two hlow
  · exact
      satisfies_explicit_n
        (by omega) hn

/-- Uniform ordered explicit-transversal packet through cutoff three. -/
noncomputable def
    explicit_n_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    TAPkta.{u} d n 1 1 :=
  explicitRecipePacket
    (satisfies_explicit_three hn)

end ECLow
end TCTex
end Submission

/-!
# Global signed-profile symbolic recollection polynomials

The explicit recipe transversal is a convenient evaluator for the fixed
global recollection packet.  The collector itself consumes the equivalent
signed-profile presentation: one homogeneous signed-profile formula attached
to each erased Hall word in the finite correction-closure skeleton.

This file packages that signed-profile list after arbitrary symbolic parent
substitution and proves that its ordered evaluation is exactly the evaluation
of the explicit recipe-polynomial transversal.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  FRPolys

universe u

open scoped commutatorElement

open
  EPSplit
open
  CFExp
open
  CFSubsti
open
  CRPolyno
open
  CETransv
open
  RASem
open
  FCAssign
open
  UCSuppor

/-- Fixed signed-profile packets attached to the deduplicated erased-word
skeleton. -/
noncomputable def signedRecollectionPackets
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List RFPkt :=
  (positiveProfileAssignment
    n leftWeight rightWeight hleftWeight hrightWeight)
      |>.toSPAssign.toPackets

/-- Substitute two arbitrary symbolic Hall parents into the fixed
signed-profile packet list. -/
noncomputable def globalProfileRecollection
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    List (SPFactor H ι) :=
  CFExp.symbolicFactors
    normalizer
    (signedRecollectionPackets
      n leftWeight rightWeight hleftWeight hrightWeight)
    left right

/-- The fixed signed-profile packet list has one packet for every skeleton
word. -/
lemma length_profile_packets
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (signedRecollectionPackets
      n leftWeight rightWeight hleftWeight hrightWeight).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  unfold signedRecollectionPackets
  rw [← List.length_map]
  exact congrArg List.length
    ((positiveProfileAssignment
      n leftWeight rightWeight hleftWeight hrightWeight)
        |>.toSPAssign.word_packets)

/-- The substituted signed-profile factor list has fixed skeleton
cardinality. -/
lemma length_global_recollection
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    (globalProfileRecollection normalizer
      n leftWeight rightWeight hleftWeight hrightWeight left right).length =
      (erasedShapeVocabulary n leftWeight rightWeight).length := by
  unfold globalProfileRecollection
  unfold
    CFExp.symbolicFactors
  rw [List.length_map,
    length_profile_packets]

/-- The words of the signed-profile factors are the same substituted
deduplicated skeleton words as in the explicit recipe presentation. -/
lemma word_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    (globalProfileRecollection normalizer
      n leftWeight rightWeight hleftWeight hrightWeight left right).map
        SPFactor.word =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
  unfold globalProfileRecollection
  unfold
    CFExp.symbolicFactors
  rw [List.map_map]
  calc
    _ =
      (signedRecollectionPackets
        n leftWeight rightWeight hleftWeight hrightWeight).map
          (fun packet =>
            CWord.hallPairBind
              left.word right.word packet.word) := by
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      ((signedRecollectionPackets
        n leftWeight rightWeight hleftWeight hrightWeight).map
          RFPkt.word).map
            (fun word =>
              CWord.hallPairBind left.word right.word word) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      (erasedShapeVocabulary n leftWeight rightWeight).map fun word =>
        CWord.hallPairBind left.word right.word word := by
      unfold signedRecollectionPackets
      rw [
        SPAssign.word_packets]

/-- Every substituted signed-profile factor lies below cutoff at symbolic
parents of the declared weights. -/
lemma global_profile_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right factor : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight)
    (hfactor :
      factor ∈
        globalProfileRecollection normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) :
    factor.word.weight HEAddres.weight < n := by
  unfold globalProfileRecollection at hfactor
  rcases
      CFExp.packet_symbolic_factors
        hfactor with
    ⟨packet, hpacket, rfl⟩
  have hword :
      packet.word ∈ erasedShapeVocabulary n leftWeight rightWeight := by
    unfold signedRecollectionPackets at hpacket
    exact
      SPAssign.word_vocabulary_packets
        _ hpacket
  rw [packet.word_symbolicFactor, packet.weight_boundWord, hleft, hright]
  simpa [HPAtom.weight] using
    erased_shape_vocabulary hword

/-- Physical truncation removes no fixed signed-profile recollection
factor. -/
@[simp]
lemma truncate_profile_self
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι)
    (hleft :
      left.word.weight HEAddres.weight = leftWeight)
    (hright :
      right.word.weight HEAddres.weight = rightWeight) :
    SPFactor.truncate n
        (globalProfileRecollection normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) =
      globalProfileRecollection normalizer
        n leftWeight rightWeight hleftWeight hrightWeight left right := by
  apply List.filter_eq_self.2
  intro factor hfactor
  simpa only [decide_eq_true_eq] using
    global_profile_factors
      normalizer hleftWeight hrightWeight left right factor
        hleft hright hfactor

/--
After arbitrary symbolic substitution, the signed-profile presentation and
the explicit-recipe presentation have exactly the same ordered evaluation.
-/
lemma global_recollection_symbolic
    {d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := truncation) e
        (globalProfileRecollection normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) =
      SPFactor.listEval (n := truncation) e
        (globalSymbolicFactors normalizer
          n leftWeight rightWeight hleftWeight hrightWeight left right) := by
  unfold globalProfileRecollection
  rw [
    CFExp.listSymbolicFactors,
    recollection_explicit_recipes]
  unfold signedRecollectionPackets
  unfold globalRecollectionRecipes
  exact
    assignment_explicit_recipes
      hleftWeight hrightWeight
      (left.wordValue (n := truncation))
      (right.wordValue (n := truncation))
      (left.coefficient.eval e)
      (right.coefficient.eval e)

/--
At root weights, the remaining explicit-transversal law gives the powered
commutator equation directly in the fixed signed-profile polynomial language.
-/
lemma recollection_factors_commutator
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hlistEval :
      SatisfiesExplicitRecipe.{u} d n)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalProfileRecollection normalizer
          n 1 1 (by simp) (by simp) left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ := by
  rw [
    global_recollection_symbolic]
  exact
    global_symbolic_recollection
      normalizer e hlistEval left right

end
  FRPolys
end TCTex
end Submission

/-!
# Retained-recipe profile assignments for the finite correction closure

The generic recursive recipe-coefficient assignment remembers only that its
chosen coefficient has some shape-equivalent recipe witness.  For class-three
reasoning it is useful to preserve more provenance: the witness should belong
to the retained finite correction closure itself.

This file chooses one retained recipe for every skeleton word, attaches its
singleton homogeneous signed profile, and packages the resulting assignment
with an explicit retained-recipe motive.  The construction works at arbitrary
cutoff.  At cutoff at most four, the class-three source separation theorem
then identifies the selected triple coefficients.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CTAssigna

open HACoeff
open BRSpec
open ECLow
open
  CFSubsti
open
  CTPacket
open
  SWSep
open
  ACAlign
open
  UCAdapt
open
  RASem
open
  FCAssign
open
  UCSuppor
open UCVocabu

/--
One homogeneous signed profile has retained-recipe provenance when it is the
coefficient formula of a shape-equivalent recipe in the finite closure.
-/
def RecipeCoefficientProfile
    (n : ℕ)
    (word : CWord HPAtom)
    (profiles :
      HFPkt
        word.pairLeftDegree word.pairRightDegree) :
    Prop :=
  ∃ recipe ∈ correctionClosureRecipes n 1 1,
    recipe.erasedShape = word ∧
      ∀ leftExponent rightExponent : ℤ,
        profiles.value leftExponent rightExponent =
          coefficientValue recipe leftExponent rightExponent

/-- Choose one retained closure recipe representing a finite-skeleton word. -/
noncomputable def retainedRecipeWord
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    BRecipe :=
  Classical.choose (recipe_erased_vocabulary word.2)

/-- The chosen recipe remains in the retained finite correction closure. -/
lemma retained_recipe_word
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    retainedRecipeWord word ∈ correctionClosureRecipes n 1 1 :=
  (Classical.choose_spec
    (recipe_erased_vocabulary word.2)).1

/-- The chosen retained recipe erases to its requested skeleton word. -/
lemma erased_shape_recipe
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    (retainedRecipeWord word).erasedShape = word.1 :=
  (Classical.choose_spec
    (recipe_erased_vocabulary word.2)).2

/-- Attach the singleton homogeneous profile of the chosen retained recipe. -/
noncomputable def retainedRecipeProfiles
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    HFPkt
      word.1.pairLeftDegree word.1.pairRightDegree :=
  HFPkt.ofRecipeChunk word.1
    [retainedRecipeWord word] (by
      intro recipe hrecipe
      simp only [List.mem_singleton] at hrecipe
      subst recipe
      exact erased_shape_recipe word)

/-- The transported singleton profile has the chosen recipe's coefficient. -/
lemma value_recipe_profiles
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (leftExponent rightExponent : ℤ) :
    (retainedRecipeProfiles word).value leftExponent rightExponent =
      coefficientValue (retainedRecipeWord word)
        leftExponent rightExponent := by
  simp [retainedRecipeProfiles]

/--
Choose one retained-recipe coefficient profile for every finite-skeleton
word, preserving the retained provenance as a word-local motive.
-/
noncomputable def blockProfileAssignment
    (n : ℕ) :
    PAMotive
      n 1 1 (RecipeCoefficientProfile n) where
  toSPAssign :=
    { profiles := fun word hword =>
        retainedRecipeProfiles ⟨word, hword⟩ }
  profiles_motive := by
    intro word hword
    exact
      ⟨retainedRecipeWord ⟨word, hword⟩,
        retained_recipe_word ⟨word, hword⟩,
        erased_shape_recipe ⟨word, hword⟩,
        value_recipe_profiles ⟨word, hword⟩⟩

/-- Selected retained recipes, one for each skeleton word in skeleton order. -/
noncomputable def recipeCoefficientRecipes
    (n : ℕ) :
    List BRecipe :=
  (erasedShapeVocabulary n 1 1).attach.map retainedRecipeWord

/-- Erasing the retained recipe transversal recovers the finite skeleton. -/
lemma erased_coefficient_recipes
    (n : ℕ) :
    (recipeCoefficientRecipes n).map BRecipe.erasedShape =
      erasedShapeVocabulary n 1 1 := by
  unfold recipeCoefficientRecipes
  rw [List.map_map]
  calc
    (erasedShapeVocabulary n 1 1).attach.map
          (BRecipe.erasedShape ∘ retainedRecipeWord) =
        (erasedShapeVocabulary n 1 1).attach.map Subtype.val := by
      apply List.map_congr_left
      intro word _hword
      exact erased_shape_recipe word
    _ = erasedShapeVocabulary n 1 1 :=
      List.attach_map_subtype_val _

/-- Every selected transversal recipe remains in the retained closure. -/
lemma closure_recipes_coefficient
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ recipeCoefficientRecipes n) :
    recipe ∈ correctionClosureRecipes n 1 1 := by
  rcases List.mem_map.mp hrecipe with ⟨word, _hword, rfl⟩
  exact retained_recipe_word word

/--
At cutoff at most four, the retained profile chosen for the raw left triple
word has coefficient `choose a 2 * b`.
-/
lemma value_profiles_triple
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (hword : word.1 = inverseLeftTriple)
    (leftExponent rightExponent : ℤ) :
    (retainedRecipeProfiles word).value leftExponent rightExponent =
      Ring.choose leftExponent 2 * rightExponent := by
  rw [value_recipe_profiles]
  apply coefficient_choose_bidegree
    (retained_recipe_word word)
  · rw [← (retainedRecipeWord word).erased_left_degree,
      erased_shape_recipe word, hword]
    simp [inverseLeftTriple, rootSwapWord, CWord.hallPairBase]
  · rw [← (retainedRecipeWord word).erased_shape_degree,
      erased_shape_recipe word, hword]
    simp [inverseLeftTriple, rootSwapWord, CWord.hallPairBase]

/--
The retained profile chosen for the basic Hall-pair word has coefficient
`a * b`.
-/
lemma value_profiles_base
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (hword : word.1 = CWord.hallPairBase)
    (leftExponent rightExponent : ℤ) :
    (retainedRecipeProfiles word).value leftExponent rightExponent =
      leftExponent * rightExponent := by
  rw [value_recipe_profiles]
  apply coefficient_value_bidegree
  · rw [← (retainedRecipeWord word).erased_left_degree,
      erased_shape_recipe word, hword]
    rfl
  · rw [← (retainedRecipeWord word).erased_shape_degree,
      erased_shape_recipe word, hword]
    rfl

/--
At cutoff at most four, the retained profile chosen for the raw right triple
word has coefficient `a * choose b 2`.
-/
lemma profiles_choose_triple
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (hword : word.1 = inverseTripleWord)
    (leftExponent rightExponent : ℤ) :
    (retainedRecipeProfiles word).value leftExponent rightExponent =
      leftExponent * Ring.choose rightExponent 2 := by
  rw [value_recipe_profiles]
  apply value_choose_bidegree
    (retained_recipe_word word)
  · rw [← (retainedRecipeWord word).erased_left_degree,
      erased_shape_recipe word, hword]
    simp [inverseTripleWord, rootSwapWord, CWord.hallPairBase]
  · rw [← (retainedRecipeWord word).erased_shape_degree,
      erased_shape_recipe word, hword]
    simp [inverseTripleWord, rootSwapWord, CWord.hallPairBase]

/--
Through cutoff four, every retained selected profile is one of the three
standard class-three coefficient formulas.
-/
theorem profiles_cases_four
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (leftExponent rightExponent : ℤ) :
    (word.1 = inverseLeftTriple ∧
        (retainedRecipeProfiles word).value
            leftExponent rightExponent =
          Ring.choose leftExponent 2 * rightExponent) ∨
      (word.1 = CWord.hallPairBase ∧
          (retainedRecipeProfiles word).value
              leftExponent rightExponent =
            leftExponent * rightExponent) ∨
        (word.1 = inverseTripleWord ∧
          (retainedRecipeProfiles word).value
              leftExponent rightExponent =
            leftExponent * Ring.choose rightExponent 2) := by
  rcases
      or_vocabulary_four
        hn word.2 with
    hword | hword | hword
  · exact
      Or.inl
        ⟨hword,
          value_profiles_triple
            word hword leftExponent rightExponent⟩
  · exact
      Or.inr
        (Or.inl
          ⟨hword,
            value_profiles_base
              word hword leftExponent rightExponent⟩)
  · exact
      Or.inr
        (Or.inr
          ⟨hword,
            profiles_choose_triple
              word hword leftExponent rightExponent⟩)

end
  CTAssigna
end TCTex
end Submission

/-!
# Global symbolic recollection polynomials at the first cutoffs

The explicit recipe-coefficient transversal satisfies its collection law
through cutoff three.  This discharges the remaining semantic hypothesis for
both fixed global presentations in that range.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  URPolys

universe u

open scoped commutatorElement

open
  ECLow
open
  FRPolys
open
  CRPolyno

/--
Through cutoff three, the fixed explicit-recipe polynomial list evaluates to
the powered commutator.
-/
lemma recollection_n_three
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hn : n ≤ 3)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalSymbolicFactors normalizer
          n 1 1 (by simp) (by simp) left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  global_symbolic_recollection
    normalizer e
      (satisfies_explicit_three hn)
      left right

/--
Through cutoff three, the fixed signed-profile polynomial list evaluates to
the powered commutator.
-/
lemma
    global_recollection_n
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hn : n ≤ 3)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalProfileRecollection normalizer
          n 1 1 (by simp) (by simp) left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  recollection_factors_commutator
    normalizer e
      (satisfies_explicit_three hn)
      left right

end
  URPolys
end TCTex
end Submission

/-!
# Canonical finite-closure inventory overcounts the first operational packet

The finite correction closure is a conservative support inventory.  Its
canonical regrouping preserves occurrence multiplicity, so it is not itself
the operational Hall-Petresco packet.

Already at cutoff three, the universal raw source vocabulary contains at
least two retained principal occurrences.  Both survive the finite closure
filter and canonical regrouping.  The genuine class-two collection packet is
the singleton basic packet, so the flattened canonical closure inventory
cannot be used as that packet.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CCOverco

open HACoeff
open BRSpec
open
  ECLow
open
  CFSubsti
open
  CPSplit
open
  CTAssigna
open
  ACAlign
open
  UCSuppor
open UCVocabu
open URVocabu

/-- The depth-zero source list remains a sublist of every finite closure layer. -/
lemma source_sublist_closure
    (source : List BRecipe)
    (depth : ℕ) :
    source.Sublist (correctionClosure source depth) := by
  induction depth with
  | zero =>
      exact List.Sublist.refl source
  | succ depth ih =>
      exact ih.trans (List.sublist_append_left _ _)

/--
Every universal source occurrence survives the below-cutoff finite closure
filter.  This is an occurrence-level statement, not merely a membership
statement.
-/
lemma recipes_sublist_closure
    (n leftWeight rightWeight : ℕ) :
    (sourceRecipes n leftWeight rightWeight).Sublist
      (correctionClosureRecipes n leftWeight rightWeight) := by
  unfold correctionClosureRecipes
  have hfilter :
      (sourceRecipes n leftWeight rightWeight).filter
          (fun recipe =>
            decide (weightedWordWeight leftWeight rightWeight recipe < n)) =
        sourceRecipes n leftWeight rightWeight :=
    List.filter_eq_self.2 (fun recipe hrecipe =>
      decide_eq_true
        (weighted_cutoff_recipes hrecipe))
  have hsublist :=
    (source_sublist_closure
      (sourceRecipes n leftWeight rightWeight) n).filter
        (fun recipe =>
          decide (weightedWordWeight leftWeight rightWeight recipe < n))
  simpa only [hfilter] using hsublist

/--
At cutoff three, canonical regrouping still contains at least two principal
recipe occurrences.
-/
lemma bidegree_recipes_three :
    2 ≤
      (canonicalRecipes 3 1 1).countP
        (fun recipe => recipe.leftDegree == 1 && recipe.rightDegree == 1) := by
  have hsource :
      2 ≤
        (correctionClosureRecipes 3 1 1).countP
          (fun recipe => recipe.leftDegree == 1 &&
            recipe.rightDegree == 1) :=
    (count_bidegree_recipes.trans
      (recipes_sublist_closure 3 1 1).countP_le)
  rw [
    (recipes_perm_closure
      3 1 1).countP_eq
        (fun recipe => recipe.leftDegree == 1 &&
          recipe.rightDegree == 1)]
  exact hsource

/-- The flattened canonical cutoff-three inventory has at least two recipes. -/
lemma two_length_recipes :
    2 ≤ (canonicalRecipes 3 1 1).length :=
  bidegree_recipes_three.trans
    List.countP_le_length

/--
The flattened canonical cutoff-three inventory is not the singleton basic
recipe packet used by the genuine class-two Hall-Petresco collection law.
-/
lemma recipes_singleton_pair :
    canonicalRecipes 3 1 1 ≠ [hallPair] := by
  intro hrecipes
  have hlength := two_length_recipes
  rw [hrecipes] at hlength
  simp at hlength

/--
The unique canonical basic-word chunk at cutoff three contains at least two
recipe occurrences.
-/
lemma length_recipes_base :
    2 ≤
      (recipesForWord 3 1 1 CWord.hallPairBase).length := by
  rw [←
    recipes_chunk_n
      (n := 3) (by omega) (by omega)]
  exact two_length_recipes

/-- Sum a list of integer-valued terms that are all equal to one. -/
private lemma length_forall_one
    {α : Type*}
    (values : List α)
    (f : α → ℤ)
    (hvalue : ∀ value ∈ values, f value = 1) :
    (values.map f).sum = values.length := by
  induction values with
  | nil =>
      rfl
  | cons value values ih =>
      simp only [List.mem_cons] at hvalue
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        hvalue value (Or.inl rfl), ih (fun next hnext =>
          hvalue next (Or.inr hnext))]
      omega

/--
Every recipe in the cutoff-three canonical basic-word chunk contributes one
at source exponents `(1, 1)`, so its aggregate coefficient is the chunk
length.
-/
lemma recipes_pair_base :
    ((recipesForWord 3 1 1 CWord.hallPairBase).map fun recipe =>
      coefficientValue recipe 1 1).sum =
        (recipesForWord 3 1 1 CWord.hallPairBase).length := by
  apply length_forall_one
  intro recipe hrecipe
  simpa using
    coefficient_value_bidegree recipe
      (by
        rw [← recipe.erased_left_degree,
          erased_shape_recipes hrecipe]
        rfl)
      (by
        rw [← recipe.erased_shape_degree,
          erased_shape_recipes hrecipe]
        rfl)
      1 1

/--
Consequently, the summed canonical basic-word profile has value at least two
at `(1, 1)`.
-/
lemma assignment_pair_base
    (hword :
      CWord.hallPairBase ∈ erasedShapeVocabulary 3 1 1) :
    (2 : ℤ) ≤
      ((canonicalProfileAssignment 3 1 1).profiles
        CWord.hallPairBase hword).value 1 1 := by
  change
    (2 : ℤ) ≤
      (HFPkt.ofRecipeChunk
        CWord.hallPairBase
        (recipesForWord 3 1 1 CWord.hallPairBase)
        (fun _recipe hrecipe =>
          erased_shape_recipes hrecipe)).value 1 1
  rw [HFPkt.value_recipe_chunk,
    recipes_pair_base]
  exact_mod_cast
    length_recipes_base

/--
The selected retained transversal has the correct singleton basic
coefficient at cutoff three.
-/
lemma value_profile_assignment
    (hword :
      CWord.hallPairBase ∈ erasedShapeVocabulary 3 1 1) :
    ((blockProfileAssignment 3)
        |>.toSPAssign.profiles
          CWord.hallPairBase hword).value 1 1 =
      1 := by
  change
    (retainedRecipeProfiles
      ⟨CWord.hallPairBase, hword⟩).value 1 1 =
      1
  simpa using
    value_profiles_base
      ⟨CWord.hallPairBase, hword⟩ rfl 1 1

/--
At cutoff three, summing the conservative closure chunk is observably
different from choosing the operational retained transversal.
-/
lemma assignment_base_ne
    (hword :
      CWord.hallPairBase ∈ erasedShapeVocabulary 3 1 1) :
    (canonicalProfileAssignment 3 1 1).profiles
          CWord.hallPairBase hword ≠
      ((blockProfileAssignment 3)
          |>.toSPAssign.profiles
            CWord.hallPairBase hword) := by
  intro hprofiles
  have hvalue :=
    congrArg (fun profiles => profiles.value 1 1) hprofiles
  dsimp only at hvalue
  rw [
    value_profile_assignment
      hword] at hvalue
  have hcanonical :=
    assignment_pair_base
      hword
  omega

end
  CCOverco
end TCTex
end Submission

/-!
# Class-three collection for the retained-recipe profile assignment

The retained-recipe assignment enumerates the deduplicated finite skeleton in
its inherited closure order.  At cutoff four this order need not be the
conventional Hall-Petresco order.  The two triple factors are central,
however, so any permutation of the three surviving skeleton words has the
same product.

This file proves the resulting class-three list-evaluation law and packages
the retained selector as an all-integral ordered cutoff packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  FTCollec

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  UCAll
open
  CTPacket
open
  CTAssigna
open
  SWSep
open
  CPSplit
open CLPacket
open
  FCAssign
open
  UCSuppor

/--
Through cutoff four and above weight three, the finite skeleton is a
permutation of the conventional three-word class-three support list.
-/
lemma erased_perm_words
    {n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    List.Perm (erasedShapeVocabulary n 1 1)
      [inverseLeftTriple, CWord.hallPairBase,
        inverseTripleWord] := by
  apply
    (List.perm_ext_iff_of_nodup
      (List.nodup_dedup _)
      (by
        simp [inverseLeftTriple, inverseTripleWord, rootSwapWord,
          CWord.hallPairBase])).2
  intro word
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using
    (erased_vocabulary_four
      (word := word) hlow hhigh)

/-- Below the first bracket weight, the finite skeleton is empty. -/
lemma vocabulary_nil_n
    {n : ℕ}
    (hn : n ≤ 2) :
    erasedShapeVocabulary n 1 1 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro word hword
  have hlt :
      word.weight (HPAtom.weight 1 1) < n :=
    erased_shape_vocabulary hword
  rw [CWord.pair_atom_degree] at hlt
  simp only [Nat.mul_one] at hlt
  have hpositive :
      word.PBPos :=
    bidegree_positive_vocabulary hword
  have hleftPositive :
      0 < word.pairLeftDegree :=
    hpositive.1
  have hrightPositive :
      0 < word.pairRightDegree :=
    hpositive.2
  omega

/-- Pure factor attached to one possible class-three skeleton word. -/
def classThreeFactor
    {d n : ℕ}
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ)
    (word : CWord HPAtom) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  if word = inverseLeftTriple then
    inverseLeftTriple.eval (HPAtom.eval left right) ^
      (Ring.choose leftExponent 2 * rightExponent)
  else if word = CWord.hallPairBase then
    ⁅left, right⁆ ^ (leftExponent * rightExponent)
  else
    inverseTripleWord.eval (HPAtom.eval left right) ^
      (leftExponent * Ring.choose rightExponent 2)

@[simp]
lemma inverse_triple_word
    {d n : ℕ}
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    classThreeFactor left right leftExponent rightExponent
        inverseLeftTriple =
      inverseLeftTriple.eval (HPAtom.eval left right) ^
        (Ring.choose leftExponent 2 * rightExponent) := by
  simp [classThreeFactor]

@[simp]
lemma class_pair_base
    {d n : ℕ}
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    classThreeFactor left right leftExponent rightExponent
        CWord.hallPairBase =
      ⁅left, right⁆ ^ (leftExponent * rightExponent) := by
  simp [classThreeFactor, inverseLeftTriple, rootSwapWord,
    CWord.hallPairBase]

@[simp]
lemma class_triple_word
    {d n : ℕ}
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    classThreeFactor left right leftExponent rightExponent
        inverseTripleWord =
      inverseTripleWord.eval (HPAtom.eval left right) ^
        (leftExponent * Ring.choose rightExponent 2) := by
  simp [classThreeFactor, inverseLeftTriple, inverseTripleWord,
    rootSwapWord, CWord.hallPairBase]

/-- The raw left triple evaluation is central through cutoff four. -/
lemma commute_triple_n
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    Commute x
      (inverseLeftTriple.eval (HPAtom.eval left right)) := by
  rw [left_triple_word hn]
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hinner :
      ⁅left, right⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using element_lower_series hleft hright
  have hnested :
      ⁅left, ⁅left, right⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hleft hinner
  exact
    HCThree.commute_series_four
      hn x hnested

/-- The raw right triple evaluation is central through cutoff four. -/
lemma commute_triple_four
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    Commute x
      (inverseTripleWord.eval (HPAtom.eval left right)) := by
  rw [eval_triple_word hn]
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hinner :
      ⁅left, right⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using element_lower_series hleft hright
  have hnested :
      ⁅right, ⁅left, right⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using element_lower_series hright hinner
  exact
    HCThree.commute_series_four
      hn x hnested

/-- The conventional three class-three factors commute pairwise. -/
lemma pairwise_commute_factor
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ([inverseLeftTriple, CWord.hallPairBase,
      inverseTripleWord].map
        (classThreeFactor left right leftExponent rightExponent)).Pairwise
          Commute := by
  simp only [List.map_cons, List.map_nil,
    inverse_triple_word, class_pair_base,
    class_triple_word]
  apply List.pairwise_cons.2
  constructor
  · intro next hnext
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnext
    rcases hnext with rfl | rfl
    · exact
        ((commute_triple_n
          hn left right ⁅left, right⁆).symm.zpow_zpow
            (Ring.choose leftExponent 2 * rightExponent)
            (leftExponent * rightExponent))
    · exact
        ((commute_triple_n
          hn left right
            (inverseTripleWord.eval (HPAtom.eval left right))).symm
          |>.zpow_zpow
            (Ring.choose leftExponent 2 * rightExponent)
            (leftExponent * Ring.choose rightExponent 2))
  · constructor
    · intro next hnext
      simp only [List.mem_singleton] at hnext
      subst next
      exact
          (commute_triple_four
            hn left right ⁅left, right⁆).zpow_zpow
              (leftExponent * rightExponent)
              (leftExponent * Ring.choose rightExponent 2)
    · exact List.pairwise_singleton Commute _

/--
The retained selected factor attached to one skeleton word is its pure
class-three factor.
-/
lemma zpow_profiles_factor
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    word.1.eval (HPAtom.eval left right) ^
          (retainedRecipeProfiles word).value
            leftExponent rightExponent =
      classThreeFactor left right leftExponent rightExponent word.1 := by
  rcases
      profiles_cases_four
        hn word leftExponent rightExponent with
    ⟨hword, hvalue⟩ | ⟨hword, hvalue⟩ | ⟨hword, hvalue⟩
  · rw [hvalue]
    rw [hword, inverse_triple_word]
  · rw [hvalue]
    rw [hword, class_pair_base,
      CWord.eval_pair_base]
  · rw [hvalue]
    rw [hword, class_triple_word]

/-- The retained-selector packet product is the product of pure factors. -/
lemma list_recipe_factor
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ((erasedShapeVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod := by
  unfold SPAssign.toPackets
  rw [List.map_map]
  simp only [blockProfileAssignment]
  change
    (((erasedShapeVocabulary n 1 1).attach.map fun word =>
      word.1.eval (HPAtom.eval left right) ^
        (retainedRecipeProfiles word).value
          leftExponent rightExponent).prod) =
      ((erasedShapeVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod
  rw [List.map_congr_left (fun word _hword =>
    zpow_profiles_factor
      hn left right leftExponent rightExponent word)]
  simpa only [List.map_map, Function.comp_apply] using
    congrArg
      (fun words => (words.map
        (classThreeFactor left right leftExponent rightExponent)).prod)
      (List.attach_map_subtype_val (erasedShapeVocabulary n 1 1))

/-- Below the first bracket weight, the retained assignment is empty. -/
lemma assignment_n_two
    {d n : ℕ}
    (hn : n ≤ 2)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  rw [
    list_recipe_factor
      (by omega) left right leftExponent rightExponent,
    vocabulary_nil_n hn]
  simpa only [List.map_nil, List.prod_nil] using
    (empty_n_two (d := d) hn).listEval_eq
      left right leftExponent rightExponent

/-- In class two, the retained assignment is the singleton basic factor. -/
lemma
    assignment_n_three
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 3)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  rw [
    list_recipe_factor
      (by omega) left right leftExponent rightExponent,
    erased_vocabulary_singleton
      hlow hhigh]
  simpa only [List.map_singleton, List.prod_singleton,
    class_pair_base, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, erased_shape_pair, coefficient_value_pair,
    CWord.eval_pair_base,
    PFSubsti.TAPkt.n_three] using
    (PFSubsti.TAPkt.n_three
      (d := d) hhigh).listEval_eq
        left right leftExponent rightExponent

/-- The conventional three-factor product is the powered commutator. -/
lemma prod_element_zpow
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ([inverseLeftTriple, CWord.hallPairBase,
      inverseTripleWord].map
        (classThreeFactor left right leftExponent rightExponent)).prod =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, inverse_triple_word,
    class_pair_base, class_triple_word]
  rw [left_triple_word hn, eval_triple_word hn]
  simpa only [mul_assoc] using
    (HCThree.element_zpow_class
      hn left right leftExponent rightExponent).symm

/--
Above weight three and through cutoff four, the retained-recipe assignment
satisfies the complete ordered list-evaluation law.
-/
lemma assignment_n_four
    {d n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  rw [
    list_recipe_factor
      hhigh left right leftExponent rightExponent]
  calc
    ((erasedShapeVocabulary n 1 1).map
        (classThreeFactor left right leftExponent rightExponent)).prod =
        ([inverseLeftTriple, CWord.hallPairBase,
          inverseTripleWord].map
            (classThreeFactor left right leftExponent rightExponent)).prod := by
      exact
        (((erased_perm_words hlow hhigh).symm.map
          (classThreeFactor left right leftExponent rightExponent)).prod_eq'
            (pairwise_commute_factor
              hhigh left right leftExponent rightExponent)).symm
    _ = ⁅left ^ leftExponent, right ^ rightExponent⁆ :=
      prod_element_zpow
        hhigh left right leftExponent rightExponent

/-- Through cutoff four, the retained assignment satisfies collection. -/
lemma list_recipe_four
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) =
      ⁅left ^ leftExponent, right ^ rightExponent⁆ := by
  by_cases htwo : n ≤ 2
  · exact
      assignment_n_two htwo
        left right leftExponent rightExponent
  by_cases hthree : n ≤ 3
  · exact
      assignment_n_three
        (by omega) hthree left right leftExponent rightExponent
  · exact
      assignment_n_four
        (by omega) hn left right leftExponent rightExponent

/--
At cutoff four, the provenance-preserving retained selector compiles to an
all-integral ordered cutoff packet.
-/
noncomputable def
    retained_n_four
    {d n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    TAPkta.{u} d n 1 1 where
  toOBPkt :=
    (blockProfileAssignment n)
      |>.toSPAssign
      |>.orderedBlockPacket (by simp) (by simp)
  listEval_eq :=
    assignment_n_four
      hlow hhigh

/--
Through cutoff four, the provenance-preserving retained selector compiles to
an all-integral ordered cutoff packet.
-/
noncomputable def packet_n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    TAPkta.{u} d n 1 1 where
  toOBPkt :=
    (blockProfileAssignment n)
      |>.toSPAssign
      |>.orderedBlockPacket (by simp) (by simp)
  listEval_eq :=
    list_recipe_four hn

end
  FTCollec
end TCTex
end Submission

/-!
# Recursive decomposition of the retained recipe-coefficient transversal

The retained recipe-coefficient transversal selects one actual finite-closure
recipe for each erased Hall word in the root-weight skeleton.  Unlike the
general shape-equivalent transversal, every selected recipe preserves
finite-closure provenance.

This file transfers closure decomposition to that exact selected list and
packages the resulting well-founded induction principle.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  RCTransv

open HACoeff
open BRSpec
open
  CTAssigna
open
  CRDecomp
open
  UCSuppor
open UCVocabu
open URVocabu

/--
The retained recipe selected for one skeleton word occurs in the complete
retained transversal.
-/
lemma retained_coefficient_recipes
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    retainedRecipeWord word ∈ recipeCoefficientRecipes n := by
  unfold recipeCoefficientRecipes
  exact List.mem_map.mpr ⟨word, List.mem_attach _ _, rfl⟩

/--
Every retained closure recipe has a selected retained-transversal
representative with the same erased Hall word.
-/
lemma recipes_erased_shape
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ correctionClosureRecipes n 1 1) :
    ∃ selectedRecipe ∈ recipeCoefficientRecipes n,
      selectedRecipe.erasedShape = recipe.erasedShape := by
  let word :
      { word // word ∈ erasedShapeVocabulary n 1 1 } :=
    ⟨recipe.erasedShape, shape_vocabulary_recipes hrecipe⟩
  exact
    ⟨retainedRecipeWord word,
      retained_coefficient_recipes word,
      erased_shape_recipe word⟩

/--
Every selected retained recipe is either a source recipe or is represented
by a commutator of two selected retained recipes of strictly smaller weighted
Hall degree.
-/
lemma
    source_recipes_coeff
    {n : ℕ}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ recipeCoefficientRecipes n) :
    recipe ∈ sourceRecipes n 1 1 ∨
      ∃ leftRecipe ∈ recipeCoefficientRecipes n,
        ∃ rightRecipe ∈ recipeCoefficientRecipes n,
          recipe.erasedShape =
              .commutator leftRecipe.erasedShape rightRecipe.erasedShape ∧
            weightedWordWeight 1 1 leftRecipe <
                weightedWordWeight 1 1 recipe ∧
              weightedWordWeight 1 1 rightRecipe <
                weightedWordWeight 1 1 recipe := by
  have hretained :
      recipe ∈ correctionClosureRecipes n 1 1 :=
    closure_recipes_coefficient
      hrecipe
  rcases
      recipes_or_parent
        (by simp) (by simp) hretained with
    hsource |
      ⟨left, hleft, right, hright, heq, hleftLt, hrightLt⟩
  · exact Or.inl hsource
  · rcases
        recipes_erased_shape
          hleft with
      ⟨leftRecipe, hleftRecipe, hleftShape⟩
    rcases
        recipes_erased_shape
          hright with
      ⟨rightRecipe, hrightRecipe, hrightShape⟩
    refine
      Or.inr
        ⟨leftRecipe, hleftRecipe, rightRecipe, hrightRecipe, ?_, ?_, ?_⟩
    · rw [heq, BRecipe.erasedShape_corr,
        hleftShape, hrightShape]
    · simpa only [weightedWordWeight, hleftShape] using hleftLt
    · simpa only [weightedWordWeight, hrightShape] using hrightLt

/--
Well-founded induction over the retained selected transversal.  The source
case keeps exact source membership, while the correction case receives
selected parents already known to satisfy the motive.
-/
theorem coefficient_recipes_induction
    {n : ℕ}
    {motive : BRecipe → Prop}
    (source :
      ∀ recipe ∈ recipeCoefficientRecipes n,
        recipe ∈ sourceRecipes n 1 1 →
          motive recipe)
    (correction :
      ∀ recipe leftRecipe rightRecipe,
        recipe ∈ recipeCoefficientRecipes n →
          leftRecipe ∈ recipeCoefficientRecipes n →
            rightRecipe ∈ recipeCoefficientRecipes n →
              recipe.erasedShape =
                  .commutator
                    leftRecipe.erasedShape rightRecipe.erasedShape →
                motive leftRecipe →
                  motive rightRecipe →
                    motive recipe) :
    ∀ recipe ∈ recipeCoefficientRecipes n,
      motive recipe := by
  intro recipe hrecipe
  refine
    (InvImage.wf
      (fun nextRecipe : BRecipe =>
        weightedWordWeight 1 1 nextRecipe)
      Nat.lt_wfRel.wf).induction
        (C := fun nextRecipe =>
          nextRecipe ∈ recipeCoefficientRecipes n →
            motive nextRecipe)
        recipe ?_ hrecipe
  intro nextRecipe ih hnextRecipe
  rcases
      source_recipes_coeff
        hnextRecipe with
    hsource |
      ⟨leftRecipe, hleftRecipe, rightRecipe, hrightRecipe, hshape, hleftLt,
        hrightLt⟩
  · exact source nextRecipe hnextRecipe hsource
  · exact correction nextRecipe leftRecipe rightRecipe
      hnextRecipe hleftRecipe hrightRecipe hshape
      (ih leftRecipe hleftLt hleftRecipe)
      (ih rightRecipe hrightLt hrightRecipe)

end
  RCTransv
end TCTex
end Submission

/-!
# Canonical finite-closure inventory is not the class-two semantic packet

The conservative finite correction closure retains at least two occurrences
of the basic Hall-pair recipe at cutoff three.  This file upgrades that
coefficient overcount to a semantic obstruction: the resulting canonical
recipe inventory cannot satisfy the required collection identity in the free
class-two truncation on two generators.

The proof evaluates at two distinct free generators and passes to the
weight-two associated-graded quotient.  The basic commutator class is a
concrete Hall-basis vector, whereas the canonical inventory scales that vector
by a coefficient at least two.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CSObstru

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  CCOverco
open
  CPSplit
open
  ACAlign

/--
The single natural `(1, 1)` instance of the canonical recipe-product law.

This deliberately weak boundary is enough to expose the cutoff-three
overcount: the conservative inventory already repeats the basic Hall-pair
contribution when collecting one copy of each source generator.
-/
def SatisfiesCanonicalRecipe
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n),
    ((canonicalRecipes n 1 1).map fun recipe =>
      recipe.erasedShape.eval (HPAtom.eval left right) ^
        coefficientValue recipe 1 1).prod =
      ⁅left, right⁆

/--
If two free generators are ordered so their bracket is a Hall basic tree, the
cutoff-three canonical recipe inventory cannot satisfy the collection law.
-/
private theorem false_satisfies_three
    (leftGenerator rightGenerator : FreeGenerator.{u} 2)
    (horder :
      HallTree.atom rightGenerator < HallTree.atom leftGenerator)
    (hlistEval : SatisfiesCanonicalRecipe.{u} 2 3) :
    False := by
  let left :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} 2)) 3 :=
    freeTruncationValue 2 3 leftGenerator
  let right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} 2)) 3 :=
    freeTruncationValue 2 3 rightGenerator
  let tree : HallTree (FreeGenerator.{u} 2) :=
    HallTree.commutator (HallTree.atom leftGenerator) (HallTree.atom rightGenerator)
  have htreeBasic : tree.IsBasic := by
    simp [tree, horder]
  have htreeWeight : tree.weight = 2 := by
    simp [tree]
  obtain ⟨i, hi⟩ :=
    concrete_commutator_word htreeBasic htreeWeight
  let H := concreteCommutatorsWeight.{u} 2 2
  let hall := H.commutator i
  let g :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} 2)) 3 :=
    hall.freeLowerTruncation
  have hg : g = ⁅left, right⁆ := by
    change hall.word.eval (freeTruncationValue 2 3) =
      ⁅freeTruncationValue 2 3 leftGenerator,
        freeTruncationValue 2 3 rightGenerator⁆
    rw [hi]
    rfl
  let recipes :=
    recipesForWord 3 1 1 CWord.hallPairBase
  have hcanonicalPow :
      ((canonicalRecipes 3 1 1).map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe 1 1).prod =
        g ^ (recipes.length : ℤ) := by
    rw [
      recipes_chunk_n
        (n := 3) (by omega) (by omega)]
    calc
      (recipes.map fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue recipe 1 1).prod =
          (recipes.map fun recipe =>
            g ^ coefficientValue recipe 1 1).prod := by
            apply congrArg List.prod
            apply List.map_congr_left
            intro recipe hrecipe
            rw [erased_shape_recipes hrecipe,
              CWord.eval_pair_base, hg]
      _ = g ^ (recipes.map fun recipe =>
            coefficientValue recipe 1 1).sum :=
        list_prod_zpow g
          (fun recipe => coefficientValue recipe 1 1) recipes
      _ = g ^ (recipes.length : ℤ) := by
        rw [
          recipes_pair_base]
  have hcanonicalEq :
      ((canonicalRecipes 3 1 1).map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe 1 1).prod =
        g := by
    simpa [hg] using hlistEval left right
  have hgpow : g ^ (recipes.length : ℤ) = g :=
    hcanonicalPow.symm.trans hcanonicalEq
  let N : Type u :=
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} 2)) 3
  let A : Subgroup N := Subgroup.lowerCentralSeries N 1
  let B : Subgroup A := (Subgroup.lowerCentralSeries N 2).subgroupOf A
  let q : A →* A ⧸ B := QuotientGroup.mk' B
  let gTerm : A := hall.evalin_freelower_centtrunterm
  have hgpowTerm : gTerm ^ (recipes.length : ℤ) = gTerm := by
    apply Subtype.ext
    exact hgpow
  have hclass :
      (recipes.length : ℤ) • hall.associatedGradedClass (n := 3) =
        hall.associatedGradedClass (n := 3) := by
    have hqpow :=
      congrArg (fun x : A => Additive.ofMul (q x)) hgpowTerm
    change
      (recipes.length : ℤ) • Additive.ofMul (q gTerm) =
        Additive.ofMul (q gTerm)
    rw [← ofMul_zpow, ← map_zpow]
    exact hqpow
  have hforms : H.FormsAssocGradedbasis (n := 3) :=
    concrete_forms_associated
      2 3 2 (by omega) (by omega)
  obtain ⟨basis, hbasis⟩ := hforms
  have hlengthEq : (recipes.length : ℤ) = 1 := by
    apply basis.linearIndependent.smul_left_injective i
    rw [hbasis i]
    change
      (recipes.length : ℤ) • hall.associatedGradedClass (n := 3) =
        (1 : ℤ) • hall.associatedGradedClass (n := 3)
    rw [one_smul]
    exact hclass
  have hlengthTwo : (2 : ℤ) ≤ recipes.length := by
    exact_mod_cast
      length_recipes_base
  omega

/--
The canonical finite-closure recipe inventory fails even the single natural
`(1, 1)` Hall-Petresco law already in `F₂ / γ₃(F₂)`.
-/
theorem not_satisfies_three :
    ¬ SatisfiesCanonicalRecipe.{u} 2 3 := by
  intro hlistEval
  let first : FreeGenerator.{u} 2 := ULift.up ⟨0, by omega⟩
  let second : FreeGenerator.{u} 2 := ULift.up ⟨1, by omega⟩
  have hne : HallTree.atom first ≠ HallTree.atom second := by
    intro h
    have : first = second := HallTree.atom.inj h
    exact Fin.zero_ne_one (congrArg (fun generator => generator.down) this)
  rcases lt_or_gt_of_ne hne with horder | horder
  · exact
      false_satisfies_three
        second first horder hlistEval
  · exact
      false_satisfies_three
        first second horder hlistEval

/--
The canonical finite-closure recipe inventory is not a semantic
Hall-Petresco packet already in `F₂ / γ₃(F₂)`.
-/
theorem not_satisfies_truncated :
    ¬ SatisfiesRecipeTruncated.{u} 2 3 := by
  intro hlistEval
  apply not_satisfies_three
  intro left right
  simpa using hlistEval left right 1 1

end
  CSObstru
end TCTex
end Submission

/-!
# Principal splits from retained class-three profiles

Above the first surviving bracket cutoff, the retained-profile selector has one
literal basic Hall-pair occurrence.  Its all-integral packet therefore supplies
the physically truncated principal-factor split used by polynomial residual
routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  FPSplit

universe u

open
  CTAssigna
open
  FTCollec
open
  CPWord
open
  UCFtry
open
  APWord
open TAPkta
open TSPkt

/--
Above cutoff two and through cutoff four, the retained-profile packet has one
literal basic Hall-pair occurrence.
-/
lemma
    n_unique_occurrence
    {d n : ℕ}
    (hlow : 2 < n)
    (hhigh : n ≤ 4) :
    OBPkt.UniqueBaseOccurrence
      ((packet_n_four (d := d) hhigh)
        |>.toOBPkt) := by
  exact
    SPAssign.unique_occurrence_packet
      ((blockProfileAssignment n)
        |>.toSPAssign)
      hlow

/--
Above cutoff two and through cutoff four, retained profiles route one root
correction to a principal weight-two factor and strict weight-three tails.
-/
noncomputable def
    factoryHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      packet_n_four (d := d) hhigh
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factory_split_unique
      (packet_n_four (d := d) hhigh)
      normalizers left right hleftSupported hrightSupported
      (n_unique_occurrence
        (d := d) hlow hhigh)
      hleft hright

end
  FPSplit
end TCTex
end Submission

/-!
# Retained-recipe class-three packets

The retained-profile selector was built from one retained recipe for each
finite-skeleton word.  Its class-three signed-profile product law therefore
transports back to the selected recipe list itself.  This exposes a
provenance-preserving recipe packet for the existing automatic collectors.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CCThree

universe u

open scoped commutatorElement

open BRSpec
open
  CTAssigna
open
  FTCollec
open
  FCAssign

/-- The selected retained recipe list satisfies the class-three collection law. -/
def SatisfiesRecipeCoefficient
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((recipeCoefficientRecipes n).map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
Evaluating the selected retained recipes agrees with evaluating their attached
singleton profile packets.
-/
lemma coefficient_recipes_assignment
    {d n : ℕ}
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ((recipeCoefficientRecipes n).map fun recipe =>
      recipe.erasedShape.eval (HPAtom.eval left right) ^
        coefficientValue recipe leftExponent rightExponent).prod =
      (((blockProfileAssignment n)
        |>.toSPAssign.toPackets.map fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod) := by
  classical
  unfold recipeCoefficientRecipes SPAssign.toPackets
  rw [List.map_map, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro word _hword
  simp only [Function.comp_apply,
    blockProfileAssignment]
  rw [erased_shape_recipe,
    value_recipe_profiles]

/-- Through cutoff four, the selected retained recipes satisfy collection. -/
lemma satisfies_coefficient_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    SatisfiesRecipeCoefficient.{u} d n := by
  intro left right leftExponent rightExponent
  rw [
    coefficient_recipes_assignment
      left right leftExponent rightExponent]
  exact
    list_recipe_four
      hn left right leftExponent rightExponent

/--
Through cutoff four, the selected retained recipes form an all-integral
Hall-Petresco recipe packet.
-/
noncomputable def all_n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes :=
    recipeCoefficientRecipes n
  listEval_eq :=
    satisfies_coefficient_four hn

end
  CCThree
end TCTex
end Submission

/-!
# Operational stabilization for truncated profile assignments

The arbitrary-cutoff symbolic collector should construct one fixed signed-profile
assignment on the finite correction-closure skeleton.  Its packets may contain
sums of several weighted signed profiles, so reducing them to one selected
recipe per erased word is not generally sound.

This file factors the cutoff-specific all-integral law of such an assignment
through the genuine operational endpoint.  The factorization is exact: the
assignment law is equivalent to order-aware natural stabilization against every
truncated concrete operational packet together with the signed lift of that
fixed packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  TAStab

universe u

open
  CSAggreg
open
  CCTrunc
open
  UNPkt
open
  UCAll
open
  FCAssign
open
  UTAssign
open SPAssign

/--
The order-aware natural operational stabilization obligation for one fixed
root-weight summed profile assignment.
-/
def AssignmentNaturalStabilization
    (kernel : OCShape)
    (d : ℕ)
    {n : ℕ}
    (assignment : SPAssign n 1 1) :
    Prop :=
  TNStab.{u}
    kernel d n 1 1 assignment.toPackets

/--
A stabilized profile assignment supplies the fixed natural packet consumed by
the signed-lift interface.
-/
noncomputable def profileAssignmentPacket
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment) :
    TBPkt.{u} d n :=
  stabilization.truncNaturalPacket

@[simp]
lemma packets_assignment_packet
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment) :
    (profileAssignmentPacket stabilization).packets =
      assignment.toPackets :=
  rfl

/-- The remaining signed extension after natural operational stabilization. -/
abbrev AssignmentAllLift
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment) :
    Prop :=
  (profileAssignmentPacket stabilization)
    |>.AILift

/--
The cutoff-specific all-integral assignment law automa stabilizes its
fixed packets against every truncated concrete operational packet.
-/
noncomputable def
    assignment_natural_stabilization
    (kernel : OCShape)
    {d n : ℕ}
    (assignment : SPAssign n 1 1)
    (hlistEval :
      SatisfiesTruncEval.{u} (d := d) assignment) :
    AssignmentNaturalStabilization.{u}
      kernel d assignment := by
  simpa only [
    packetsTruncAll
  ] using
    ((truncAllPacket
      assignment (d := d) (by simp) (by simp) hlistEval)
      |>.stabilizedBlockPacket kernel
      |>.truncatedNaturalStabilization)

/--
The cutoff-specific all-integral assignment law also supplies the signed lift
of any already stabilized copy of its fixed packet list.
-/
def assignment_all_satisfies
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment)
    (hlistEval :
      SatisfiesTruncEval.{u} (d := d) assignment) :
    AssignmentAllLift stabilization where
  listEval_eq := by
    intro left right leftExponent rightExponent
    simpa only [
      packets_assignment_packet] using
        hlistEval left right leftExponent rightExponent

/--
A signed lift of an operationally stabilized profile assignment recovers its
cutoff-specific all-integral assignment law.
-/
lemma satisfies_assignment_all
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment)
    (lift : AssignmentAllLift stabilization) :
    SatisfiesTruncEval.{u} (d := d) assignment := by
  intro left right leftExponent rightExponent
  simpa only [
    packets_assignment_packet] using
      lift.listEval_eq left right leftExponent rightExponent

/--
After natural operational stabilization, the remaining signed lift is exactly
the cutoff-specific all-integral law for the fixed summed profile assignment.
-/
theorem satisfies_assignment_lift
    {kernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment) :
    SatisfiesTruncEval.{u} (d := d) assignment ↔
      AssignmentAllLift stabilization :=
  ⟨assignment_all_satisfies stabilization,
    satisfies_assignment_all
      stabilization⟩

/--
The profile-assignment law is equivalent to the existence of an order-aware
natural operational stabilization together with its signed extension.
-/
theorem
    satisfies_assignment_stabilization
    (kernel : OCShape)
    {d n : ℕ}
    (assignment : SPAssign n 1 1) :
    SatisfiesTruncEval.{u} (d := d) assignment ↔
      ∃ stabilization :
          AssignmentNaturalStabilization.{u}
            kernel d assignment,
        AssignmentAllLift stabilization := by
  constructor
  · intro hlistEval
    let stabilization :=
      assignment_natural_stabilization
        kernel assignment hlistEval
    exact
      ⟨stabilization,
        assignment_all_satisfies
          stabilization hlistEval⟩
  · rintro ⟨stabilization, lift⟩
    exact
      satisfies_assignment_all
        stabilization lift

namespace TSInput

/--
An order-aware stabilized profile assignment and its signed lift supply the
Claim 5 coordinate polynomials without selecting one recipe per erased word.
-/
theorem
    assignmentStabilizationLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (assignment : SPAssign n 1 1)
    (stabilization :
      AssignmentNaturalStabilization.{u}
        kernel d assignment)
    (lift : AssignmentAllLift stabilization)
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
  input.coordinateProfileAssignment
    hn H hH (kernel := kernel) assignment
      (satisfies_assignment_all
        stabilization lift)
      hsourceSupported factorNormalization hinputWeight

end TSInput

end
  TAStab
end TCTex
end Submission

/-!
# Evaluated principal splits from retained class-three profiles

Through cutoff four, the retained-profile correction packet exposes one
physical weight-two principal Hall-pair factor surrounded by strict
weight-three tails.  This file records the evaluated commutator identity and
the factor-level routing facts consumed by recursive collection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace PSEvalua

universe u

open scoped commutatorElement

open
  FPSplit
open TSPkt

/--
The retained-profile physical principal split evaluates to the root
commutator correction.
-/
lemma
    principal_split_commutator
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      factoryHigherSplit
        normalizers left right hlow hhigh hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (factoryHigherSplit
      normalizers left right hlow hhigh hleftSupported hrightSupported
        hleft hright).list_split_commutator e

/--
The retained-profile principal factor is the literal Hall-pair bind of its
root-weight parents.
-/
lemma
    principal_tail_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let split :=
      factoryHigherSplit
        normalizers left right hlow hhigh hleftSupported hrightSupported
          hleft hright
    split.principalFactor.word =
      CWord.hallPairBind
        left.word right.word CWord.hallPairBase := by
  exact
    (factoryHigherSplit
      normalizers left right hlow hhigh hleftSupported hrightSupported
        hleft hright).principal_word_eq

/--
Every retained-profile prefix factor lies in the strict weight-three tail.
-/
lemma
    before_least_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let split :=
      factoryHigherSplit
        normalizers left right hlow hhigh hleftSupported hrightSupported
          hleft hright
    SPFactor.WordWeightLeast
      3 split.beforeFactors := by
  exact
    (factoryHigherSplit
      normalizers left right hlow hhigh hleftSupported hrightSupported
        hleft hright).before_weight_least

/--
Every retained-profile suffix factor lies in the strict weight-three tail.
-/
lemma
    after_least_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let split :=
      factoryHigherSplit
        normalizers left right hlow hhigh hleftSupported hrightSupported
          hleft hright
    SPFactor.WordWeightLeast
      3 split.afterFactors := by
  exact
    (factoryHigherSplit
      normalizers left right hlow hhigh hleftSupported hrightSupported
        hleft hright).after_weight_least

end PSEvalua
end TCTex
end Submission

/-!
# Recipe-chunk alignment for retained class-three recipes

The retained class-three recipe transversal contains one selected recipe for
each finite-skeleton word.  Its singleton chunks align with the retained
signed-profile assignment.  Consequently the retained recipe packet itself
compiles to the ordered cutoff packet and physical principal split consumed by
recursive polynomial collection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RCAligna

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open
  CFSubsti
open
  UCAll
open
  CTAssigna
open
  FTCollec
open
  CCThree
open
  UCFtry
open
  ACAlign
open
  FCAssign
open
  UCSuppor
open UCVocabu
open SPAssign
open TAPkta
open TSPkt

/-- Singleton chunks of selected retained recipes, in skeleton order. -/
noncomputable def recipeCoefficientChunks
    (n : ℕ) :
    List (List BRecipe) :=
  (erasedShapeVocabulary n 1 1).attach.map fun word =>
    [retainedRecipeWord word]

/-- Each selected retained recipe is aligned with its singleton profile. -/
noncomputable def retainedChunkAlignment
    {n : ℕ}
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    RFPkt.RCAlign
      {
        word := word.1
        positive :=
          bidegree_positive_vocabulary word.2
        profiles :=
          (blockProfileAssignment n)
            |>.toSPAssign.profiles word.1 word.2
      }
      [retainedRecipeWord word] where
  erased_shape_word := by
    intro recipe hrecipe
    simp only [List.mem_singleton] at hrecipe
    subst recipe
    exact erased_shape_recipe word
  profiles_value_sum := by
    intro leftExponent rightExponent
    simpa [blockProfileAssignment] using
      value_recipe_profiles
        word leftExponent rightExponent

/--
The retained signed-profile assignment is aligned with the selected
singleton recipe transversal.
-/
noncomputable def recipeCoefficientChunk
    (n : ℕ) :
    SPAssign.RCAlign
      ((blockProfileAssignment n)
        |>.toSPAssign)
      (recipeCoefficientRecipes n) where
  chunks :=
    recipeCoefficientChunks n
  packets_chunks := by
    unfold SPAssign.toPackets
    unfold recipeCoefficientChunks
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro word _hword
    exact retainedChunkAlignment word
  flatten_chunks := by
    unfold recipeCoefficientChunks
    unfold recipeCoefficientRecipes
    induction (erasedShapeVocabulary n 1 1).attach with
    | nil =>
        rfl
    | cons word words ih =>
        simp [ih]

/--
Through cutoff four, singleton chunk alignment compiles the retained recipe
packet to its ordered signed-profile packet.
-/
noncomputable def aligned_n_four
    {d n : ℕ}
    (hn4 : n ≤ 4) :
    TAPkta.{u} d n 1 1 :=
  allChunkAlignment
    ((blockProfileAssignment n)
      |>.toSPAssign)
    (all_n_four hn4)
    (by simp)
    (by simp)
    (recipeCoefficientChunk n)

/--
The aligned recipe packet and the direct retained-profile packet expose the
same ordered signed factors.
-/
@[simp]
lemma packets_aligned_four
    {d n : ℕ}
    (hn4 : n ≤ 4) :
    (aligned_n_four
      (d := d) hn4).packets =
        (packet_n_four
          (d := d) hn4).packets :=
  rfl

/--
Above cutoff two and through cutoff four, the aligned retained recipe packet
routes one principal weight-two Hall-pair factor and strict weight-three
tails.
-/
noncomputable def alignedHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let assignment :=
      (blockProfileAssignment n)
        |>.toSPAssign
    let recipePacket :=
      all_n_four
        (d := d) hhigh
    let packet :=
      allChunkAlignment
        assignment recipePacket (by simp) (by simp)
          (recipeCoefficientChunk n)
    let correctionPacket :=
      (supportedPacketFactory packet
        normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryChunkAlignment
      ((blockProfileAssignment n)
        |>.toSPAssign)
      (all_n_four
        (d := d) hhigh)
      (recipeCoefficientChunk n)
      normalizers left right hlow hleftSupported hrightSupported
        hleft hright

/--
The aligned retained recipe principal split evaluates to the root commutator
correction.
-/
lemma aligned_higher_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hlow : 2 < n)
    (hhigh : n ≤ 4)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      alignedHigherSplit
        normalizers left right hlow hhigh hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (alignedHigherSplit
      normalizers left right hlow hhigh hleftSupported hrightSupported
        hleft hright).list_split_commutator e

end RCAligna
end TCTex
end Submission

/-!
# Global retained signed-profile recollection polynomials in class three

The general recursive positive selector intentionally remembers only a
shape-equivalent recipe witness.  At root weights and through cutoff four, the
retained-provenance selector supplies a stronger fixed symbolic endpoint: one
signed-profile polynomial factor for each word in the finite skeleton, with
an unconditional powered-commutator evaluation law.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  RPThree

universe u

open scoped commutatorElement

open
  CFExp
open
  CFSubsti
open
  CTAssigna
open
  FTCollec
open
  CCThree
open
  FCAssign
open
  UCSuppor

/-- Fixed retained-provenance packets attached to the root-weight skeleton. -/
noncomputable def globalSignedPackets
    (n : ℕ) :
    List RFPkt :=
  (blockProfileAssignment n)
    |>.toSPAssign.toPackets

/-- Substitute arbitrary symbolic Hall parents into the fixed retained packet
list. -/
noncomputable def globalProfileFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n : ℕ)
    (left right : SPFactor H ι) :
    List (SPFactor H ι) :=
  symbolicFactors normalizer
    (globalSignedPackets n) left right

/-- Forgetting profiles recovers the deduplicated root-weight skeleton. -/
@[simp]
lemma profile_recollection_packets
    (n : ℕ) :
    (globalSignedPackets n).map
        RFPkt.word =
      erasedShapeVocabulary n 1 1 := by
  unfold globalSignedPackets
  exact SPAssign.word_packets _

/-- There is exactly one retained-provenance packet per skeleton word. -/
lemma length_global_packets
    (n : ℕ) :
    (globalSignedPackets n).length =
      (erasedShapeVocabulary n 1 1).length := by
  rw [← List.length_map,
    profile_recollection_packets]

/-- The substituted retained factor list still has fixed skeleton
cardinality. -/
lemma length_global_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n : ℕ)
    (left right : SPFactor H ι) :
    (globalProfileFactors normalizer
      n left right).length =
      (erasedShapeVocabulary n 1 1).length := by
  unfold globalProfileFactors
  unfold symbolicFactors
  rw [List.length_map,
    length_global_packets]

/-- Substituted retained-factor words are the root skeleton after Hall-pair
substitution. -/
lemma signed_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (n : ℕ)
    (left right : SPFactor H ι) :
    (globalProfileFactors normalizer
      n left right).map SPFactor.word =
      (erasedShapeVocabulary n 1 1).map fun word =>
        CWord.hallPairBind left.word right.word word := by
  unfold globalProfileFactors
  unfold symbolicFactors
  rw [List.map_map]
  calc
    _ =
      (globalSignedPackets n).map
        (fun packet =>
          CWord.hallPairBind left.word right.word packet.word) := by
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      ((globalSignedPackets n).map
        RFPkt.word).map
          (fun word =>
            CWord.hallPairBind left.word right.word word) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro packet _hpacket
      rfl
    _ =
      (erasedShapeVocabulary n 1 1).map fun word =>
        CWord.hallPairBind left.word right.word word := by
      rw [profile_recollection_packets]

/-- Every substituted retained factor lies below cutoff at root-weight
parents. -/
lemma profile_recollection_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n : ℕ}
    (left right factor : SPFactor H ι)
    (hleft : left.word.weight HEAddres.weight = 1)
    (hright : right.word.weight HEAddres.weight = 1)
    (hfactor :
      factor ∈
        globalProfileFactors normalizer
          n left right) :
    factor.word.weight HEAddres.weight < n := by
  unfold globalProfileFactors at hfactor
  rcases packet_symbolic_factors hfactor with
    ⟨packet, hpacket, rfl⟩
  have hword :
      packet.word ∈ erasedShapeVocabulary n 1 1 := by
    unfold globalSignedPackets at hpacket
    exact
      SPAssign.word_vocabulary_packets
        _ hpacket
  rw [packet.word_symbolicFactor, packet.weight_boundWord, hleft, hright]
  simpa [HPAtom.weight] using
    erased_shape_vocabulary hword

/-- Physical truncation removes no retained root-weight factor. -/
@[simp]
lemma truncate_recollection_self
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {n : ℕ}
    (left right : SPFactor H ι)
    (hleft : left.word.weight HEAddres.weight = 1)
    (hright : right.word.weight HEAddres.weight = 1) :
    SPFactor.truncate n
        (globalProfileFactors normalizer
          n left right) =
      globalProfileFactors normalizer
        n left right := by
  apply List.filter_eq_self.2
  intro factor hfactor
  simpa only [decide_eq_true_eq] using
    profile_recollection_factors
      normalizer left right factor hleft hright hfactor

/--
After arbitrary symbolic substitution, the fixed retained-profile list
evaluates exactly as its selected retained recipe transversal.
-/
lemma
    profile_recollection_recipes
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalProfileFactors normalizer
          n left right) =
      ((recipeCoefficientRecipes n).map fun recipe =>
          recipe.erasedShape.eval
            (HPAtom.eval
              (left.wordValue (n := n))
              (right.wordValue (n := n))) ^
          BRSpec.coefficientValue recipe
            (left.coefficient.eval e) (right.coefficient.eval e)).prod := by
  unfold globalProfileFactors
  unfold globalSignedPackets
  rw [listSymbolicFactors]
  exact
    (coefficient_recipes_assignment
      (left.wordValue (n := n))
      (right.wordValue (n := n))
      (left.coefficient.eval e)
      (right.coefficient.eval e)).symm

/--
The retained-transversal semantic law gives the powered commutator directly
in the fixed retained-profile symbolic language.
-/
lemma profile_recollection_commutator
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hlistEval : SatisfiesRecipeCoefficient.{u} d n)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalProfileFactors normalizer
          n left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ := by
  rw [
    profile_recollection_recipes]
  exact
    hlistEval
      (left.wordValue (n := n))
      (right.wordValue (n := n))
      (left.coefficient.eval e)
      (right.coefficient.eval e)

/--
Through cutoff four, the fixed retained-provenance symbolic list evaluates
unconditionally to the powered commutator.
-/
lemma
    recollection_n_four
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (hn : n ≤ 4)
    (left right : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (globalProfileFactors normalizer
          n left right) =
      ⁅left.wordValue (n := n) ^ left.coefficient.eval e,
        right.wordValue (n := n) ^ right.coefficient.eval e⁆ :=
  profile_recollection_commutator
    normalizer e
      (satisfies_coefficient_four hn)
      left right

end
  RPThree
end TCTex
end Submission

/-!
# Finite-closure profile assignments from pending-presentation stabilization

The complete compatible operational route presents both its closed-grid packet
and its genuine-prefix pending packet homogeneously.  Its remaining global
normalization theorem is an order-aware comparison with one fixed packet list.

When that fixed list is the packet list of a finite-correction-closure profile
assignment, the full aggregate-and-pending stabilization theorem implies the
cutoff-specific operational stabilization consumed by Claim 5.  The only
remaining cutoff theorem is the signed lift of the same fixed packet list.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  PAStab

universe u

open
  PIComp
open
  PFStab
open
  CSAggreg
open
  CCTrunc
open
  UNPkt
open
  FCAssign
open
  UTAssign
open
  TAStab
open TSInput

/--
The full order-aware aggregate-and-pending stabilization theorem for the packet
list attached to one finite-closure profile assignment.
-/
abbrev SatisfiesAggregatedStabilization
    (presentationKernel :
      OAPendin)
    {n : ℕ}
    (assignment : SPAssign n 1 1) :
    Prop :=
  CPStab
    presentationKernel assignment.toPackets

/--
Full aggregate-and-pending stabilization implies the cutoff-specific
operational stabilization of the same profile assignment against any concrete
shape-block kernel.
-/
noncomputable def profileAssignmentStabilization
    {presentationKernel :
      OAPendin}
    {operationalKernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment) :
    AssignmentNaturalStabilization.{u}
      operationalKernel d assignment where
  leftWeight_pos := by simp
  rightWeight_pos := by simp
  packet_prod_concrete M N left right hleft hright :=
    (stabilization.nat_cast_group
      M N left right).trans
        (concrete_packets_pow
          (by simp) (by simp) operationalKernel M N left right
            hleft hright).symm

/--
The natural packet supplied directly by full aggregate-and-pending
stabilization.
-/
noncomputable def
    pendingPresentationAssignment
    {presentationKernel :
      OAPendin}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment) :
    TBPkt.{u} d n :=
  stabilization.truncNaturalPacket d n

@[simp]
lemma packets_pending_assignment
    {presentationKernel :
      OAPendin}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment) :
    (pendingPresentationAssignment
      (d := d) stabilization).packets =
        assignment.toPackets :=
  rfl

/--
The signed extension theorem left after full aggregate-and-pending natural
stabilization.
-/
abbrev PendingPresentationAssignment
    {presentationKernel :
      OAPendin}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment) :
    Prop :=
  (pendingPresentationAssignment.{u}
    (d := d) stabilization).AILift

/--
The signed lift of the full aggregate-and-pending packet is the signed lift of
its cutoff-specific operational stabilization.
-/
def assignmentAllLift
    {presentationKernel :
      OAPendin}
    {operationalKernel : OCShape}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment)
    (lift :
      PendingPresentationAssignment.{u}
        (d := d) stabilization) :
    AssignmentAllLift.{u}
      (profileAssignmentStabilization.{u}
        (operationalKernel := operationalKernel) (d := d) stabilization) where
  listEval_eq left right leftExponent rightExponent := by
    simpa only [
      packets_assignment_packet,
      packets_pending_assignment
    ] using lift.listEval_eq left right leftExponent rightExponent

/--
After full aggregate-and-pending stabilization, its signed lift is exactly the
cutoff-specific all-integral law for the finite-closure profile assignment.
-/
theorem
    satisfies_pending_assignment
    {presentationKernel :
      OAPendin}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment) :
    SatisfiesTruncEval.{u} (d := d) assignment ↔
      PendingPresentationAssignment.{u}
        (d := d) stabilization := by
  constructor
  · intro hlistEval
    exact
      {
        listEval_eq := by
          intro left right leftExponent rightExponent
          simpa only [
            packets_pending_assignment
          ] using hlistEval left right leftExponent rightExponent
      }
  · intro lift left right leftExponent rightExponent
    simpa only [
      packets_pending_assignment
    ] using lift.listEval_eq left right leftExponent rightExponent

namespace TSInput

/--
Aggregate-and-pending fixed-packet stabilization and its signed lift provide
the Claim 5 coordinate polynomials through the finite-closure profile
assignment.
-/
theorem
    presentationStabilizationLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {presentationKernel :
      OAPendin}
    {operationalKernel : OCShape}
    (assignment : SPAssign n 1 1)
    (stabilization :
      SatisfiesAggregatedStabilization
        presentationKernel assignment)
    (lift :
      PendingPresentationAssignment.{u}
        (d := d) stabilization)
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
  assignmentStabilizationLift
    hn H hH (kernel := operationalKernel) assignment
      (profileAssignmentStabilization
        (operationalKernel := operationalKernel) (d := d) stabilization)
      (assignmentAllLift
        (operationalKernel := operationalKernel) (d := d)
          stabilization lift)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  PAStab
end TCTex
end Submission

/-!
# Operational stabilization for recursive profile assignments

Local source and correction profile builders recursively construct one fixed
signed-profile assignment on the retained finite correction closure.  For Claim
5, that assignment need not satisfy an all-groups product identity.  It is enough
to stabilize the genuine truncated operational packets in occurrence order and
to extend the resulting natural packet to integral source exponents.

This file packages that sharper recursive interface and routes it directly to
the coordinate-polynomial adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  RAStab

universe u

open
  CSAggreg
open
  CRAssign
open
  FCAssign
open
  UTAssign
open
  TAStab
open TSInput

/--
The fixed root-weight profile assignment recursively constructed from local
source and correction builders.
-/
noncomputable def recursiveBlockAssignment
    {n : ℕ}
    (recursiveKernel : RPKern n 1 1) :
    SPAssign n 1 1 :=
  recursiveKernel.signedProfileAssignment (by simp) (by simp)

/--
The order-aware operational stabilization obligation for a recursively
constructed root-weight profile assignment.
-/
abbrev SatisfiesAssignmentStabilization
    (kernel : OCShape)
    (d : ℕ)
    {n : ℕ}
    (recursiveKernel : RPKern n 1 1) :
    Prop :=
  AssignmentNaturalStabilization.{u}
    kernel d (recursiveBlockAssignment recursiveKernel)

/--
The remaining signed extension after stabilization of a recursively constructed
profile assignment.
-/
abbrev RecursiveAssignmentLift
    {kernel : OCShape}
    {d n : ℕ}
    {recursiveKernel : RPKern n 1 1}
    (stabilization :
      SatisfiesAssignmentStabilization.{u}
        kernel d recursiveKernel) :
    Prop :=
  AssignmentAllLift stabilization

/--
The truncated all-integral law for a recursively constructed profile assignment
is equivalent to order-aware operational stabilization together with its signed
lift.
-/
theorem
    rec_assignment_stabilization
    (kernel : OCShape)
    {d n : ℕ}
    (recursiveKernel : RPKern n 1 1) :
    SatisfiesTruncEval.{u} (d := d)
        (recursiveBlockAssignment recursiveKernel) ↔
      ∃ stabilization :
          SatisfiesAssignmentStabilization.{u}
            kernel d recursiveKernel,
        RecursiveAssignmentLift stabilization :=
  satisfies_assignment_stabilization
    kernel (recursiveBlockAssignment recursiveKernel)

namespace TSInput

/--
Recursive local profile builders, order-aware natural stabilization, and its
signed lift supply the Claim 5 coordinate polynomials without an all-groups
product-law hypothesis.
-/
theorem
    recursiveAssignmentStabilization
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (recursiveKernel : RPKern n 1 1)
    (stabilization :
      SatisfiesAssignmentStabilization.{u}
        kernel d recursiveKernel)
    (lift : RecursiveAssignmentLift stabilization)
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
  assignmentStabilizationLift
    hn H hH (kernel := kernel)
      (recursiveBlockAssignment recursiveKernel)
      stabilization lift input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  RAStab
end TCTex
end Submission

/-!
# Recursive provenance for global retained symbolic recollection polynomials

Every factor in the fixed retained-profile symbolic list comes from one
selected retained recipe.  Its word is the Hall-pair substitution of that
recipe's erased shape, its evaluation is the corresponding generalized
binomial recipe factor, and its recipe is either a source or admits selected
parents of strictly smaller weighted Hall degree.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  PRDecomp

universe u

open HACoeff
open BRSpec
open
  CFExp
open
  CFSubsti
open
  CTAssigna
open
  RPThree
open
  FCAssign
open
  RCTransv
open URVocabu

/--
Every fixed retained symbolic factor has an actual selected retained recipe
witness for both its substituted word and its evaluation.
-/
lemma
    recipe_recollection_factors
    {d cutoff n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈
        globalProfileFactors normalizer
          n left right) :
    ∃ recipe ∈ recipeCoefficientRecipes n,
      factor.word =
          CWord.hallPairBind
            left.word right.word recipe.erasedShape ∧
        factor.eval (n := cutoff) e =
          recipe.erasedShape.eval
              (HPAtom.eval
                (left.wordValue (n := cutoff))
                (right.wordValue (n := cutoff))) ^
            coefficientValue recipe
              (left.coefficient.eval e) (right.coefficient.eval e) := by
  unfold globalProfileFactors at hfactor
  rcases packet_symbolic_factors hfactor with
    ⟨packet, hpacket, rfl⟩
  unfold globalSignedPackets at hpacket
  unfold SPAssign.toPackets at hpacket
  rcases List.mem_map.mp hpacket with ⟨word, _hword, rfl⟩
  refine
    ⟨retainedRecipeWord word,
      retained_coefficient_recipes word,
      ?_, ?_⟩
  · rw [RFPkt.word_symbolicFactor,
      RFPkt.boundWord,
      erased_shape_recipe]
  · rw [
      CFExp.eval_symbolicFactor,
      blockProfileAssignment,
      value_recipe_profiles,
      erased_shape_recipe]

/--
Every fixed retained symbolic factor has a selected recipe witness whose
recursive branch is either a source recipe or two selected smaller parents.
-/
lemma
    recipe_recollect_factors
    {d cutoff n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (left right : SPFactor H ι)
    (e : ι → HEFam H)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈
        globalProfileFactors normalizer
          n left right) :
    ∃ recipe ∈ recipeCoefficientRecipes n,
      factor.word =
          CWord.hallPairBind
            left.word right.word recipe.erasedShape ∧
        factor.eval (n := cutoff) e =
          recipe.erasedShape.eval
              (HPAtom.eval
                (left.wordValue (n := cutoff))
                (right.wordValue (n := cutoff))) ^
            coefficientValue recipe
              (left.coefficient.eval e) (right.coefficient.eval e) ∧
        (recipe ∈ sourceRecipes n 1 1 ∨
          ∃ leftRecipe ∈ recipeCoefficientRecipes n,
            ∃ rightRecipe ∈ recipeCoefficientRecipes n,
              recipe.erasedShape =
                  .commutator
                    leftRecipe.erasedShape rightRecipe.erasedShape ∧
                weightedWordWeight 1 1 leftRecipe <
                    weightedWordWeight 1 1 recipe ∧
                  weightedWordWeight 1 1 rightRecipe <
                    weightedWordWeight 1 1 recipe) := by
  rcases
      recipe_recollection_factors
        normalizer left right e hfactor with
    ⟨recipe, hrecipe, hword, heval⟩
  exact
    ⟨recipe, hrecipe, hword, heval,
      source_recipes_coeff
        hrecipe⟩

end
  PRDecomp
end TCTex
end Submission

/-!
# Principal splits from retained recipe-coefficient transversals

The retained recipe-coefficient transversal preserves an actual
finite-correction-closure representative for every skeleton word.  This file
compiles any proof of its cutoff-specific ordered recipe-product identity into
the closure-supported signed packet and polynomial principal split consumed by
residual routing.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace
  CPSplita

universe u

open scoped commutatorElement

open
  UCAll
open
  CTAssigna
open
  CCThree
open
  RPThree
open
  UCFtry
open
  ACAlign
open
  FCAssign
open RCAligna
open SPAssign
open TAPkta
open TSPkt

/-- A retained recipe-product law is a cutoff-specific all-integral packet. -/
noncomputable def retainedAllPacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesRecipeCoefficient d n) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes :=
    recipeCoefficientRecipes n
  listEval_eq :=
    hlistEval

/--
Singleton chunk alignment compiles the retained recipe-product law to the
ordered root-weight signed packet required by correction stabilization.
-/
noncomputable def
    coefficientTruncatedPacket
    {d n : ℕ}
    (hlistEval :
      SatisfiesRecipeCoefficient d n) :
    TAPkta.{u} d n 1 1 :=
  allChunkAlignment
      ((blockProfileAssignment n)
        |>.toSPAssign)
      (retainedAllPacket hlistEval)
      (by simp)
      (by simp)
      (recipeCoefficientChunk n)

/--
The aligned packet exposes exactly the retained-provenance fixed packet list.
-/
@[simp]
lemma packets_block_packet
    {d n : ℕ}
    (hlistEval :
      SatisfiesRecipeCoefficient d n) :
    (coefficientTruncatedPacket
      hlistEval).packets =
        globalSignedPackets n :=
  rfl

/--
At supported root-weight parents, physical routing emits exactly the fixed
global retained symbolic recollection factors.
-/
lemma supported_factory_global
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesRecipeCoefficient d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    ((supportedPacketFactory
        (coefficientTruncatedPacket
          hlistEval)
        normalizers lowerWeight).packet
          left right hleftSupported hrightSupported).factors =
      globalProfileFactors
        (normalizers.normalizer ι) n left right := by
  rw [
    supported_factory_symbolic
      (coefficientTruncatedPacket
        hlistEval)
      normalizers left right hleftSupported hrightSupported hleft hright]
  rfl

/--
At root-weight parents and cutoff above two, a retained-transversal
collection law supplies one physical weight-two principal factor and strict
weight-three-or-higher tails.
-/
noncomputable def principalHigherSplit
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesRecipeCoefficient d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1) :
    let packet :=
      coefficientTruncatedPacket
        hlistEval
    let correctionPacket :=
      (supportedPacketFactory
        packet normalizers lowerWeight).packet
          left right hleftSupported hrightSupported
    correctionPacket.PTSplit
      (CWord.hallPairBind
        left.word right.word CWord.hallPairBase)
      (1 + 1)
      (1 + 1 + 1) := by
  exact
    factoryChunkAlignment
      ((blockProfileAssignment n)
        |>.toSPAssign)
      (retainedAllPacket hlistEval)
      (recipeCoefficientChunk n)
      normalizers left right hn hleftSupported hrightSupported hleft hright

/--
The physical principal split assembled from the retained-transversal law
evaluates to the root commutator correction.
-/
lemma principal_higher_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hlistEval :
      SatisfiesRecipeCoefficient d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (left right : SPFactor H ι)
    (hn : 2 < n)
    (hleftSupported :
      lowerWeight ≤ left.word.weight HEAddres.weight)
    (hrightSupported :
      lowerWeight ≤ right.word.weight HEAddres.weight)
    (hleft :
      left.word.weight HEAddres.weight = 1)
    (hright :
      right.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    let split :=
      principalHigherSplit
        hlistEval normalizers left right hn hleftSupported hrightSupported
          hleft hright
    SPFactor.listEval (n := n) e split.beforeFactors *
          (split.principalFactor.eval e *
            SPFactor.listEval e split.afterFactors) =
      ⁅left.eval (n := n) e, right.eval (n := n) e⁆ := by
  exact
    (principalHigherSplit
      hlistEval normalizers left right hn hleftSupported hrightSupported
        hleft hright).list_split_commutator e

end
  CPSplita
end TCTex
end Submission

/-!
# Ordered natural chunk alignment for pending-presentation profile assignments

The finite correction-closure vocabulary is a support skeleton, not a
noncommutative schedule.  A fixed profile assignment can nevertheless absorb a
concrete operational packet list when each of its packets corresponds to one
contiguous same-word chunk and the ordered chunks flatten back to the concrete
list exactly.

Chunks may be empty.  This allows the fixed closure skeleton to retain words
which do not occur at one natural specialization.  No permutation or
commutative regrouping is used.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  PNChunk

universe u

open scoped commutatorElement

open
  PIComp
open
  PFStab
open
  CSAggreg
open
  CFSubsti
open
  PAStab
open TSInput
open
  FCAssign
open PPColl
open PPColl.RCColl.RPAggreg

namespace RFPkt

/--
At one natural specialization, one fixed signed-profile packet absorbs one
contiguous concrete packet chunk when every concrete word is the fixed word and
the fixed coefficient is the sum of the concrete coefficients.
-/
structure SCAlign
    (packet : RFPkt)
    (chunk : List RFPkt)
    (M N : ℕ) :
    Prop where
  word_eq :
    ∀ nextPacket ∈ chunk,
      nextPacket.word = packet.word
  profiles_value_sum :
    packet.profiles.value (M : ℤ) (N : ℤ) =
      (chunk.map fun nextPacket =>
        nextPacket.profiles.value (M : ℤ) (N : ℤ)).sum

namespace SCAlign

private lemma zpow_profiles_prod
    {G : Type*}
    [Group G]
    (word : CWord HPAtom)
    (chunk : List RFPkt)
    (hword :
      ∀ nextPacket ∈ chunk,
        nextPacket.word = word)
    (left right : G)
    (M N : ℕ) :
    word.eval (HPAtom.eval left right) ^
          (chunk.map fun nextPacket =>
            nextPacket.profiles.value (M : ℤ) (N : ℤ)).sum =
      (chunk.map fun nextPacket =>
        nextPacket.word.eval (HPAtom.eval left right) ^
          nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod := by
  induction chunk with
  | nil =>
      simp
  | cons nextPacket chunk ih =>
      have hnextPacket :
          nextPacket.word = word :=
        hword nextPacket (by simp)
      have htail :
          ∀ tailPacket ∈ chunk,
            tailPacket.word = word := by
        intro tailPacket htailPacket
        exact hword tailPacket (by simp [htailPacket])
      have hnextEval :
          word.eval (HPAtom.eval left right) =
            nextPacket.word.eval (HPAtom.eval left right) :=
        (congrArg
          (fun nextWord =>
            nextWord.eval (HPAtom.eval left right))
          hnextPacket).symm
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [zpow_add, ih htail, hnextEval]

/-- A same-word chunk alignment preserves the ordered chunk evaluation. -/
lemma eval_eq_chunk
    {G : Type*}
    [Group G]
    {packet : RFPkt}
    {chunk : List RFPkt}
    {M N : ℕ}
    (alignment : SCAlign packet chunk M N)
    (left right : G) :
    packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value (M : ℤ) (N : ℤ) =
      (chunk.map fun nextPacket =>
        nextPacket.word.eval (HPAtom.eval left right) ^
          nextPacket.profiles.value (M : ℤ) (N : ℤ)).prod := by
  rw [alignment.profiles_value_sum]
  exact zpow_profiles_prod packet.word chunk
    alignment.word_eq left right M N

end SCAlign
end RFPkt

/--
At one natural specialization, a fixed ordered packet list absorbs a concrete
ordered packet list by contiguous same-word chunks.
-/
structure NCAlign
    (fixedPackets concretePackets :
      List RFPkt)
    (M N : ℕ) where
  chunks :
    List (List RFPkt)
  packets_chunks :
    List.Forall₂
      (fun packet chunk =>
        RFPkt.SCAlign
          packet chunk M N)
      fixedPackets chunks
  flatten_chunks :
    chunks.flatten = concretePackets

namespace NCAlign

private lemma list_flatten_chunks
    {G : Type*}
    [Group G]
    {fixedPackets : List RFPkt}
    {chunks : List (List RFPkt)}
    {M N : ℕ}
    (alignment :
      List.Forall₂
        (fun packet chunk =>
          RFPkt.SCAlign
            packet chunk M N)
        fixedPackets chunks)
    (left right : G) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      (chunks.flatten.map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod := by
  induction alignment with
  | nil =>
      simp
  | cons headAlignment _tailAlignment ih =>
      simp only [List.map_cons, List.prod_cons, List.flatten_cons,
        List.map_append, List.prod_append]
      rw [headAlignment.eval_eq_chunk, ih]

/-- Ordered chunk alignment preserves evaluation without reordering factors. -/
lemma list_concrete_packets
    {G : Type*}
    [Group G]
    {fixedPackets concretePackets :
      List RFPkt}
    {M N : ℕ}
    (alignment :
      NCAlign
        fixedPackets concretePackets M N)
    (left right : G) :
    (fixedPackets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value (M : ℤ) (N : ℤ)).prod =
      (concretePackets.map fun packet =>
        packet.word.eval (HPAtom.eval left right) ^
          packet.profiles.value (M : ℤ) (N : ℤ)).prod := by
  rw [← alignment.flatten_chunks]
  exact list_flatten_chunks alignment.packets_chunks left right

end NCAlign

/--
The constructive ordered-chunk obligation for one finite-closure profile
assignment against the aggregate-and-pending presentation route.
-/
structure AggregatedChunkAlignment
    (presentationKernel :
      OAPendin)
    {n : ℕ}
    (assignment : SPAssign n 1 1) where
  alignment :
    ∀ M N : ℕ,
      NCAlign
        assignment.toPackets
        (presentationKernel.concretePackets M N)
        M N

/--
Ordered same-word chunks compile to the full aggregate-and-pending
fixed-packet stabilization theorem.
-/
def aggregatedPendingStabilization
    {presentationKernel :
      OAPendin}
    {n : ℕ}
    {assignment : SPAssign n 1 1}
    (chunkAlignment :
      AggregatedChunkAlignment
        presentationKernel assignment) :
    SatisfiesAggregatedStabilization
      presentationKernel assignment where
  packet_prod_concrete M N :=
    (chunkAlignment.alignment M N).list_concrete_packets
      universalLeft universalRight

namespace TSInput

/--
Ordered same-word chunk alignment and the resulting signed lift provide the
Claim 5 coordinate polynomials.
-/
theorem
    coordChunkLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {presentationKernel :
      OAPendin}
    {operationalKernel : OCShape}
    (assignment : SPAssign n 1 1)
    (chunkAlignment :
      AggregatedChunkAlignment
        presentationKernel assignment)
    (lift :
      PendingPresentationAssignment.{u}
        (d := d)
        (aggregatedPendingStabilization
          chunkAlignment))
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
  presentationStabilizationLift
    hn H hH (operationalKernel := operationalKernel) assignment
      (aggregatedPendingStabilization chunkAlignment)
      lift input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  PNChunk
end TCTex
end Submission

/-!
# Sorted pending-presentation chunk alignment for Claim 5

Primary erased-shape sorting now constructs the complete shape-fiber law used
by the aggregate-and-pending presentation compiler.  Ordered contiguous
same-word chunks then compile a fixed finite-closure profile assignment to the
full natural stabilization theorem without any permutation or noncommutative
regrouping.

This file threads those two reductions together and exposes the resulting
Claim 5 coordinate-polynomial adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace
  ENChunk

universe u

open
  PIComp
open
  PRPolys
open
  CSAggreg
open
  PNChunk
open TSInput
open
  PAStab
open
  FCAssign

/--
The sorted aggregate-and-pending presentation facade used by the final
order-aware chunk compiler.
-/
abbrev SortedPendingPresentation :=
  CPRecoll

/-- Forget sorting only after compiling it to a complete shape-fiber witness. -/
noncomputable def presentationKernel
    (kernel : SortedPendingPresentation) :
    OAPendin :=
  kernel.presentationGlobalSymbolic

/--
The remaining constructive fixed-profile obligation against a sorted
aggregate-and-pending presentation kernel.
-/
abbrev SortedChunkAlignment
    (kernel : SortedPendingPresentation)
    {n : ℕ}
    (assignment : SPAssign n 1 1) :=
  AggregatedChunkAlignment
    (presentationKernel kernel) assignment

/--
Ordered chunks against a sorted presentation facade compile to the full
aggregate-and-pending fixed-packet stabilization theorem.
-/
def sortedPresentationStabilization
    {kernel : SortedPendingPresentation}
    {n : ℕ}
    {assignment : SPAssign n 1 1}
    (chunkAlignment :
      SortedChunkAlignment
        kernel assignment) :
    SatisfiesAggregatedStabilization
      (presentationKernel kernel) assignment :=
  aggregatedPendingStabilization chunkAlignment

/--
The signed extension theorem left after sorted presentation alignment has been
compiled to natural stabilization.
-/
abbrev SortedPendingAssignment
    {kernel : SortedPendingPresentation}
    {d n : ℕ}
    {assignment : SPAssign n 1 1}
    (chunkAlignment :
      SortedChunkAlignment
        kernel assignment) :
    Prop :=
  PendingPresentationAssignment.{u}
    (d := d)
    (sortedPresentationStabilization chunkAlignment)

namespace TSInput

/--
Sorted aggregate-and-pending presentations, ordered same-word chunks, and the
resulting signed lift provide the Claim 5 coordinate polynomials.
-/
theorem
    coordPolyLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : SortedPendingPresentation}
    {operationalKernel : OCShape}
    (assignment : SPAssign n 1 1)
    (chunkAlignment :
      SortedChunkAlignment
        kernel assignment)
    (lift :
      SortedPendingAssignment.{u}
        (d := d) chunkAlignment)
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
  coordChunkLift
    hn H hH (operationalKernel := operationalKernel) assignment
      chunkAlignment lift input hsourceSupported factorNormalization
        hinputWeight

end TSInput

end
  ENChunk
end TCTex
end Submission
