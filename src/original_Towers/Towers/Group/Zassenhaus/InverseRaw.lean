import Towers.Group.Zassenhaus.BlockRecipe
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.RetainedHistoryFibers

/-!
# Polynomial-orbit normalization of retained inverse-raw sources

The dependent labelled word carried by a standardized inverse-raw source may
change when the source is embedded into a larger ambient multiplicity.  Its
symbolic one-block factor does not: the left and right block degrees and the
erased Hall word are invariant.

This file upgrades the retained dummy-vocabulary coverage theorem from
polynomial equivalence to literal equality of polynomial-orbit keys.  The
result is the multiplicity-independent source dictionary required by later
finite-index raw-profile constructions.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RONorm

open HACoeff
open ROAggreg
open RHRecurs
open RHRecipe
open HHTrunc
open RRVocabu
open RRVocabu.IRecipe
open URVocabu

namespace IRecipe

/--
Embedding a minimal inverse-raw source into larger ambient multiplicities
preserves its literal polynomial-orbit key.
-/
@[simp]
lemma key_recipe_instantiate
    {M N : ℕ}
    (recipe : IRecipe)
    (left : Fin recipe.linear.leftDegree ↪o Fin M)
    (right : Fin recipe.linear.rightDegree ↪o Fin N) :
    polynomialOrbitKey (recipe.instantiate left right).blockRecipe =
      polynomialOrbitKey recipe.blockRecipe := by
  rw [polynomial_orbit_key]
  exact
    block_recipe_equivalent
      (recipe.polynomia_instanti left right)

end IRecipe

/--
Every retained inverse-raw history has an exactly matching orbit key in the
cutoff-sized dummy source vocabulary.
-/
lemma key_recipes_histories
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {history : RHistor M N}
    (hhistory :
      history ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)) :
    ∃ recipe ∈ retainedInitialRecipes n n leftWeight rightWeight,
      polynomialOrbitKey recipe.blockRecipe =
        polynomialOrbitKey
          (RRVocabu.RHistor.initialRecipe
            history (mem_retainedHistories.mp hhistory).1).blockRecipe := by
  rcases polynomial_equivalent_histories
      hleftWeight hrightWeight hhistory with
    ⟨recipe, hrecipe, hequivalent⟩
  refine ⟨recipe, hrecipe, ?_⟩
  rw [polynomial_orbit_key]
  exact
    block_recipe_equivalent
      hequivalent

/--
Equivalently, every retained inverse-raw history is keyed by one source entry
in the universal cutoff recipe vocabulary.
-/
lemma orbit_key_histories
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {history : RHistor M N}
    (hhistory :
      history ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)) :
    ∃ recipe ∈ sourceRecipes n leftWeight rightWeight,
      polynomialOrbitKey recipe =
        polynomialOrbitKey
          (RRVocabu.RHistor.initialRecipe
            history (mem_retainedHistories.mp hhistory).1).blockRecipe := by
  rcases
      key_recipes_histories
        hleftWeight hrightWeight hhistory with
    ⟨recipe, hrecipe, hkey⟩
  exact ⟨recipe.blockRecipe, List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩, hkey⟩

end RONorm
end TCTex
end Towers

/-!
# Finite-index polynomial-orbit traces for retained inverse-raw shape fibers

The retained inverse-raw packet has a fixed finite polynomial-orbit alphabet.
Every retained history occurrence is represented by one alphabet index.  This
file identifies that chosen source trace with the concrete standardized raw
histories and proves that filtering the finite-index trace by erased Hall
shape counts the exact raw-history shape fiber.

The resulting reduction is occurrence preserving: repeated orbit indices
remain repeated occurrences.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace RFIndex

open HACoeff
open ROAggreg
open
  RHFiber
open
  RFLocal
open RRVocabu
open OREnvelo
open
  RITrace
open
  IEDecomp
open RPEnvelo

/-- Concrete orbit-key packet obtained by standardizing every retained raw
history occurrence. -/
noncomputable def concreteRawPacket
    (M N n leftWeight rightWeight : ℕ) :
    List POKey :=
  (rawHistoriesAttached M N n leftWeight rightWeight).map
    fun history =>
      polynomialOrbitKey
        (initialRawHistory history).blockRecipe

/-- Choosing cutoff-vocabulary source representatives preserves the literal
ordered orbit-key packet. -/
lemma universal_concrete_raw
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    universalOrbitPacket
        M N n leftWeight rightWeight hleftWeight hrightWeight =
      concreteRawPacket
        M N n leftWeight rightWeight := by
  unfold universalOrbitPacket
  unfold concreteRawPacket
  apply List.map_congr_left
  intro history _hhistory
  rw [polynomial_orbit_key]
  exact
    IRecipe.block_recipe_equivalent
      (universal_history_equivalent
        hleftWeight hrightWeight history)

/-- Decoding the finite source trace recovers the ordered chosen source-key
packet exactly. -/
lemma key_universal_trace
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight).map
        retainedOrbitKey =
      universalOrbitPacket
        M N n leftWeight rightWeight hleftWeight hrightWeight := by
  unfold universalIndexTrace
  exact
    retained_key_trace
      (universalOrbitPacket
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      (fun _key hkey =>
        vocabulary_universal_packet
          hkey)

/-- The concrete standardized key of one retained raw history has the
history's erased Hall shape. -/
@[simp]
lemma erased_key_history
    {M N n leftWeight rightWeight : ℕ}
    (history : RetainedRawHistory M N n leftWeight rightWeight) :
    (polynomialOrbitKey
      (initialRawHistory history).blockRecipe).erasedShape =
        collapseWord history.1.word := by
  rw [polynomialOrbitKey, initialRawHistory,
    IRecipe.blockRecipe, BRecipe.erased_shape_linear,
    RRVocabu.RHistor.initialRecipe,
    erased_label_linear]

/--
Filtering the finite source-index trace by erased shape counts exactly the
corresponding retained inverse-raw history fiber.
-/
lemma
    filter_key_histories
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    ((universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight).filter fun index =>
        decide ((retainedOrbitKey index).erasedShape = word)).length =
      ((HHTrunc.retainedHistories
        n leftWeight rightWeight
          (RHRecipe.inverseRawHistories M N)).filter
            fun history =>
              decide (collapseWord history.word = word)).length := by
  rw [←
    List.length_map
      (f := retainedOrbitKey)
      (as :=
        (universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).filter
            fun index =>
              decide
                ((retainedOrbitKey index).erasedShape = word))]
  rw [show
    ((universalIndexTrace
      M N n leftWeight rightWeight hleftWeight hrightWeight).filter fun index =>
        decide
          ((retainedOrbitKey index).erasedShape = word)).map
            retainedOrbitKey =
      ((universalIndexTrace
        M N n leftWeight rightWeight hleftWeight hrightWeight).map
          retainedOrbitKey).filter fun key =>
            decide (key.erasedShape = word) by
      rw [List.filter_map]
      rfl]
  rw [
    key_universal_trace,
    universal_concrete_raw]
  simp only [concreteRawPacket, List.filter_map,
    List.length_map]
  rw [show
    ((fun key : POKey => decide (key.erasedShape = word)) ∘
      fun history =>
        polynomialOrbitKey
          (initialRawHistory history).blockRecipe) =
      fun history =>
        decide (collapseWord history.1.word = word) by
      funext history
      simp]
  let histories :=
    HHTrunc.retainedHistories
      n leftWeight rightWeight
        (RHRecipe.inverseRawHistories M N)
  let predicate :=
    fun history : RHRecurs.RHistor M N =>
      decide (collapseWord history.word = word)
  change
    (histories.attach.filter fun history => predicate history.1).length =
      (histories.filter predicate).length
  simpa only [List.length_map, List.length_attach] using
    congrArg List.length (List.filter_attach histories predicate)

/--
The local homogeneous raw profile specializes to a filtered finite-alphabet
source trace.  Thus raw stabilization has been reduced to polynomial counting
of fixed finite-index trace fibers.
-/
lemma fiber_cast_filter
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    (retainedFiberProfile
      M N n leftWeight rightWeight word).value (M : ℤ) (N : ℤ) =
        (((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).filter
            (fun index =>
              decide
                ((retainedOrbitKey index).erasedShape = word))).length :
                  ℤ) := by
  rw [fiber_filter_length]
  exact_mod_cast
    (by
      rw [filter_key_histories]
      simpa only [DFTerm.erased_shape_family] using
        length_collapse_histories
          M N n leftWeight rightWeight word)

end RFIndex
end TCTex
end Towers
