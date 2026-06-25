import Towers.Group.Zassenhaus.FiniteIndexProfiles

/-!
# Natural endpoint certificates for selected cutoff-full traces

The cutoff-full collector already produces a literal occurrence rewrite run
at every natural specialization.  Its selected finite-index trace is a
counting trace: filtering by erased Hall shape recovers the fixed-slot
coordinate vector of the collected endpoint.

This file packages that concrete natural endpoint theorem without asserting a
fixed multiplicity-independent trace or an all-integral lift.  Those are the
remaining interpolation obligations for the arbitrary-cutoff symbolic
collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  NECert

universe u

open scoped commutatorElement

open HACoeff
open CFCollec
open CRLayer
open
  NRCoordi
open
  NRSubinv
open
  UCSuppor
open
  RITrace
open
  PCBridge
open
  FIBridge

/--
The selected endpoint trace counted shape-by-shape over the fixed ordered Hall
vocabulary.  The trace may depend on the natural specialization; the output
vector has a specialization-independent slot order.
-/
noncomputable def selectedFiberVector
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List ℕ :=
  (orderedErasedVocabulary n leftWeight rightWeight).map fun word =>
    ((selectedFullEndpoint
      layer M N hleftWeight hrightWeight).filter fun index =>
        decide
          ((retainedOrbitKey index).erasedShape = word)).length

/--
The selected finite-index trace recovers the padded natural endpoint
coordinates exactly.
-/
lemma selected_fiber_slot
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    selectedFiberVector
        layer M N hleftWeight hrightWeight =
      naturalSlotVector
        layer hleftWeight hrightWeight M N := by
  exact
    (natural_slot_mult
      layer hleftWeight hrightWeight M N).symm

/--
Counting the selected trace by erased Hall shape and evaluating the resulting
fixed-slot vector still computes the powered commutator in every matching
nilpotent target.
-/
lemma zip_selected_fiber
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n leftWeight rightWeight)
        (selectedFiberVector
          layer M N hleftWeight hrightWeight)).prod =
      ⁅x ^ M, y ^ N⁆ := by
  rw [
    selected_fiber_slot]
  exact
    zip_slot_vector
      layer hleftWeight hrightWeight M N x y hx hy hbot

/--
The literal collected endpoint occurrence list evaluates to the natural
powered commutator.
-/
lemma collapsed_evaluated_endpoint
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod =
      ⁅x ^ M, y ^ N⁆ := by
  simpa [
    collapsedEvaluatedFactors,
    CFCollec.DFTerm.collapsedList
  ] using
    (layer.endpoint M N).collapsed_list_pow
      x y hleftWeight hrightWeight hx hy hbot

/--
The literal collected endpoint and the selected trace's fixed-slot shape
counts have the same ordered product.  This comparison passes through their
common powered-commutator value; it does not assert an occurrence permutation.
-/
lemma
    collapsed_evaluated_vector
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {G : Type*}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod =
      (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n leftWeight rightWeight)
        (selectedFiberVector
          layer M N hleftWeight hrightWeight)).prod := by
  rw [
    collapsed_evaluated_endpoint
      layer M N hleftWeight hrightWeight x y hx hy hbot,
    zip_selected_fiber
      layer M N hleftWeight hrightWeight x y hx hy hbot]

/--
One concrete natural specialization simultaneously carries:

* the literal cutoff-aware occurrence rewrite run;
* the exact fixed-slot shape-fiber coordinate vector;
* the powered-commutator evaluation of that vector.

This is the constructible natural endpoint certificate before choosing one
fixed interpolating trace and proving its all-integral lift.
-/
structure SOCert
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    Prop where
  rewrites :
    TORwa
      (collapsedEvaluatedFactors x y
        (inverseDecoratedTerms M N))
      (collapsedEvaluatedFactors x y (layer.endpoint M N).factors)
  vector_fixed_slots :
    selectedFiberVector
        layer M N (by simp) (by simp) =
      naturalSlotVector layer (by simp) (by simp) M N
  zip_vector_pow :
    (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n 1 1)
        (selectedFiberVector
          layer M N (by simp) (by simp))).prod =
      ⁅x ^ M, y ^ N⁆
  endpoint_fiber_vector :
    (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod =
      (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n 1 1)
        (selectedFiberVector
          layer M N (by simp) (by simp))).prod

namespace SOCert

/-- The literal rewrite run preserves the ordered product from the inverse-raw
source to the selected cutoff-full endpoint. -/
lemma endpoint_prod_source
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {M N : ℕ}
    {x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (certificate :
      SOCert
        layer M N x y) :
    (collapsedEvaluatedFactors x y (layer.endpoint M N).factors).prod =
      (collapsedEvaluatedFactors x y
        (inverseDecoratedTerms M N)).prod :=
  certificate.rewrites.list_prod_eq

/-- Composing the literal rewrite run with endpoint shape-fiber counting gives
a direct source-to-profile product equality. -/
lemma fiber_multiplicity_vector
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {M N : ℕ}
    {x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (certificate :
      SOCert
        layer M N x y) :
    (collapsedEvaluatedFactors x y
      (inverseDecoratedTerms M N)).prod =
      (List.zipWith
        (fun word multiplicity =>
          word.eval (HPAtom.eval x y) ^ multiplicity)
        (orderedErasedVocabulary n 1 1)
        (selectedFiberVector
          layer M N (by simp) (by simp))).prod :=
  certificate.endpoint_prod_source.symm.trans
    certificate.endpoint_fiber_vector

end SOCert

namespace NRLayer

/--
Every natural specialization of a root-weight cutoff-full recollection layer
constructs its concrete occurrence-profile certificate.
-/
noncomputable def selectedOccurrenceCertificate
    {d n : ℕ}
    (layer : NRLayer n 1 1)
    (M N : ℕ)
    (x y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    SOCert
      layer M N x y where
  rewrites :=
    PCBridge.NRLayer.endpointOccRewrites
      layer M N x y
  vector_fixed_slots :=
    selected_fiber_slot
      layer M N (by simp) (by simp)
  zip_vector_pow :=
    zip_selected_fiber
      layer M N (by simp) (by simp) x y (by simp) (by simp)
        SCFactor.trunc_last_bot
  endpoint_fiber_vector :=
    collapsed_evaluated_vector
      layer M N (by simp) (by simp) x y (by simp) (by simp)
        SCFactor.trunc_last_bot

end NRLayer

end
  NECert
end TCTex
end Towers
