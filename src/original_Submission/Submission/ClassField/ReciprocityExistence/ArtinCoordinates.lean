import Submission.ClassField.ReciprocityExistence.FiniteLayerAbsolute

/-!
# Coordinate formulas for finite-layer Artin products

The global product in `FAProduc` is built from a restricted
finite product and the finite product over infinite places.  This file proves
that evaluating it on a one-coordinate idèle recovers exactly the selected
local homomorphism.  These are the coordinate identities needed to turn the
canonical local norm-residue maps into an `LayerArtinProduct`.
-/

namespace Submission.CField.RExist

open scoped IsMulCommutative
open NumberField IsDedekindDomain
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

variable {K G : Type u} [Field K] [NumberField K] [CommGroup G]

noncomputable local instance finiteAbelianSubextensionNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

set_option maxHeartbeats 1000000 in
-- The dependent restricted product must reduce its one-coordinate embedding.
/-- The finite part of an Artin product has its prescribed value on a
one-coordinate finite idèle. -/
theorem FAProduc.artin_place_embedding
    (D : FAProduc K G)
    (P : HeightOneSpectrum (RingOfIntegers K))
    (x : (P.adicCompletion K)ˣ) :
    D.artin (finitePlaceEmbedding (RingOfIntegers K) K P x) =
      D.finite.localHom P x := by
  classical
  change D.infiniteHom 1 *
      D.finite.restrictedProductHom
        (fun Q : HeightOneSpectrum (RingOfIntegers K) ↦
          IdeleUnitSubgroup (RingOfIntegers K) K Q)
        (RestrictedProduct.mulSingle
          (fun Q : HeightOneSpectrum (RingOfIntegers K) ↦
            IdeleUnitSubgroup (RingOfIntegers K) K Q) P x) = _
  rw [map_one, one_mul]
  exact RLFam.restricted_product_single
    (U := fun Q : HeightOneSpectrum (RingOfIntegers K) ↦
      IdeleUnitSubgroup (RingOfIntegers K) K Q)
    D.finite P x

set_option maxHeartbeats 1000000 in
-- The infinite adèle equivalence must reduce the dependent `Pi.mulSingle`.
set_option synthInstance.maxHeartbeats 200000 in
/-- The infinite part of an Artin product has its prescribed value on a
one-coordinate infinite idèle. -/
theorem FAProduc.artin_infinite_embedding
    (D : FAProduc K G)
  (v : InfinitePlace K) (x : v.1.Completionˣ) :
    D.artin (infinitePlaceEmbedding (RingOfIntegers K) K v x) =
      D.infinite v x := by
  classical
  change D.infiniteHom (infiniteLocalEmbedding K v x) *
      D.finite.restrictedProductHom
        (fun P : HeightOneSpectrum (RingOfIntegers K) ↦
          IdeleUnitSubgroup (RingOfIntegers K) K P) 1 = _
  rw [map_one, mul_one]
  have hsingle :
      MulEquiv.piUnits (infiniteLocalEmbedding K v x) =
        (Pi.mulSingle v x : (q : InfinitePlace K) → q.1.Completionˣ) := by
    exact MulEquiv.apply_symm_apply _ _
  change (∏ w : InfinitePlace K,
      D.infinite w (MulEquiv.piUnits (infiniteLocalEmbedding K v x) w)) =
    D.infinite v x
  rw [hsingle]
  calc
    (∏ w : InfinitePlace K,
        D.infinite w
          ((Pi.mulSingle v x : (q : InfinitePlace K) → q.1.Completionˣ) w)) =
        D.infinite v
          ((Pi.mulSingle v x : (q : InfinitePlace K) → q.1.Completionˣ) v) := by
      apply Fintype.prod_eq_single v
      intro w hwv
      rw [Pi.mulSingle_eq_of_ne hwv]
      exact map_one (D.infinite w)
    _ = D.infinite v x := by rw [Pi.mulSingle_eq_same]

/-- An explicit product of local Artin maps is a finite-layer Artin product
as soon as its selected coordinate maps have the required local
norm-residue normalizations. -/
theorem FAProduc.layerArtinProduct
    (L : FASubext K)
    (D : FAProduc K Gal(L.1/K))
    (hfinite : ∀ (P : HeightOneSpectrum (RingOfIntegers K))
        (Q : UpperPrimeFactors (K := K) (L := L.1) P),
      LayerLocalArtin L P Q (D.finite.localHom P))
    (hinfinite : ∀ (v : InfinitePlace K)
        (w : InfinitePlacesAbove (K := K) (L := L.1) v),
      InfiniteLayerArtin L v w (D.infinite v)) :
    LayerArtinProduct L D.artin := by
  constructor
  · intro P Q
    exact ⟨D.finite.localHom P, hfinite P Q,
      D.artin_place_embedding P⟩
  · intro v w
    exact ⟨D.infinite v, hinfinite v w,
      D.artin_infinite_embedding v⟩

end

end Submission.CField.RExist
