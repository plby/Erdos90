import Towers.ClassField.NormIndex.IdeleExtensionMap
import Towers.ClassField.NormIndex.IdeleTowerPlaces

/-!
# Transitivity of finite coordinate embeddings

The canonical embedding between prime-adic completions agrees in a tower.
The proof uses density of the global field in its completion and the already
proved formula on completion embeddings.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

theorem cast_embedding_tower
    {K : Type u} [Field K] [NumberField K]
    {P P' : HeightOneSpectrum (OK K)} (h : P = P') (x : K) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K) h
        (FinitePlace.embedding P x) =
      FinitePlace.embedding P' x := by
  subst P'
  rfl

theorem cast_continuous_tower
    {K : Type u} [Field K] [NumberField K]
    {P P' : HeightOneSpectrum (OK K)} (h : P = P') :
    Continuous (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K) h) := by
  subst P'
  exact continuous_id

theorem place_cast_symm
    {K : Type u} [Field K] [NumberField K]
    {P P' : HeightOneSpectrum (OK K)} (h : P = P')
    (z : P.adicCompletion K) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K) h.symm
        (RingEquiv.cast h z) = z := by
  subst P'
  rfl

set_option maxHeartbeats 2000000 in
-- Comparing three dependent completion homomorphisms needs a larger
-- normalization budget after the dense-range reduction.
set_option maxRecDepth 100000 in
/-- The literal finite-coordinate embedding is transitive in a finite
Galois tower. -/
theorem extension_ring_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L]
    (R : HeightOneSpectrum (OK L)) :
    let Q := R.under (OK E)
    let P := R.under (OK K)
    let hQP : Q.under (OK K) = P := height_one_spectrum R
    ((coordinateExtensionHom (K := E) (L := L) R).comp
      (coordinateExtensionHom (K := K) (L := E) Q)).comp
        (RingEquiv.cast
          (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
          hQP.symm).toRingHom =
      coordinateExtensionHom (K := K) (L := L) R := by
  let Q := R.under (OK E)
  let P := R.under (OK K)
  let hQP : Q.under (OK K) = P := height_one_spectrum R
  apply DFunLike.ext _ _
  intro z
  exact congrFun
    ((P.denseRange_algebraMap K).equalizer
      (((extension_ring_continuous
          (K := E) (L := L) R).comp
        (extension_ring_continuous
          (K := K) (L := E) Q)).comp
        (cast_continuous_tower hQP.symm))
      (extension_ring_continuous
        (K := K) (L := L) R)
      (funext fun a ↦ by
        change coordinateExtensionHom (K := E) (L := L) R
            (coordinateExtensionHom (K := K) (L := E) Q
              (RingEquiv.cast hQP.symm (FinitePlace.embedding P a))) =
          coordinateExtensionHom (K := K) (L := L) R
            (FinitePlace.embedding P a)
        rw [cast_embedding_tower]
        have hKE := extension_comp_embedding
          (K := K) (L := E) Q a
        change coordinateExtensionHom (K := K) (L := E) Q
            (FinitePlace.embedding (Q.under (OK K)) a) =
          FinitePlace.embedding Q (algebraMap K E a) at hKE
        rw [hKE]
        have hEL := extension_comp_embedding
          (K := E) (L := L) R (algebraMap K E a)
        change coordinateExtensionHom (K := E) (L := L) R
            (FinitePlace.embedding Q (algebraMap K E a)) =
          FinitePlace.embedding R
            (algebraMap E L (algebraMap K E a)) at hEL
        rw [hEL]
        rw [← IsScalarTower.algebraMap_apply K E L]
        exact (extension_comp_embedding
          (K := K) (L := L) R a).symm)) z

end

end Towers.CField.NIndex
