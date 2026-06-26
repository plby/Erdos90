import Towers.ClassField.NormIndex.IdeleExtensionTower

/-!
# Compatibility of factor and literal finite-completion embeddings

The semilocal factor map and the literal-prime coordinate map agree after
transporting their lower completion index.  The dense-range argument is
isolated here so downstream norm files only import its opaque result.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- Both completed homomorphisms are compared on the dense global field.
set_option maxRecDepth 100000 in
/-- For a factor-indexed upper prime, the literal completion embedding agrees
with the factor embedding after transporting the contracted lower prime. -/
theorem extension_comp_cast
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : UpperPrimeFactors (K := K) (L := L) P) :
    let R := upperPrime (K := K) (L := L) P q
    let hRP : R.under (NumberField.RingOfIntegers K) = P :=
      upperPrime_under (K := K) (L := L) P q
    (factorExtensionHom (K := K) (L := L) P q).comp
        (RingEquiv.cast
          (R := fun V : HeightOneSpectrum (NumberField.RingOfIntegers K) ↦
            V.adicCompletion K) hRP).toRingHom =
      coordinateExtensionHom (K := K) (L := L) R := by
  let R := upperPrime (K := K) (L := L) P q
  let hRP : R.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P q
  apply DFunLike.ext _ _
  intro z
  exact congrFun
    (((R.under (NumberField.RingOfIntegers K)).denseRange_algebraMap K).equalizer
      ((factor_extension_continuous
        (K := K) (L := L) P q).comp
          (cast_continuous_tower hRP))
      (extension_ring_continuous
        (K := K) (L := L) R)
      (funext fun a ↦ by
        change factorExtensionHom (K := K) (L := L) P q
            (RingEquiv.cast hRP
              (FinitePlace.embedding
                (R.under (NumberField.RingOfIntegers K)) a)) =
          coordinateExtensionHom (K := K) (L := L) R
            (FinitePlace.embedding
              (R.under (NumberField.RingOfIntegers K)) a)
        rw [cast_embedding_tower]
        have hfactor := ring_comp_embedding
          (K := K) (L := L) P q a
        have hcoord := extension_comp_embedding
          (K := K) (L := L) R a
        exact hfactor.trans hcoord.symm)) z

end

end Towers.CField.NIndex
