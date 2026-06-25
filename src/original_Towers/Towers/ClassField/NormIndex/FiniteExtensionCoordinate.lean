import Towers.ClassField.NormIndex.FiniteOrbitReindexing

/-!
# Finite idèle extension at one coordinate

This module isolates the restricted-product projection calculation so that
later norm-product arguments can reuse its checked result opaquely.
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option maxHeartbeats 300000 in
-- The cast from the factor-indexed upper prime to the literal coordinate is
-- definitionally simple but lies inside a dependent completion ring.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
theorem extension_monoid_hom
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (y : ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K)ˣ) :
    extensionMonoidHom (K := K) (L := L) Q y =
      Units.map
        ((RingEquiv.cast
          (R := fun V : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => V.adicCompletion L)
          (upper_prime_factor (K := K) (L := L) Q)).toRingHom.toMonoidHom)
        (factorMonoidHom (K := K) (L := L)
          (Q.under (NumberField.RingOfIntegers K))
          (upperPrimeFactor (K := K) (L := L) Q) y) := by
  apply Units.ext
  rw [extension_monoid_val,
    coordinate_extension_hom,
    factor_monoid_hom]
  rfl

set_option maxHeartbeats 300000 in
-- Unfolding the restricted-product extension at one coordinate carries its
-- local integrality witnesses and needs a larger elaboration budget.
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] [IsGalois K L] in
theorem idele_monoid_hom
    (y : FiniteIdeles (NumberField.RingOfIntegers K) K)
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (ideleMonoidHom (K := K) (L := L) y).1 Q =
      extensionMonoidHom (K := K) (L := L) Q
        (y.1 (Q.under (NumberField.RingOfIntegers K))) := by
  rfl

end


end Towers.CField.NIndex
