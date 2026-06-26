import Towers.ClassField.ReciprocityExistence.CompletionShapiro
import Towers.ClassField.NormIndex.CompletionPlaceComparison
import Towers.ClassField.NormIndex.IdeleExtensionMap
import Towers.ClassField.NormIndex.FiniteExtensionCoordinate

/-!
# Concrete evaluation of a finite completion orbit

The finite-orbit Shapiro morphism selects the upper prime corresponding to
the chosen absolute-value completion and transports its prime-adic unit back
to that completion.
-/

namespace Towers.CField.RExist

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Evaluation of a prime-adic finite orbit at the prime centered on a
chosen completion, written in the absolute-value completion model. -/
noncomputable def orbitChosenMonoid
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
      (Q.1.adicCompletion L)ˣ) →* w.1.Completionˣ :=
  let Q := upperPrimesAbove
    (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  (placeUnitsAdic
      (K := K) (L := L) P w).symm.toMonoidHom.comp
    (Pi.evalMonoidHom
      (fun R : FinitePrimesAbove (K := K) (L := L) P =>
        (R.1.adicCompletion L)ˣ) Q)

set_option maxHeartbeats 1000000 in
-- The inverse orbit reindexing and dependent chosen coordinate elaborate together.
set_option synthInstance.maxHeartbeats 300000 in
-- The inverse orbit reindexing and dependent chosen coordinate elaborate together.
/-- The representation morphism used by finite-orbit Shapiro has the
concrete value given by `orbitChosenMonoid`. -/
theorem resized_chosen_hom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : Rep.res
      (CompletionPlaceStabilizer (FinitePlace.mk P).val w).subtype
      (resizedAboveRepresentation
        (K := K) (L := L) P)) :
    chosenRepresentationHom
        (K := K) (L := L) P w x =
      Additive.ofMul
        (orbitChosenMonoid
          (K := K) (L := L) P w x.toMul) := by
  rw [resized_representation_hom]
  rfl

/-- Transport a dependent family of prime-adic units along an equality of
prime indices. -/
private theorem units_cast_dependent
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    (h : P = P')
    (x : ∀ R : HeightOneSpectrum (NumberField.RingOfIntegers F),
      (R.adicCompletion F)ˣ) :
    Units.map
        ((RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers F) => R.adicCompletion F)
          h).toRingHom.toMonoidHom) (x P) =
      x P' := by
  subst P'
  rfl

/-- The base-field prime-adic unit embedded into the chosen upper
absolute-value completion, through the literal upper-prime coordinate. -/
noncomputable def chosenMonoidHom
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (P.adicCompletion K)ˣ →* w.1.Completionˣ := by
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  exact (placeUnitsAdic
      (K := K) (L := L) P w).symm.toMonoidHom.comp
    ((NIndex.extensionMonoidHom
        (K := K) (L := L) Q).comp
      (Units.map
        ((RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers K) => R.adicCompletion K)
          hQ.symm).toRingHom.toMonoidHom)))

set_option maxHeartbeats 3000000 in
-- The restricted-product coordinate and both completion models elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
-- The prime-factor and literal-prime indices must normalize simultaneously.
set_option maxRecDepth 100000 in
-- The dependent restricted-product coordinate unfolds through two completion models.
/-- Evaluating the finite orbit of an extended base idèle gives the
canonical embedding of its base coordinate into the chosen completion. -/
theorem orbit_chosen_monoid
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    orbitChosenMonoid (K := K) (L := L) P w
        (primesAboveMonoid (K := K) (L := L) P
          (NIndex.ideleExtensionMonoid
            (K := K) (L := L) a)) =
      chosenMonoidHom
        (K := K) (L := L) P w (a.2.1 P) := by
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  let eL := placeUnitsAdic
    (K := K) (L := L) P w
  calc
    orbitChosenMonoid (K := K) (L := L) P w
        (primesAboveMonoid (K := K) (L := L) P
          (NIndex.ideleExtensionMonoid
            (K := K) (L := L) a)) =
      eL.symm
        ((NIndex.ideleMonoidHom
          (K := K) (L := L) a.2).1 Q) := by
            rfl
    _ = eL.symm
        (NIndex.extensionMonoidHom
          (K := K) (L := L) Q
          (a.2.1 (Q.under (NumberField.RingOfIntegers K)))) := by
            rw [NIndex.idele_monoid_hom]
    _ = eL.symm
        (NIndex.extensionMonoidHom
          (K := K) (L := L) Q
          (Units.map
            ((RingEquiv.cast
              (R := fun R : HeightOneSpectrum
                (NumberField.RingOfIntegers K) => R.adicCompletion K)
              hQ.symm).toRingHom.toMonoidHom) (a.2.1 P))) := by
            rw [units_cast_dependent]
    _ = chosenMonoidHom
        (K := K) (L := L) P w (a.2.1 P) := by
            rfl

end

end Towers.CField.RExist
