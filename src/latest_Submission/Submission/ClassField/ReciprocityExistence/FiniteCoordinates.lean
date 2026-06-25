import Submission.ClassField.ReciprocityExistence.IdeleCup
import Submission.ClassField.ReciprocityExistence.CupNaturality
import Submission.ClassField.HasseNorm.FiniteStageDecomposition
import Submission.ClassField.BrauerLocalization.H2Naturality

/-!
# Finite-coordinate naturality of the multiplicative idèle cup

Before applying Shapiro and the local crossed-product comparison, the
finite coordinate of the idèle cup is simply obtained by evaluating the
literal idèle-valued cocycle at all upper primes over the chosen base prime.
-/

namespace Submission.CField.RExist

open scoped IsMulCommutative
open CategoryTheory groupCohomology
open IsDedekindDomain NumberField
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm
open Submission.CField.BLoc

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

local instance finiteCoordinateIdeleAction :
    MulDistribMulAction Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  (concreteActionData (K := K) (L := L)).action

local instance finiteCoordinateOrbitAction
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulDistribMulAction Gal(L/K)
      (∀ Q : FinitePrimesAbove (K := K) (L := L) P,
        (Q.1.adicCompletion L)ˣ) :=
  aboveUnitsAction (K := K) (L := L) P

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent product action requires an enlarged instance search.
omit [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] in
/-- Evaluation at the finite primes above a base prime is equivariant for
the concrete idèle action. -/
theorem above_monoid_equivariant
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (g : Gal(L/K))
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    primesAboveMonoid (K := K) (L := L) P (g • x) =
      g • primesAboveMonoid (K := K) (L := L) P x := by
  rfl

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent product action requires an enlarged instance search.
omit [FiniteDimensional K L] in
/-- Mapping the literal idèle cup class to the orbit over a finite place
gives the same literal cup construction with the evaluated base idèle. -/
theorem multiplicative_cup_orbit
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    MHTwo.mapCoefficientsHom
        (primesAboveMonoid (K := K) (L := L) P)
        (above_monoid_equivariant K L P)
        (globalMultiplicativeClass K L a chi) =
      invariantCharacterCup
        (primesAboveMonoid (K := K) (L := L) P
          (ideleExtensionMonoid (K := K) (L := L) a))
        (fun g => by
          rw [← above_monoid_equivariant K L P]
          exact congrArg
            (primesAboveMonoid (K := K) (L := L) P)
            (global_multiplicative_fixed K L a g))
        chi := by
  rw [globalMultiplicativeClass,
    invariantCharacterCup,
    invariantCharacterCup,
    MHTwo.coefficients_hom_mk]
  rfl

set_option synthInstance.maxHeartbeats 300000 in
-- The two resized coefficient presentations are definitionally equal only
-- after the dependent finite-orbit action has been synthesized.
omit [IsMulCommutative Gal(L/K)] in
/-- The coefficient path through the resized concrete idèle representation
is the direct linearization of finite-orbit evaluation. -/
theorem resized_orbit_path
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (multiplicativeIsoConcrete K L).hom ≫
        resizedConcreteAbove
          (K := K) (L := L) P =
      uliftCoefficientHom
        (primesAboveMonoid (K := K) (L := L) P)
        (above_monoid_equivariant K L P) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

set_option synthInstance.maxHeartbeats 300000 in
-- Functoriality must compare the dependent finite-orbit representation
-- with the direct multiplicative presentation.
/-- The resized categorical idèle cup has the expected finite-orbit
coordinate before Shapiro decomposition. -/
theorem global_multiplicative_orbit
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedConcreteAbove
          (K := K) (L := L) P) 2
        (globalMultiplicative2 K L a chi) =
      multiplicativeLiftAdditive
        (invariantCharacterCup
          (primesAboveMonoid (K := K) (L := L) P
            (ideleExtensionMonoid (K := K) (L := L) a))
          (fun g => by
            rw [← above_monoid_equivariant K L P]
            exact congrArg
              (primesAboveMonoid (K := K) (L := L) P)
              (global_multiplicative_fixed K L a g))
          chi) := by
  change groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedConcreteAbove
        (K := K) (L := L) P) 2
      (groupCohomology.map (MonoidHom.id Gal(L/K))
        (multiplicativeIsoConcrete K L).hom 2
        (multiplicativeLiftAdditive
          (globalMultiplicativeClass K L a chi))) = _
  rw [← ConcreteCategory.comp_apply]
  rw [← groupCohomology.map_id_comp]
  have hpath := congrArg
    (fun q :
        uliftMulRepresentation
            (G := Gal(L/K))
            (M := IdeleGroup (NumberField.RingOfIntegers L) L) ⟶
          resizedAboveRepresentation
            (K := K) (L := L) P =>
      groupCohomology.map
        (A := uliftMulRepresentation
          (G := Gal(L/K))
          (M := IdeleGroup (NumberField.RingOfIntegers L) L))
        (B := resizedAboveRepresentation
          (K := K) (L := L) P)
        (MonoidHom.id Gal(L/K)) q 2)
    (resized_orbit_path K L P)
  let x := multiplicativeLiftAdditive
    (globalMultiplicativeClass K L a chi)
  calc
    _ = groupCohomology.map (MonoidHom.id Gal(L/K))
        (uliftCoefficientHom
          (primesAboveMonoid (K := K) (L := L) P)
          (above_monoid_equivariant K L P)) 2 x :=
      ConcreteCategory.congr_hom hpath x
    _ = multiplicativeLiftAdditive
        (MHTwo.mapCoefficientsHom
          (primesAboveMonoid (K := K) (L := L) P)
          (above_monoid_equivariant K L P)
          (globalMultiplicativeClass K L a chi)) := by
      exact multiplicative_u_coefficients
        (primesAboveMonoid (K := K) (L := L) P)
        (above_monoid_equivariant K L P)
        (globalMultiplicativeClass K L a chi)
    _ = _ := congrArg multiplicativeLiftAdditive
      (multiplicative_cup_orbit K L P a chi)

set_option synthInstance.maxHeartbeats 300000 in
-- The direct-limit decomposition and the dependent finite-orbit map must
-- expose the same resized representation.
/-- The finite coordinate of the final idèle H² decomposition is the
literal finite-orbit cup class. -/
theorem global_multiplicative_cup
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    resizedHDecomposition
        (K := K) (L := L)
        (globalMultiplicative2 K L a chi) (.inl P) =
      resizedPlaceProduct
        (K := K) (L := L) P
        (multiplicativeLiftAdditive
          (invariantCharacterCup
            (primesAboveMonoid (K := K) (L := L) P
              (ideleExtensionMonoid (K := K) (L := L) a))
            (fun g => by
              rw [← above_monoid_equivariant K L P]
              exact congrArg
                (primesAboveMonoid (K := K) (L := L) P)
                (global_multiplicative_fixed K L a g))
            chi)) := by
  rw [(resizedIdeleFormula
    (K := K) (L := L)).1]
  rw [global_multiplicative_orbit K L P a chi]

set_option synthInstance.maxHeartbeats 300000 in
-- The two direct-sum maps have dependent fibers at the selected place.
/-- The finite coordinate of the final absolute-Brauer-valued idèle cup,
expressed before the local Shapiro and crossed-product calculation. -/
theorem global_multiplicative_finite
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : CharacterModule (Additive Gal(L/K))) :
    multiplicativeIdeleCup K L chi
        (Additive.ofMul a) (.inl P) =
      localBrauerInclusion K L
        (completionChoice K L) (.inl P)
        (completionRelativeBrauer
          (K := K) (L := L) (completionChoice K L) (.inl P)
          (resizedPlaceProduct
            (K := K) (L := L) P
            (multiplicativeLiftAdditive
              (invariantCharacterCup
                (primesAboveMonoid (K := K) (L := L) P
                  (ideleExtensionMonoid (K := K) (L := L) a))
                (fun g => by
                  rw [← above_monoid_equivariant K L P]
                  exact congrArg
                    (primesAboveMonoid
                      (K := K) (L := L) P)
                    (global_multiplicative_fixed K L a g))
                chi)))) := by
  change (brauerDirectInclusion K L
      (completionChoice K L)
      (directRelativeBrauer
        K L (completionChoice K L)
        (resizedHDecomposition
          (K := K) (L := L)
          (globalMultiplicative2 K L a chi)))) (.inl P) = _
  change localBrauerInclusion K L
      (completionChoice K L) (.inl P)
      (directRelativeBrauer
        K L (completionChoice K L)
        (resizedHDecomposition
          (K := K) (L := L)
          (globalMultiplicative2 K L a chi)) (.inl P)) = _
  rw [direct_relative_brauer]
  rw [global_multiplicative_cup K L P a chi]

end

end Submission.CField.RExist
