import Towers.ClassField.LocalGlobalPowers.CyclicDescent
import Towers.NumberTheory.Completions.SemilocalCoordinateAlgebra
import Towers.NumberTheory.Completions.DifferentCompletionConcrete

/-!
# Compatibility of global embeddings with semilocal completion coordinates

This is the completion base-change input used to transport the local-power
hypothesis to a finite extension in Theorem VIII.1.4.
-/

namespace Towers.CField.LGPowers

open IsDedekindDomain NumberField Polynomial
open Towers.NumberTheory.Milne

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

set_option synthInstance.maxHeartbeats 500000 in
-- Normalizing the two completed-field embeddings requires a larger instance-search budget.
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
/-- The semilocal coordinate map between completed fields agrees with the
two global embeddings on the ground field. -/
theorem adic_global_compatibility
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap (OK K) (OK L)))).toFinset)
    (x : K) :
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap (OK K) (OK L))) Q).adicCompletion L
    letI : Algebra (P.adicCompletion K) E :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    algebraMap (P.adicCompletion K) E
        (algebraMap K (P.adicCompletion K) x) =
      algebraMap L E (algebraMap K L x) := by
  let R := OK K
  let S := OK L
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let Bfamily : ι → Type u := fun Q' ↦
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q').adicCompletionIntegers L
  let V := factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q
  let B := V.adicCompletionIntegers L
  let E := V.adicCompletion L
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : IsScalarTower S B E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro s
    rfl
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI (Q' : ι) : Algebra C (Bfamily Q') :=
    adicCompletionAlgebra
      (K := K) (L := L) P hP Q'
  letI : Algebra C (∀ Q', Bfamily Q') :=
    piIntegersAlgebra
      (K := K) (L := L) P hP
  let e₀ : TensorProduct R C S ≃ₐ[C] (∀ Q', Bfamily Q') :=
    integersPiDifferent
      (K := K) (L := L) P hP
  have hinteger (r : R) :
      algebraMap F E (algebraMap K F (algebraMap R K r)) =
        algebraMap L E (algebraMap K L (algebraMap R K r)) := by
    have hCB : algebraMap C B (algebraMap R C r) =
        algebraMap S B (algebraMap R S r) := by
      have hleft :=
        pi_different_tmul
          (K := K) (L := L) P hP (algebraMap R C r) (1 : S) Q
      have hright :=
        pi_different_tmul
          (K := K) (L := L) P hP (1 : C) (algebraMap R S r) Q
      have htensor :
          (algebraMap R C r) ⊗ₜ[R] (1 : S) =
            (1 : C) ⊗ₜ[R] algebraMap R S r := by
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
      calc
        algebraMap C B (algebraMap R C r) =
            e₀ ((algebraMap R C r) ⊗ₜ[R] (1 : S)) Q := by
              simpa using hleft.symm
        _ = e₀ ((1 : C) ⊗ₜ[R] algebraMap R S r) Q := by
              rw [htensor]
        _ = algebraMap S B (algebraMap R S r) := by
              simpa using hright
    calc
      algebraMap F E (algebraMap K F (algebraMap R K r)) =
          algebraMap F E (algebraMap C F (algebraMap R C r)) := by
            congr 1
      _ = algebraMap C E (algebraMap R C r) := by
            exact (adic_integer_algebra
              (K := K) (L := L) P hP Q (algebraMap R C r)).symm
      _ = algebraMap B E (algebraMap C B (algebraMap R C r)) := rfl
      _ = algebraMap B E (algebraMap S B (algebraMap R S r)) := by rw [hCB]
      _ = algebraMap L E (algebraMap S L (algebraMap R S r)) := by
            rfl
      _ = algebraMap L E (algebraMap K L (algebraMap R K r)) := by
            rw [← IsScalarTower.algebraMap_apply R S L,
              ← IsScalarTower.algebraMap_apply R K L]
  change algebraMap F E (algebraMap K F x) =
    algebraMap L E (algebraMap K L x)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  rw [← hab]
  simp only [map_div₀]
  rw [hinteger a, hinteger b]

end

end Towers.CField.LGPowers
