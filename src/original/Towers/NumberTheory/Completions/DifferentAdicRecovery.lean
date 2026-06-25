import Towers.NumberTheory.Completions.CompletedSemilocalBound
import Towers.NumberTheory.Completions.DifferentCompletionConcrete
import Towers.NumberTheory.Completions.PureTensorLocalization

/-!
# Recovery of the different from prime-adic completion

This file specializes the semilocal trace-dual recovery theorem to the
canonical product of the completions at the primes above a fixed prime.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain Module Submodule nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

variable {R S K L κ : Type u}
  [CommRing R] [IsDedekindDomain R] [CharZero R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Finite κ]

set_option synthInstance.maxHeartbeats 500000 in
-- The proof installs and compares algebra structures on two dependent
-- products of completed fields before invoking trace-dual recovery.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
theorem extended_different_factor
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (b : Basis κ R S) :
    let C := P.adicCompletionIntegers K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let B : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    let E : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI (Q : ι) : Algebra C (B Q) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI (Q : ι) : Module.IsTorsionFree C (B Q) :=
      adic_torsion_free
        (K := K) (L := L) P hP Q
    ∀ Q : ι,
      FractionalIdeal.extendedHom (E Q) (B Q)
          (((differentIdeal R S : Ideal S) :
            FractionalIdeal (nonZeroDivisors S) L)) =
        ((differentIdeal C (B Q) : Ideal (B Q)) :
          FractionalIdeal (nonZeroDivisors (B Q)) (E Q)) := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  let A := C ⊗[R] S
  letI : Algebra C A := Algebra.TensorProduct.leftAlgebra
  letI : Algebra C F := C.subtype.toAlgebra
  let hC :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := R) (K := K) (v := P)
  letI : IsFractionRing C F := hC.isFractionRing
  letI : IsScalarTower R C F := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : Module.IsTorsionFree C (B Q) :=
    adic_torsion_free
      (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra (B Q) (E Q) :=
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L).subtype.toAlgebra
  letI (Q : ι) : Algebra C (E Q) :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C (B Q) (E Q) :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower S (B Q) (E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  letI (Q : ι) : IsScalarTower S L (E Q) := by infer_instance
  letI (Q : ι) : Module.IsTorsionFree S (B Q) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y hxy
    apply IsFractionRing.injective S L
    apply (algebraMap L (E Q)).injective
    rw [← IsScalarTower.algebraMap_apply S L (E Q),
      ← IsScalarTower.algebraMap_apply S L (E Q),
      IsScalarTower.algebraMap_apply S (B Q) (E Q),
      IsScalarTower.algebraMap_apply S (B Q) (E Q), hxy]
  letI (Q : ι) : Algebra F (E Q) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C F (E Q) :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsLocalization
      (Algebra.algebraMapSubmonoid (B Q) C⁰) (E Q) :=
    adic_localization_coordinate
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsFractionRing (B Q) (E Q) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L)
      (v := factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q)).isFractionRing
  letI (Q : ι) : IsIntegralClosure (B Q) C (E Q) :=
    adic_integer_closure
      (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  letI : Algebra C (∀ Q, E Q) := Pi.algebra _ _
  letI : Algebra F (∀ Q, E Q) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e₀ : A ≃ₐ[C] (∀ Q, B Q) :=
    integersPiDifferent
      (K := K) (L := L) P hP
  letI : Algebra A (∀ Q, E Q) :=
    piLocalizationTarget B E e₀
  letI : IsScalarTower C A (∀ Q, E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c Q
    change algebraMap C (E Q) c =
      algebraMap (B Q) (E Q) (e₀ (algebraMap C A c) Q)
    rw [e₀.commutes]
    exact (IsScalarTower.algebraMap_apply C (B Q) (E Q) c).symm
  letI : IsScalarTower C F (∀ Q, E Q) := inferInstance
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A C⁰) (∀ Q, E Q) :=
    localization_pi_alg B E e₀
  letI : IsFractionRing (∀ Q, B Q) (∀ Q, E Q) :=
    fraction_ring_pi B E
  letI : IsFractionRing A (∀ Q, E Q) :=
    IsFractionRing.of_ringEquiv_left e₀.toRingEquiv (fun _ => rfl)
  letI : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  let eF : F ⊗[K] L ≃ₐ[F] (∀ Q, E Q) :=
    adicScalarPi (K := K) (L := L) P hP
  letI : Module.Finite F (∀ Q, E Q) := Module.Finite.equiv eF.toLinearEquiv
  letI (Q : ι) : Module.Finite F (E Q) := Module.Finite.of_pi E Q
  letI : CharZero K := CharZero.of_addMonoidHom
    (algebraMap R K).toAddMonoidHom (by simp)
    (FaithfulSMul.algebraMap_injective R K)
  letI : CharZero F := CharZero.of_addMonoidHom
    (algebraMap K F).toAddMonoidHom (by simp)
    (FaithfulSMul.algebraMap_injective K F)
  letI (Q : ι) : Algebra.IsSeparable F (E Q) := inferInstance
  letI (Q : ι) : Module.Free F (E Q) := inferInstance
  letI : Algebra L (∀ Q, E Q) := Pi.algebra _ _
  let eQ : (∀ Q, E Q) ≃ₐ[F] (∀ Q, E Q) := AlgEquiv.refl
  have he : eQ.restrictScalars C =
      fractionRingAlg (X := ∀ Q, E Q) B E e₀ := by
    apply AlgEquiv.ext
    intro x
    have hr : eQ.toRingEquiv.toRingHom =
        (fractionRingAlg
          (X := ∀ Q, E Q) B E e₀).toRingEquiv.toRingHom := by
      apply IsLocalization.ringHom_ext A⁰
      apply DFunLike.ext _ _
      intro a
      change algebraMap A (∀ Q, E Q) a =
        fractionRingAlg (X := ∀ Q, E Q) B E e₀
          (algebraMap A (∀ Q, E Q) a)
      rw [show fractionRingAlg (X := ∀ Q, E Q) B E e₀
          (algebraMap A (∀ Q, E Q) a) =
        algebraMap (∀ Q, B Q) (∀ Q, E Q) (e₀ a) by
          exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
            e₀.toRingEquiv a]
      rfl
    exact DFunLike.congr_fun hr x
  have hpure : ∀ x : L,
      eQ (scalarFractionTensor
          (R := R) (S := S) (K := K) (L := L)
          (C := C) (F := F) (Q := ∀ Q, E Q) ((1 : F) ⊗ₜ[K] x)) =
        (fun Q => algebraMap L (E Q) x) := by
    intro x
    change scalarFractionTensor
          (R := R) (S := S) (K := K) (L := L)
          (C := C) (F := F) (Q := ∀ Q, E Q) ((1 : F) ⊗ₜ[K] x) =
        algebraMap L (∀ Q, E Q) x
    apply scalar_tmul_integers
    intro s
    rw [scalar_fraction_tmul]
    simp only [map_one, one_mul]
    ext Q
    change algebraMap (B Q) (E Q) (e₀ ((1 : C) ⊗ₜ[R] s) Q) =
      algebraMap L (E Q) (algebraMap S L s)
    rw [pi_different_tmul]
    simp only [map_one, one_mul]
    rw [← IsScalarTower.algebraMap_apply S (B Q) (E Q),
      ← IsScalarTower.algebraMap_apply S L (E Q)]
  let I : FractionalIdeal (nonZeroDivisors S) L :=
    (((differentIdeal R S : Ideal S) :
      FractionalIdeal (nonZeroDivisors S) L))⁻¹
  have hI : I = FractionalIdeal.dual R K
      (1 : FractionalIdeal (nonZeroDivisors S) L) := by
    dsimp [I]
    rw [coeIdeal_differentIdeal R K L S, inv_inv]
  have himage :=
    completed_pi_extended
      B E e₀ eQ I
        (pi_different_tmul
          (K := K) (L := L) P hP) hpure
  apply extended_semilocal_dual
    (R := R) (S := S) (K := K) (L := L)
    (C := C) (F := F) (Q := ∀ Q, E Q) (ι := ι) (κ := κ)
    B E b e₀ eQ he
      (fun Q => FractionalIdeal.extendedHom (E Q) (B Q))
  rw [← FractionalIdeal.coe_dual_one, ← hI]
  simpa only [I] using himage

set_option synthInstance.maxHeartbeats 500000 in
-- The coercion to fractional ideals uses the completed field of the
-- selected coordinate as a common ambient fraction field.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- Ideal form of `extended_different_factor`. -/
theorem different_adic_factor
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (b : Basis κ R S) :
    let C := P.adicCompletionIntegers K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let B : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI (Q : ι) : Algebra C (B Q) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI (Q : ι) : Module.IsTorsionFree C (B Q) :=
      adic_torsion_free
        (K := K) (L := L) P hP Q
    ∀ Q : ι,
      (differentIdeal R S).map (algebraMap S (B Q)) =
        differentIdeal C (B Q) := by
  dsimp only
  let C := P.adicCompletionIntegers K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : Module.IsTorsionFree C (B Q) :=
    adic_torsion_free
      (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra (B Q) (E Q) :=
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L).subtype.toAlgebra
  letI (Q : ι) : IsFractionRing (B Q) (E Q) :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L)
      (v := factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q)).isFractionRing
  intro Q
  have hfrac := extended_different_factor
    (R := R) (S := S) (K := K) (L := L) P hP b Q
  apply FractionalIdeal.coeIdeal_injective (K := E Q)
  change (((differentIdeal R S).map (algebraMap S (B Q)) : Ideal (B Q)) :
      FractionalIdeal (nonZeroDivisors (B Q)) (E Q)) =
    ((differentIdeal C (B Q) : Ideal (B Q)) :
      FractionalIdeal (nonZeroDivisors (B Q)) (E Q))
  rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map
    (K := L) (E Q) (B Q)]
  exact hfrac

end

end Towers.NumberTheory.Milne
