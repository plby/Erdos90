import Submission.NumberTheory.Completions.CompletedProductBound
import Submission.NumberTheory.Dedekind.LocalizationQuotientPowers
import Submission.NumberTheory.Locals.OpenIdealQuotient
import Submission.NumberTheory.Completions.FractionRingBridge
import Submission.NumberTheory.Completions.SemilocalCommonDenominator
import Submission.NumberTheory.Completions.CoordinateCompatibility
import Submission.NumberTheory.Locals.CompleteDVRHenselian


/-!
# The uniform different bound in completed semilocal coordinates

This file specializes the abstract completed-product different estimate to
the prime-adic scalar extension and its concrete completed valuation rings.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain nonZeroDivisors
open scoped TensorProduct WithZero

noncomputable section

universe u

variable {R S K L : Type u}
  [CommRing R] [IsDedekindDomain R] [CharZero R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]

omit [CharZero R] in
/-- The residue field of a prime-adic completion is finite when the original
Dedekind domain has finite quotients. -/
theorem residue_adic_integers
    [Ring.HasFiniteQuotients R] (P : HeightOneSpectrum R) :
    Finite (IsLocalRing.ResidueField (P.adicCompletionIntegers K)) := by
  let A := Localization.AtPrime P.asIdeal
  let C := P.adicCompletionIntegers K
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : P.asIdeal.IsMaximal := P.isMaximal
  let eResidue : R ⧸ P.asIdeal ^ 1 ≃+*
      A ⧸ IsLocalRing.maximalIdeal A :=
    (quotientLocalizationPrime R P.asIdeal 1).trans
      (Ideal.quotEquivOfEq (by
        rw [pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal]))
  letI : Finite (R ⧸ P.asIdeal ^ 1) := by
    simpa only [pow_one] using (inferInstance : Finite (R ⧸ P.asIdeal))
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_equiv (R ⧸ P.asIdeal ^ 1) eResidue.toEquiv
  let f : A →+* C := primeAdicIntegers (K := K) P
  letI : IsLocalHom f :=
    adic_integers_hom (K := K) P
  letI : IsTopologicalRing C :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation (P.adicCompletion K) ℤᵐ⁰).integer
  let eDense : A ⧸ (IsLocalRing.maximalIdeal C).comap f ≃+*
      C ⧸ IsLocalRing.maximalIdeal C :=
    denseRangeOpen f
      (adic_integers_range (K := K) P)
      (IsLocalRing.maximalIdeal C)
      (by
        simpa only [pow_one] using
          open_maximal_integers (K := K) P 1)
  let eCompletion : A ⧸ IsLocalRing.maximalIdeal A ≃+*
      C ⧸ IsLocalRing.maximalIdeal C :=
    (Ideal.quotEquivOfEq (IsLocalRing.maximalIdeal_comap f).symm).trans eDense
  exact Finite.of_equiv (A ⧸ IsLocalRing.maximalIdeal A) eCompletion.toEquiv

/-- The completed valuation integer ring inherits characteristic zero from
the original Dedekind domain. -/
@[reducible] noncomputable def adicIntegersChar
    (P : HeightOneSpectrum R) : CharZero (P.adicCompletionIntegers K) :=
  CharZero.of_addMonoidHom
    (algebraMap R (P.adicCompletionIntegers K)).toAddMonoidHom
    (by simp)
    (FaithfulSMul.algebraMap_injective R (P.adicCompletionIntegers K))

omit [CharZero R] in
/-- A prime-adic completed valuation ring is Henselian. -/
theorem adic_integers_henselian
    (P : HeightOneSpectrum R) [Finite (R ⧸ P.asIdeal)] :
    HenselianLocalRing (P.adicCompletionIntegers K) := by
  let C := P.adicCompletionIntegers K
  letI : IsAdicComplete (IsLocalRing.maximalIdeal C) C :=
    adic_integers_complete (K := K) P
  exact {
    toIsLocalRing := inferInstance
    is_henselian := by
      intro p hp a ha hpa
      exact @HenselianRing.is_henselian C _
        (IsLocalRing.maximalIdeal C)
        (IsAdicComplete.henselianRing C (IsLocalRing.maximalIdeal C))
        p hp a ha
          (hpa.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal C))) }

set_option synthInstance.maxHeartbeats 300000 in
-- Injectivity is checked after including both valuation rings into the
-- corresponding completed fields.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
omit [CharZero R] [Algebra R L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L] in
/-- A completed upper integer coordinate is torsion-free over the completed
lower integer ring. -/
theorem adic_torsion_free
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    Module.IsTorsionFree C B := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let B := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C F E :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  intro x y hxy
  apply Subtype.val_injective
  apply (algebraMap F E).injective
  calc
    algebraMap F E (x : F) = algebraMap C E x :=
      (adic_integer_algebra
        (K := K) (L := L) P hP Q x).symm
    _ = algebraMap C E y := congrArg (fun z : B => (z : E)) hxy
    _ = algebraMap F E (y : F) :=
      adic_integer_algebra
        (K := K) (L := L) P hP Q y

set_option synthInstance.maxHeartbeats 300000 in
-- The target is a dependent product of completed valuation integer rings.
set_option maxHeartbeats 2000000 in
/-- The integral product decomposition with the concrete lower completed
valuation ring as its tensor factor. -/
noncomputable def adicIntegersPi
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    let C := P.adicCompletionIntegers K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let B : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI (Q : ι) : Algebra C (B Q) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : Algebra C (∀ Q, B Q) :=
      piIntegersAlgebra (K := K) (L := L) P hP
    C ⊗[R] S ≃ₐ[C] (∀ Q, B Q) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let eC : A ≃+* C := adicRingIntegers (K := K) P
  letI : Algebra C A := eC.symm.toRingHom.toAlgebra
  let eCR : C ≃ₐ[R] A := AlgEquiv.ofRingEquiv (f := eC.symm) fun r => by
    apply eC.injective
    rw [eC.apply_symm_apply]
    change algebraMap R C r = eC (AdicCompletion.of P.asIdeal R r)
    symm
    change adicRingEquiv (K := K) P
        (adicCompletionPrime P
          (AdicCompletion.of P.asIdeal R r)) = algebraMap R C r
    rw [adic_completion_equiv,
      adic_ring_equiv,
      adic_integers_algebra]
  let eTensorR : C ⊗[R] S ≃ₐ[R] A ⊗[R] S :=
    Algebra.TensorProduct.congr eCR (AlgEquiv.refl : S ≃ₐ[R] S)
  letI : Algebra C (A ⊗[R] S) :=
    adicTensorAlgebra (S := S) (K := K) P
  let eTensor : C ⊗[R] S ≃ₐ[C] A ⊗[R] S :=
    AlgEquiv.ofRingEquiv (f := eTensorR.toRingEquiv) fun c => by
      change eC.symm c ⊗ₜ[R] (1 : S) =
        algebraMap A (A ⊗[R] S) (eC.symm c)
      rfl
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  exact eTensor.trans <|
    adicPiIntegers
      (K := K) (L := L) P hP

set_option synthInstance.maxHeartbeats 300000 in
-- The localization target and both product algebra structures are dependent.
set_option maxHeartbeats 4000000 in
/-- The named scalar-extension decomposition into the completed field
coordinates above `P`. -/
noncomputable def adicScalarPi
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    let F := P.adicCompletion K
    let ι := (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset
    let E : ι → Type u := fun Q =>
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI (Q : ι) : Algebra F (E Q) :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    letI : Algebra F (∀ Q, E Q) :=
      piCompletionsAlgebra (K := K) (L := L) P hP
    F ⊗[K] L ≃ₐ[F] (∀ Q, E Q) := by
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
  letI (Q : ι) : Algebra (B Q) (E Q) :=
    ((factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L).subtype.toAlgebra
  letI (Q : ι) : Algebra C (E Q) :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C (B Q) (E Q) :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : Algebra F (E Q) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI (Q : ι) : IsScalarTower C F (E Q) :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI (Q : ι) : IsLocalization
      (Algebra.algebraMapSubmonoid (B Q) C⁰) (E Q) :=
    adic_localization_coordinate
      (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  letI : Algebra C (∀ Q, E Q) := Pi.algebra _ _
  letI : Algebra F (∀ Q, E Q) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e0 : A ≃ₐ[C] (∀ Q, B Q) :=
    adicIntegersPi (K := K) (L := L) P hP
  letI : Algebra A (∀ Q, E Q) :=
    piLocalizationTarget B E e0
  letI : IsScalarTower C A (∀ Q, E Q) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c Q
    change algebraMap C (E Q) c =
      algebraMap (B Q) (E Q) (e0 (algebraMap C A c) Q)
    rw [e0.commutes]
    rfl
  letI : IsScalarTower C F (∀ Q, E Q) := inferInstance
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid A C⁰) (∀ Q, E Q) :=
    localization_pi_alg B E e0
  exact scalarFractionTensor
    (R := R) (S := S) (K := K) (L := L)
    (C := C) (F := F) (Q := ∀ Q, E Q)

set_option synthInstance.maxHeartbeats 500000 in
-- The specialization installs dependent completion, residue-field, and
-- fraction-ring instances for every coordinate simultaneously.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Every completed factor above `P` satisfies the degree-uniform different
bound coming from the global extension `L/K`. -/
theorem different_dvd_maximal
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (N : ℕ) (hdegree : Module.finrank K L ≤ N)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : CharZero C := adicIntegersChar (K := K) P
    letI : Module.IsTorsionFree C B :=
      adic_torsion_free
        (K := K) (L := L) P hP Q
    differentIdeal C B ∣
      IsLocalRing.maximalIdeal B ^
        (N * (dvrCastValuation C N.factorial + 1)) := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let vQ := factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q
  let B := vQ.adicCompletionIntegers L
  let EQ := vQ.adicCompletion L
  let E : ι → Type u := fun i =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) i).adicCompletion L
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI (i : ι) : Finite (S ⧸ (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) i).asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) i).ne_bot
  letI : CharZero S :=
    CharZero.of_addMonoidHom
      (algebraMap R S).toAddMonoidHom (by simp)
      (FaithfulSMul.algebraMap_injective R S)
  letI : Algebra C F := C.subtype.toAlgebra
  let hC :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := R) (K := K) (v := P)
  letI : IsFractionRing C F := hC.isFractionRing
  letI : CharZero C := adicIntegersChar (K := K) P
  letI : HenselianLocalRing C :=
    adic_integers_henselian (K := K) P
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B EQ := B.subtype.toAlgebra
  letI : Algebra C EQ :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C B EQ :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra F EQ :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C F EQ :=
    adic_scalar_tower
      (K := K) (L := L) P hP Q
  letI (i : ι) : Algebra F (E i) :=
    adicFactorAlgebra (K := K) (L := L) P hP i
  letI : Module.Finite C B :=
    adic_integer_module (K := K) (L := L) P hP Q
  letI : Algebra.IsIntegral C B :=
    adic_integer_integral (K := K) (L := L) P hP Q
  letI : Algebra.IsAlgebraic C B := Algebra.IsIntegral.isAlgebraic
  letI : FaithfulSMul C B := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.val_injective
    apply (algebraMap F EQ).injective
    change algebraMap F EQ (algebraMap C F x) =
      algebraMap F EQ (algebraMap C F y)
    calc
      algebraMap F EQ (algebraMap C F x) = algebraMap C EQ x :=
        (IsScalarTower.algebraMap_apply C F EQ x).symm
      _ = algebraMap B EQ (algebraMap C B x) :=
        IsScalarTower.algebraMap_apply C B EQ x
      _ = algebraMap B EQ (algebraMap C B y) :=
        congrArg (algebraMap B EQ) hxy
      _ = algebraMap C EQ y :=
        (IsScalarTower.algebraMap_apply C B EQ y).symm
      _ = algebraMap F EQ (algebraMap C F y) :=
        IsScalarTower.algebraMap_apply C F EQ y
  letI : Module.IsTorsionFree C B :=
    adic_torsion_free
      (K := K) (L := L) P hP Q
  letI : IsFractionRing B EQ :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L) (v := vQ)).isFractionRing
  letI : CharZero B :=
    CharZero.of_addMonoidHom
      (algebraMap S B).toAddMonoidHom (by simp)
      (FaithfulSMul.algebraMap_injective S B)
  letI : HenselianLocalRing B :=
    adic_integers_henselian (K := L) vQ
  letI : Module.Finite K L :=
    Module.Finite.of_isLocalization R S R⁰
  letI : FiniteDimensional K L := inferInstance
  letI : Algebra F (∀ i, E i) :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e : F ⊗[K] L ≃ₐ[F] (∀ i, E i) :=
    adicScalarPi (K := K) (L := L) P hP
  letI : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  letI : Module.Finite F (∀ i, E i) := Module.Finite.equiv e.toLinearEquiv
  letI (i : ι) : FiniteDimensional F (E i) := Module.Finite.of_pi E i
  have hfield : Module.finrank F EQ ≤ N :=
    (finrank_tensor_pi E e Q).trans hdegree
  have hring : Module.finrank C B ≤ N :=
    finrank_fraction_fields N hfield
  letI : Finite (IsLocalRing.ResidueField C) :=
    residue_adic_integers (K := K) P
  letI : PerfectField (IsLocalRing.ResidueField C) := inferInstance
  letI : IsLocalHom (algebraMap C B) :=
    Algebra.IsIntegral.isLocalHom C B
  letI : FiniteDimensional (IsLocalRing.ResidueField C)
      (IsLocalRing.ResidueField B) := inferInstance
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField C)
      (IsLocalRing.ResidueField B) := inferInstance
  letI : Module.Flat C B := inferInstance
  letI : Algebra (FractionRing C) (FractionRing B) :=
    fractionRingFlat C B
  letI : IsScalarTower C (FractionRing C) (FractionRing B) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact (fraction_algebra_flat
      (A := C) (B := B) c).symm
  letI : Algebra.IsAlgebraic (FractionRing C) (FractionRing B) :=
    isAlgebraic_of_isFractionRing
      (R := C) (S := B) (FractionRing C) (FractionRing B)
  letI : Algebra.IsSeparable (FractionRing C) (FractionRing B) := inferInstance
  exact
    different_henselian_dvr
      C B N hring

end

end Submission.NumberTheory.Milne
