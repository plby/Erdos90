import Submission.NumberTheory.Completions.TotalQuotientAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure


/-!
# Algebraic properties of semilocal completion coordinates

Each integral coordinate in the completed semilocal decomposition is finite,
and hence integral, over the concrete completed lower valuation ring.  Its
completed field is obtained by localizing this integral coordinate at the
non-zero elements of the lower ring.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

noncomputable section

universe u

variable {R S K L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product equivalence reconstructs every coordinate algebra.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- Every integral factor in the completed semilocal decomposition is finite
over the concrete completed lower valuation ring. -/
theorem adic_integer_module
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    letI : Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    Module.Finite (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) := by
  let C := P.adicCompletionIntegers K
  let A := AdicCompletion P.asIdeal R
  let T := A ⊗[R] S
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let B : ι → Type u := fun Q =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  letI : Algebra C T :=
    adicTensorAlgebra (S := S) (K := K) P
  letI (Q : ι) : Algebra C (B Q) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C (∀ Q, B Q) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  have hT : Module.Finite C T := by
    let eAC : A ≃+* C := adicRingIntegers (K := K) P
    letI : Module.Finite A T := Module.Finite.base_change R A S
    exact Module.Finite.of_equiv_equiv
      (A₁ := A) (B₁ := T) (A₂ := C) (B₂ := T)
      eAC (RingEquiv.refl T) (by
        ext a
        change algebraMap A T (eAC.symm (eAC a)) = algebraMap A T a
        rw [eAC.symm_apply_apply])
  let e := adicPiIntegers
    (K := K) (L := L) P hP
  letI : Module.Finite C T := hT
  letI : Module.Finite C (∀ Q, B Q) := Module.Finite.equiv e.toLinearEquiv
  exact Module.Finite.of_pi B Q

set_option synthInstance.maxHeartbeats 100000 in
-- The coordinate algebra is a dependent valuation-subring type.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- Every integral factor in the completed semilocal decomposition is
integral over the concrete completed lower valuation ring. -/
theorem adic_integer_integral
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    letI : Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    Algebra.IsIntegral (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) := by
  letI : Algebra (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Module.Finite (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    adic_integer_module (K := K) (L := L) P hP Q
  exact Algebra.IsIntegral.of_finite _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The target field is a dependent completed valuation coordinate.
/-- The lower completed integer ring acts on an upper completed field by
first acting on its upper completed integer ring and then including it in
the field. -/
@[reducible] noncomputable def adicIntegerAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    Algebra (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  let B := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra (P.adicCompletionIntegers K) B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  exact RingHom.toAlgebra <|
    (algebraMap B E).comp (algebraMap (P.adicCompletionIntegers K) B)

/-- The flat fraction-ring action sends an integral scalar to the same
scalar in the upper fraction ring. -/
private theorem fraction_ring_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (a : A) :
    @algebraMap (FractionRing A) (FractionRing B) _ _
        (fractionRingFlat A B) (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (algebraMap A B a) := by
  change IsLocalization.lift _ (algebraMap A (FractionRing A) a) = _
  rw [IsLocalization.lift_eq]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Both semilocal equivalences have dependent products of valuation rings.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The action through the upper integer coordinate agrees with restriction
of the existing action between completed fields. -/
theorem adic_integer_algebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset)
    (c : P.adicCompletionIntegers K) :
    let C := P.adicCompletionIntegers K
    let F := P.adicCompletion K
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI : Algebra C F := C.subtype.toAlgebra
    letI : Algebra F E :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    letI : Algebra C E :=
      adicIntegerAlgebra (K := K) (L := L) P hP Q
    algebraMap C E c = algebraMap F E (algebraMap C F c) := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let T := AdicCompletion P.asIdeal R ⊗[R] S
  let B := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let Bs : ι → Type u := fun Q' =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q').adicCompletionIntegers L
  let Es : ι → Type u := fun Q' =>
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q').adicCompletion L
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra C T :=
    adicTensorAlgebra (S := S) (K := K) P
  letI : Algebra F (FractionRing T) :=
    adicCompletionTensor (S := S) (K := K) P
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI (Q' : ι) : Algebra C (Bs Q') :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q'
  letI : Algebra C (∀ Q', Bs Q') :=
    piIntegersAlgebra (K := K) (L := L) P hP
  letI (Q' : ι) : Algebra F (Es Q') :=
    adicFactorAlgebra (K := K) (L := L) P hP Q'
  letI : Algebra F (∀ Q', Es Q') :=
    piCompletionsAlgebra (K := K) (L := L) P hP
  let e0 := adicPiIntegers
    (K := K) (L := L) P hP
  let e := fractionPiCompletions
    (K := K) (L := L) P hP
  have hx : algebraMap T (FractionRing T) (algebraMap C T c) =
      algebraMap F (FractionRing T) (algebraMap C F c) := by
    let A := AdicCompletion P.asIdeal R
    let eC : A ≃+* C := adicRingIntegers (K := K) P
    let eF : FractionRing A ≃+* F :=
      adicFractionRing (K := K) P
    change algebraMap T (FractionRing T)
        (algebraMap A T (eC.symm c)) =
      @algebraMap (FractionRing A) (FractionRing T) _ _
        (adicTensorFraction P.asIdeal)
        (eF.symm (algebraMap C F c))
    rw [show eF.symm (algebraMap C F c) =
        algebraMap A (FractionRing A) (eC.symm c) by
      exact IsFractionRing.ringEquivOfRingEquiv_algebraMap eC.symm c]
    exact (fraction_ring_flat
      (A := A) (B := T) (eC.symm c)).symm
  have hcompat :
      e (algebraMap T (FractionRing T) (algebraMap C T c)) Q =
        algebraMap B E (e0 (algebraMap C T c) Q) := by
    let e0' : T ≃+* (∀ Q', Bs Q') :=
      (adicTensorRing P.asIdeal).toRingEquiv.trans
        (completionPiIntegers (K := L)
          (P.asIdeal.map (algebraMap R S)) hP)
    letI : IsFractionRing (∀ Q', Bs Q') (∀ Q', Es Q') :=
      fraction_ring_pi _ _
    change IsFractionRing.ringEquivOfRingEquiv
        (K := FractionRing T) (L := ∀ Q', Es Q') e0'
        (algebraMap T (FractionRing T) (algebraMap C T c)) Q = _
    exact congrFun
      (IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (K := FractionRing T) (L := ∀ Q', Es Q') e0'
        (algebraMap C T c)) Q
  have he0 := congrFun (e0.commutes c) Q
  have he := congrFun (e.commutes (algebraMap C F c)) Q
  rw [hx, he] at hcompat
  rw [he0] at hcompat
  exact hcompat.symm

set_option synthInstance.maxHeartbeats 100000 in
-- Comparing the composed algebra map unfolds the dependent completion coordinate.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- The composed lower-integers/upper-integers/upper-field algebra structures
form a scalar tower. -/
theorem integer_scalar_tower
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    letI : Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      adicIntegerAlgebra (K := K) (L := L) P hP Q
    IsScalarTower (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  let C := P.adicCompletionIntegers K
  let B := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
  let E := (factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  change IsScalarTower C B E
  have hmap (c : C) :
      algebraMap C E c = algebraMap B E (algebraMap C B c) := rfl
  constructor
  intro c b e
  simp only [Algebra.smul_def, hmap, map_mul, mul_assoc]

set_option synthInstance.maxHeartbeats 100000 in
-- The valuation-subring coordinate carries several reducible completion instances.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- An upper completed valuation integer ring is the integral closure of the
concrete lower completed valuation integer ring in the upper completed
field, for the coordinate algebra structures. -/
theorem adic_integer_closure
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : Algebra B E := B.subtype.toAlgebra
    letI : Algebra C E :=
      adicIntegerAlgebra (K := K) (L := L) P hP Q
    IsIntegralClosure B C E := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let v := factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q
  let B := v.adicCompletionIntegers L
  let E := v.adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C B E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra.IsIntegral C B :=
    adic_integer_integral (K := K) (L := L) P hP Q
  let hv :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L) (v := v)
  letI : IsFractionRing B E := hv.isFractionRing
  letI : IsIntegrallyClosed B :=
    hv.isIntegrallyClosed
  exact IsIntegralClosure.of_isIntegrallyClosed B C E

set_option synthInstance.maxHeartbeats 100000 in
-- Fraction-ring lifting unfolds both dependent coordinate algebra structures.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The upper completed field is obtained from its completed integer ring by
inverting the images of the non-zero elements of the concrete lower
completed integer ring. -/
theorem adic_integer_localization
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    let C := P.adicCompletionIntegers K
    let B := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L
    letI : Algebra C B :=
      adicCompletionAlgebra (K := K) (L := L) P hP Q
    letI : Algebra B E := B.subtype.toAlgebra
    letI : Algebra C E :=
      adicIntegerAlgebra (K := K) (L := L) P hP Q
    IsLocalization (Algebra.algebraMapSubmonoid B C⁰) E := by
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let v := factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q
  let B := v.adicCompletionIntegers L
  let E := v.adicCompletion L
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra B E := B.subtype.toAlgebra
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  letI : IsScalarTower C B E :=
    integer_scalar_tower
      (K := K) (L := L) P hP Q
  letI : Algebra.IsIntegral C B :=
    adic_integer_integral (K := K) (L := L) P hP Q
  let hv :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := S) (K := L) (v := v)
  letI : IsFractionRing B E := hv.isFractionRing
  letI : IsIntegralClosure B C E :=
    adic_integer_closure
      (K := K) (L := L) P hP Q
  letI : FaithfulSMul B E :=
    (faithfulSMul_iff_algebraMap_injective B E).mpr
      (IsIntegralClosure.algebraMap_injective B C E)
  letI : Algebra C F := C.subtype.toAlgebra
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : FaithfulSMul C E := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply Subtype.val_injective
    apply FaithfulSMul.algebraMap_injective F E
    change algebraMap F E (algebraMap C F x) =
      algebraMap F E (algebraMap C F y)
    exact (adic_integer_algebra
      (K := K) (L := L) P hP Q x).symm.trans <|
        hxy.trans (adic_integer_algebra
          (K := K) (L := L) P hP Q y)
  letI : Algebra (FractionRing C) E := FractionRing.liftAlgebra C E
  letI : IsScalarTower C (FractionRing C) E :=
    FractionRing.isScalarTower_liftAlgebra C E
  letI : Algebra.IsAlgebraic (FractionRing C) E :=
    isAlgebraic_of_isFractionRing (R := C) (S := B) (FractionRing C) E
  exact IsIntegralClosure.isLocalization C (FractionRing C) E B

end

end Submission.NumberTheory.Milne
