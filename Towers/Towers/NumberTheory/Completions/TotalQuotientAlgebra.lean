import Towers.NumberTheory.Completions.SemilocalTotalQuotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Algebra structures on semilocal total quotient rings

Flatness makes regular elements of a base ring act regularly after scalar
extension.  Consequently the total quotient ring of a flat algebra is
canonically an algebra over the total quotient ring of the base.  This
upgrades the semilocal fraction-ring decomposition to an algebra
equivalence.  At a height-one prime, its base is identified with the
concrete adic completion field.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped TensorProduct

noncomputable section

universe u

/-- A regular scalar remains a non-zero-divisor in a flat commutative
algebra. -/
theorem non_divisors_flat
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {a : A} (ha : a ∈ nonZeroDivisors A) :
    algebraMap A B a ∈ nonZeroDivisors B := by
  rw [← isRegular_iff_mem_nonZeroDivisors]
  rw [Commute.isRegular_iff (fun b : B => mul_comm _ b)]
  change IsSMulRegular B (algebraMap A B a)
  rw [isSMulRegular_algebraMap_iff]
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors ha

/-- The canonical algebra structure between total quotient rings induced
by a flat algebra. -/
@[reducible] noncomputable def fractionRingFlat
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] : Algebra (FractionRing A) (FractionRing B) := by
  let g : A →+* FractionRing B :=
    (algebraMap B (FractionRing B)).comp (algebraMap A B)
  exact RingHom.toAlgebra <| IsLocalization.lift
      (M := nonZeroDivisors A) (S := FractionRing A) (g := g) fun y => by
    have hy : algebraMap A B (y : A) ∈ nonZeroDivisors B :=
      non_divisors_flat y.property
    exact IsLocalization.map_units (FractionRing B)
      (⟨algebraMap A B (y : A), hy⟩ : nonZeroDivisors B)

/-- Transport an algebra structure across a ring equivalence. -/
@[reducible] noncomputable def RingEquiv.transportAlgebra
    {F X Y : Type*} [CommSemiring F] [CommRing X] [CommRing Y]
    [Algebra F X] (e : X ≃+* Y) : Algebra F Y :=
  RingHom.toAlgebra (e.toRingHom.comp (algebraMap F X))

/-- A ring equivalence is an algebra equivalence for the transported
algebra structure. -/
noncomputable def RingEquiv.alg_equiv_transport
    {F X Y : Type*} [CommSemiring F] [CommRing X] [CommRing Y]
    [Algebra F X] (e : X ≃+* Y) :
    letI : Algebra F Y := RingEquiv.transportAlgebra e
    X ≃ₐ[F] Y :=
  by
    letI : Algebra F Y := RingEquiv.transportAlgebra e
    exact AlgEquiv.ofRingEquiv (f := e) fun _ => rfl

variable {R S L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [FaithfulSMul R S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The canonical action of the completed base total quotient ring on the
total quotient ring of completed scalar extension. -/
@[reducible] noncomputable def adicTensorFraction
    (I : Ideal R) :
    Algebra (FractionRing (AdicCompletion I R))
      (FractionRing (AdicCompletion I R ⊗[R] S)) := by
  letI : Module.Flat R S := inferInstance
  letI : Module.Flat (AdicCompletion I R)
      (AdicCompletion I R ⊗[R] S) :=
    Module.Flat.baseChange R (AdicCompletion I R) S
  exact fractionRingFlat _ _

/-- The completed-base total quotient algebra structure on one factor
field, obtained by composing the semilocal equivalence with evaluation. -/
@[reducible] noncomputable def adicFractionAlgebra
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥)
    (P : (UniqueFactorizationMonoid.factors
      (I.map (algebraMap R S))).toFinset) :
    letI : Algebra (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)) :=
      adicTensorFraction I
    Algebra (FractionRing (AdicCompletion I R))
      ((factorHeightSpectrum
        (I.map (algebraMap R S)) P).adicCompletion L) := by
  letI : Algebra (FractionRing (AdicCompletion I R))
      (FractionRing (AdicCompletion I R ⊗[R] S)) :=
    adicTensorFraction I
  exact RingHom.toAlgebra <|
    ((Pi.evalRingHom
      (fun Q : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset =>
          (factorHeightSpectrum
            (I.map (algebraMap R S)) Q).adicCompletion L) P).comp
      (adicFractionCompletions
        (L := L) I hI).toRingHom).comp
      (algebraMap (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)))

/-- The product of completed fields with the standard coordinatewise
algebra structure over the completed-base total quotient ring. -/
@[reducible] noncomputable def piCompletionsFraction
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)) :=
      adicTensorFraction I
    Algebra (FractionRing (AdicCompletion I R))
      (∀ P : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum (I.map (algebraMap R S)) P).adicCompletion L) :=
  by
    letI : Algebra (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)) :=
      adicTensorFraction I
    letI (P : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset) :
        Algebra (FractionRing (AdicCompletion I R))
          ((factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletion L) :=
      adicFractionAlgebra I hI P
    exact Pi.algebra _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product and both transported algebra structures are expensive to synthesize.
set_option maxHeartbeats 1000000 in
/-- The semilocal total-quotient decomposition as an algebra equivalence
over the completed base total quotient ring. -/
noncomputable def adicPiCompletions
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)) :=
      adicTensorFraction I
    letI (P : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset) :
        Algebra (FractionRing (AdicCompletion I R))
          ((factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletion L) :=
      adicFractionAlgebra I hI P
    letI : Algebra (FractionRing (AdicCompletion I R))
        (∀ P : (UniqueFactorizationMonoid.factors
          (I.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletion L) :=
      piCompletionsFraction I hI
    FractionRing (AdicCompletion I R ⊗[R] S) ≃ₐ[
      FractionRing (AdicCompletion I R)]
      (∀ P : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum (I.map (algebraMap R S)) P).adicCompletion L) :=
  by
    letI : Algebra (FractionRing (AdicCompletion I R))
        (FractionRing (AdicCompletion I R ⊗[R] S)) :=
      adicTensorFraction I
    letI : Algebra (FractionRing (AdicCompletion I R))
        (∀ P : (UniqueFactorizationMonoid.factors
          (I.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (I.map (algebraMap R S)) P).adicCompletion L) :=
      piCompletionsFraction I hI
    exact AlgEquiv.ofRingEquiv
      (f := adicFractionCompletions
        (L := L) I hI) fun _ => by
          funext P
          rfl

variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The abstract prime-adic completion ring is the concrete completed
valuation integer ring. -/
noncomputable def adicRingIntegers
    [Ring.HasFiniteQuotients R] (P : HeightOneSpectrum R) :
    AdicCompletion P.asIdeal R ≃+* P.adicCompletionIntegers K := by
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  exact (adicCompletionPrime P).trans
    (adicRingEquiv (K := K) P)

/-- At a height-one prime, the total quotient ring of the abstract adic
completion is the concrete adic completion field. -/
noncomputable def adicFractionRing
    [Ring.HasFiniteQuotients R] (P : HeightOneSpectrum R) :
    FractionRing (AdicCompletion P.asIdeal R) ≃+* P.adicCompletion K := by
  exact IsFractionRing.ringEquivOfRingEquiv
    (adicRingIntegers (K := K) P)

/-- The completed integral tensor ring as an algebra over the concrete
lower completed valuation ring. -/
@[reducible] noncomputable def adicTensorAlgebra
    [Ring.HasFiniteQuotients R] (P : HeightOneSpectrum R) :
    Algebra (P.adicCompletionIntegers K)
      (AdicCompletion P.asIdeal R ⊗[R] S) :=
  RingHom.toAlgebra <|
    (algebraMap (AdicCompletion P.asIdeal R)
      (AdicCompletion P.asIdeal R ⊗[R] S)).comp
        (adicRingIntegers (K := K) P).symm.toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent integral factor type makes its ring structure expensive to synthesize.
set_option maxHeartbeats 1000000 in
/-- The concrete lower completed valuation ring acts on one upper
completed valuation integer ring through the integral semilocal
decomposition. -/
@[reducible] noncomputable def adicCompletionAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    Algebra (P.adicCompletionIntegers K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) := by
  letI : Algebra (P.adicCompletionIntegers K)
      (AdicCompletion P.asIdeal R ⊗[R] S) :=
    adicTensorAlgebra (S := S) (K := K) P
  let e₀ : AdicCompletion P.asIdeal R ⊗[R] S ≃+*
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    (adicTensorRing P.asIdeal).toRingEquiv.trans
      (completionPiIntegers (K := L)
        (P.asIdeal.map (algebraMap R S)) hP)
  exact RingHom.toAlgebra <|
    ((Pi.evalRingHom
      (fun Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset =>
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) Q).comp
      e₀.toRingHom).comp
      (algebraMap (P.adicCompletionIntegers K)
        (AdicCompletion P.asIdeal R ⊗[R] S))

set_option synthInstance.maxHeartbeats 100000 in
-- The standard Pi algebra synthesizes every dependent integral coordinate.
set_option maxHeartbeats 1000000 in
/-- The product of upper completed valuation integer rings with its
standard coordinatewise lower-integer-ring algebra structure. -/
@[reducible] noncomputable def piIntegersAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    Algebra (P.adicCompletionIntegers K)
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) := by
  letI (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
      Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  exact Pi.algebra _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent coordinate algebra structures make the integral Pi equivalence expensive.
set_option maxHeartbeats 1000000 in
/-- The integral completed scalar extension as an algebra equivalence over
the concrete lower completed valuation integer ring. -/
noncomputable def adicPiIntegers
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (P.adicCompletionIntegers K)
        (AdicCompletion P.asIdeal R ⊗[R] S) :=
      adicTensorAlgebra (S := S) (K := K) P
    letI : Algebra (P.adicCompletionIntegers K)
        (∀ Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
      piIntegersAlgebra (K := K) (L := L) P hP
    (AdicCompletion P.asIdeal R ⊗[R] S) ≃ₐ[P.adicCompletionIntegers K]
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) := by
  letI : Algebra (P.adicCompletionIntegers K)
      (AdicCompletion P.asIdeal R ⊗[R] S) :=
    adicTensorAlgebra (S := S) (K := K) P
  letI (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
      Algebra (P.adicCompletionIntegers K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra (P.adicCompletionIntegers K)
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletionIntegers L) :=
    piIntegersAlgebra (K := K) (L := L) P hP
  exact AlgEquiv.ofRingEquiv
    (f := (adicTensorRing P.asIdeal).toRingEquiv.trans
      (completionPiIntegers (K := L)
        (P.asIdeal.map (algebraMap R S)) hP)) fun _ => by
          funext Q
          change _ =
            (adicCompletionAlgebra
              (K := K) (L := L) P hP Q).algebraMap _
          rfl

set_option synthInstance.maxHeartbeats 100000 in
-- This formula unfolds the integral dependent product only at a pure tensor.
set_option maxHeartbeats 1000000 in
omit [FaithfulSMul R S] in
/-- The integral algebra equivalence has the expected pure-tensor formula. -/
@[simp]
theorem pi_integers_tmul
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (a : AdicCompletion P.asIdeal R) (s : S) :
    adicPiIntegers
        (K := K) (L := L) P hP (a ⊗ₜ[R] s) =
      completionPiIntegers (K := L)
        (P.asIdeal.map (algebraMap R S)) hP
        (adicBaseChange P.asIdeal
          (a • AdicCompletion.of P.asIdeal S s)) := by
  change completionPiIntegers (K := L)
      (P.asIdeal.map (algebraMap R S)) hP
      (adicTensorRing P.asIdeal (a ⊗ₜ[R] s)) = _
  rw [adic_alg_tmul]

/-- Transport the canonical total-quotient action from the abstract
completed base to the concrete completion field. -/
@[reducible] noncomputable def adicCompletionTensor
    [Ring.HasFiniteQuotients R] (P : HeightOneSpectrum R) :
    Algebra (P.adicCompletion K)
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) := by
  letI : Algebra (FractionRing (AdicCompletion P.asIdeal R))
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) :=
    adicTensorFraction P.asIdeal
  exact RingHom.toAlgebra <|
    (algebraMap (FractionRing (AdicCompletion P.asIdeal R))
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S))).comp
        (adicFractionRing (K := K) P).symm.toRingHom

set_option synthInstance.maxHeartbeats 100000 in
-- This transports a field action through the dependent product equivalence.
set_option maxHeartbeats 1000000 in
/-- The canonical algebra structure of one upper completed factor over the
concrete lower completion field. -/
@[reducible] noncomputable def adicFactorAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
    Algebra (P.adicCompletion K)
      ((factorHeightSpectrum
        (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  letI : Algebra (P.adicCompletion K)
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) :=
    adicCompletionTensor (S := S) (K := K) P
  exact RingHom.toAlgebra <|
    ((Pi.evalRingHom
      (fun Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset =>
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) Q).comp
      (adicFractionCompletions
        (L := L) P.asIdeal hP).toRingHom).comp
      (algebraMap (P.adicCompletion K)
        (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)))

set_option synthInstance.maxHeartbeats 100000 in
-- The standard Pi algebra must synthesize all dependent coordinate actions.
set_option maxHeartbeats 1000000 in
/-- The product of upper adic completion fields as an algebra over the
concrete lower adic completion field. -/
@[reducible] noncomputable def piCompletionsAlgebra
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    Algebra (P.adicCompletion K)
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) := by
  letI : Algebra (P.adicCompletion K)
      (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) :=
    adicCompletionTensor (S := S) (K := K) P
  letI (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap R S))).toFinset) :
      Algebra (P.adicCompletion K)
        ((factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  exact Pi.algebra _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The prime-field specialization combines both transported algebra structures.
set_option maxHeartbeats 1000000 in
/-- For a prime-adic completion, the total quotient decomposition is an
algebra equivalence over the concrete completed base field. -/
noncomputable def fractionPiCompletions
    [Ring.HasFiniteQuotients R] [Ring.HasFiniteQuotients S]
    (P : HeightOneSpectrum R)
    (hP : P.asIdeal.map (algebraMap R S) ≠ ⊥) :
    letI : Algebra (P.adicCompletion K)
        (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) :=
      adicCompletionTensor (S := S) (K := K) P
    letI (Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset) :
        Algebra (P.adicCompletion K)
          ((factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    letI : Algebra (P.adicCompletion K)
        (∀ Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      piCompletionsAlgebra (K := K) (L := L) P hP
    FractionRing (AdicCompletion P.asIdeal R ⊗[R] S) ≃ₐ[P.adicCompletion K]
      (∀ Q : (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum
          (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
  by
    letI : Algebra (P.adicCompletion K)
        (FractionRing (AdicCompletion P.asIdeal R ⊗[R] S)) :=
      adicCompletionTensor (S := S) (K := K) P
    letI : Algebra (P.adicCompletion K)
        (∀ Q : (UniqueFactorizationMonoid.factors
          (P.asIdeal.map (algebraMap R S))).toFinset,
          (factorHeightSpectrum
            (P.asIdeal.map (algebraMap R S)) Q).adicCompletion L) :=
      piCompletionsAlgebra (K := K) (L := L) P hP
    exact AlgEquiv.ofRingEquiv
      (f := adicFractionCompletions
        (L := L) P.asIdeal hP) fun _ => by
          funext Q
          rfl

end

end Towers.NumberTheory.Milne
