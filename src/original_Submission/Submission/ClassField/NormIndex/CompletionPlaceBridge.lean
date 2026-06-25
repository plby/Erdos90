import Submission.ClassField.NormIndex.CompletionProductNorm
import Submission.ClassField.NormIndex.IdeleExtensionMap

/-!
# Finite completion places and prime-adic factors

The norm identity on products of absolute-value completions is indexed by
normalized extensions of a base absolute value.  Finite idèles instead use
literal height-one primes and their prime-adic completions.  This file gives
the elementary correspondence between those two models, in the source order
needed for Chapter VII.
-/

namespace Submission.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

/-- The centered upper prime of a normalized completion place above `P`. -/
noncomputable def placeAboveBase
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    PrimesAboveBase (K := K) (L := L) P := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  refine ⟨Q, ?_⟩
  apply HeightOneSpectrum.ext
  exact (nonarchimedean_spectrum_lies
    P w.1 w.2 hw hwna).over.symm

/-- Centering a normalized finite completion place is equivariant for
Galois conjugation. -/
theorem above_base_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    (placeAboveBase (K := K) (L := L) P
        (sigma • w)).1 =
      sigma • (placeAboveBase
        (K := K) (L := L) P w).1 := by
  letI := finitePrimeAction (K := K) (L := L)
  apply HeightOneSpectrum.ext
  rw [prime_action_ideal]
  exact centered_smul_ideal w.1
    (absolute_extension_nontrivial (FinitePlace.mk P).val w)
    (absolute_extension_nonarchimedean (FinitePlace.mk P).val w)
    sigma

/-- A normalized absolute-value completion above `P` centered at a specified
upper prime factor. -/
structure PrimeCompletionModel
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) where
  place : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val
  isEquiv_upper : place.1.IsEquiv
    (FinitePlace.mk (upperPrime (K := K) (L := L) P Q)).val

/-- Choose the normalized completion place centered at a prescribed upper
prime. -/
noncomputable def primeCompletionModel
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    PrimeCompletionModel K L P Q := by
  classical
  let v := (FinitePlace.mk P).val
  let q₀ := upperPrime (K := K) (L := L) P Q
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  letI : Nonempty W :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  let w : W := Classical.choice (inferInstance : Nonempty W)
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : q.asIdeal.IsPrime := q.isPrime
  letI : q.asIdeal.LiesOver P.asIdeal :=
    nonarchimedean_spectrum_lies P w.1 w.2 hw hwna
  letI : q₀.asIdeal.IsPrime := q₀.isPrime
  letI : q₀.asIdeal.LiesOver P.asIdeal := ⟨by
    exact congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q) |>.symm⟩
  letI : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L
  let hexists := Ideal.exists_smul_eq_of_isGaloisGroup
    P.asIdeal q.asIdeal q₀.asIdeal Gal(L/K)
  let sigma := Classical.choose hexists
  have hsigma := Classical.choose_spec hexists
  let w₀ : W := sigma • w
  have hw₀ : w₀.1.IsNontrivial :=
    absolute_extension_nontrivial v w₀
  have hw₀na : IsNonarchimedean w₀.1 :=
    absolute_extension_nonarchimedean v w₀
  have hcenter :
      nonarchimedeanHeightSpectrum w₀.1 hw₀ hw₀na = q₀ := by
    apply HeightOneSpectrum.ext
    change (nonarchimedeanHeightSpectrum
      (sigma • w.1) hw₀ hw₀na).asIdeal = q₀.asIdeal
    rw [centered_smul_ideal w.1 hw hwna sigma, hsigma]
  refine ⟨w₀, ?_⟩
  have h := place_centered_prime w₀.1 hw₀ hw₀na
  rwa [hcenter] at h

/-- The selected normalized completion model is centered at its prescribed
upper prime. -/
theorem model_center_upper
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    let model := primeCompletionModel K L P Q
    let w := model.place
    let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
    let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
    nonarchimedeanHeightSpectrum w.1 hw hwna =
      upperPrime (K := K) (L := L) P Q := by
  dsimp only
  let model := primeCompletionModel K L P Q
  let w := model.place
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  apply HeightOneSpectrum.ext
  ext x
  change x ∈ nonarchimedeanPrimeIdeal w.1 hwna ↔
    x ∈ (upperPrime (K := K) (L := L) P Q).asIdeal
  rw [nonarchimedean_prime_ideal,
    ← FinitePlace.norm_lt_one_iff_mem L
      (upperPrime (K := K) (L := L) P Q) x]
  exact model.isEquiv_upper.lt_one_iff

/-- The prime factor centered at a normalized completion place. -/
noncomputable def placeUpperFactor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val →
      UpperPrimeFactors (K := K) (L := L) P :=
  fun w => (upperAboveBase
    (K := K) (L := L) P).symm
      (placeAboveBase (K := K) (L := L) P w)

/-- The normalized completion place selected for an upper prime factor. -/
noncomputable def upperCompletionPlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P →
      CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
  fun Q => (primeCompletionModel K L P Q).place

/-- Normalized completion places above `P` are exactly the factors of
`P O_L`. -/
noncomputable def placesAboveFactors
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val ≃
      UpperPrimeFactors (K := K) (L := L) P where
  toFun := placeUpperFactor (K := K) (L := L) P
  invFun := upperCompletionPlace (K := K) (L := L) P
  left_inv := by
    intro w
    let Q := placeUpperFactor (K := K) (L := L) P w
    let model := primeCompletionModel K L P Q
    let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
    let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
    have hcenterW :
        nonarchimedeanHeightSpectrum w.1 hw hwna =
          upperPrime (K := K) (L := L) P Q := by
      have hfiber := (upperAboveBase
        (K := K) (L := L) P).apply_symm_apply
          (placeAboveBase (K := K) (L := L) P w)
      exact congrArg Subtype.val hfiber |>.symm
    have hmodel : model.place.1.IsEquiv
        (FinitePlace.mk (upperPrime (K := K) (L := L) P Q)).val :=
      model.isEquiv_upper
    have hwfinite : w.1.IsEquiv
        (FinitePlace.mk
          (nonarchimedeanHeightSpectrum w.1 hw hwna)).val :=
      place_centered_prime w.1 hw hwna
    rw [hcenterW] at hwfinite
    apply Subtype.ext
    exact absolute_value_lies
      (v := (FinitePlace.mk P).val) model.place.1 w.1
        model.place.2 w.2 (hmodel.trans hwfinite.symm)
  right_inv := by
    intro Q
    apply (upperAboveBase
      (K := K) (L := L) P).injective
    change (upperAboveBase
        (K := K) (L := L) P)
          ((upperAboveBase
            (K := K) (L := L) P).symm
              (placeAboveBase (K := K) (L := L) P
                (upperCompletionPlace
                  (K := K) (L := L) P Q))) =
      (upperAboveBase (K := K) (L := L) P) Q
    rw [(upperAboveBase
      (K := K) (L := L) P).apply_symm_apply]
    apply Subtype.ext
    exact model_center_upper
      (K := K) (L := L) P Q

@[simp]
theorem place_upper_symm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    placeUpperFactor (K := K) (L := L) P
        ((placesAboveFactors
          (K := K) (L := L) P).symm Q) = Q :=
  (placesAboveFactors
    (K := K) (L := L) P).apply_symm_apply Q

/-- The completion attached to a normalized finite place is the prime-adic
completion at its centered upper prime factor. -/
noncomputable def completionPlaceAdic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    w.1.Completion ≃+*
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletion L := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q := by
    have hfiber := (upperAboveBase
      (K := K) (L := L) P).apply_symm_apply
        (placeAboveBase (K := K) (L := L) P w)
    exact congrArg Subtype.val hfiber |>.symm
  exact ((completionRing
      (place_centered_prime w.1 hw hwna)).trans
        (placeCompletionAdic q)).trans
    (RingEquiv.cast hq)

theorem adic_completion_embedding
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') (x : L) :
    RingEquiv.cast (R := fun v => v.adicCompletion L) h
        (FinitePlace.embedding Q x) =
      FinitePlace.embedding Q' x := by
  subst Q'
  rfl

/-- The finite completion/adic-completion comparison extends the identity
embedding of the global field. -/
@[simp]
theorem place_adic_embedding
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : L) :
    completionPlaceAdic (K := K) (L := L) P w
        (completionEmbedding w.1 x) =
      FinitePlace.embedding
        (upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w)) x := by
  unfold completionPlaceAdic
  dsimp only [RingEquiv.trans_apply]
  rw [completion_ring_embedding,
    finite_place_adic]
  apply adic_completion_embedding

/-- Multiplicative form of the finite completion/adic-completion
comparison. -/
noncomputable def placeUnitsAdic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    w.1.Completionˣ ≃*
      ((upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w)).adicCompletion L)ˣ :=
  Units.mapEquiv (completionPlaceAdic
    (K := K) (L := L) P w).toMulEquiv

end

end Submission.CField.NIndex
