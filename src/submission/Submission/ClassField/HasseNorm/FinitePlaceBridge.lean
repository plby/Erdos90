import Submission.ClassField.HasseNorm.IdeleDecomposition
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Finite places above a base prime

The idèle coordinates are indexed by all height-one primes of the upper
integer ring, whereas the semilocal completion and norm constructions index
the primes above a fixed base prime by the prime factors of its extended
ideal.  This file identifies those two finite index types.  It is the
reindexing needed before the finite part of `I_{L,T}` can be written as a
product of completion-product representations.
-/

namespace Submission.CField.HNorm

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The height-one primes of `O_L` contracting to `P`. -/
abbrev FinitePrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {Q : HeightOneSpectrum (NumberField.RingOfIntegers L) //
    Q.under (NumberField.RingOfIntegers K) = P}

/-- A prime factor of the extended ideal determines its literal upper
height-one prime, together with the contraction equality. -/
noncomputable def upperFactorAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P → FinitePrimesAbove (K := K) (L := L) P :=
  fun Q => ⟨upperPrime (K := K) (L := L) P Q,
    upperPrime_under (K := K) (L := L) P Q⟩

omit [FiniteDimensional K L] in
/-- Distinct prime factors give distinct height-one primes. -/
theorem upper_factor_injective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Injective
      (upperFactorAbove (K := K) (L := L) P) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  have h' := congrArg
    (fun Q : FinitePrimesAbove (K := K) (L := L) P => Q.1.asIdeal) h
  exact h'

omit [FiniteDimensional K L] in
/-- Every upper height-one prime above `P` occurs among the prime factors of
the extended ideal `P O_L`. -/
theorem upper_factor_surjective
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective
      (upperFactorAbove (K := K) (L := L) P) := by
  intro Q
  let I : Ideal (NumberField.RingOfIntegers L) :=
    P.asIdeal.map (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L))
  have hI : I ≠ 0 := Ideal.map_ne_bot_of_ne_bot P.ne_bot
  have hQtop : Q.1.asIdeal ≠ ⊤ := Q.1.isPrime.ne_top
  letI : P.asIdeal.IsMaximal := P.isMaximal
  have hlies : Q.1.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal Q.2).symm
  have hdiv : Q.1.asIdeal ∣ I :=
    (Ideal.liesOver_iff_dvd_map hQtop).mp hlies
  have hirr : Irreducible Q.1.asIdeal :=
    (Ideal.prime_of_isPrime Q.1.ne_bot Q.1.isPrime).irreducible
  obtain ⟨q, hqmem, hQq⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI hirr hdiv
  let q' : UpperPrimeFactors (K := K) (L := L) P :=
    ⟨q, Multiset.mem_toFinset.mpr hqmem⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  exact associated_iff_eq.mp hQq.symm

/-- Prime factors of `P O_L` are exactly the literal upper primes
contracting to `P`. -/
noncomputable def upperPrimesAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P ≃
      FinitePrimesAbove (K := K) (L := L) P :=
  Equiv.ofBijective
    (upperFactorAbove (K := K) (L := L) P)
    ⟨upper_factor_injective (K := K) (L := L) P,
      upper_factor_surjective (K := K) (L := L) P⟩

omit [FiniteDimensional K L] in
@[simp]
theorem upper_primes_above
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    (upperPrimesAbove (K := K) (L := L) P Q).1 =
      upperPrime (K := K) (L := L) P Q :=
  rfl

section Galois

variable [IsGalois K L]

local instance finitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

/-- The centered upper prime of a normalized completion place above `P`. -/
noncomputable def completionPlaceAbove
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    FinitePrimesAbove (K := K) (L := L) P := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  refine ⟨Q, ?_⟩
  apply HeightOneSpectrum.ext
  exact (nonarchimedean_spectrum_lies
    P w.1 w.2 hw hwna).over.symm

/-- Passing from a normalized finite completion place to its centered upper
prime is equivariant for Galois conjugation. -/
theorem place_above_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    (completionPlaceAbove (K := K) (L := L) P
        (sigma • w)).1 =
      sigma • (completionPlaceAbove
        (K := K) (L := L) P w).1 := by
  letI := finitePrimeAction (K := K) (L := L)
  apply HeightOneSpectrum.ext
  rw [prime_action_ideal]
  exact centered_smul_ideal w.1
    (absolute_extension_nontrivial (FinitePlace.mk P).val w)
    (absolute_extension_nonarchimedean (FinitePlace.mk P).val w)
    sigma

/-- The selected completion model is centered at precisely the prescribed
upper prime factor. -/
theorem hasse_model_center
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    let model := hasseCompletionModel K L P Q
    let w := model.place
    let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
    let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
    nonarchimedeanHeightSpectrum w.1 hw hwna =
      upperPrime (K := K) (L := L) P Q := by
  dsimp only
  let model := hasseCompletionModel K L P Q
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

/-- A normalized finite completion place determines the corresponding prime
factor of `P O_L`. -/
noncomputable def placeUpperFactor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val →
      UpperPrimeFactors (K := K) (L := L) P :=
  fun w => (upperPrimesAbove
    (K := K) (L := L) P).symm
      (completionPlaceAbove (K := K) (L := L) P w)

/-- The prime factor indexing the Hasse completion model recovers that
model's completion place. -/
noncomputable def upperCompletionPlace
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    UpperPrimeFactors (K := K) (L := L) P →
      CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
  fun Q => (hasseCompletionModel K L P Q).place

/-- Normalized completion places above `P` are exactly the prime factors of
`P O_L`.  The normalization on the base field removes the usual ambiguity
of equivalent absolute values. -/
noncomputable def placesAboveFactors
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val ≃
      UpperPrimeFactors (K := K) (L := L) P where
  toFun := placeUpperFactor (K := K) (L := L) P
  invFun := upperCompletionPlace (K := K) (L := L) P
  left_inv := by
    intro w
    let Q := placeUpperFactor (K := K) (L := L) P w
    let model := hasseCompletionModel K L P Q
    let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
    let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
    have hcenterW :
        nonarchimedeanHeightSpectrum w.1 hw hwna =
          upperPrime (K := K) (L := L) P Q := by
      have hfiber := (upperPrimesAbove
        (K := K) (L := L) P).apply_symm_apply
          (completionPlaceAbove (K := K) (L := L) P w)
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
    apply (upperPrimesAbove
      (K := K) (L := L) P).injective
    change (upperPrimesAbove
        (K := K) (L := L) P)
          ((upperPrimesAbove
            (K := K) (L := L) P).symm
              (completionPlaceAbove (K := K) (L := L) P
                (upperCompletionPlace (K := K) (L := L) P Q))) =
      (upperPrimesAbove (K := K) (L := L) P) Q
    rw [(upperPrimesAbove
      (K := K) (L := L) P).apply_symm_apply]
    apply Subtype.ext
    exact hasse_model_center
      (K := K) (L := L) P Q

/-- The completion attached to a normalized absolute value above `P` is the
prime-adic completion indexed by the corresponding factor of `P O_L`. -/
noncomputable def completionPlaceAdic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    w.1.Completion ≃+*
      (upperPrime (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w)).adicCompletion L := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q := by
    have hfiber := (upperPrimesAbove
      (K := K) (L := L) P).apply_symm_apply
        (completionPlaceAbove (K := K) (L := L) P w)
    exact congrArg Subtype.val hfiber |>.symm
  exact ((completionRing
      (place_centered_prime w.1 hw hwna)).trans
        (placeCompletionAdic q)).trans
    (RingEquiv.cast hq)

private theorem adic_completion_embedding
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

/-- Multiplicative form of `completionPlaceAdic`. -/
noncomputable def placeUnitsAdic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    w.1.Completionˣ ≃*
      ((upperPrime (K := K) (L := L) P
        (placeUpperFactor (K := K) (L := L) P w)).adicCompletion L)ˣ :=
  Units.mapEquiv (completionPlaceAdic
    (K := K) (L := L) P w).toMulEquiv

/-- Reindex the whole finite completion product by the prime factors of the
extended base ideal and identify each absolute-value completion with its
prime-adic completion. -/
noncomputable def ringAdicFactors
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val,
        CompletionFamilyAbove (L := L) (FinitePlace.mk P).val w) ≃+*
      (∀ Q : UpperPrimeFactors (K := K) (L := L) P,
        (upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
  (RingEquiv.piCongrRight fun w =>
      completionPlaceAdic (K := K) (L := L) P w).trans
    (RingEquiv.piCongrLeft
      (fun Q : UpperPrimeFactors (K := K) (L := L) P =>
        (upperPrime (K := K) (L := L) P Q).adicCompletion L)
      (placesAboveFactors
        (K := K) (L := L) P))

/-- Multiplicative reindexing of all completed finite-place factors above
`P`. -/
noncomputable def unitsAdicFactors
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val,
        CompletionFamilyAbove (L := L) (FinitePlace.mk P).val w)ˣ ≃*
      (∀ Q : UpperPrimeFactors (K := K) (L := L) P,
        (upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ :=
  Units.mapEquiv (ringAdicFactors
    (K := K) (L := L) P).toMulEquiv

/-- Coordinatewise version of the finite completion-product reindexing,
matching the actual finite-idèle coordinate type. -/
noncomputable def piAdicFactor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val,
        CompletionFamilyAbove (L := L) (FinitePlace.mk P).val w)ˣ ≃*
      (∀ Q : UpperPrimeFactors (K := K) (L := L) P,
        ((upperPrime (K := K) (L := L) P Q).adicCompletion L)ˣ) :=
  (unitsAdicFactors
    (K := K) (L := L) P).trans MulEquiv.piUnits

end Galois

end

end Submission.CField.HNorm
