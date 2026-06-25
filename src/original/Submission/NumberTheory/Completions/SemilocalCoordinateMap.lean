import Submission.NumberTheory.Completions.SemilocalCompletionAssembly

/-!
# Coordinates of the semilocal completion map

The product decomposition of an ideal-adic completion sends a global ring
element to its canonical image in every completed prime factor.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain

noncomputable section

universe u

variable {S L : Type u}
  [CommRing S] [IsDedekindDomain S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- The CRT decomposition into completions at prime powers preserves the
canonical image of a global element. -/
theorem adic_completion_pi
    (I : Ideal S) (hI : I ≠ ⊥) (s : S) :
    adicCompletionPi I hI (AdicCompletion.of I S s) =
      fun P : (UniqueFactorizationMonoid.factors I).toFinset => AdicCompletion.of
        ((P : Ideal S) ^ Multiset.count (P : Ideal S)
          (UniqueFactorizationMonoid.factors I)) S s := by
  classical
  let F := (UniqueFactorizationMonoid.factors I).toFinset
  let J : F → Ideal S := fun P =>
    (P : Ideal S) ^ Multiset.count (P : Ideal S)
      (UniqueFactorizationMonoid.factors I)
  have hprime (P : F) : Prime (P : Ideal S) :=
    UniqueFactorizationMonoid.prime_of_factor (P : Ideal S)
      (Multiset.mem_toFinset.mp P.prop)
  have hcoprime : Pairwise (fun P P' => IsCoprime (J P) (J P')) := by
    intro P P' hPP'
    apply IsCoprime.pow
    exact Ideal.isCoprime_iff_sup_eq.mpr <|
      IsMaximal.coprime_of_ne
        (IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P)) (hprime P).ne_zero)
        (IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P')) (hprime P').ne_zero)
        (Subtype.coe_injective.ne hPP')
  have hprod : ∏ P : F, J P = I := by
    calc
      (∏ P : F, J P) =
          ∏ P ∈ (UniqueFactorizationMonoid.factors I).toFinset,
            P ^ Multiset.count P (UniqueFactorizationMonoid.factors I) := by
        exact (UniqueFactorizationMonoid.factors I).toFinset.prod_coe_sort
          (fun P => P ^ Multiset.count P
            (UniqueFactorizationMonoid.factors I))
      _ = ((UniqueFactorizationMonoid.factors I).map fun P => P).prod :=
        (Finset.prod_multiset_map_count
          (UniqueFactorizationMonoid.factors I) id).symm
      _ = (UniqueFactorizationMonoid.factors I).prod := by
        rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp
        (UniqueFactorizationMonoid.factors_prod hI)
  let e := chineseRemainderRing J hcoprime
  have cast_of (I' I'' : Ideal S) (h : I' = I'') :
      (RingEquiv.cast
        (R := fun J : Ideal S => AdicCompletion J S) h).symm
          (AdicCompletion.of I'' S s) = AdicCompletion.of I' S s := by
    subst I''
    rfl
  have hcast : (RingEquiv.cast
      (R := fun J : Ideal S => AdicCompletion J S) hprod).symm
        (AdicCompletion.of I S s) =
      AdicCompletion.of (∏ P : F, J P) S s :=
    cast_of (∏ P : F, J P) I hprod
  change ((RingEquiv.cast
      (R := fun J : Ideal S => AdicCompletion J S) hprod).symm.trans e)
      (AdicCompletion.of I S s) = _
  rw [RingEquiv.trans_apply, hcast,
    chinese_remainder_ring]

/-- Passing from prime-power completions to prime completions preserves the
canonical image of a global element. -/
theorem adic_pi_factors
    (I : Ideal S) (hI : I ≠ ⊥) (s : S) :
    adicPiFactors I hI (AdicCompletion.of I S s) =
      fun P : (UniqueFactorizationMonoid.factors I).toFinset =>
        AdicCompletion.of (P : Ideal S) S s := by
  rw [adicPiFactors, RingEquiv.trans_apply,
    adic_completion_pi I hI s]
  funext P
  change adicPowRing (P : Ideal S)
      (Multiset.count (P : Ideal S) (UniqueFactorizationMonoid.factors I))
      (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.prop))
      (AdicCompletion.of
        ((P : Ideal S) ^ Multiset.count (P : Ideal S)
          (UniqueFactorizationMonoid.factors I)) S s) = _
  exact adic_completion_ring _ _ _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The final dependent product contains concrete valuation-subring factors.
set_option maxHeartbeats 1000000 in
/-- The semilocal completion equivalence preserves the diagonal map from the
original ring. -/
theorem completion_pi_integers
    [Ring.HasFiniteQuotients S]
    (I : Ideal S) (hI : I ≠ ⊥) (s : S) :
    completionPiIntegers (K := L) I hI
        (AdicCompletion.of I S s) =
      fun Q => algebraMap S
        ((factorHeightSpectrum I Q).adicCompletionIntegers L) s := by
  rw [completionPiIntegers, RingEquiv.trans_apply,
    adic_pi_factors I hI s]
  funext Q
  letI : Finite (S ⧸ (factorHeightSpectrum I Q).asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (factorHeightSpectrum I Q).ne_bot
  change adicRingEquiv (K := L)
      (factorHeightSpectrum I Q)
      (adicCompletionPrime (factorHeightSpectrum I Q)
        (AdicCompletion.of (factorHeightSpectrum I Q).asIdeal S s)) = _
  rw [adic_completion_equiv,
    adic_ring_equiv,
    adic_integers_algebra]

/-- Coordinate form of `completion_pi_integers`. -/
theorem adic_pi_integers
    [Ring.HasFiniteQuotients S]
    (I : Ideal S) (hI : I ≠ ⊥) (s : S)
    (Q : (UniqueFactorizationMonoid.factors I).toFinset) :
    completionPiIntegers (K := L) I hI
        (AdicCompletion.of I S s) Q =
      algebraMap S
        ((factorHeightSpectrum I Q).adicCompletionIntegers L) s :=
  congrFun (completion_pi_integers (L := L) I hI s) Q

end


end Submission.NumberTheory.Milne
