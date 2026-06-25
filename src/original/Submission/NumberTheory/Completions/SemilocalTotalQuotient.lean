import Submission.NumberTheory.Completions.AdicBaseChange
import Submission.NumberTheory.Completions.SemilocalCompletionAssembly
import Mathlib.Algebra.Regular.Pi
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Pi

/-!
# Total quotient rings of semilocal completions

The total quotient ring of a finite product of domains is the product of
their fraction fields.  Applying this to the semilocal completed integral
lattice identifies the total quotient ring of completed scalar extension
with the product of the corresponding completed fields.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain
open scoped TensorProduct

noncomputable section

universe u

/-- A product of fraction rings is the total quotient ring of the product.
The statement does not require the index type to be finite. -/
theorem fraction_ring_pi
    {ι : Type*} (A F : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, CommRing (F i)]
    [∀ i, Algebra (A i) (F i)]
    [∀ i, IsFractionRing (A i) (F i)] :
    IsFractionRing (∀ i, A i) (∀ i, F i) := by
  let M : ∀ i, Submonoid (A i) := fun i => nonZeroDivisors (A i)
  have hM : nonZeroDivisors (∀ i, A i) = Submonoid.pi Set.univ M := by
    ext x
    rw [Submonoid.mem_pi]
    simp only [Set.mem_univ, true_implies]
    dsimp only [M]
    simpa only [← isRegular_iff_mem_nonZeroDivisors] using
      (Pi.isRegular_iff (a := x))
  change IsLocalization (nonZeroDivisors (∀ i, A i)) (∀ i, F i)
  rw [hM]
  infer_instance

variable {R S L : Type u}
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Field L] [Algebra S L] [IsFractionRing S L]

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product of completion fields makes typeclass search expensive.
set_option maxHeartbeats 1000000 in
/-- The completed scalar extension has total quotient ring equal to the
product of the completed fields at the prime factors of the extended
ideal. -/
noncomputable def adicFractionCompletions
    [Ring.HasFiniteQuotients S]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊥) :
    FractionRing (AdicCompletion I R ⊗[R] S) ≃+*
      (∀ P : (UniqueFactorizationMonoid.factors
        (I.map (algebraMap R S))).toFinset,
        (factorHeightSpectrum (I.map (algebraMap R S)) P).adicCompletion L) := by
  let J : Ideal S := I.map (algebraMap R S)
  let e : AdicCompletion I R ⊗[R] S ≃+*
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletionIntegers L) :=
    (adicTensorRing I).toRingEquiv.trans
      (completionPiIntegers (K := L) J hI)
  letI : IsFractionRing
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletionIntegers L)
      (∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
        (factorHeightSpectrum J P).adicCompletion L) :=
    fraction_ring_pi
      (fun P : (UniqueFactorizationMonoid.factors J).toFinset =>
        (factorHeightSpectrum J P).adicCompletionIntegers L)
      (fun P : (UniqueFactorizationMonoid.factors J).toFinset =>
        (factorHeightSpectrum J P).adicCompletion L)
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing (AdicCompletion I R ⊗[R] S))
    (L := ∀ P : (UniqueFactorizationMonoid.factors J).toFinset,
      (factorHeightSpectrum J P).adicCompletion L)
    e

end

end Submission.NumberTheory.Milne
