import Submission.ClassField.KummerTheory.KummerCorrespondenceProof
import Submission.ClassField.KummerNormIndex.FinitePrimePart
import Submission.ClassField.KummerNormIndex.PlaceUnits
import Submission.ClassField.BrauerLocalization.IdeleIdealSupport

/-!
# Choosing the places in the algebraic second-inequality proof

Before Lemma VII.6.2, Milne enlarges a finite set of places so that it
contains all infinite places, all divisors of `p`, prime-ideal generators of
the class group, and the finite supports of the Kummer radicands for `L`.
This file carries out that choice for an arbitrary finite subgroup of power
classes.  It is the arithmetic input needed to construct
`M = K[U(S)^(1/p)]` rather than assume that construction as auxiliary data.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.KTheory
open Submission.CField.NIndex

noncomputable section

universe u

/-- The finite places at which a nonzero field element has nontrivial
normalized absolute value, regarded as number-field places. -/
noncomputable def finiteSupportPlaces
    (K : Type u) [Field K] [NumberField K] (x : Kˣ) :
    Finset (NumberFieldPlace K) := by
  have hfinite :
      {w : FinitePlace K | w (x : K) ≠ 1}.Finite := by
    simpa only [Function.HasFiniteMulSupport, Function.mulSupport] using
      (FinitePlace.hasFiniteMulSupport x.ne_zero)
  exact (hfinite.image fun w ↦
    (Sum.inl w.maximalIdeal : NumberFieldPlace K)).toFinset

theorem support_places_normalized
    (K : Type u) [Field K] [NumberField K] (x : Kˣ)
    (P : FinitePrime K)
    (hP : normalizedPlaceValue K (Sum.inl P) (x : K) ≠ 1) :
    (Sum.inl P : NumberFieldPlace K) ∈ finiteSupportPlaces K x := by
  classical
  unfold finiteSupportPlaces
  rw [Set.Finite.mem_toFinset]
  let w : FinitePlace K := FinitePlace.equivHeightOneSpectrum.symm P
  refine ⟨w, ?_, ?_⟩
  · simpa only [normalizedPlaceValue,
      FinitePlace.equivHeightOneSpectrum_symm_apply] using hP
  · exact congrArg Sum.inl
      (FinitePlace.equivHeightOneSpectrum.apply_symm_apply P)

/-- At a finite place, normalized absolute value one is equivalent in the
needed direction to multiplicative valuation one. -/
private theorem prime_valuation_normalized
    (K : Type u) [Field K] [NumberField K]
    (P : FinitePrime K) {x : K}
    (hx : normalizedPlaceValue K (Sum.inl P) x = 1) :
    P.valuation K x = 1 := by
  have hnorm : ‖FinitePlace.embedding P x‖ = 1 := by
    simpa only [normalizedPlaceValue,
      FinitePlace.equivHeightOneSpectrum_symm_apply] using hx
  rw [FinitePlace.norm_embedding'] at hnorm
  have h' :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero P)
          (P.valuation K x) = 1 := by
    exact_mod_cast hnorm
  exact (WithZeroMulInt.toNNReal_eq_one_iff
    (P.valuation K x)
    (HeightOneSpectrum.absNorm_ne_zero P)
    (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal P))).mp h'

/-- If a chosen set of places contains the finite support of `x`, then `x`
is an `S`-unit. -/
theorem s_places_subset
    (K : Type u) [Field K] [NumberField K]
    (x : Kˣ) (S : Finset (NumberFieldPlace K))
    (hsub : finiteSupportPlaces K x ⊆ S) :
    x ∈ Set.unit (finitePrimePart K S) K := by
  intro P hP
  apply prime_valuation_normalized K P
  by_contra hne
  apply hP
  exact hsub (support_places_normalized K x P hne)

/-- Containing ideal-class generators is preserved when the set of places
is enlarged. -/
theorem CIGenera.mono
    (K : Type u) [Field K] [NumberField K]
    {S T : Finset (NumberFieldPlace K)}
    (hS : CIGenera K S) (hST : S ⊆ T) :
    CIGenera K T := by
  unfold CIGenera at hS ⊢
  apply top_unique
  rw [← hS]
  apply Subgroup.map_mono
  apply Subgroup.closure_mono
  rintro I ⟨P, hPS, rfl⟩
  exact ⟨P, hST hPS, rfl⟩

/-- The four properties imposed on `S` immediately before Lemma VII.6.2,
with the finitely many radicands represented by a finite subgroup of
`Kˣ / Kˣᵖ`. -/
structure SecondInequalityData
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (B : PCSubgro K p) where
  S : Finset (NumberFieldPlace K)
  containsInfinite : ContainsAllPlaces K S
  containsDivisors : ∀ v : NumberFieldPlace K,
    normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S
  containsClassGenerators : CIGenera K S
  representativesSUnits : ∀ b : B.carrier,
    powerClassRepresentative K p b.1 ∈ Set.unit (finitePrimePart K S) K

/-- The finite set of places satisfying Milne's conditions (a)--(d)
exists for every finite family of Kummer power classes. -/
theorem second_inequality_places
    (p : ℕ) (hp : p.Prime)
    (K : Type u) [Field K] [NumberField K]
    (B : PCSubgro K p) :
    Nonempty (SecondInequalityData p K B) := by
  classical
  obtain ⟨admissible⟩ :=
    Submission.CField.BLoc.admissiblePlacesBridge K K
  obtain ⟨classPlaces, hclass, _hcontractions⟩ :=
    admissible.containsClassGenerators
  letI : Fintype B.carrier := B.finite_carrier.fintype
  let infinitePlaces : Finset (NumberFieldPlace K) :=
    Finset.univ.image Sum.inr
  have hpK : (p : K) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  let pUnit : Kˣ := Units.mk0 (p : K) hpK
  let representativeSupport : Finset (NumberFieldPlace K) :=
    Finset.univ.biUnion fun b : B.carrier ↦
      finiteSupportPlaces K (powerClassRepresentative K p b.1)
  let S : Finset (NumberFieldPlace K) :=
    classPlaces ∪ infinitePlaces ∪ finiteSupportPlaces K pUnit ∪
      representativeSupport
  refine ⟨⟨S, ?_, ?_, ?_, ?_⟩⟩
  · intro v
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  · intro v hv
    cases v with
    | inl P =>
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact support_places_normalized
          K pUnit P (by simpa [pUnit] using hv)
    | inr v =>
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  · apply CIGenera.mono K hclass
    intro v hv
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
  · intro b
    apply s_places_subset
    intro v hv
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hv⟩

end

end Submission.CField.KNIndex
