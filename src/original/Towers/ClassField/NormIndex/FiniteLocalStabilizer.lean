import Towers.ClassField.NormIndex.CompletionPlaceComparison

/-!
# Finite local norms as stabilizer products

This file is the centered local step in the finite-idèle norm calculation.
After identifying an absolute-value completion with the prime-adic completion
at its centered upper prime, the local field norm is the product of the
decomposition-stabilizer action.
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteLocalNormNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteLocalNormCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance finiteLocalNormStabilizerFintype
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Fintype (CompletionPlaceStabilizer (FinitePlace.mk P).val w) :=
  Fintype.ofFinite (CompletionPlaceStabilizer (FinitePlace.mk P).val w)

/-- A stabilizer element fixes the upper prime centered at its completion
place.  The inverse appears because coordinate actions read their source at
`sigma⁻¹ • q`. -/
theorem centered_upper_stabilizer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : CompletionPlaceStabilizer (FinitePlace.mk P).val w) :
    letI := finitePrimeAction (K := K) (L := L)
    let q := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    q = sigma.1⁻¹ • q := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  have hw : sigma.1⁻¹ • w = w := (sigma⁻¹).2
  exact (congrArg
    (fun w' => upperPrime (K := K) (L := L) P
      (placeUpperFactor
        (K := K) (L := L) P w')) hw.symm).trans
    (upper_place_smul
      (K := K) (L := L) P sigma.1⁻¹ w)

set_option maxHeartbeats 2000000 in
-- The proof simultaneously transports the two local algebra structures and
-- expands the local Galois norm as a product of automorphisms.
set_option maxRecDepth 100000 in
/-- At the centered upper prime, extending a local prime-adic norm equals
the product of the completion-place stabilizer action. -/
theorem extension_algebra_stabilizer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : (upperPrime (K := K) (L := L) P
      (placeUpperFactor
        (K := K) (L := L) P w)).adicCompletion L) :
    letI := finitePrimeAction (K := K) (L := L)
    let Q := placeUpperFactor (K := K) (L := L) P w
    let q := upperPrime (K := K) (L := L) P Q
    let hP : P.asIdeal.map
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P hP Q
    factorExtensionHom (K := K) (L := L) P Q
        (Algebra.norm (P.adicCompletion K) x) =
      ∏ sigma : CompletionPlaceStabilizer (FinitePlace.mk P).val w,
        finitePlaceTransport (K := K) sigma.1 q
          (RingEquiv.cast
            (R := fun R : HeightOneSpectrum
              (NumberField.RingOfIntegers L) => R.adicCompletion L)
            (centered_upper_stabilizer
              (K := K) (L := L) P w sigma) x) := by
  classical
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  letI : Nonempty W :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  let Q := placeUpperFactor (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  let hP : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : FiniteDimensional (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let z : w.1.Completion := eL.symm x
  have hz : eL z = x := eL.apply_symm_apply x
  have hnorm :
      eK (Algebra.norm v.Completion z) =
        Algebra.norm (P.adicCompletion K) x := by
    have hnorm₀ := place_adic_norm
      (K := K) (L := L) P w z
    change eK (Algebra.norm v.Completion z) =
      Algebra.norm (P.adicCompletion K) (eL z) at hnorm₀
    exact hnorm₀.trans (congrArg
      (fun y : q.adicCompletion L =>
        Algebra.norm (P.adicCompletion K) y) hz)
  calc
    factorExtensionHom (K := K) (L := L) P Q
        (Algebra.norm (P.adicCompletion K) x) =
        factorExtensionHom (K := K) (L := L) P Q
          (eK (Algebra.norm v.Completion z)) := by rw [hnorm]
    _ = eL (completionLies v w.1 w.2
          (Algebra.norm v.Completion z)) :=
      RingHom.congr_fun
        (place_adic_algebra
          (K := K) (L := L) P w) (Algebra.norm v.Completion z)
    _ = eL (∏ sigma : CompletionPlaceStabilizer v w,
          stabilizerRingHom v w sigma z) :=
      congrArg eL
        (completion_algebra_stabilizer
          (K := K) (L := L) v w z)
    _ = ∏ sigma : CompletionPlaceStabilizer v w,
          eL (stabilizerRingHom v w sigma z) := by
      have h := eL.map_prod
        (fun sigma : CompletionPlaceStabilizer v w =>
          stabilizerRingHom v w sigma z) Finset.univ
      change eL (∏ sigma : CompletionPlaceStabilizer v w,
          stabilizerRingHom v w sigma z) =
        ∏ sigma : CompletionPlaceStabilizer v w,
          eL (stabilizerRingHom v w sigma z) at h
      exact h
    _ = ∏ sigma : CompletionPlaceStabilizer v w,
          finitePlaceTransport (K := K) sigma.1 q
            (RingEquiv.cast
              (R := fun R : HeightOneSpectrum
                (NumberField.RingOfIntegers L) => R.adicCompletion L)
              (centered_upper_stabilizer
                (K := K) (L := L) P w sigma) x) := by
      apply Finset.prod_congr rfl
      intro sigma _
      rw [← hz]
      exact adic_stabilizer_transport
        (K := K) (L := L) P w sigma z

end

end Towers.CField.NIndex
