import Towers.ClassField.NormIndex.CompletionPlaceBridge

/-!
# Comparing finite completion models

This file contains the analytic and algebraic comparison between normalized
absolute-value completions and the prime-adic factors used by finite idèles.
It is separated from the underlying place correspondence so the two layers
can be checked independently.
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance comparisonFinitePlaceNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance comparisonFinitePlaceCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

private theorem continuous_place_adic
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Continuous (placeCompletionAdic P) := by
  let h := completion_universal (FinitePlace.mk P).val
    (FinitePlace.embedding P) (by
      intro x
      exact (FinitePlace.mk_apply P x).symm)
  change Continuous h.choose
  exact h.choose_spec.1.1.continuous

private theorem continuous_adic_cast
    {Q Q' : HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : Q = Q') :
    Continuous (RingEquiv.cast
      (R := fun v => v.adicCompletion L) h) := by
  subst Q'
  exact continuous_id

/-- The finite completion/adic-completion comparison is continuous. -/
theorem place_adic_continuous
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    Continuous (completionPlaceAdic
      (K := K) (L := L) P w) := by
  let hw := absolute_extension_nontrivial (FinitePlace.mk P).val w
  let hwna := absolute_extension_nonarchimedean (FinitePlace.mk P).val w
  let q := nonarchimedeanHeightSpectrum w.1 hw hwna
  let Q := placeUpperFactor (K := K) (L := L) P w
  have hq : q = upperPrime (K := K) (L := L) P Q := by
    have hfiber := (upperAboveBase
      (K := K) (L := L) P).apply_symm_apply
        (placeAboveBase (K := K) (L := L) P w)
    exact congrArg Subtype.val hfiber |>.symm
  unfold completionPlaceAdic
  exact (continuous_adic_cast hq).comp
    ((continuous_place_adic q).comp
      (continuous_ring_equiv
        (place_centered_prime w.1 hw hwna)))

set_option maxHeartbeats 2000000 in
-- The two dependent completion algebra structures normalize simultaneously.
set_option maxRecDepth 100000 in
/-- The absolute-completion and prime-adic models give the same algebra
embedding of the completed base field. -/
theorem place_adic_algebra
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    let Q := placeUpperFactor (K := K) (L := L) P w
    let eK := placeCompletionAdic P
    let eL := completionPlaceAdic (K := K) (L := L) P w
    (factorExtensionHom (K := K) (L := L) P Q).comp
        eK.toRingHom =
      eL.toRingHom.comp
        (completionLies (FinitePlace.mk P).val w.1 w.2) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let Q := placeUpperFactor (K := K) (L := L) P w
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  apply DFunLike.ext _ _
  intro z
  exact congrFun ((dense_range_embedding v).equalizer
    ((factor_extension_continuous
        (K := K) (L := L) P Q).comp
      (continuous_place_adic P))
    ((place_adic_continuous
        (K := K) (L := L) P w).comp
      (completion_lies_isometry v w.1 w.2).continuous)
    (funext fun x => by
      change factorExtensionHom (K := K) (L := L) P Q
          (eK (completionEmbedding v x)) =
        eL (completionLies v w.1 w.2
          (completionEmbedding v x))
      rw [show eK (completionEmbedding v x) =
          FinitePlace.embedding P x by
        exact finite_place_adic P x]
      rw [show factorExtensionHom (K := K) (L := L) P Q
            (FinitePlace.embedding P x) =
          FinitePlace.embedding
            (upperPrime (K := K) (L := L) P Q) (algebraMap K L x) by
        exact ring_comp_embedding
          (K := K) (L := L) P Q x]
      rw [show completionLies v w.1 w.2
          (completionEmbedding v x) =
            completionEmbedding w.1 (algebraMap K L x) by
        exact RingHom.congr_fun
          (completion_lies_comp v w.1 w.2) x]
      exact (place_adic_embedding
        (K := K) (L := L) P w (algebraMap K L x)).symm)) z

set_option maxHeartbeats 2000000 in
-- Transporting both finite-dimensional algebra structures is elaboration-heavy.
set_option maxRecDepth 100000 in
/-- Algebra norms agree elementwise in the absolute-completion and
prime-adic models. -/
theorem place_adic_norm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (z : w.1.Completion) :
    let Q := placeUpperFactor (K := K) (L := L) P w
    let eK := placeCompletionAdic P
    let eL := completionPlaceAdic (K := K) (L := L) P w
    let hP : P.asIdeal.map
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot P.ne_bot
    letI : Algebra (P.adicCompletion K)
        ((upperPrime (K := K) (L := L) P Q).adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P hP Q
    letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk P).val w.1 w.2).toAlgebra
    eK (Algebra.norm (FinitePlace.mk P).val.Completion z) =
      Algebra.norm (P.adicCompletion K) (eL z) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let Q := placeUpperFactor (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
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
  have hn := Algebra.norm_eq_of_equiv_equiv eK eL
    (place_adic_algebra
      (K := K) (L := L) P w) z
  apply eK.symm.injective
  rw [eK.symm_apply_apply]
  exact hn

/-- The upper prime factor attached to a completion place is its centered
literal height-one prime. -/
theorem upper_place_factor
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) =
      (placeAboveBase
        (K := K) (L := L) P w).1 := by
  have h := (upperAboveBase
    (K := K) (L := L) P).apply_symm_apply
      (placeAboveBase (K := K) (L := L) P w)
  exact congrArg Subtype.val h

/-- The upper prime factor attached to a completion place is equivariant
under Galois conjugation. -/
theorem upper_place_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : Gal(L/K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    letI := finitePrimeAction (K := K) (L := L)
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P (sigma • w)) =
      sigma • upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w) := by
  letI := finitePrimeAction (K := K) (L := L)
  calc
    upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P (sigma • w)) =
        (placeAboveBase
          (K := K) (L := L) P (sigma • w)).1 :=
      upper_place_factor
        (K := K) (L := L) P (sigma • w)
    _ = sigma • (placeAboveBase
          (K := K) (L := L) P w).1 :=
      above_base_smul
        (K := K) (L := L) P sigma w
    _ = sigma • upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w) := by
      rw [upper_place_factor]

set_option maxHeartbeats 1000000 in
-- Fixing the completion place avoids normalizing an arbitrary dependent
-- source place while retaining the decomposition-group comparison used by
-- the local norm formula.
set_option maxRecDepth 5000 in
/-- On a stabilized completion, the absolute-completion action agrees with
the prime-adic action at its centered upper prime. -/
theorem adic_stabilizer_transport
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (z : w.1.Completion) :
    letI := finitePrimeAction (K := K) (L := L)
    let q := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let hq : q = sigma.1⁻¹ • q := by
      have hw : sigma.1⁻¹ • w = w := (sigma⁻¹).2
      exact (congrArg
        (fun w' => upperPrime (K := K) (L := L) P
          (placeUpperFactor
            (K := K) (L := L) P w')) hw.symm).trans
        (upper_place_smul
          (K := K) (L := L) P sigma.1⁻¹ w)
    completionPlaceAdic (K := K) (L := L) P w
        (stabilizerRingHom
          (FinitePlace.mk P).val w sigma z) =
      finitePlaceTransport (K := K) sigma.1 q
        (RingEquiv.cast
          (R := fun Q : HeightOneSpectrum
            (NumberField.RingOfIntegers L) => Q.adicCompletion L)
          hq
          (completionPlaceAdic (K := K) (L := L) P w z)) := by
  letI := finitePrimeAction (K := K) (L := L)
  dsimp only
  let v := (FinitePlace.mk P).val
  let q := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  let hq : q = sigma.1⁻¹ • q := by
    have hw : sigma.1⁻¹ • w = w := (sigma⁻¹).2
    exact (congrArg
      (fun w' => upperPrime (K := K) (L := L) P
        (placeUpperFactor
          (K := K) (L := L) P w')) hw.symm).trans
      (upper_place_smul
        (K := K) (L := L) P sigma.1⁻¹ w)
  let e := completionPlaceAdic (K := K) (L := L) P w
  have hfun :
      (fun y : w.1.Completion =>
        e (stabilizerRingHom v w sigma y)) =
      fun y : w.1.Completion =>
        finitePlaceTransport (K := K) sigma.1 q
          (RingEquiv.cast
            (R := fun Q : HeightOneSpectrum
              (NumberField.RingOfIntegers L) => Q.adicCompletion L)
            hq (e y)) :=
    (dense_range_embedding w.1).equalizer
      ((place_adic_continuous
          (K := K) (L := L) P w).comp
        (place_stabilizer_isometry v w sigma).continuous)
      ((finite_transport_continuous (K := K) sigma.1 q).comp
        ((continuous_adic_cast hq).comp
          (place_adic_continuous
            (K := K) (L := L) P w)))
      (funext fun x => by
        change e (stabilizerRingHom v w sigma
              (completionEmbedding w.1 x)) =
          finitePlaceTransport (K := K) sigma.1 q
            (RingEquiv.cast hq (e (completionEmbedding w.1 x)))
        rw [place_stabilizer_embedding]
        rw [place_adic_embedding]
        rw [place_adic_embedding]
        rw [adic_completion_embedding]
        rw [place_transport_embedding])
  exact congrFun hfun z

end

end Towers.CField.NIndex
