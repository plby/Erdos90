import Towers.ClassField.HasseNorm.GlobalComparison
import Towers.ClassField.HasseNorm.LocalGlobalCriterion
import Towers.ClassField.GrunwaldWang.PossibleInfiniteDegree

/-!
# Local norm quotients as cyclic degree-two cohomology

This file constructs the placewise comparison needed by the Hasse norm
argument.  It treats one chosen completion at a time and does not assemble
the idèle direct sum.
-/

namespace Towers.CField.HNorm

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.GWang
open groupCohomology

noncomputable section

universe u

/-- Transport a quotient along a multiplicative equivalence when the source
subgroup is the comap of the target subgroup. -/
private noncomputable def quotientMulComap
    {A B : Type u} [CommGroup A] [CommGroup B]
    (e : A ≃* B) (H : Subgroup B) (K : Subgroup A)
    (hcomap : H.comap e.toMonoidHom = K) :
    A ⧸ K ≃* B ⧸ H := by
  have hforward : K ≤ H.comap e.toMonoidHom := by
    rw [hcomap]
  have hbackward : H ≤ K.comap e.symm.toMonoidHom := by
    intro x hx
    change e.symm x ∈ K
    rw [← hcomap]
    change e (e.symm x) ∈ H
    simpa using hx
  exact
    { toFun := QuotientGroup.map K H e.toMonoidHom hforward
      invFun := QuotientGroup.map H K e.symm.toMonoidHom hbackward
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
        apply congrArg (QuotientGroup.mk' K)
        exact e.symm_apply_apply x
      right_inv := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
        apply congrArg (QuotientGroup.mk' H)
        exact e.apply_symm_apply x
      map_mul' := by
        intro x y
        exact map_mul _ x y }

/-- An absolute-value completion above `P` whose centered prime is the
specified upper prime `Q`. -/
structure HasseCompletionModel
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) where
  place : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val
  isEquiv_upper : place.1.IsEquiv
    (FinitePlace.mk (upperPrime (K := K) (L := L) P Q)).val

/-- Choose the absolute-value completion corresponding to a prescribed
upper finite prime.  Galois transitivity moves an arbitrary completion to
the desired centered prime. -/
noncomputable def hasseCompletionModel
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) :
    HasseCompletionModel K L P Q := by
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

/-- The resized units representation of the absolute-value completion
corresponding to the chosen upper finite prime. -/
noncomputable def hasseNormRepresentation
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P) := by
  let v := (FinitePlace.mk P).val
  let model := hasseCompletionModel K L P Q
  let w := model.place
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  exact hasseGlobalRepresentation v.Completion w.1.Completion

set_option synthInstance.maxHeartbeats 500000 in
-- Completion, norm, quotient, and cohomology instances elaborate simultaneously.
set_option maxHeartbeats 3000000 in
/-- A chosen finite local norm quotient is cyclic degree-two cohomology of
the corresponding absolute-value completion. -/
noncomputable def hasseH2
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Additive (HasseLocalQuotient completion (.inl P)) ≃+
      H2 (hasseNormRepresentation K L P
        (completion.finiteUpper P)) := by
  letI : IsCyclic Gal(L/K) := hcyclic
  let Q := completion.finiteUpper P
  let v := (FinitePlace.mk P).val
  let model := hasseCompletionModel K L P Q
  let w := model.place
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  have hlocalCyclic : IsCyclic Gal(w.1.Completion/v.Completion) :=
    (decompositionCompletionExtension v w.1).isCyclic.mp
      (Subgroup.isCyclic (absoluteValueDecomposition v w.1))
  let eK := placeCompletionAdic P
  let eUnits : (P.adicCompletion K)ˣ ≃* v.Completionˣ :=
    Units.mapEquiv eK.symm.toMulEquiv
  have hrange := completion_norm_range
    (K := K) (L := L) P Q w.1 w.2 model.isEquiv_upper
      (inferInstance : Module.Finite v.Completion w.1.Completion)
  have hcomap :
      (normSubgroup v.Completion w.1.Completion).comap
          eUnits.toMonoidHom =
        (finiteCompletionNorm (K := K) (L := L) P Q).range := by
    simpa [eUnits] using hrange
  let eQuot := quotientMulComap eUnits
    (normSubgroup v.Completion w.1.Completion)
    (finiteCompletionNorm (K := K) (L := L) P Q).range hcomap
  change Additive
      ((P.adicCompletion K)ˣ ⧸
        (finiteCompletionNorm (K := K) (L := L) P Q).range) ≃+ _
  exact eQuot.toAdditive.trans
    (hasseGlobal2
      v.Completion w.1.Completion hlocalCyclic)

/-- The completed extension at a chosen infinite place is Galois.  This is
the archimedean half of the decomposition-group/completion comparison. -/
@[reducible]
noncomputable def infiniteHasseGalois
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    IsGalois v.1.Completion w.1.1.Completion := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  apply IsGalois.of_card_aut_eq_finrank
  calc
    Nat.card Gal(w.1.1.Completion/v.1.Completion) =
        Nat.card (absoluteValueDecomposition v.1 w.1.1) :=
      Nat.card_congr
        (infiniteDecompositionGroup v w.1).symm.toEquiv
    _ = Module.finrank v.1.Completion w.1.1.Completion :=
      (infiniteDegreeCompatibility K L v w).symm

/-- The resized units representation at the chosen infinite completion. -/
noncomputable def infiniteHasseRepresentation
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  exact hasseGlobalRepresentation v.1.Completion w.1.1.Completion

set_option synthInstance.maxHeartbeats 500000 in
-- Archimedean completion and cohomology instances elaborate simultaneously.
set_option maxHeartbeats 3000000 in
/-- A chosen infinite local norm quotient is cyclic degree-two cohomology of
the corresponding completed extension. -/
noncomputable def infiniteHasse2
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcyclic : IsCyclic Gal(L/K))
    (completion : HasseCompletionData K L)
    (v : InfinitePlace K) :
    Additive (HasseLocalQuotient completion (.inr v)) ≃+
      H2 (infiniteHasseRepresentation K L v
        (completion.infiniteUpper v)) := by
  letI : IsCyclic Gal(L/K) := hcyclic
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  have hlocalCyclic : IsCyclic Gal(w.1.1.Completion/v.1.Completion) :=
    (infiniteDecompositionGroup v w.1).isCyclic.mp
      (Subgroup.isCyclic
        (absoluteValueDecomposition v.1 w.1.1))
  change Additive
      (v.1.Completionˣ ⧸
        (infiniteCompletionNorm (K := K) (L := L) v w).range) ≃+ _
  change Additive
      (v.1.Completionˣ ⧸
        normSubgroup v.1.Completion w.1.1.Completion) ≃+ _
  exact hasseGlobal2
    v.1.Completion w.1.1.Completion hlocalCyclic

end

end Towers.CField.HNorm
