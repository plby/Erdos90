import Submission.ClassField.LocalReciprocity.UniverseAlgEquiv
import Submission.ClassField.Reciprocity.CompletionPlaceConjugation
import Submission.ClassField.Reciprocity.UniversePlaceArtin

/-!
# Choice-independence of the ambient-universe finite-place Artin map

The original completion-place independence theorem uses the `Type 0`
norm-residue map.  This file repeats the same conjugation argument with the
ambient-universe Proposition III.3.6 map.  It is the finite local input needed
to make Proposition V.5.2 and Lemma VII.8.4 genuinely universe-polymorphic.
-/

namespace Submission.CField.Recip

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

set_option maxHeartbeats 5000000 in
-- The completion, local Galois group, and decomposition-group embeddings elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient-universe local Artin map at a completed finite place, with
values in the global Galois group. -/
noncomputable def globalArtinUniverse
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (FinitePlace.mk P).val.Completionˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  exact completionArtinGlobal v w
    (abelianArtinUniverse v.Completion w.1.Completion)

set_option maxHeartbeats 5000000 in
-- Naturality and completion conjugation are instantiated simultaneously.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient-universe local Artin map at `w`, transported to the
conjugate completion `sigma • w` and embedded in the global Galois group. -/
noncomputable def conjugateArtinUniverse
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    (FinitePlace.mk P).val.Completionˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho => decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (decomp.symm tau) (decomp.symm rho)
  exact completionArtinGlobal v (sigma • w)
    (conjugateCompletionArtin v w sigma
      (abelianArtinUniverse v.Completion w.1.Completion))

set_option maxHeartbeats 5000000 in
-- Naturality and completion conjugation are instantiated simultaneously.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient local Artin map at a conjugate completion is the transported
map from the original completion. -/
theorem artin_universe_smul
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    globalArtinUniverse P (sigma • w) =
      conjugateArtinUniverse P w sigma := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : FiniteDimensional v.Completion (sigma • w).1.Completion :=
    placeCompletionDimensional v (sigma • w)
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : IsGalois v.Completion (sigma • w).1.Completion :=
    placeCompletionGalois v (sigma • w)
  let decompW := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho => decompW.symm.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (decompW.symm tau) (decompW.symm rho)
  let decompSigma :=
    decompositionCompletionExtension v (sigma • w).1
  letI : IsMulCommutative
      Gal((sigma • w).1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho => decompSigma.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompSigma.symm tau) (decompSigma.symm rho)
  let e := placeConjugationAlg v w sigma
  have hlocal := abelian_universe_alg
    v.Completion w.1.Completion (sigma • w).1.Completion e
  unfold globalArtinUniverse
  unfold conjugateArtinUniverse
  apply congrArg (completionArtinGlobal v (sigma • w))
  exact hlocal.symm

set_option maxHeartbeats 5000000 in
-- The conjugation square and the abelian global target elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The ambient-universe completed finite-place Artin map is independent of
the chosen place above the fixed base prime. -/
theorem artin_universe_independent
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    globalArtinUniverse P w =
      globalArtinUniverse P q := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) w q
  subst q
  rw [artin_universe_smul]
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho => decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm (decomp.symm tau) (decomp.symm rho)
  unfold conjugateArtinUniverse
  unfold globalArtinUniverse
  rw [artin_conjugation_compatibility]
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [mul_comm sigma
    (completionArtinGlobal v w
      (abelianArtinUniverse v.Completion w.1.Completion) x),
    mul_inv_cancel_right]

/-- The existing prime-adic ambient Artin map is the completed ambient map
precomposed with the canonical adic-completion equivalence. -/
theorem artin_universe_completion
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicArtinUniverse K L P w =
      (globalArtinUniverse P w).comp
        (Units.map
          (placeCompletionAdic P).symm.toRingHom) := by
  rfl

/-- Prime-adic source form of ambient-universe completion-place
choice-independence. -/
theorem global_universe_independent
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicArtinUniverse K L P w =
      adicArtinUniverse K L P q := by
  rw [artin_universe_completion,
    artin_universe_completion,
    artin_universe_independent P w q]

end

end Submission.CField.Recip
