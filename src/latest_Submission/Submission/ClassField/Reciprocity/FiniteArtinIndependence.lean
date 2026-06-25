import Submission.ClassField.LocalReciprocity.AlgEquiv
import Submission.ClassField.Reciprocity.CompletionArtinHom

/-!
# Choice-independence of the finite completed Artin map

Lemma V.5.1 already compares a local Artin map with its transport to a
Galois-conjugate completion.  Naturality of the normalized Artin map under
an algebra equivalence identifies that transported map with the normalized
map constructed directly at the conjugate completion.  Consequently the
global-valued completed Artin map is independent of the chosen place above
the fixed finite prime.
-/

namespace Submission.CField.Recip

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped IsMulCommutative

noncomputable section

set_option maxHeartbeats 5000000 in
-- Transporting the completed Artin map unfolds several dependent completion fields.
set_option synthInstance.maxHeartbeats 1000000 in
-- The conjugate completion fields carry several transported algebra instances.
/-- The finite local Artin map constructed directly at a conjugate
completion is the transport of the one at the original completion. -/
theorem global_artin_smul
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    globalArtinHom P (sigma • w) =
      conjugateGlobalArtin P w sigma := by
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
    simpa only [map_mul] using
      mul_comm (decompW.symm tau) (decompW.symm rho)
  let decompSigma :=
    decompositionCompletionExtension v (sigma • w).1
  letI : IsMulCommutative
      Gal((sigma • w).1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho => decompSigma.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompSigma.symm tau) (decompSigma.symm rho)
  let e := placeConjugationAlg v w sigma
  have hlocal := abelian_artin_alg
    v.Completion w.1.Completion (sigma • w).1.Completion e
  unfold globalArtinHom
  unfold conjugateGlobalArtin
  apply congrArg (completionArtinGlobal v (sigma • w))
  exact hlocal.symm

set_option maxHeartbeats 5000000 in
-- Comparing two chosen completions elaborates the pretransitive place action.
set_option synthInstance.maxHeartbeats 1000000 in
-- Pretransitivity and the two completed Artin maps form a deep instance tower.
/-- At a fixed finite prime, the canonical global-valued completed Artin
homomorphism is independent of the chosen normalized upper place. -/
theorem global_artin_independent
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    globalArtinHom P w =
      globalArtinHom P q := by
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
  rw [global_artin_smul]
  exact (artin_independent_conjugate
    P w sigma).symm

/-- Prime-adic source form of finite-place choice-independence. -/
theorem adic_artin_independent
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    adicGlobalArtin P w =
      adicGlobalArtin P q := by
  unfold adicGlobalArtin
  rw [global_artin_independent P w q]

end

end Submission.CField.Recip
