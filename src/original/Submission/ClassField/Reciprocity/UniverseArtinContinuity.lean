import Submission.ClassField.LocalReciprocity.UniverseContinuity
import Submission.ClassField.Reciprocity.UniverseLocalPredicate

/-!
# Continuity of the ambient finite-place Artin map

The local normalization predicate identifies the kernel of the prime-adic
Artin map with the preimage of a completion norm subgroup.  That subgroup is
open, so the usual open-kernel argument proves continuity without unfolding
the transported Artin-map definition.
-/

namespace Submission.CField.Recip

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex

noncomputable section

universe u

set_option maxHeartbeats 3000000 in
-- The local-predicate kernel is compared with the open completion norm subgroup.
set_option synthInstance.maxHeartbeats 500000 in
/-- The ambient finite-place Artin homomorphism of a finite abelian layer is
continuous in arbitrary universes. -/
theorem artin_universe_continuous
    {K : Type u} [Field K] [NumberField K]
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L.1) (FinitePlace.mk P).val) :
    Continuous (adicArtinUniverse K L.1 P w) := by
  let v := (FinitePlace.mk P).val
  let placesEquiv :=
    placesAboveFactors
      (K := K) (L := L.1) P
  let Q := placesEquiv w
  have hpred : LayerLocalArtin L P Q
      (adicArtinUniverse K L.1 P w) := by
    have h :=
      global_artin_universe
        L P Q
    simpa only [Q, placesEquiv, Equiv.symm_apply_apply] using h
  change ∃ (q : AbsoluteValue L.1 ℝ)
      (hqv : AbsoluteValue.LiesOver q v),
    q.IsEquiv
        (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val ∧
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : NontriviallyNormedField v.Completion :=
        placeNontriviallyNormed P
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : ValuativeRel v.Completion :=
        placeValuativeRel P
      letI : IsNonarchimedeanLocalField v.Completion :=
        placeNonarchimedeanField P
      letI : Fact (AbsoluteValue.LiesOver q v) := ⟨hqv⟩
      letI : Algebra v.Completion q.Completion :=
        (completionLies v q hqv).toAlgebra
      ∃ e : (v.Completionˣ ⧸ normSubgroup v.Completion q.Completion) ≃*
          Gal(q.Completion/v.Completion),
        (∀ x : (P.adicCompletion K)ˣ,
          adicArtinUniverse K L.1 P w x =
            ((decompositionCompletionExtension v q).symm
              (e (QuotientGroup.mk'
                (normSubgroup v.Completion q.Completion)
                (Units.map
                  (placeCompletionAdic P).symm.toRingHom
                  x))) : Gal(L.1/K))) ∧
        ∀ q' : CompletionPlacesAbove (L := L.1) v,
          adicArtinUniverse K L.1 P w =
            adicArtinUniverse K L.1 P q' at hpred
  rcases hpred with ⟨q, hqv, -, e, hformula, -⟩
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
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
      inferInstance
  letI : Fact (AbsoluteValue.LiesOver q v) := ⟨hqv⟩
  letI : Algebra v.Completion q.Completion :=
    (completionLies v q hqv).toAlgebra
  letI : Finite (CompletionPlacesAbove (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (CompletionPlacesAbove (L := L.1) v) :=
    completion_above_pretransitive P
  let qAbove : CompletionPlacesAbove (L := L.1) v := ⟨q, hqv⟩
  letI : FiniteDimensional v.Completion q.Completion :=
    placeCompletionDimensional v qAbove
  letI : IsGalois v.Completion q.Completion :=
    placeCompletionGalois v qAbove
  let decomp := decompositionCompletionExtension v q
  letI : IsMulCommutative Gal(q.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  let toAbsoluteCompletion : (P.adicCompletion K)ˣ →* v.Completionˣ :=
    Units.map
      (placeCompletionAdic P).symm.toRingHom
  have hcompletion : Continuous toAbsoluteCompletion := by
    apply Continuous.units_map
    exact adic_symm_continuous P
  letI : Finite
      (v.Completionˣ ⧸ normSubgroup v.Completion q.Completion) :=
    Finite.of_injective e e.injective
  letI : (normSubgroup v.Completion q.Completion).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let phi := adicArtinUniverse K L.1 P w
  have hker : (phi.ker : Set (P.adicCompletion K)ˣ) =
      toAbsoluteCompletion ⁻¹'
        (normSubgroup v.Completion q.Completion : Set v.Completionˣ) := by
    ext x
    change phi x = 1 ↔
      toAbsoluteCompletion x ∈ normSubgroup v.Completion q.Completion
    constructor
    · intro hx
      let qx := QuotientGroup.mk'
        (normSubgroup v.Completion q.Completion)
        (toAbsoluteCompletion x)
      have hglobal : ((decomp.symm (e qx) :
          absoluteValueDecomposition v q) : Gal(L.1/K)) = 1 := by
        simpa only [phi, qx, toAbsoluteCompletion, decomp] using
          (hformula x).symm.trans hx
      have hdecomp : decomp.symm (e qx) = 1 := by
        apply Subtype.ext
        exact hglobal
      have he : e qx = 1 := by
        apply decomp.symm.injective
        simpa only [map_one] using hdecomp
      have hq : qx = 1 := by
        apply e.injective
        simpa only [map_one] using he
      exact (QuotientGroup.eq_one_iff (toAbsoluteCompletion x)).1 hq
    · intro hx
      have hquot : QuotientGroup.mk'
          (normSubgroup v.Completion q.Completion)
          (toAbsoluteCompletion x) = 1 :=
        (QuotientGroup.eq_one_iff (toAbsoluteCompletion x)).2 hx
      rw [hformula x]
      change ((decomp.symm
        (e (QuotientGroup.mk'
          (normSubgroup v.Completion q.Completion)
          (toAbsoluteCompletion x))) :
            absoluteValueDecomposition v q) : Gal(L.1/K)) = 1
      rw [hquot, map_one, map_one]
      rfl
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, nhds_discrete Gal(L.1/K), map_one,
    Filter.tendsto_pure]
  change (phi.ker : Set (P.adicCompletion K)ˣ) ∈ nhds 1
  rw [hker]
  exact ((norm_subgroup v.Completion q.Completion).preimage
    hcompletion).mem_nhds (by
      change toAbsoluteCompletion 1 ∈
        normSubgroup v.Completion q.Completion
      rw [map_one]
      exact Subgroup.one_mem _)

end

end Submission.CField.Recip
