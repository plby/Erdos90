import Submission.ClassField.Ideles.Ideles
import Submission.NumberTheory.Completions.AdicLocalRing
import Submission.NumberTheory.Completions.PlaceFactorCorrespondence
import Submission.NumberTheory.Completions.AdicIntegersComplete
import Submission.NumberTheory.Dedekind.LocalizationQuotientPowers
import Submission.NumberTheory.Locals.NonarchimedeanClassification
import Submission.NumberTheory.Locals.OpenIdealQuotient

/-!
# Comparing the two finite-place completion models

Decomposition groups use the completion of the normalized absolute value
attached to a finite place, while finite ideles use the adic completion at
the corresponding height-one prime.  These are canonically isomorphic.
-/

namespace Submission.CField.Ideles

open AbsoluteValue Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Valued.integer
open scoped Topology WithZero

noncomputable section

/-- The absolute value underlying a finite place is nontrivial. -/
theorem absolute_value_nontrivial
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (FinitePlace.mk v).val.IsNontrivial := by
  have hvbot : (⊥ : Ideal (NumberField.RingOfIntegers K)) < v.asIdeal :=
    bot_lt_iff_ne_bot.mpr v.ne_bot
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt hvbot
  simp only [Ideal.mem_bot] at hx0
  refine ⟨algebraMap (NumberField.RingOfIntegers K) K x, ?_, ?_⟩
  · intro hzero
    apply hx0
    apply IsFractionRing.injective (NumberField.RingOfIntegers K) K
    simpa using hzero
  · apply ne_of_lt
    change ‖FinitePlace.embedding v
      (algebraMap (NumberField.RingOfIntegers K) K x)‖ < 1
    exact (FinitePlace.norm_lt_one_iff_mem K v x).2 hx

/-- The completion of a number field at a finite place has a nontrivial
norm.  This packages nontriviality of the normalized finite absolute value
in the form expected by the local-field APIs. -/
@[reducible]
noncomputable def placeNontriviallyNormed
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NontriviallyNormedField (FinitePlace.mk v).val.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases absolute_value_nontrivial v with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding (FinitePlace.mk v).val x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding (FinitePlace.mk v).val)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

/-- The metric on a finite-place completion is ultrametric. -/
@[reducible]
def placeUltrametricDist
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk v).val.Completion := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
  intro n
  rw [← map_natCast (completionEmbedding (FinitePlace.mk v).val) n,
    norm_completionEmbedding]
  exact
    (show IsNonarchimedean (FinitePlace.mk v).val from
      fun x y => (FinitePlace.mk v).add_le x y)
      |>.apply_natCast_le_one

/-- The valuative relation on a finite-place completion defined by its norm
valuation. -/
@[reducible]
noncomputable def placeValuativeRel
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ValuativeRel (FinitePlace.mk v).val.Completion := by
  letI : NontriviallyNormedField (FinitePlace.mk v).val.Completion :=
    placeNontriviallyNormed v
  letI : IsUltrametricDist (FinitePlace.mk v).val.Completion :=
    placeUltrametricDist v
  exact ValuativeRel.ofValuation
    (NormedField.valuation (K := (FinitePlace.mk v).val.Completion))

/-- Passing from a number field to its adic completion at a finite prime does
not change the residue field. -/
noncomputable def placeAdicResidue
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    v.asIdeal.ResidueField ≃+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) := by
  let A := Localization.AtPrime v.asIdeal
  let C := v.adicCompletionIntegers K
  let f : A →+* C := primeAdicIntegers (K := K) v
  letI : IsLocalHom f :=
    adic_integers_hom (K := K) v
  letI : IsTopologicalRing C :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer
  let eDense : A ⧸ (IsLocalRing.maximalIdeal C).comap f ≃+*
      C ⧸ IsLocalRing.maximalIdeal C :=
    denseRangeOpen f
      (adic_integers_range (K := K) v)
      (IsLocalRing.maximalIdeal C)
      (by
        simpa only [pow_one] using
          open_maximal_integers (K := K) v 1)
  exact
    (Ideal.quotEquivOfEq (IsLocalRing.maximalIdeal_comap f).symm).trans
      eDense

/-- The norm-defined integer ring used by local class field theory agrees
with the valuation-defined integer ring of the adic completion. -/
noncomputable def normedIntegerIntegers
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Valuation.integer
        (NormedField.valuation (K := v.adicCompletion K)) ≃+*
      v.adicCompletionIntegers K :=
  RingEquiv.subringCongr <| by
    ext x
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    change ‖x‖₊ ≤ 1 ↔ Valued.v x ≤ 1
    exact_mod_cast
      (Valued.toNormedField.norm_le_one_iff (x := x))

/-- The residue fields obtained from the norm and from the original adic
valuation are canonically equivalent. -/
noncomputable def normedAdicCompletion
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsLocalRing.ResidueField
        (Valuation.integer
          (NormedField.valuation (K := v.adicCompletion K))) ≃+*
      IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  IsLocalRing.ResidueField.mapEquiv
    (normedIntegerIntegers v)

/-- The residue cardinality of the adic completion is the cardinality of the
residue field at the original global prime. -/
theorem place_adic_card
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Nat.card v.asIdeal.ResidueField := by
  exact Nat.card_congr
    (placeAdicResidue v).symm.toEquiv

/-- The residue cardinality of the completion at a finite prime is the
absolute norm of that prime. -/
theorem adic_abs_norm
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [place_adic_card]
  let eQuotient :
      (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≃+*
        v.asIdeal.ResidueField :=
    RingEquiv.ofBijective
      (algebraMap
        (NumberField.RingOfIntegers K ⧸ v.asIdeal)
        v.asIdeal.ResidueField)
      v.asIdeal.bijective_algebraMap_quotient_residueField
  calc
    Nat.card v.asIdeal.ResidueField =
        Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
      Nat.card_congr eQuotient.symm.toEquiv
    _ = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- In the norm-defined presentation used by local class field theory, the
residue cardinality is the absolute norm of the centered global prime. -/
theorem normed_abs_norm
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card
        (IsLocalRing.ResidueField
          (Valuation.integer
            (NormedField.valuation (K := v.adicCompletion K)))) =
      Ideal.absNorm v.asIdeal := by
  calc
    Nat.card
        (IsLocalRing.ResidueField
          (Valuation.integer
            (NormedField.valuation (K := v.adicCompletion K)))) =
        Nat.card
          (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
      Nat.card_congr
        (normedAdicCompletion v).toEquiv
    _ = Ideal.absNorm v.asIdeal :=
      adic_abs_norm v

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
-- The adic-completion integer model unfolds several quotient-ring instances.
/-- The residue field of a number-field adic completion is finite. -/
theorem adicResidueField
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  let R := NumberField.RingOfIntegers K
  let A := Localization.AtPrime v.asIdeal
  let C := v.adicCompletionIntegers K
  letI : Finite (R ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let eResidue : R ⧸ v.asIdeal ^ 1 ≃+*
      A ⧸ IsLocalRing.maximalIdeal A :=
    (quotientLocalizationPrime R v.asIdeal 1).trans
      (Ideal.quotEquivOfEq (by
        rw [pow_one, IsLocalization.AtPrime.map_eq_maximalIdeal]))
  letI : Finite (R ⧸ v.asIdeal ^ 1) := by
    simpa only [pow_one] using (inferInstance : Finite (R ⧸ v.asIdeal))
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Finite.of_equiv (R ⧸ v.asIdeal ^ 1) eResidue.toEquiv
  let f : A →+* C := primeAdicIntegers (K := K) v
  letI : IsLocalHom f :=
    adic_integers_hom (K := K) v
  letI : IsTopologicalRing C :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer
  let eDense : A ⧸ (IsLocalRing.maximalIdeal C).comap f ≃+*
      C ⧸ IsLocalRing.maximalIdeal C :=
    denseRangeOpen f
      (adic_integers_range (K := K) v)
      (IsLocalRing.maximalIdeal C)
      (by
        simpa only [pow_one] using
          open_maximal_integers (K := K) v 1)
  let eCompletion : A ⧸ IsLocalRing.maximalIdeal A ≃+*
      C ⧸ IsLocalRing.maximalIdeal C :=
    (Ideal.quotEquivOfEq (IsLocalRing.maximalIdeal_comap f).symm).trans eDense
  exact Finite.of_equiv (A ⧸ IsLocalRing.maximalIdeal A) eCompletion.toEquiv

/-- The adic completion of a number field at a finite prime is locally
compact.  Its ring of integers is a complete discrete valuation ring with
finite residue field, so the completed field is proper. -/
@[reducible]
noncomputable def adicLocallySpace
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    LocallyCompactSpace (v.adicCompletion K) := by
  let C := v.adicCompletion K
  letI : NontriviallyNormedField C :=
    Valued.toNontriviallyNormedField C ℤᵐ⁰
  letI : IsDiscreteValuationRing
      (Valuation.integer (Valued.v : Valuation C ℤᵐ⁰)) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  letI : Finite
      (IsLocalRing.ResidueField
        (Valuation.integer (Valued.v : Valuation C ℤᵐ⁰))) := by
    change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
    exact adicResidueField v
  letI : ProperSpace C :=
    (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := C)).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- The absolute-value completion at a finite place is locally compact. -/
@[reducible]
noncomputable def placeLocallySpace
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    LocallyCompactSpace (FinitePlace.mk v).val.Completion := by
  let w := (FinitePlace.mk v).val
  letI : LocallyCompactSpace (v.adicCompletion K) :=
    adicLocallySpace v
  let h := completion_universal w
    (FinitePlace.embedding v) (by
      intro x
      exact (FinitePlace.mk_apply v x).symm)
  exact h.choose_spec.1.1.isClosedEmbedding.locallyCompactSpace

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
-- The valuative-topology criterion synthesizes the completion's discrete rank-one valuation.
/-- A finite-place completion, equipped with its norm-valuative relation,
is a nonarchimedean local field. -/
@[reducible]
noncomputable def placeNonarchimedeanField
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    @IsNonarchimedeanLocalField (FinitePlace.mk v).val.Completion
      inferInstance (placeValuativeRel v) inferInstance := by
  letI : NontriviallyNormedField (FinitePlace.mk v).val.Completion :=
    placeNontriviallyNormed v
  letI : IsUltrametricDist (FinitePlace.mk v).val.Completion :=
    placeUltrametricDist v
  letI : ValuativeRel (FinitePlace.mk v).val.Completion :=
    placeValuativeRel v
  letI : Valuation.Compatible
      (NormedField.valuation (K := (FinitePlace.mk v).val.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := (FinitePlace.mk v).val.Completion))
  haveI htop : IsValuativeTopology (FinitePlace.mk v).val.Completion := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : (FinitePlace.mk v).val.Completion) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation
              (K := (FinitePlace.mk v).val.Completion)))ˣ,
          {x | (NormedField.valuation
            (K := (FinitePlace.mk v).val.Completion)).restrict x < γ.1} ⊆ s from
      (NormedField.toValued
        (K := (FinitePlace.mk v).val.Completion)).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := (FinitePlace.mk v).val.Completion))
        |>.exists_setOf_restrict_le_iff 0 s
  letI hcompact : LocallyCompactSpace (FinitePlace.mk v).val.Completion :=
    placeLocallySpace v
  haveI hnontrivial :
      ValuativeRel.IsNontrivial (FinitePlace.mk v).val.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation
        (K := (FinitePlace.mk v).val.Completion))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }

/-- The absolute-value completion at a finite place is canonically the adic
completion used in the finite-idele restricted product. -/
noncomputable def placeCompletionAdic
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (FinitePlace.mk v).val.Completion ≃+* v.adicCompletion K := by
  let h := completion_universal (FinitePlace.mk v).val
    (FinitePlace.embedding v) (by
      intro x
      exact (FinitePlace.mk_apply v x).symm)
  let F := h.choose
  have hFisometry : Isometry F := h.choose_spec.1.1
  have hFcomp : F.comp (completionEmbedding (FinitePlace.mk v).val) =
      FinitePlace.embedding v := h.choose_spec.1.2
  apply RingEquiv.ofBijective F
  refine ⟨hFisometry.injective, ?_⟩
  have hfun :
      (F : (FinitePlace.mk v).val.Completion → v.adicCompletion K) ∘
        completionEmbedding (FinitePlace.mk v).val =
      algebraMap K (v.adicCompletion K) := by
    funext x
    exact RingHom.congr_fun hFcomp x
  have hdense : DenseRange F := by
    apply DenseRange.of_comp
    rw [hfun]
    exact v.denseRange_algebraMap K
  apply Set.range_eq_univ.mp
  calc
    Set.range F = closure (Set.range F) :=
      hFisometry.isClosedEmbedding.isClosed_range.closure_eq.symm
    _ = Set.univ := dense_iff_closure_eq.mp hdense

/-- The comparison agrees with the two canonical embeddings of the global
field. -/
@[simp]
theorem finite_place_adic
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    placeCompletionAdic v
        (completionEmbedding (FinitePlace.mk v).val x) =
      FinitePlace.embedding v x := by
  let h := completion_universal (FinitePlace.mk v).val
    (FinitePlace.embedding v) (by
      intro y
      exact (FinitePlace.mk_apply v y).symm)
  exact RingHom.congr_fun h.choose_spec.1.2 x

end

end Submission.CField.Ideles
