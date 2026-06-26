import Submission.ClassField.LocalReciprocity.CompositumArtinMaps
import Submission.ClassField.LocalReciprocity.AmbientCompatibility
import Submission.ClassField.Reciprocity.UniverseArtinIndependence
import Submission.ClassField.NormIndex.CompletionPlaceComparison
import Submission.ClassField.ReciprocityExistence.FiniteLayerAbsolute
import Submission.NumberTheory.Ramification.RamificationDiscriminant
import Submission.ClassField.HasseNorm.UnramifiedLocal
import Submission.ClassField.GrunwaldWang.CompletionNormCompatibility

/-!
# The finite local compositum square in Lemma VII.8.4

At a finite prime we choose one completion of the global compositum above
the prescribed middle-field prime.  Its restrictions give compatible
completions of the lower abelian extension.  Lemma III.3.2, applied in a
normal closure of the resulting local tower, supplies the norm square.
-/

namespace Submission.CField.RExist

open AbsoluteValue Filter Set
open NumberField IsDedekindDomain
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.ICohomo
open Submission.CField.NIndex
open scoped IsMulCommutative

noncomputable section

private abbrev OK (K : Type) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Raising a nonarchimedean absolute value to a positive real power again
gives an absolute value.  This is the normalization operation needed to
make a prescribed upper finite prime lie over the *normalized* lower
finite place. -/
private def absoluteValueRpow
    {F : Type} [Field F]
    (v : AbsoluteValue F ℝ) (hv : IsNonarchimedean v)
    (c : ℝ) (hc : 0 < c) : AbsoluteValue F ℝ where
  toFun := fun x ↦ v x ^ c
  map_mul' := fun x y ↦ by
    rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) c
  eq_zero' x := by
    rw [Real.rpow_eq_zero (v.nonneg x) hc.ne', map_eq_zero]
  add_le' x y := by
    calc
      v (x + y) ^ c ≤ max (v x) (v y) ^ c :=
        Real.rpow_le_rpow (v.nonneg _) (hv x y) hc.le
      _ = max (v x ^ c) (v y ^ c) :=
        Real.rpow_max (v.nonneg x) (v.nonneg y) hc.le
      _ ≤ v x ^ c + v y ^ c := max_le_add_of_nonneg
        (Real.rpow_nonneg (v.nonneg x) c)
        (Real.rpow_nonneg (v.nonneg y) c)

/-- The finite place at a literal upper prime, restricted to the lower
field, is equivalent to the normalized finite place at its contraction. -/
private theorem place_comap_equiv
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (P : HeightOneSpectrum (OK K))
    (Q : HeightOneSpectrum (OK L))
    (hQP : Q.under (OK K) = P) :
    let qv := (FinitePlace.mk Q).val
    let u := qv.comp (algebraMap K L).injective
    u.IsEquiv (FinitePlace.mk P).val := by
  dsimp only
  let qv := (FinitePlace.mk Q).val
  let u := qv.comp (algebraMap K L).injective
  have huNontrivial : u.IsNontrivial := by
    obtain ⟨x, hx, hx0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    let xK : K := algebraMap (OK K) K x
    have hxK : xK ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff (OK K) K).not.2 hx0
    refine ⟨xK, hxK, ?_⟩
    have hxQ : algebraMap (OK K) (OK L) x ∈ Q.asIdeal := by
      have : x ∈ Ideal.under (OK K) Q.asIdeal := by
        have hunder := congrArg HeightOneSpectrum.asIdeal hQP
        change Ideal.under (OK K) Q.asIdeal = P.asIdeal at hunder
        rwa [hunder]
      exact this
    have hlt := (FinitePlace.norm_lt_one_iff_mem (K := L) Q
      (algebraMap (OK K) (OK L) x)).2 hxQ
    have hglobal :
        algebraMap K L (algebraMap (OK K) K x) =
          algebraMap (OK L) L (algebraMap (OK K) (OK L) x) := by
      rfl
    intro hone
    have : u xK < 1 := by
      change qv (algebraMap K L xK) < 1
      rw [hglobal]
      exact hlt
    exact this.ne hone
  have huNA : IsNonarchimedean u := by
    rw [nonarchimedean_nat_cast]
    intro n
    change qv (algebraMap K L (n : K)) ≤ 1
    rw [map_natCast]
    exact IsNonarchimedean.apply_natCast_le_one
      (place_nonarchimedean (FinitePlace.mk Q))
  let U := nonarchimedeanHeightSpectrum u huNontrivial huNA
  have hUP : U = P := by
    apply HeightOneSpectrum.ext
    ext x
    rw [show x ∈ U.asIdeal ↔ u (algebraMap (OK K) K x) < 1 by
      exact nonarchimedean_prime_ideal u huNA x]
    rw [show u (algebraMap (OK K) K x) < 1 ↔
        algebraMap (OK K) (OK L) x ∈ Q.asIdeal by
      have hglobal :
          algebraMap K L (algebraMap (OK K) K x) =
            algebraMap (OK L) L (algebraMap (OK K) (OK L) x) := by
        rfl
      change qv (algebraMap K L (algebraMap (OK K) K x)) < 1 ↔ _
      rw [hglobal]
      exact FinitePlace.norm_lt_one_iff_mem (K := L) Q
        (algebraMap (OK K) (OK L) x)]
    have hunder := congrArg HeightOneSpectrum.asIdeal hQP
    change Ideal.under (OK K) Q.asIdeal = P.asIdeal at hunder
    rw [← hunder]
    rfl
  have h := place_centered_prime u huNontrivial huNA
  simpa [U, hUP] using h

/-- A completion place above `P` normalized so that its centered upper
prime is a prescribed literal prime `Q`.  Unlike the older Galois-only
bridge, this construction works for every finite number-field extension. -/
private structure LiteralCompletionModel
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) where
  place : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val
  isEquiv_upper : place.1.IsEquiv (FinitePlace.mk Q.1).val

private noncomputable def literalCompletionModel
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) :
    LiteralCompletionModel K L P Q := by
  let v := (FinitePlace.mk P).val
  let qv := (FinitePlace.mk Q.1).val
  let u := qv.comp (algebraMap K L).injective
  have hu : u.IsEquiv v := place_comap_equiv P Q.1 Q.2
  let hex := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hu
  let c := Classical.choose hex
  have hc : 0 < c := (Classical.choose_spec hex).1
  have hpow : (u · ^ c) = v := (Classical.choose_spec hex).2
  let w : AbsoluteValue L ℝ := absoluteValueRpow qv
    (place_nonarchimedean (FinitePlace.mk Q.1)) c hc
  have hwv : AbsoluteValue.LiesOver w v := by
    constructor
    ext x
    change qv (algebraMap K L x) ^ c = v x
    exact congrFun hpow x
  have hwq : w.IsEquiv qv := by
    apply AbsoluteValue.IsEquiv.symm
    apply AbsoluteValue.isEquiv_iff_exists_rpow_eq.mpr
    exact ⟨c, hc, rfl⟩
  exact ⟨⟨w, hwv⟩, hwq⟩

private noncomputable def literalRingAdic
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {P : HeightOneSpectrum (OK K)}
    {Q : PlacesAbovePrime K L P}
    (m : LiteralCompletionModel K L P Q) :
    m.place.1.Completion ≃+* Q.1.adicCompletion L :=
  (completionRing m.isEquiv_upper).trans
    (placeCompletionAdic Q.1)

@[simp] private theorem
    literal_adic_embedding
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {P : HeightOneSpectrum (OK K)}
    {Q : PlacesAbovePrime K L P}
    (m : LiteralCompletionModel K L P Q) (x : L) :
    literalRingAdic m (completionEmbedding m.place.1 x) =
      FinitePlace.embedding Q.1 x := by
  unfold literalRingAdic
  rw [RingEquiv.trans_apply,
    completion_ring_embedding,
    finite_place_adic]

private theorem literal_adic_continuous
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {P : HeightOneSpectrum (OK K)}
    {Q : PlacesAbovePrime K L P}
    (m : LiteralCompletionModel K L P Q) :
    Continuous (literalRingAdic m) :=
  (place_adic_isometry Q.1).continuous.comp
    (continuous_ring_equiv m.isEquiv_upper)

set_option maxHeartbeats 2000000 in
-- Extending the dense completion identity unfolds both literal adic models.
set_option maxRecDepth 100000 in
private theorem literal_adic_algebra
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P)
    (m : LiteralCompletionModel K L P
      ⟨upperPrime (K := K) (L := L) P q,
        upperPrime_under (K := K) (L := L) P q⟩) :
    let v := (FinitePlace.mk P).val
    let eK := placeCompletionAdic P
    let eL := literalRingAdic m
    (factorExtensionHom (K := K) (L := L) P q).comp
        eK.toRingHom =
      eL.toRingHom.comp (completionLies v m.place.1 m.place.2) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let eK := placeCompletionAdic P
  let eL := literalRingAdic m
  apply DFunLike.ext _ _
  intro z
  exact congrFun ((dense_range_embedding v).equalizer
    ((factor_extension_continuous
        (K := K) (L := L) P q).comp
      (place_adic_isometry P).continuous)
    ((literal_adic_continuous m).comp
      (completion_lies_isometry v m.place.1 m.place.2).continuous)
    (funext fun x ↦ by
      change factorExtensionHom (K := K) (L := L) P q
          (eK (completionEmbedding v x)) =
        eL (completionLies v m.place.1 m.place.2
          (completionEmbedding v x))
      rw [finite_place_adic]
      rw [ring_comp_embedding]
      rw [show completionLies v m.place.1 m.place.2
          (completionEmbedding v x) =
            completionEmbedding m.place.1 (algebraMap K L x) by
        exact RingHom.congr_fun
          (completion_lies_comp v m.place.1 m.place.2) x]
      exact (literal_adic_embedding
        m (algebraMap K L x)).symm)) z

set_option maxHeartbeats 2000000 in
-- Transporting the norm through the literal completion equivalence unfolds both algebra maps.
set_option maxRecDepth 100000 in
private theorem literal_adic_norm
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P)
    (m : LiteralCompletionModel K L P
      ⟨upperPrime (K := K) (L := L) P q,
        upperPrime_under (K := K) (L := L) P q⟩)
    (z : m.place.1.Completion) :
    let v := (FinitePlace.mk P).val
    let eK := placeCompletionAdic P
    let eL := literalRingAdic m
    letI : Algebra v.Completion m.place.1.Completion :=
      (completionLies v m.place.1 m.place.2).toAlgebra
    letI : Algebra (P.adicCompletion K)
        ((upperPrime (K := K) (L := L) P q).adicCompletion L) :=
      adicFactorAlgebra
        (K := K) (L := L) P
          (Ideal.map_ne_bot_of_ne_bot P.ne_bot) q
    eK (Algebra.norm v.Completion z) =
      Algebra.norm (P.adicCompletion K) (eL z) := by
  dsimp only
  let v := (FinitePlace.mk P).val
  let eK := placeCompletionAdic P
  let eL := literalRingAdic m
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion m.place.1.Completion :=
    (completionLies v m.place.1 m.place.2).toAlgebra
  letI : FiniteDimensional v.Completion m.place.1.Completion :=
    placeCompletionDimensional v m.place
  letI : Algebra (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P q).adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P
        (Ideal.map_ne_bot_of_ne_bot P.ne_bot) q
  letI : FiniteDimensional (P.adicCompletion K)
      ((upperPrime (K := K) (L := L) P q).adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P q
  have hn := Algebra.norm_eq_of_equiv_equiv eK eL
    (literal_adic_algebra P q m) z
  calc
    eK (Algebra.norm v.Completion z) =
        eK (eK.symm (Algebra.norm (P.adicCompletion K) (eL z))) :=
      congrArg eK hn
    _ = Algebra.norm (P.adicCompletion K) (eL z) :=
      eK.apply_symm_apply _

/-- A fixed, choice-independent finite local Artin map with global Galois
target.  Choice-independence is proved in Lemma V.5.1. -/
noncomputable def canonicalArtinHom
    (K L : Type) [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (OK K)) :
    (P.adicCompletion K)ˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NumberField L := NumberField.of_module_finite K L
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  let w : CompletionPlacesAbove (L := L) v :=
    Classical.choice (absolute_value_extension (K := K) (L := L) v)
  exact adicArtinUniverse K L P w

theorem canonical_global_artin
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (OK K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    canonicalArtinHom K L P =
      adicArtinUniverse K L P w := by
  unfold canonicalArtinHom
  exact global_universe_independent P _ w

/-! ### Restricted-product support of the canonical finite factors -/

/-- The finite base primes admitting a ramified prime in `L`. -/
private def canonicalRamifiedPrimes
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    Set (HeightOneSpectrum (OK K)) :=
  {P | ∃ Q : Ideal (OK L), Q.IsPrime ∧ Q ≠ ⊥ ∧
    Q.under (OK K) = P.asIdeal ∧
      Ideal.ramificationIdx P.asIdeal Q ≠ 1}

private theorem canonical_ramified_primes
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    (canonicalRamifiedPrimes K L).Finite := by
  let bad : Set (Ideal (OK K)) :=
    {p | ∃ Q : Ideal (OK L), Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.under (OK K) = p ∧ Ideal.ramificationIdx p Q ≠ 1}
  have hbad : bad.Finite :=
    ramified_base_primes (OK K) (OK L)
  have hinj : Function.Injective
      (fun P : HeightOneSpectrum (OK K) ↦ P.asIdeal) := by
    intro P Q h
    exact HeightOneSpectrum.ext_iff.mpr h
  change ((fun P : HeightOneSpectrum (OK K) ↦ P.asIdeal) ⁻¹' bad).Finite
  exact Set.Finite.preimage hinj.injOn hbad

private theorem canonical_chosen_unramified
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (hP : P ∉ canonicalRamifiedPrimes K L) :
    let Q := placeUpperFactor
      (K := K) (L := L) P w
    Algebra.IsUnramifiedAt (OK K)
      (upperPrime (K := K) (L := L) P Q).asIdeal := by
  let Q := placeUpperFactor
    (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  letI : q.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q)).symm
  apply (unramified_ramification_idx
    P.asIdeal q.asIdeal q.ne_bot).2
  by_contra hram
  apply hP
  exact ⟨q.asIdeal, q.isPrime, q.ne_bot,
    congrArg HeightOneSpectrum.asIdeal
      (upperPrime_under (K := K) (L := L) P Q), hram⟩

set_option maxHeartbeats 3000000 in
-- The global-valued local Artin map unfolds the chosen completion and decomposition group.
set_option synthInstance.maxHeartbeats 100000 in
-- The completed local-field structures require deeper instance search.
private theorem global_artin_units
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (OK K))
    (hP : P ∉ canonicalRamifiedPrimes K L)
    (x : (P.adicCompletion K)ˣ)
    (hx : x ∈ IdeleUnitSubgroup (OK K) K P) :
    canonicalArtinHom K L P x = 1 := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  let w : CompletionPlacesAbove (L := L) v :=
    Classical.choice (absolute_value_extension (K := K) (L := L) v)
  let Q := placeUpperFactor
    (K := K) (L := L) P w
  let q := upperPrime (K := K) (L := L) P Q
  have hQ : Algebra.IsUnramifiedAt (OK K) q.asIdeal :=
    canonical_chosen_unramified K L P w hP
  have hxNorm : x ∈
      (finiteCompletionNorm (K := K) (L := L) P Q).range :=
    Submission.CField.HNorm.units_range_unramified
      (K := K) (L := L) P Q hQ hx
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
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
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  have hwq : w.1.IsEquiv (FinitePlace.mk q).val := by
    have h := (primeCompletionModel K L P Q).isEquiv_upper
    change ((placesAboveFactors
      (K := K) (L := L) P).symm Q).1.IsEquiv
        (FinitePlace.mk q).val at h
    rw [show (placesAboveFactors
        (K := K) (L := L) P).symm Q = w by
      exact (placesAboveFactors
        (K := K) (L := L) P).symm_apply_apply w] at h
    exact h
  have hnormRange :=
    Submission.CField.GWang.completion_norm_range
      (K := K) (L := L) P Q w.1 w.2 hwq
      (inferInstance : Module.Finite v.Completion w.1.Completion)
  have hxAbsolute :
      Units.map (placeCompletionAdic P).symm.toRingHom x ∈
        normSubgroup v.Completion w.1.Completion := by
    change x ∈ (normSubgroup v.Completion w.1.Completion).comap
      (Units.map
        (placeCompletionAdic P).symm.toRingHom)
    rw [hnormRange]
    exact hxNorm
  have hlocalOne : abelianArtinHom
      v.Completion w.1.Completion
      (Units.map
        (placeCompletionAdic P).symm.toRingHom x) = 1 := by
    have hquot : QuotientGroup.mk' (normSubgroup v.Completion w.1.Completion)
        (Units.map
          (placeCompletionAdic P).symm.toRingHom x) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hxAbsolute
    unfold abelianArtinHom
    simp only [MonoidHom.comp_apply]
    rw [hquot, map_one]
  have hlocalOneUniverse : abelianArtinUniverse
      v.Completion w.1.Completion
      (Units.map
        (placeCompletionAdic P).symm.toRingHom x) = 1 := by
    rw [← abelian_local_universe]
    exact hlocalOne
  rw [canonical_global_artin K L P w]
  rw [artin_universe_completion]
  unfold globalArtinUniverse completionArtinGlobal
  simp only [MonoidHom.comp_apply]
  change (absoluteValueDecomposition v w.1).subtype
      (decomp.symm (abelianArtinUniverse
        v.Completion w.1.Completion
        (Units.map
          (placeCompletionAdic P).symm.toRingHom x))) = 1
  rw [hlocalOneUniverse]
  simp only [map_one]

/-- The canonical finite local Artin maps satisfy the finite-support
condition required to define their restricted product. -/
theorem eventually_trivial_units
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] :
    ∀ᶠ P in Filter.cofinite,
      ∀ x : (P.adicCompletion K)ˣ,
        x ∈ IdeleUnitSubgroup (OK K) K P →
          canonicalArtinHom K L P x = 1 := by
  rw [Filter.eventually_cofinite]
  exact (canonical_ramified_primes K L).subset (by
    intro P hPbad
    by_contra hP
    apply hPbad
    intro x hx
    exact global_artin_units K L P hP x hx)

/-- The literal-prime form of the completed norm carries an upper local
unit to a lower local unit. -/
theorem literal_unit_subgroup
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P)
    (z : (Q.1.adicCompletion L)ˣ)
    (hz : z ∈ IdeleUnitSubgroup (OK L) L Q.1) :
    completionNormLiteral (K := K) (L := L) P Q z ∈
      IdeleUnitSubgroup (OK K) K P := by
  revert hz z
  let e := upperPlacesAbove
    (K := K) (L := L) P
  let property : PlacesAbovePrime K L P → Prop := fun R ↦
    ∀ z : (R.1.adicCompletion L)ˣ,
      z ∈ IdeleUnitSubgroup (OK L) L R.1 →
        completionNormLiteral (K := K) (L := L) P R z ∈
          IdeleUnitSubgroup (OK K) K P
  change property Q
  obtain ⟨q, rfl⟩ := e.surjective Q
  intro z hz
  rw [completion_literal_equiv]
  exact completion_unit_subgroup (K := K) (L := L) P q z hz

/-- The upper map and its III.3.2 certificate at one literal finite prime.
The lower map is the fixed canonical map, so the package can be used for
every prime of `K'` above the same prime of `K`. -/
structure CLData
    (K K' M : Type)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K K' P) where
  upper : (Q.1.adicCompletion K')ˣ →* Gal(M/K')
  projected_square : PSquare
    (completionNormLiteral (K := K) (L := K') P Q)
    (canonicalArtinHom K E P) upper
    (compositumGaloisRestriction (K := K) (K' := K') (M := M) E)

set_option maxHeartbeats 50000000 in
-- The common-completion construction normalizes the full local compositum square.
set_option synthInstance.maxHeartbeats 1000000 in
-- The local tower carries several dependent completion and Galois instances.
set_option maxRecDepth 100000 in
/-- Construct the finite local data from a common completion and the
projected norm square of Lemma III.3.2. -/
noncomputable def CLData.canonical
    (K K' M : Type)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K K' P) :
    CLData K K' M E P Q := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField M := NumberField.of_module_finite K' M
  let factorEquiv := upperPlacesAbove
    (K := K) (L := K') P
  let q := factorEquiv.symm Q
  have hQ : factorEquiv q = Q := factorEquiv.apply_symm_apply Q
  rw [← hQ]
  let v := (FinitePlace.mk P).val
  let Qq : PlacesAbovePrime K K' P :=
    ⟨upperPrime (K := K) (L := K') P q,
      upperPrime_under (K := K) (L := K') P q⟩
  have hQq : Qq = factorEquiv q := by rfl
  let wModel := literalCompletionModel K K' P Qq
  let w : CompletionPlacesAbove (L := K') v := wModel.place
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
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
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : CharZero v.Completion :=
    (RingHom.charZero_iff (algebraMap K v.Completion).injective).mp
      inferInstance
  let hwna : IsNonarchimedean w.1 :=
    (nonarchimedean_equiv wModel.isEquiv_upper).mpr
      (place_nonarchimedean (FinitePlace.mk Qq.1))
  letI : Fact w.1.IsNontrivial :=
    ⟨absolute_extension_nontrivial v w⟩
  letI : IsUltrametricDist w.1.Completion :=
    absoluteUltrametricDist w.1 hwna
  letI : Algebra.IsSeparable K' M := IsGalois.to_isSeparable
  let t : CompletionPlacesAbove (L := M) w.1 :=
    Classical.choice
      (absolute_value_extension (K := K') (L := M) w.1)
  let u : AbsoluteValue E ℝ := t.1.comp (algebraMap E M).injective
  have htv : AbsoluteValue.LiesOver t.1 v := by
    constructor
    ext x
    change t.1 (algebraMap K M x) = v x
    rw [IsScalarTower.algebraMap_apply K K' M]
    have ht := DFunLike.congr_fun t.2.comp_eq (algebraMap K K' x)
    have hw := DFunLike.congr_fun w.2.comp_eq x
    exact ht.trans hw
  have huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change t.1 (algebraMap E M (algebraMap K E x)) = v x
    rw [← IsScalarTower.algebraMap_apply K E M]
    exact DFunLike.congr_fun htv.comp_eq x
  have htu : AbsoluteValue.LiesOver t.1 u := by
    constructor
    rfl
  let uAbove : CompletionPlacesAbove (L := E) v := ⟨u, huv⟩
  let tAboveV : CompletionPlacesAbove (L := M) v := ⟨t.1, htv⟩
  let tAboveU : CompletionPlacesAbove (L := M) u := ⟨t.1, htu⟩
  letI : Fact u.IsNontrivial :=
    ⟨absolute_extension_nontrivial v uAbove⟩
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u
      (absolute_extension_nonarchimedean v uAbove)
  letI : Fact (AbsoluteValue.LiesOver u v) := ⟨huv⟩
  letI : Fact (AbsoluteValue.LiesOver t.1 u) := ⟨htu⟩
  letI : Fact (AbsoluteValue.LiesOver t.1 w.1) := ⟨t.2⟩
  let Wt := CompletionPlacesAbove (L := M) w.1
  letI : Finite Wt := absolute_extensions_separable w.1
  letI : Nonempty Wt := ⟨t⟩
  letI : MulAction.IsPretransitive Gal(M/K') Wt :=
    above_pretr_nonar w.1 hwna
  let huNA : IsNonarchimedean u :=
    absolute_extension_nonarchimedean v uAbove
  let Wu := CompletionPlacesAbove (L := E) v
  letI : Finite Wu := absolute_extensions_separable v
  letI : Nonempty Wu := ⟨uAbove⟩
  letI : MulAction.IsPretransitive Gal(E/K) Wu :=
    above_pretr_nonar v
      (place_nonarchimedean (FinitePlace.mk P))
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra w.1.Completion t.1.Completion :=
    (completionLies w.1 t.1 t.2).toAlgebra
  letI : Algebra v.Completion t.1.Completion :=
    (completionLies v t.1 htv).toAlgebra
  letI : IsScalarTower v.Completion w.1.Completion t.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (completion_lies_trans v w.1 t.1
      w.2 t.2 htv).symm
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion t.1.Completion :=
    (completionLies u t.1 htu).toAlgebra
  letI : IsScalarTower v.Completion u.Completion t.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (completion_lies_trans v u t.1
      huv htu htv).symm
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : FiniteDimensional w.1.Completion t.1.Completion :=
    placeCompletionDimensional w.1 t
  letI : IsGalois w.1.Completion t.1.Completion :=
    placeCompletionGalois w.1 t
  letI : FiniteDimensional v.Completion u.Completion :=
    placeCompletionDimensional v uAbove
  letI : IsGalois v.Completion u.Completion :=
    placeCompletionGalois v uAbove
  let iE : u.Completion →ₐ[v.Completion] t.1.Completion :=
    IsScalarTower.toAlgHom v.Completion u.Completion t.1.Completion
  let Eloc : IntermediateField v.Completion t.1.Completion := iE.fieldRange
  let eE : u.Completion ≃ₐ[v.Completion] Eloc :=
    IntermediateField.topEquiv.symm |>.trans
      ((IntermediateField.equivMap
        (⊤ : IntermediateField v.Completion u.Completion) iE).trans
        (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map iE).symm))
  letI : FiniteDimensional v.Completion Eloc :=
    Module.Finite.equiv eE.toLinearEquiv
  letI : IsGalois v.Completion Eloc := IsGalois.of_algEquiv eE
  let decompE := decompositionCompletionExtension v u
  letI : IsMulCommutative Gal(u.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau => decompE.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompE.symm sigma) (decompE.symm tau)
  letI : IsMulCommutative Gal(Eloc/v.Completion) := by
    refine ⟨⟨fun sigma tau => eE.autCongr.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (eE.autCongr.symm sigma) (eE.autCongr.symm tau)
  let decompM := decompositionCompletionExtension w.1 t.1
  letI : IsMulCommutative Gal(t.1.Completion/w.1.Completion) := by
    refine ⟨⟨fun sigma tau => decompM.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decompM.symm sigma) (decompM.symm tau)
  let localData := CAMaps.canonical
    v.Completion w.1.Completion t.1.Completion Eloc
  let lowerTarget : Gal(Eloc/v.Completion) →* Gal(E/K) :=
    (absoluteValueDecomposition v u).subtype.comp
      (decompE.symm.toMonoidHom.comp eE.autCongr.symm.toMonoidHom)
  let upperTarget : Gal(t.1.Completion/w.1.Completion) →* Gal(M/K') :=
    (absoluteValueDecomposition w.1 t.1).subtype.comp
      decompM.symm.toMonoidHom
  let globalTarget : Gal(M/K') →* Gal(E/K) :=
    compositumGaloisRestriction (K := K) (K' := K') (M := M) E
  have htarget : lowerTarget.comp (localCompositumRestriction Eloc) =
      globalTarget.comp upperTarget := by
    apply MonoidHom.ext
    intro sigma
    let rhoE : Gal(u.Completion/v.Completion) :=
      eE.autCongr.symm (localCompositumRestriction Eloc sigma)
    let tauE : absoluteValueDecomposition v u := decompE.symm rhoE
    let tauM : absoluteValueDecomposition w.1 t.1 :=
      decompM.symm sigma
    change (tauE.1 : Gal(E/K)) =
      AlgEquiv.restrictNormalHom E (tauM.1.restrictScalars K)
    apply AlgEquiv.ext
    intro x
    apply (completionEmbedding u).injective
    calc
      completionEmbedding u (tauE.1 x) =
          rhoE (completionEmbedding u x) := by
        rw [← decompE.apply_symm_apply rhoE]
        exact (decomposition_alg_embedding
          v u tauE x).symm
      _ = completionEmbedding u
          (AlgEquiv.restrictNormalHom E
            (tauM.1.restrictScalars K) x) := by
        apply eE.injective
        apply Subtype.ext
        have hrho :
            eE (rhoE (completionEmbedding u x)) =
              (localCompositumRestriction Eloc sigma)
                (eE (completionEmbedding u x)) := by
          have hcongr := congrArg
            (fun tau : Gal(Eloc/v.Completion) ↦
              tau (eE (completionEmbedding u x)))
            (eE.autCongr.apply_symm_apply
              (localCompositumRestriction Eloc sigma))
          simpa only [rhoE, AlgEquiv.autCongr_apply,
            AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] using hcongr
        have hrhoVal :
            (eE (rhoE (completionEmbedding u x)) : t.1.Completion) =
              sigma (iE (completionEmbedding u x)) := by
          calc
            _ = (((localCompositumRestriction Eloc sigma)
                (eE (completionEmbedding u x)) : Eloc) :
                  t.1.Completion) :=
              congrArg Subtype.val hrho
            _ = sigma (iE (completionEmbedding u x)) := by
              change ((AlgEquiv.restrictNormalHom Eloc
                  (sigma.restrictScalars v.Completion))
                    (eE (completionEmbedding u x)) : t.1.Completion) = _
              simpa using AlgEquiv.restrictNormalHom_apply Eloc
                (sigma.restrictScalars v.Completion)
                (eE (completionEmbedding u x))
        rw [hrhoVal]
        change sigma (iE (completionEmbedding u x)) =
          iE (completionEmbedding u
            (AlgEquiv.restrictNormalHom E
              (tauM.1.restrictScalars K) x))
        have hiE (y : E) : iE (completionEmbedding u y) =
            completionEmbedding t.1 (algebraMap E M y) := by
          exact RingHom.congr_fun
            (completion_lies_comp u t.1 htu) y
        rw [hiE, hiE]
        have hrestrict :
            algebraMap E M
                (AlgEquiv.restrictNormalHom E
                  (tauM.1.restrictScalars K) x) =
              tauM.1 (algebraMap E M x) := by
          exact AlgEquiv.restrictNormal_commutes
            (tauM.1.restrictScalars K) E x
        rw [hrestrict]
        rw [← decompM.apply_symm_apply sigma]
        exact decomposition_alg_embedding
          w.1 t.1 tauM (algebraMap E M x)
  let baseSource : (P.adicCompletion K)ˣ ≃* v.Completionˣ :=
    Units.mapEquiv
      (placeCompletionAdic P).symm.toMulEquiv
  let upperRingEquiv : w.1.Completion ≃+*
      ((factorEquiv q).1.adicCompletion K') :=
    (literalRingAdic wModel).trans
      (RingEquiv.cast (congrArg Subtype.val hQq))
  let upperSource :
      ((factorEquiv q).1.adicCompletion K')ˣ ≃*
        w.1.Completionˣ :=
    Units.mapEquiv upperRingEquiv.symm.toMulEquiv
  have hnorm : baseSource.toMonoidHom.comp
        (completionNormLiteral (K := K) (L := K') P
          (factorEquiv q)) =
      (normOnUnits v.Completion w.1.Completion).comp
        upperSource.toMonoidHom := by
    apply MonoidHom.ext
    intro z
    apply Units.ext
    change (placeCompletionAdic P).symm
        (completionNormLiteral (K := K) (L := K') P
          (factorEquiv q) z : P.adicCompletion K) =
      Algebra.norm v.Completion
        (upperRingEquiv.symm (z :
          (factorEquiv q).1.adicCompletion K'))
    apply (placeCompletionAdic P).injective
    rw [RingEquiv.apply_symm_apply]
    rw [completion_literal_equiv]
    have hn := literal_adic_norm P q wModel
      (upperRingEquiv.symm (z :
        (factorEquiv q).1.adicCompletion K'))
    simpa [upperRingEquiv, hQq, Qq] using hn.symm
  let upper : ((factorEquiv q).1.adicCompletion K')ˣ →*
      Gal(M/K') :=
    upperTarget.comp (localData.upper.comp upperSource.toMonoidHom)
  refine ⟨upper, ?_⟩
  have hsquare := localData.projected_square.postcompose
    lowerTarget upperTarget globalTarget htarget
  have hpre := hsquare.precompose baseSource upperSource
    (completionNormLiteral (K := K) (L := K') P (factorEquiv q))
    hnorm
  have hlower :
      (lowerTarget.comp localData.lower).comp baseSource.toMonoidHom =
        canonicalArtinHom K E P := by
    rw [canonical_global_artin K E P uAbove]
    rw [artin_universe_completion]
    apply MonoidHom.ext
    intro z
    rw [localData.lower_normalized]
    let a : v.Completionˣ := baseSource z
    have he := DFunLike.congr_fun
      (abelian_artin_alg
        v.Completion u.Completion Eloc eE) a
    have he' : eE.autCongr.symm
        (abelianArtinHom v.Completion Eloc a) =
      abelianArtinHom v.Completion u.Completion a := by
      rw [← he]
      exact eE.autCongr.symm_apply_apply _
    change (absoluteValueDecomposition v u).subtype
        (decompE.symm
          (eE.autCongr.symm
            (abelianArtinHom v.Completion Eloc a))) =
      globalArtinUniverse P uAbove a
    rw [he']
    unfold globalArtinUniverse
      completionArtinGlobal
    simp only [MonoidHom.comp_apply]
    rw [← abelian_local_universe]
    rfl
  rw [hlower] at hpre
  simpa only [upper, MonoidHom.comp_assoc] using hpre

/-- The canonical upper finite-place Artin map, indexed by a literal prime
of the upper number field. -/
noncomputable def compositumUpperArtin
    (K K' M : Type)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (Q : HeightOneSpectrum (OK K')) :
    (Q.adicCompletion K')ˣ →* Gal(M/K') :=
  (CLData.canonical K K' M E
    (Q.under (OK K)) ⟨Q, rfl⟩).upper

/-- The upper map just defined carries its canonical projected III.3.2
certificate. -/
theorem compositum_projected_square
    (K K' M : Type)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (Q : HeightOneSpectrum (OK K')) :
    PSquare
      (completionNormLiteral (K := K) (L := K')
        (Q.under (OK K)) ⟨Q, rfl⟩)
      (canonicalArtinHom K E (Q.under (OK K)))
      (compositumUpperArtin K K' M E Q)
      (compositumGaloisRestriction (K := K) (K' := K') (M := M) E) :=
  (CLData.canonical K K' M E
    (Q.under (OK K)) ⟨Q, rfl⟩).projected_square

/-! ### Restricted-product support of the upper compositum factors -/

/-- Contracting finite primes through a finite number-field extension tends
to the cofinite filter. -/
private theorem prime_tendsto_cofinite
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    Filter.Tendsto
      (fun Q : HeightOneSpectrum (OK L) ↦ Q.under (OK K))
      cofinite cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro P
  let e : PlacesAbovePrime K L P →
      HeightOneSpectrum (OK L) := Subtype.val
  have hfinite : Set.Finite (e '' Set.univ) :=
    Set.finite_univ.image e
  refine hfinite.subset ?_
  intro Q hQ
  have hQP : Q.under (OK K) = P := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hQ
  exact ⟨⟨Q, hQP⟩, Set.mem_univ _, rfl⟩

set_option maxHeartbeats 5000000 in
-- The support proof unfolds the canonical compositum square at a varying upper prime.
/-- The III.3.2 upper finite maps have finite support.  Away from the
pullback of the lower ramification set, the completed norm carries units to
units, the lower Artin factor is trivial, and injectivity of compositum
restriction forces the upper factor to be trivial. -/
theorem compositum_upper_eventually
    (K K' M : Type)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]
    (hcompositum : E ⊔ IntermediateField.adjoin K
      (Set.range (algebraMap K' M)) = ⊤) :
    ∀ᶠ Q in cofinite,
      IdeleUnitSubgroup (OK K') K' Q ≤
        (compositumUpperArtin K K' M E Q).ker := by
  letI : NumberField E := NumberField.of_module_finite K E
  have hlower := eventually_trivial_units K E
  have hcontract := prime_tendsto_cofinite K K'
  filter_upwards [hcontract hlower] with Q hQ
  intro x hx
  let P := Q.under (OK K)
  let QP : PlacesAbovePrime K K' P := ⟨Q, rfl⟩
  have hnormUnit :
      completionNormLiteral (K := K) (L := K') P QP x ∈
        IdeleUnitSubgroup (OK K) K P :=
    literal_unit_subgroup K K' P QP x hx
  let target := compositumGaloisRestriction
    (K := K) (K' := K') (M := M) E
  have hinjective : Function.Injective target :=
    compositum_restriction_injective
      (K := K) (K' := K') (M := M) E hcompositum
  have hcomm := DFunLike.congr_fun
    (compositum_projected_square
      K K' M E Q).commutes x
  rw [MonoidHom.mem_ker]
  apply hinjective
  exact hcomm.trans ((hQ _ hnormUnit).trans target.map_one.symm)

end

end Submission.CField.RExist
