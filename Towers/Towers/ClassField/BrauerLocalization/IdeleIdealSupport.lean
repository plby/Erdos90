import Towers.ClassField.NormIndex.ClassGenerators
import Towers.ClassField.NormIndex.RestrictedQuotient
import Towers.ClassField.HerbrandQuotients.PermutationAssembly
import Towers.ClassField.BrauerLocalization.HerbrandExact
import Towers.ClassField.BrauerLocalization.RestrictedNegOne
import Towers.ClassField.HasseNorm.IdealMapBridge
import Towers.NumberTheory.ClassGroup.ClassNumberFinite
import Towers.NumberTheory.Ramification.RamificationDiscriminant

/-!
# Lemma VII.4.2 assembly for Theorem VIII.4.2

The prime exponent of the ideal attached to an idèle is its normalized local
order. This identifies integrality outside a finite set with support of the
attached fractional ideal and closes the ideal-map inputs to Lemma VII.4.2.
-/

namespace Towers.CField.BLoc

open Filter Ideal IsDedekindDomain NumberField Set
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HQuotie
open Towers.CField.NIndex
open Towers.CField.HNorm
open scoped nonZeroDivisors RestrictedProduct WithZero

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

private theorem fractional_ideals_places
    {K : Type u} [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K))
    (I : (FractionalIdeal (OK K)⁰ K)ˣ) :
    I ∈ fractionalIdealsPlaces K S ↔
      ∀ P : HeightOneSpectrum (OK K),
        (Sum.inl P : NumberFieldPlace K) ∉ S →
          FractionalIdeal.count K P
            (I : FractionalIdeal (OK K)⁰ K) = 0 := by
  classical
  let Z : Subgroup ((FractionalIdeal (OK K)⁰ K)ˣ) :=
  { carrier := {J | ∀ P : HeightOneSpectrum (OK K),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        FractionalIdeal.count K P
          (J : FractionalIdeal (OK K)⁰ K) = 0}
    one_mem' := by
      intro P _
      exact FractionalIdeal.count_one K P
    mul_mem' := by
      intro A B hA hB P hP
      rw [Units.val_mul,
        FractionalIdeal.count_mul K P A.ne_zero B.ne_zero,
        hA P hP, hB P hP, add_zero]
    inv_mem' := by
      intro A hA P hP
      rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv,
        hA P hP, neg_zero] }
  constructor
  · intro hI
    have hle : fractionalIdealsPlaces K S ≤ Z := by
      apply (Subgroup.closure_le Z).mpr
      rintro J ⟨P, hPS, rfl⟩
      intro Q hQS
      change FractionalIdeal.count K Q
        (P.asIdeal : FractionalIdeal (OK K)⁰ K) = 0
      rw [FractionalIdeal.count_maximal]
      simp only [ite_eq_right_iff]
      intro hQP
      subst Q
      exact (hQS hPS).elim
    exact hle hI
  · intro hI
    let f : HeightOneSpectrum (OK K) →
        (FractionalIdeal (OK K)⁰ K)ˣ := fun P ↦
      fractionalIdealPrime K P ^
        FractionalIdeal.count K P (I : FractionalIdeal (OK K)⁰ K)
    have hf : ∀ P, f P ∈ fractionalIdealsPlaces K S := by
      intro P
      by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
      · exact (fractionalIdealsPlaces K S).zpow_mem
          (Subgroup.subset_closure ⟨P, hPS, rfl⟩) _
      · dsimp only [f]
        rw [hI P hPS]
        simp
    have hprod : (∏ᶠ P, f P) ∈ fractionalIdealsPlaces K S :=
      finprod_induction _
        (fractionalIdealsPlaces K S).one_mem
        (fun _ _ ↦ (fractionalIdealsPlaces K S).mul_mem)
        hf
    have hprod_eq : (∏ᶠ P, f P) = I := by
      apply Units.ext
      change (Units.coeHom (FractionalIdeal (OK K)⁰ K)) (∏ᶠ P, f P) =
        (I : FractionalIdeal (OK K)⁰ K)
      rw [(Units.coeHom (FractionalIdeal (OK K)⁰ K)).map_finprod_of_injective
        Units.coeHom_injective]
      simp only [f, map_zpow, Units.coeHom_apply,
        fractionalIdealPrime]
      change (∏ᶠ P : HeightOneSpectrum (OK K),
          (P.asIdeal : FractionalIdeal (OK K)⁰ K) ^
            FractionalIdeal.count K P
              (I : FractionalIdeal (OK K)⁰ K)) =
        (I : FractionalIdeal (OK K)⁰ K)
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero
    rwa [hprod_eq] at hprod

private theorem idele_count_zero
    {K : Type u} [Field K] [NumberField K]
    (x : IdeleGroup (OK K) K) (P : HeightOneSpectrum (OK K)) :
    x.2.1 P ∈ IdeleUnitSubgroup (OK K) K P ↔
      FractionalIdeal.count K P
        ((ideleIdealMap (OK K) K x :
          (FractionalIdeal (OK K)⁰ K)ˣ) :
          FractionalIdeal (OK K)⁰ K) = 0 := by
  rw [count_idele_ideal]
  change x.2.1 P ∈ (P.adicCompletionIntegers K).units ↔ _
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  let z := Valued.v ((x.2.1 P : (P.adicCompletion K)ˣ) :
    P.adicCompletion K)
  have hz : z ≠ 0 := by
    dsimp only [z]
    simp
  constructor
  · intro hzone
    rw [hzone, WithZero.log_one, neg_zero]
  · intro hlog
    have hlog' : WithZero.log z = 0 := neg_eq_zero.mp hlog
    calc
      z = WithZero.exp (WithZero.log z) := (WithZero.exp_log hz).symm
      _ = 1 := by simp [hlog']

/-- The valuation exponents of the idèle ideal map identify the two
restricted-idèle support conditions in Lemma VII.4.2. -/
theorem ideleSupportBridge : IdeleSupportBridge.{u} := by
  intro K _ _ S
  ext x
  change (∀ P : HeightOneSpectrum (OK K),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        x.2.1 P ∈ IdeleUnitSubgroup (OK K) K P) ↔
    ideleIdealMap (OK K) K x ∈ fractionalIdealsPlaces K S
  rw [fractional_ideals_places]
  constructor <;> intro h P hP
  · exact (idele_count_zero x P).mp
      (h P hP)
  · exact (idele_count_zero x P).mpr
      (h P hP)

/-- The ideal attached to a principal idèle is its principal fractional
ideal, supplying the second bridge in Lemma VII.4.2. -/
theorem principalIdeleBridge :
    PrincipalIdeleBridge.{u} := by
  intro K _ _ a
  exact idele_ideal_principal a

/-- Unconditional Lemma VII.4.2. -/
theorem fractionalIdealPrime : (∀ (K : Type u) [Field K] [NumberField K]
      (S : Finset (NumberFieldPlace K)),
      ContainsAllPlaces K S →
        CIGenera K S →
        principalIdeles (OK K) K ⊔ idelesAtPlaces K S = ⊤) :=
  fractional_ideal_prime
    ideleSupportBridge principalIdeleBridge

/-- The class-generator input to Theorem VII.4.3 is unconditional. -/
theorem generatorsIdelesBridge :
    GeneratorsIdelesBridge.{u} :=
  ideles_bridge_ideal
    fractionalIdealPrime

/-- The finite set of places used in Theorem VII.4.3 exists unconditionally.
It is the union of all infinite places, the finite ramified base primes, and
the contractions of the prime supports of one fractional-ideal representative
of every ideal class of `L`. -/
theorem admissiblePlacesBridge :
    AdmissiblePlacesBridge.{u} := by
  classical
  intro K L _ _ _ _ _ _ _
  let R := NumberField.RingOfIntegers K
  let T := NumberField.RingOfIntegers L
  letI : Finite (ClassGroup T) := classGroup_finite L
  let representativeIdeal : ClassGroup T → (Ideal T)⁰ := fun C ↦
    Classical.choose (ClassGroup.mk0_surjective C)
  have representativeIdeal_spec (C : ClassGroup T) :
      ClassGroup.mk0 (representativeIdeal C) = C :=
    Classical.choose_spec (ClassGroup.mk0_surjective C)
  let representative : ClassGroup T →
      (FractionalIdeal T⁰ L)ˣ := fun C ↦
    FractionalIdeal.mk0 L (representativeIdeal C)
  have representative_spec (C : ClassGroup T) :
      ClassGroup.mk L (representative C) = C := by
    change ClassGroup.mk L
      (FractionalIdeal.mk0 L (representativeIdeal C)) = C
    rw [ClassGroup.mk_mk0, representativeIdeal_spec]
  let generatorPrimes : Set (FinitePrime L) :=
    {P | ∃ C : ClassGroup T,
      FractionalIdeal.count L P
        (representative C : FractionalIdeal T⁰ L) ≠ 0}
  have generatorPrimes_finite : generatorPrimes.Finite := by
    have hfinite : (⋃ C : ClassGroup T, {P : FinitePrime L |
        FractionalIdeal.count L P
          (representative C : FractionalIdeal T⁰ L) ≠ 0}).Finite :=
      Set.finite_iUnion fun C ↦
        Filter.eventually_cofinite.mp
          (FractionalIdeal.finite_factors
            (representative C : FractionalIdeal T⁰ L))
    apply hfinite.subset
    intro P hP
    rcases hP with ⟨C, hPC⟩
    exact Set.mem_iUnion.mpr ⟨C, hPC⟩
  let generatorPlaces : Finset (NumberFieldPlace L) :=
    generatorPrimes_finite.toFinset.image Sum.inl
  let generatorContractions : Finset (NumberFieldPlace K) :=
    generatorPrimes_finite.toFinset.image fun Q ↦
      (Sum.inl (Q.under R) : NumberFieldPlace K)
  let ramifiedIdeals : Set (Ideal R) :=
    {P | ∃ Q : Ideal T, Q.IsPrime ∧ Q ≠ ⊥ ∧
      Q.under R = P ∧ Ideal.ramificationIdx P Q ≠ 1}
  have ramifiedIdeals_finite : ramifiedIdeals.Finite :=
    ramified_base_primes R T
  let ramifiedPrimes : Set (FinitePrime K) :=
    {P | P.asIdeal ∈ ramifiedIdeals}
  have ramifiedPrimes_finite : ramifiedPrimes.Finite := by
    have hinjective : Function.Injective
        (fun P : FinitePrime K ↦ P.asIdeal) := by
      intro P Q hPQ
      exact HeightOneSpectrum.ext_iff.mpr hPQ
    exact Set.Finite.preimage hinjective.injOn ramifiedIdeals_finite
  let ramifiedPlaces : Finset (NumberFieldPlace K) :=
    ramifiedPrimes_finite.toFinset.image Sum.inl
  let infinitePlaces : Finset (NumberFieldPlace K) :=
    Finset.univ.image Sum.inr
  let S : Finset (NumberFieldPlace K) :=
    infinitePlaces ∪ ramifiedPlaces ∪ generatorContractions
  refine ⟨⟨S, ?_, ?_, ?_, ?_⟩⟩
  · intro v
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (by simp [infinitePlaces]))
  · intro Q hQ
    have hramified : Q.under R ∈ ramifiedPrimes := by
      exact ⟨Q.asIdeal, Q.isPrime, Q.ne_bot, rfl, hQ⟩
    have hplace :
        (Sum.inl (Q.under R) : NumberFieldPlace K) ∈ ramifiedPlaces := by
      exact Finset.mem_image.mpr ⟨Q.under R,
        (Set.Finite.mem_toFinset ramifiedPrimes_finite).mpr hramified, rfl⟩
    exact Finset.mem_union_left generatorContractions
      (Finset.mem_union_right infinitePlaces hplace)
  · refine ⟨generatorPlaces, ?_, ?_⟩
    · unfold CIGenera
      apply top_unique
      intro C _
      refine ⟨representative C, ?_, representative_spec C⟩
      apply (fractional_ideals_places
        generatorPlaces (representative C)).2
      intro P hP
      by_contra hcount
      apply hP
      apply Finset.mem_image.mpr
      refine ⟨P, ?_, rfl⟩
      apply (Set.Finite.mem_toFinset generatorPrimes_finite).mpr
      exact ⟨C, hcount⟩
    · intro Q hQ
      have hQgenerator : Q ∈ generatorPrimes := by
        have hQ' : Q ∈ generatorPrimes_finite.toFinset := by
          simpa [generatorPlaces] using hQ
        exact (Set.Finite.mem_toFinset generatorPrimes_finite).mp hQ'
      have hcontraction :
          (Sum.inl (Q.under R) : NumberFieldPlace K) ∈
            generatorContractions := by
        exact Finset.mem_image.mpr ⟨Q,
          (Set.Finite.mem_toFinset generatorPrimes_finite).mpr hQgenerator,
          rfl⟩
      exact Finset.mem_union_right _ hcontraction
  · intro v
    rcases v with ⟨v, hv⟩
    cases v with
    | inl P =>
        letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
          ⟨absolute_value_nontrivial P⟩
        letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
          placeUltrametricDist P
        exact Classical.choice
          (absolute_value_extension (K := K) (L := L)
            (FinitePlace.mk P).val)
    | inr v =>
        let w : InfinitePlace L := Classical.choose
          (InfinitePlace.comap_surjective (K := L) v)
        have hw : w.comap (algebraMap K L) = v := Classical.choose_spec
          (InfinitePlace.comap_surjective (K := L) v)
        exact ⟨w.1, infinite_lies_comap v w hw⟩

/-- Theorem VII.4.3 with its Lemma VII.4.2 input discharged. -/
theorem assembly_remaining_results
    (h27 : LocalHerbrandFormula.{u})
    (h31 : PlacesHerbrandFormula.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)) :=
  statement_previous_results
    h27 h31 admissiblePlacesBridge
      generatorsIdelesBridge
      restrictedQuotientBridge herbrandExactBridge

/-- **Theorem VII.4.3.**  The Herbrand quotient of the idèle class group
of a finite cyclic extension is its degree. -/
theorem ideleHerbrandQuotient :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic Gal(L/K)],
      letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
      letI : CommGroup Gal(L/K) := IsCyclic.commGroup
      HerbrandQuotientValue
        (classCokernelRepresentation (K := K) (L := L))
        (Module.finrank K L : ℚ) :=
  assembly_remaining_results
    restrictedHerbrandFormula placesHerbrandFormula

end

end Towers.CField.BLoc
