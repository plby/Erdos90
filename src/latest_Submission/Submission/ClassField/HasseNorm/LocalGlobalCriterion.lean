import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.LocalFields.NormSubgroups
import Submission.ClassField.CyclotomicBrauer.LocalizationStatements
import Submission.ClassField.CyclotomicBrauer.IdeleClassRepresentation
import Submission.ClassField.IdeleCohomology.ArchimedeanProduct
import Submission.ClassField.GrunwaldWang.CompletionNormCompatibility
import Submission.NumberTheory.Locals.PlaceExtension
import Submission.NumberTheory.Galois.PlaceCompletionDegree

/-!
# Chapter VIII, Section 3, Theorem 3.1: Hasse norm theorem
-/

namespace Submission.CField.HNorm

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.CBrauer
open Submission.CField.GWang
open CategoryTheory CategoryTheory.Limits Representation
open groupCohomology

noncomputable section
universe u

/-- A global unit is a norm at one finite or infinite completion above the
specified place. -/
def LocalNormPlace
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : Kˣ) : NumberFieldPlace K → Prop
  | .inl P =>
      ∃ Q : UpperPrimeFactors (K := K) (L := L) P,
        Units.map (FinitePlace.embedding P).toMonoidHom a ∈
          (finiteCompletionNorm (K := K) (L := L) P Q).range
  | .inr v =>
      ∃ w : InfinitePlacesAbove (K := K) (L := L) v,
        Units.map (completionEmbedding v.1).toMonoidHom a ∈
          (infiniteCompletionNorm (K := K) (L := L) v w).range

/-- The global norm predicate. -/
def GlobalFieldNorm
    (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : Kˣ) : Prop :=
  a ∈ (Units.map (Algebra.norm K : L →* K)).range

/-- A simultaneous choice of one completion of `L` above every place of
`K`.  The choice is allowed to depend on the element whose local norm
classes are being tested. -/
structure HasseCompletionData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] where
  finiteUpper : ∀ P : HeightOneSpectrum (RingOfIntegers K),
    UpperPrimeFactors (K := K) (L := L) P
  infiniteUpper : ∀ v : InfinitePlace K,
    InfinitePlacesAbove (K := K) (L := L) v

/-- The completed norm subgroup belonging to a chosen place above `v`. -/
noncomputable def hasseLocalSubgroup
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (data : HasseCompletionData K L) :
    ∀ v : NumberFieldPlace K, Subgroup (placeCompletion K v)ˣ
  | .inl P =>
      (finiteCompletionNorm (K := K) (L := L) P
        (data.finiteUpper P)).range
  | .inr v =>
      (infiniteCompletionNorm (K := K) (L := L) v
        (data.infiniteUpper v)).range

/-- The global field-unit norm quotient. -/
abbrev HasseGlobalQuotient
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ normSubgroup K L

/-- The local norm quotient at a chosen completion above `v`. -/
abbrev HasseLocalQuotient
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (data : HasseCompletionData K L) (v : NumberFieldPlace K) :=
  (placeCompletion K v)ˣ ⧸ hasseLocalSubgroup data v

/-- The global-to-local map on norm quotients, including its finite-support
lift to the direct sum.  The representative formula ensures that this is
the literal localization of a global element at every place. -/
structure HasseLocalizationData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (completion : HasseCompletionData K L) where
  toLocalization : MultiplicativeLocalizationData
    (HasseGlobalQuotient K L)
    (fun v => HasseLocalQuotient completion v)
  localizeAt_mk : ∀ (v : NumberFieldPlace K) (x : Kˣ),
    toLocalization.localizeAt v
        (QuotientGroup.mk' (normSubgroup K L) x) =
      QuotientGroup.mk' (hasseLocalSubgroup completion v)
        (Units.map (algebraMap K (placeCompletion K v)) x)

/-- The two arithmetic facts needed to construct norm-quotient
localization: global norms become norms in the chosen completion, and a
global element has a nontrivial local norm class at only finitely many
places. -/
structure HasseLocalizationConstruction
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (completion : HasseCompletionData K L) where
  global_norm_comap : ∀ v,
    normSubgroup K L ≤ (hasseLocalSubgroup completion v).comap
      (Units.map (algebraMap K (placeCompletion K v)))
  non_norm_support : ∀ x : Kˣ,
    {v : NumberFieldPlace K |
      Units.map (algebraMap K (placeCompletion K v)) x ∉
        hasseLocalSubgroup completion v}.Finite

/-- The coordinate map on norm quotients induced by completion. -/
noncomputable def hasseNormLocalize
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {completion : HasseCompletionData K L}
    (data : HasseLocalizationConstruction K L completion)
    (v : NumberFieldPlace K) :
    HasseGlobalQuotient K L →* HasseLocalQuotient completion v :=
  QuotientGroup.map (normSubgroup K L)
    (hasseLocalSubgroup completion v)
    (Units.map (algebraMap K (placeCompletion K v)))
    (data.global_norm_comap v)

@[simp]
theorem hasse_localize_mk
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {completion : HasseCompletionData K L}
    (data : HasseLocalizationConstruction K L completion)
    (v : NumberFieldPlace K) (x : Kˣ) :
    hasseNormLocalize data v
        (QuotientGroup.mk' (normSubgroup K L) x) =
      QuotientGroup.mk' (hasseLocalSubgroup completion v)
        (Units.map (algebraMap K (placeCompletion K v)) x) :=
  QuotientGroup.map_mk' _ _ _ _ _

/-- Turn a dependent function with finite support into an element of the
direct sum without changing any coordinate. -/
private noncomputable def directSumSupport
    {index : Type u} {A : index → Type u} [∀ v, AddCommGroup (A v)]
    (f : ∀ v, A v) (hfinite : {v | f v ≠ 0}.Finite) :
    DirectSum index A :=
  ⟨f, Trunc.mk ⟨hfinite.toFinset.1, fun v => by
    by_cases hv : f v = 0
    · exact Or.inr hv
    · exact Or.inl (by simp [hv])⟩⟩

@[simp]
private theorem direct_sum_support
    {index : Type u} {A : index → Type u} [∀ v, AddCommGroup (A v)]
    (f : ∀ v, A v) (hfinite : {v | f v ≠ 0}.Finite) (v : index) :
    directSumSupport f hfinite v = f v :=
  rfl

/-- The arithmetic construction data canonically produces the
direct-sum-valued norm localization map. -/
noncomputable def hasseLocalizationData
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    {completion : HasseCompletionData K L}
    (data : HasseLocalizationConstruction K L completion) :
    HasseLocalizationData K L completion := by
  let localizeAt := fun v => hasseNormLocalize data v
  have hfinite (q : HasseGlobalQuotient K L) :
      {v : NumberFieldPlace K | localizeAt v q ≠ 1}.Finite := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (normSubgroup K L) q
    apply (data.non_norm_support x).subset
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro hx
    apply hv
    rw [hasse_localize_mk]
    exact (QuotientGroup.eq_one_iff _).2 hx
  let localization : Additive (HasseGlobalQuotient K L) →+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive (HasseLocalQuotient completion v)) :=
    { toFun := fun q => directSumSupport
        (fun v => Additive.ofMul (localizeAt v q.toMul)) (by
          apply (hfinite q.toMul).subset
          intro v hv
          simp only [Set.mem_setOf_eq] at hv ⊢
          intro hzero
          apply hv
          exact congrArg Additive.toMul hzero)
      map_zero' := by
        apply DFinsupp.ext
        intro v
        simp [localizeAt]
      map_add' := by
        intro x y
        apply DFinsupp.ext
        intro v
        simp [localizeAt] }
  exact
    { toLocalization :=
        { localizeAt := localizeAt
          localization := localization
          localization_apply := by
            intro q v
            rfl }
      localizeAt_mk := by
        intro v x
        exact hasse_localize_mk data v x }

/-- The exact cohomological conclusion needed for the Hasse norm theorem:
for every choice of completions, the global norm quotient injects into the
direct sum of the corresponding completed norm quotients. -/
def HasseInjectivityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      ∃ loc : HasseLocalizationData K L completion,
        Function.Injective loc.toLocalization.localization

/-- Every finite Galois extension admits a simultaneous choice of one
completion above every place. -/
def HasseExistenceBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    Nonempty (HasseCompletionData K L)

/-- Lying over at finite primes and extension of embeddings at infinite
places provide the required simultaneous choice of completions. -/
theorem hasseExistenceBridge :
    HasseExistenceBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  classical
  let data : HasseCompletionData K L :=
    { finiteUpper := fun P => by
        let q : P.asIdeal.primesOver (RingOfIntegers L) :=
          Classical.choice inferInstance
        exact ⟨q.1,
          (IsDedekindDomain.mem_primesOverFinset_iff (B := RingOfIntegers L) P.ne_bot).2 q.2⟩
      infiniteUpper := fun v => by
        let w := Classical.choose (infinite_place (L := L) v)
        exact ⟨w, Classical.choose_spec
          (infinite_place (L := L) v)⟩ }
  exact ⟨data⟩

/-- The arithmetic construction input: global norms localize to chosen
local norms, and each global element has only finitely many nontrivial local
norm classes. -/
def HasseConstructionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      Nonempty (HasseLocalizationConstruction K L completion)

/-- A global field norm becomes a norm from every chosen completed
extension.  In the Galois case this is the local conjugacy/product-of-norms
argument. -/
def HasseGlobalBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      ∀ v, normSubgroup K L ≤
        (hasseLocalSubgroup completion v).comap
          (Units.map (algebraMap K (placeCompletion K v)))

-- Completion transport and norm-subgroup comparison require deep instance search.
set_option synthInstance.maxHeartbeats 500000 in
-- Finite completion transport and norm-subgroup comparison require deep instance search.
set_option maxHeartbeats 3000000 in
/-- In a finite Galois extension, all completed norm subgroups above one
nonarchimedean place are equal. -/
private theorem place_norm_subgroup
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (RingOfIntegers K))
    (z w : ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val) :
    let v := (FinitePlace.mk P).val
    letI : Algebra v.Completion z.1.Completion :=
      (completionLies v z.1 z.2).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    normSubgroup v.Completion z.1.Completion =
      normSubgroup v.Completion w.1.Completion := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : MulAction.IsPretransitive Gal(L/K)
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) z w
  have hz : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun y => sigma⁻¹ • y) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  letI : Algebra v.Completion (sigma⁻¹ • w).1.Completion :=
    (completionLies v (sigma⁻¹ • w).1
      (sigma⁻¹ • w).2).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion (sigma⁻¹ • w).1.Completion :=
    placeCompletionDimensional v (sigma⁻¹ • w)
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  exact norm_alg_equiv v.Completion _ _
    (ICohomo.completionTransportAlg v sigma w)

-- The archimedean completion transport has the same nested instance search.
set_option synthInstance.maxHeartbeats 500000 in
-- Archimedean completion transport requires the same nested instance search.
set_option maxHeartbeats 3000000 in
/-- In a finite Galois extension, all completed norm subgroups above one
archimedean place are equal. -/
private theorem infinite_place_subgroup
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (z w : InfinitePlacesAbove (K := K) (L := L) v) :
    letI : Algebra v.1.Completion z.1.1.Completion :=
      (completionLies v.1 z.1.1
        (infinite_lies_comap v z.1 z.2)).toAlgebra
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1
        (infinite_lies_comap v w.1 w.2)).toAlgebra
    normSubgroup v.1.Completion z.1.1.Completion =
      normSubgroup v.1.Completion w.1.1.Completion := by
  letI := ICohomo.placesAboveAction
    (K := K) (L := L) v
  obtain ⟨sigma, hsigmaVal⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (z.2.trans w.2.symm)
  have hsigma : sigma • z = w := by
    apply Subtype.ext
    change ICohomo.infinitePlaceAction sigma z.1 = w.1
    apply Subtype.ext
    rw [ICohomo.infinite_action_val]
    exact congrArg (fun q : InfinitePlace L ↦ q.1) hsigmaVal
  have hz : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun y => sigma⁻¹ • y) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  letI : Algebra v.1.Completion (sigma⁻¹ • w).1.1.Completion :=
    (completionLies v.1 (sigma⁻¹ • w).1.1
      (infinite_lies_comap v
        (sigma⁻¹ • w).1 (sigma⁻¹ • w).2)).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite v.1.Completion (sigma⁻¹ • w).1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v (sigma⁻¹ • w)
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  let e : (sigma⁻¹ • w).1.1.Completion ≃ₐ[v.1.Completion]
      w.1.1.Completion :=
    { ICohomo.infiniteFamilyTransport v sigma w with
      commutes' :=
        ICohomo.infinite_transport_base v sigma w }
  exact norm_alg_equiv v.1.Completion _ _ e

-- Both completion families and the global norm product elaborate together.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both completion families and the global norm product elaborate together.
set_option maxHeartbeats 6000000 in
/-- A global field norm is a norm from every chosen completion.  The global
norm decomposes as the product of the completed norms above the base place;
Galois conjugacy identifies every one of those norm groups with the chosen
one. -/
theorem hasseGlobalBridge :
    HasseGlobalBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _completionCyclic completion place
  rintro _ ⟨x, rfl⟩
  cases place with
  | inl P =>
      let v := (FinitePlace.mk P).val
      let Q₀ := completion.finiteUpper P
      let q₀ := upperPrime (K := K) (L := L) P Q₀
      let W := ICohomo.CompletionPlacesAbove (L := L) v
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : Algebra K v.Completion := completionBaseAlgebra v
      letI : Finite W := absolute_extensions_separable v
      letI : Fintype W := Fintype.ofFinite W
      letI : Nonempty W :=
        absolute_value_extension (K := K) (L := L) v
      letI : MulAction.IsPretransitive Gal(L/K) W :=
        completion_above_pretransitive P
      letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        IsIntegralClosure.MulSemiringAction
          (RingOfIntegers K) K L (RingOfIntegers L)
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
          (upperPrime_under (K := K) (L := L) P Q₀) |>.symm⟩
      letI : IsGaloisGroup Gal(L/K) (RingOfIntegers K)
          (RingOfIntegers L) :=
        IsGaloisGroup.of_isFractionRing Gal(L/K)
          (RingOfIntegers K) (RingOfIntegers L) K L
      obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
        P.asIdeal q.asIdeal q₀.asIdeal Gal(L/K)
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
      have hw₀q : w₀.1.IsEquiv (FinitePlace.mk q₀).val := by
        have h := place_centered_prime w₀.1 hw₀ hw₀na
        rwa [hcenter] at h
      letI (z : W) : Algebra v.Completion z.1.Completion :=
        (completionLies v z.1 z.2).toAlgebra
      letI (z : W) : FiniteDimensional v.Completion z.1.Completion :=
        placeCompletionDimensional v z
      let localNorm (z : W) : v.Completionˣ :=
        normOnUnits v.Completion z.1.Completion
          (Units.map (completionEmbedding z.1).toMonoidHom x)
      have hfactor (z : W) :
          localNorm z ∈ normSubgroup v.Completion w₀.1.Completion := by
        have hz : localNorm z ∈
            normSubgroup v.Completion z.1.Completion := ⟨_, rfl⟩
        rwa [place_norm_subgroup P z w₀] at hz
      have hprod : (∏ z : W, localNorm z) ∈
          normSubgroup v.Completion w₀.1.Completion := by
        apply Subgroup.prod_mem
        intro z _
        exact hfactor z
      have hnorm :
          Units.map (algebraMap K v.Completion)
              (normOnUnits K L x) =
            ∏ z : W, localNorm z := by
        apply Units.ext
        simpa only [normOnUnits, localNorm, Units.coe_map,
          Units.coe_prod] using
          (completion_norm_trace (K := K) (L := L) v (x : L)).1
      have hbase : Units.map (algebraMap K v.Completion)
            (normOnUnits K L x) ∈
          normSubgroup v.Completion w₀.1.Completion := by
        rw [hnorm]
        exact hprod
      have hrange := completion_norm_range
        (K := K) (L := L) P Q₀ w₀.1 w₀.2 hw₀q
          (inferInstance : Module.Finite v.Completion w₀.1.Completion)
      change Units.map (FinitePlace.embedding P).toMonoidHom
          (normOnUnits K L x) ∈
        (finiteCompletionNorm (K := K) (L := L) P Q₀).range
      rw [← hrange]
      have htransport :
          Units.map
              (placeCompletionAdic P).symm.toMonoidHom
              (Units.map (FinitePlace.embedding P).toMonoidHom
                (normOnUnits K L x)) =
            Units.map (algebraMap K v.Completion) (normOnUnits K L x) := by
        apply Units.ext
        change (placeCompletionAdic P).symm
            (FinitePlace.embedding P (Algebra.norm K (x : L))) =
          completionEmbedding v (Algebra.norm K (x : L))
        apply (placeCompletionAdic P).injective
        rw [RingEquiv.apply_symm_apply,
          finite_place_adic]
      change Units.map
          (placeCompletionAdic P).symm.toMonoidHom
          (Units.map (FinitePlace.embedding P).toMonoidHom
            (normOnUnits K L x)) ∈
        normSubgroup v.Completion w₀.1.Completion
      rw [htransport]
      exact hbase
  | inr v =>
      let W := InfinitePlacesAbove (K := K) (L := L) v
      let w₀ := completion.infiniteUpper v
      letI : Fintype W := infiniteCor84ExtensionsFintype v
      letI : Algebra K v.1.Completion := completionBaseAlgebra v.1
      letI (w : W) : Algebra v.1.Completion w.1.1.Completion :=
        (completionLies v.1 w.1.1
          (infinite_lies_comap v w.1 w.2)).toAlgebra
      letI (w : W) : Module.Finite v.1.Completion w.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v w
      let localNorm (w : W) : v.1.Completionˣ :=
        normOnUnits v.1.Completion w.1.1.Completion
          (Units.map (completionEmbedding w.1.1).toMonoidHom x)
      have hfactor (w : W) :
          localNorm w ∈ normSubgroup v.1.Completion w₀.1.1.Completion := by
        have hw : localNorm w ∈
            normSubgroup v.1.Completion w.1.1.Completion := ⟨_, rfl⟩
        rwa [infinite_place_subgroup v w w₀] at hw
      have hprod : (∏ w : W, localNorm w) ∈
          normSubgroup v.1.Completion w₀.1.1.Completion := by
        apply Subgroup.prod_mem
        intro w _
        exact hfactor w
      have hnorm :
          Units.map (algebraMap K v.1.Completion)
              (normOnUnits K L x) =
            ∏ w : W, localNorm w := by
        apply Units.ext
        simpa only [normOnUnits, localNorm, Units.coe_map,
          Units.coe_prod] using
          (infinite_completion_trace
            (K := K) (L := L) v (x : L)).1
      change Units.map (completionEmbedding v.1).toMonoidHom
          (normOnUnits K L x) ∈
        (infiniteCompletionNorm (K := K) (L := L) v w₀).range
      change Units.map (algebraMap K v.1.Completion)
          (normOnUnits K L x) ∈
        normSubgroup v.1.Completion w₀.1.1.Completion
      rw [hnorm]
      exact hprod

/-- Outside finitely many places, a global element belongs to the norm
subgroup of the chosen completed extension. -/
def HasseNonBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      ∀ x : Kˣ, {v : NumberFieldPlace K |
        Units.map (algebraMap K (placeCompletion K v)) x ∉
          hasseLocalSubgroup completion v}.Finite

/-- The two arithmetic components assemble into the localization
construction data. -/
theorem hasse_construction_components
    (hglobal : HasseGlobalBridge.{u})
    (hfinite : HasseNonBridge.{u}) :
    HasseConstructionBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic completion
  exact ⟨
    { global_norm_comap := hglobal K L hcyclic completion
      non_norm_support := hfinite K L hcyclic completion }⟩

/-- The remaining cohomological input after the literal norm localization
map has been constructed.  This is the injectivity supplied by
`H¹(G,C_L)=0`, cyclic periodicity, and the idèle decomposition. -/
def HasseCohomologicalInjectivity : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      ∀ data : HasseLocalizationConstruction K L completion,
        Function.Injective
          (hasseLocalizationData data).toLocalization.localization

/-- The precise comparison data in Milne's cohomological proof.  The
global and local cyclic-periodicity isomorphisms identify degree-two
cohomology with the literal norm quotients, and the final field says that
these identifications carry the cohomology map to localization. -/
structure HCData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L)
    (localization : HasseLocalizationData K L completion) where
  resizedIdeleSequence :
    ShortComplex (Rep (ULift.{u} ℤ) Gal(L/K))
  resized_sequence_exact : resizedIdeleSequence.ShortExact
  idele1Zero : IsZero (H1 resizedIdeleSequence.X₃)
  globalComparison : Additive (HasseGlobalQuotient K L) ≃+
    H2 resizedIdeleSequence.X₁
  localComparison : H2 resizedIdeleSequence.X₂ ≃+
    DirectSum (NumberFieldPlace K)
      (fun v => Additive (HasseLocalQuotient completion v))
  localizationCompatibility : ∀ q : Additive (HasseGlobalQuotient K L),
    localization.toLocalization.localization q =
      localComparison
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          resizedIdeleSequence.f 2 (globalComparison q))

/-- Construction of the comparison data from VII.5.1, cyclic periodicity,
and Proposition VII.2.5. -/
def HasseCohomologicalBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ completion : HasseCompletionData K L,
      ∀ construction : HasseLocalizationConstruction K L completion,
        Nonempty (HCData K L completion
          (hasseLocalizationData construction))

/-- The Chapter VII short exact sequence makes localization injective once
the comparison data has been supplied. -/
theorem HCData.localization_injective
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {completion : HasseCompletionData K L}
    {localization : HasseLocalizationData K L completion}
    (data : HCData K L completion localization) :
    Function.Injective localization.toLocalization.localization := by
  intro x y hxy
  apply data.globalComparison.injective
  apply h_1_third
    data.resized_sequence_exact
    data.idele1Zero
  apply data.localComparison.injective
  rw [← data.localizationCompatibility x,
    ← data.localizationCompatibility y, hxy]

/-- The comparison-data bridge implies the cohomological injectivity
bridge used by the Hasse norm theorem. -/
theorem hasse_cohomological_injectivity
    (hdata : HasseCohomologicalBridge.{u}) :
    HasseCohomologicalInjectivity.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic completion construction
  obtain ⟨data⟩ := hdata K L hcyclic completion construction
  exact data.localization_injective

/-- Arithmetic construction plus the cohomological injection gives the
norm-localization injectivity bridge. -/
theorem hasse_injectivity_construction
    (hconstruct : HasseConstructionBridge.{u})
    (hcohomology : HasseCohomologicalInjectivity.{u}) :
    HasseInjectivityBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic completion
  obtain ⟨data⟩ := hconstruct K L hcyclic completion
  exact ⟨hasseLocalizationData data,
    hcohomology K L hcyclic completion data⟩

/-- Local norm witnesses themselves select a family of completions on
which the localized representative belongs to every chosen norm subgroup. -/
theorem hasse_data_norms
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : Kˣ) (hlocal : ∀ v, LocalNormPlace K L a v) :
    ∃ data : HasseCompletionData K L,
      ∀ v, Units.map (algebraMap K (placeCompletion K v)) a ∈
        hasseLocalSubgroup data v := by
  classical
  let data : HasseCompletionData K L :=
    { finiteUpper := fun P => Classical.choose (hlocal (.inl P))
      infiniteUpper := fun v => Classical.choose (hlocal (.inr v)) }
  refine ⟨data, ?_⟩
  intro v
  cases v with
  | inl P =>
      exact Classical.choose_spec (hlocal (.inl P))
  | inr v =>
      exact Classical.choose_spec (hlocal (.inr v))

/-- The first assertion: a fixed global element is automa a local
norm away from finitely many places of a cyclic extension. -/
def HasseAlmostEverywhere : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ a : Kˣ,
      ∃ S : Finset (NumberFieldPlace K),
        ∀ v, v ∉ S → LocalNormPlace K L a v

/-- Finite support in the localization construction proves the
almost-everywhere clause of the Hasse norm theorem. -/
theorem almost_everywhere_construction
    (hcompletion : HasseExistenceBridge.{u})
    (hconstruct : HasseConstructionBridge.{u}) :
    HasseAlmostEverywhere.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic a
  obtain ⟨completion⟩ := hcompletion K L
  obtain ⟨data⟩ := hconstruct K L hcyclic completion
  let S : Finset (NumberFieldPlace K) :=
    (data.non_norm_support a).toFinset
  refine ⟨S, ?_⟩
  intro v hv
  have hmem : Units.map (algebraMap K (placeCompletion K v)) a ∈
      hasseLocalSubgroup completion v := by
    by_contra hnot
    exact hv (by simpa [S] using hnot)
  cases v with
  | inl P =>
      exact ⟨completion.finiteUpper P, hmem⟩
  | inr v =>
      exact ⟨completion.infiniteUpper v, hmem⟩

/-- The cohomological core: `H¹(G,C_L)=0`, cyclic Tate periodicity, and the
idèle decomposition make the global norm-class localization map injective. -/
def HasseNormBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ a : Kˣ,
      (∀ v, LocalNormPlace K L a v) → GlobalFieldNorm K L a

/-- Injectivity of norm-quotient localization implies the local-global
clause of the Hasse norm theorem. -/
theorem hasse_localization_injectivity
    (hinjective : HasseInjectivityBridge.{u}) :
    HasseNormBridge.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic a hlocal
  obtain ⟨completion, ha⟩ :=
    hasse_data_norms a hlocal
  obtain ⟨loc, hlocInjective⟩ := hinjective K L hcyclic completion
  let q : HasseGlobalQuotient K L :=
    QuotientGroup.mk' (normSubgroup K L) a
  have hlocalization :
      loc.toLocalization.localization (Additive.ofMul q) = 0 := by
    apply DFinsupp.ext
    intro v
    have hcoord := loc.toLocalization.localization_apply q v
    change (loc.toLocalization.localization (Additive.ofMul q)) v =
      Additive.ofMul (loc.toLocalization.localizeAt v q) at hcoord
    rw [hcoord]
    rw [loc.localizeAt_mk]
    have hq : QuotientGroup.mk' (hasseLocalSubgroup completion v)
          (Units.map (algebraMap K (placeCompletion K v)) a) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (ha v)
    rw [hq]
    rfl
  have hqzero : Additive.ofMul q = 0 := by
    apply hlocInjective
    simpa using hlocalization
  have hqone : q = 1 := by
    exact congrArg Additive.toMul hqzero
  exact (QuotientGroup.eq_one_iff a).1 hqone

/-- **Theorem VIII.3.1 (Hasse norm theorem).** -/
def HasseGlobalPrinciple : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic Gal(L/K) → ∀ a : Kˣ,
      (∃ S : Finset (NumberFieldPlace K),
        ∀ v, v ∉ S → LocalNormPlace K L a v) ∧
      ((∀ v, LocalNormPlace K L a v) → GlobalFieldNorm K L a)

theorem hasse_theorem_bridges
    (hae : HasseAlmostEverywhere.{u})
    (hlg : HasseNormBridge.{u}) :
    HasseGlobalPrinciple.{u} := by
  intro K L _ _ _ _ _ _ _ hcyclic a
  exact ⟨hae K L hcyclic a, hlg K L hcyclic a⟩

/-- The Hasse norm theorem reduced to its precise arithmetic localization
construction and the cohomological injectivity cited in the source proof. -/
theorem hasse_localization_inputs
    (hcompletion : HasseExistenceBridge.{u})
    (hconstruct : HasseConstructionBridge.{u})
    (hcohomology : HasseCohomologicalInjectivity.{u}) :
    HasseGlobalPrinciple.{u} :=
  hasse_theorem_bridges
    (almost_everywhere_construction
      hcompletion hconstruct)
    (hasse_localization_injectivity
      (hasse_injectivity_construction
        hconstruct hcohomology))

/-- Version exposing the three genuine remaining mathematical inputs:
global norms localize to local norms, local norm classes have finite
support, and the resulting localization is cohomologically injective. -/
theorem hasse_component_inputs
    (hglobal : HasseGlobalBridge.{u})
    (hfinite : HasseNonBridge.{u})
    (hcohomology : HasseCohomologicalInjectivity.{u}) :
    HasseGlobalPrinciple.{u} :=
  hasse_localization_inputs
    hasseExistenceBridge
    (hasse_construction_components hglobal hfinite)
    hcohomology

/-- Final reduction matching the printed proof: the arithmetic norm facts
and the resized Chapter VII comparison data imply Theorem VIII.3.1. -/
theorem hasse_theorem_comparison
    (hglobal : HasseGlobalBridge.{u})
    (hfinite : HasseNonBridge.{u})
    (hdata : HasseCohomologicalBridge.{u}) :
    HasseGlobalPrinciple.{u} :=
  hasse_component_inputs hglobal hfinite
    (hasse_cohomological_injectivity hdata)

end
end Submission.CField.HNorm
