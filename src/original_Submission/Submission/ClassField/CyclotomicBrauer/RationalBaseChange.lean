import Submission.ClassField.CyclotomicBrauer.RationalCompositum
import Submission.NumberTheory.Completions.UnramifiedCompletion
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Lemma VII.7.3: base change from the rational construction

This file forms the compositum of the rational cyclic cyclotomic extension
with an arbitrary number field.  Two details are made explicit:

* normalized finite-place absolute values only agree after passing to their
  equivalence classes when restricting from `K` to `ℚ`;
* the safe uniform multiplier is `[K : ℚ]!`, since a local degree is at most,
  but need not divide, `[K : ℚ]` for non-Galois `K`.
-/

namespace Submission.CField.CBrauer

open AbsoluteValue IntermediateField IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped Pointwise TensorProduct

noncomputable section

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance baseChangeRingOfIntegersGaloisAction
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)

set_option synthInstance.maxHeartbeats 500000 in
-- The centered-prime and decomposition-group structures form a deep instance telescope.
set_option maxHeartbeats 4000000 in
/-- The completion degree of a finite Galois extension can be computed from
the centered primes for any nontrivial nonarchimedean normalization of the
base absolute value. -/
theorem centered_ramification_deg
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion =
      ((nonarchimedeanHeightSpectrum v
          (Fact.out : v.IsNontrivial) hvna).asIdeal.ramificationIdxIn
            (NumberField.RingOfIntegers L)) *
        ((nonarchimedeanHeightSpectrum v
          (Fact.out : v.IsNontrivial) hvna).asIdeal.inertiaDegIn
            (NumberField.RingOfIntegers L)) := by
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let p := nonarchimedeanHeightSpectrum
    v (Fact.out : v.IsNontrivial) hvna
  let P := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : P.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_centered
      v w.1 w.2 (Fact.out : v.IsNontrivial) hvna hw hwna
  letI : IsGaloisGroup Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L
  letI : p.asIdeal.IsMaximal := inferInstance
  letI : Field ((NumberField.RingOfIntegers K) ⧸ p.asIdeal) :=
    Ideal.Quotient.field p.asIdeal
  letI : P.asIdeal.IsMaximal := inferInstance
  letI : Field ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) :=
    Ideal.Quotient.field P.asIdeal
  letI : Algebra.IsSeparable
      ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)
      ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) := by
    letI : IsGalois
        ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)
        ((NumberField.RingOfIntegers L) ⧸ P.asIdeal) :=
      { __ := Ideal.Quotient.normal
          (A := NumberField.RingOfIntegers K) (G := Gal(L/K))
          p.asIdeal P.asIdeal }
    infer_instance
  calc
    Module.finrank v.Completion w.1.Completion =
        Nat.card (absoluteValueDecomposition v w.1) :=
      completion_decomposition_card v w
    _ = Nat.card (MulAction.stabilizer Gal(L/K) P.asIdeal) := by
      rw [centered_stabilizer_decomposition v w.1 hw hwna]
    _ = p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) :=
      Ideal.card_stabilizer_eq p.asIdeal p.ne_bot P.asIdeal

set_option synthInstance.maxHeartbeats 500000 in
-- The tensor-product decomposition installs one algebra and module per completed factor.
set_option maxHeartbeats 3000000 in
/-- A chosen completed factor of a finite separable extension has degree at
most the global degree.  No Galois hypothesis is used. -/
theorem completion_finrank_global
    {K : Type v} {L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion ≤ Module.finrank K L := by
  let F := v.Completion
  let W := {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}
  letI : NontriviallyNormedField F :=
    absoluteNontriviallyNormed v
  letI : Algebra K F := completionBaseAlgebra v
  letI : SMul K F := completionBaseSMul v
  letI : Module K F := completionBaseModule v
  letI : Finite W := absolute_extensions_separable v
  letI : Fintype W := Fintype.ofFinite W
  letI (z : W) : Algebra F z.1.Completion :=
    (completionLies v z.1 z.2).toAlgebra
  letI : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  letI : Module.Finite F (L ⊗[K] F) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K F L).toLinearEquiv
  letI (z : W) : Module.Finite F z.1.Completion :=
    Module.Finite.of_surjective
      (completionTensorPlace v z).toLinearMap
      (completions_component_surjective v z)
  let e : (L ⊗[K] F) ≃ₐ[F] (∀ z : W, z.1.Completion) :=
    completionTensorCompletions v
  have hsum :
      (∑ z : W, Module.finrank F z.1.Completion) = Module.finrank K L := by
    calc
      (∑ z : W, Module.finrank F z.1.Completion) =
          Module.finrank F (∀ z : W, z.1.Completion) :=
        (Module.finrank_pi_fintype
          (R := F) (M := fun z : W => z.1.Completion)).symm
      _ = Module.finrank F (L ⊗[K] F) := e.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank F (F ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K F L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
  calc
    Module.finrank F w.1.Completion ≤
        ∑ z : W, Module.finrank F z.1.Completion :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun z : W => Module.finrank F z.1.Completion)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    _ = Module.finrank K L := hsum

set_option synthInstance.maxHeartbeats 500000 in
-- The tensor-to-factor surjection unfolds both tensor-product algebra structures.
set_option maxHeartbeats 2000000 in
/-- A completed factor of an arbitrary finite number-field extension is
finite-dimensional over the completed base.  The existing Galois-specialized
definition is not sufficient for the `ℚ ⊆ K ⊆ KL` base-change tower. -/
@[reducible]
noncomputable def placeCompletionDimensional
    {K : Type v} {L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    FiniteDimensional v.Completion w.1.Completion := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : SMul K v.Completion := completionBaseSMul v
  letI : Module K v.Completion := completionBaseModule v
  letI : Module.Finite v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  exact Module.Finite.of_surjective
    (completionTensorPlace v w).toLinearMap
    (completions_component_surjective v w)

set_option synthInstance.maxHeartbeats 1000000 in
-- Three completion algebras and their scalar tower are elaborated simultaneously.
set_option maxHeartbeats 3000000 in
/-- Compatible places in an arbitrary finite global tower give the usual
factorization of completion degrees. -/
theorem finrank_tower_general
    {K : Type v} {D : Type w} {L : Type u} [Field K] [NumberField K]
    [Field D] [NumberField D] [Field L] [NumberField L]
    [Algebra K D] [Algebra D L] [Algebra K L]
    [IsScalarTower K D L]
    [FiniteDimensional K D] [FiniteDimensional D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (u : AbsoluteValue D ℝ) (w : AbsoluteValue L ℝ)
    (huv : AbsoluteValue.LiesOver u v)
    (hwu : AbsoluteValue.LiesOver w u)
    (hwv : AbsoluteValue.LiesOver w v) :
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra u.Completion w.Completion :=
      (completionLies u w hwu).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    Module.finrank v.Completion w.Completion =
      Module.finrank u.Completion w.Completion *
        Module.finrank v.Completion u.Completion := by
  let uAbove : {u : AbsoluteValue D ℝ // AbsoluteValue.LiesOver u v} :=
    ⟨u, huv⟩
  have hu : u.IsNontrivial := absolute_extension_nontrivial v uAbove
  have huna : IsNonarchimedean u :=
    absolute_extension_nonarchimedean v uAbove
  letI : Fact u.IsNontrivial := ⟨hu⟩
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u huna
  let wAboveU : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w u} :=
    ⟨w, hwu⟩
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.Completion :=
    (completionLies u w hwu).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : IsScalarTower v.Completion u.Completion w.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa using (completion_lies_trans v u w huv hwu hwv).symm
  letI : FiniteDimensional v.Completion u.Completion :=
    placeCompletionDimensional v uAbove
  letI : FiniteDimensional u.Completion w.Completion :=
    placeCompletionDimensional u wAboveU
  letI : FiniteDimensional v.Completion w.Completion :=
    FiniteDimensional.trans v.Completion u.Completion w.Completion
  simpa only [Nat.mul_comm] using
    (Module.finrank_mul_finrank
      v.Completion u.Completion w.Completion).symm

/-- The intermediate completion degree divides the total completion degree
in an arbitrary finite global tower. -/
theorem dvd_tower_general
    {K : Type v} {D : Type w} {L : Type u} [Field K] [NumberField K]
    [Field D] [NumberField D] [Field L] [NumberField L]
    [Algebra K D] [Algebra D L] [Algebra K L]
    [IsScalarTower K D L]
    [FiniteDimensional K D] [FiniteDimensional D L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (u : AbsoluteValue D ℝ) (w : AbsoluteValue L ℝ)
    (huv : AbsoluteValue.LiesOver u v)
    (hwu : AbsoluteValue.LiesOver w u)
    (hwv : AbsoluteValue.LiesOver w v) :
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    letI : Algebra u.Completion w.Completion :=
      (completionLies u w hwu).toAlgebra
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    Module.finrank v.Completion u.Completion ∣
      Module.finrank v.Completion w.Completion := by
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.Completion :=
    (completionLies u w hwu).toAlgebra
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  refine ⟨Module.finrank u.Completion w.Completion, ?_⟩
  rw [Nat.mul_comm]
  exact finrank_tower_general v u w huv hwu hwv

set_option synthInstance.maxHeartbeats 500000 in
-- The compositum carries simultaneous `ℚ`, `K`, rational-block, and cyclotomic towers.
set_option maxHeartbeats 5000000 in
/-- The rational-to-number-field base-change step in Lemma VII.7.3. -/
theorem changeRationalsBridge :
    ChangeRationalsBridge.{u} := by
  intro K _ _ S m _hm data hcyclic hcomplex hdegrees
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra ℚ data.L := data.algebraKL
  letI : FiniteDimensional ℚ data.L := data.finiteDimensionalKL
  letI : IsGalois ℚ data.L := data.isGaloisKL
  change IsCyclic Gal(data.L/ℚ) ∧ _ at hcyclic
  rcases hcyclic with
    ⟨cyclicL, conductor0, C, fieldC, numberFieldC, algebraQC,
      algebraLC, scalarTowerQLC, cyclotomicC0, _⟩
  letI : IsCyclic Gal(data.L/ℚ) := cyclicL
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : Algebra ℚ C := algebraQC
  letI : Algebra data.L C := algebraLC
  letI : IsScalarTower ℚ data.L C := scalarTowerQLC
  obtain ⟨conductor, hconductor, cyclotomicC⟩ :=
    nonzero_cyclotomic_conductor
      (K := ℚ) conductor0 C cyclotomicC0
  letI : NeZero conductor := ⟨hconductor⟩
  letI : IsCyclotomicExtension {conductor} ℚ C := cyclotomicC
  let Omega := AlgebraicClosure K
  let embeddingC : C →ₐ[ℚ] Omega := IsAlgClosed.lift
  let embeddingL : data.L →ₐ[ℚ] Omega :=
    embeddingC.comp (IsScalarTower.toAlgHom ℚ data.L C)
  let zeta := IsCyclotomicExtension.zeta conductor ℚ C
  have hzeta : IsPrimitiveRoot zeta conductor :=
    IsCyclotomicExtension.zeta_spec conductor ℚ C
  let D : IntermediateField K Omega :=
    IntermediateField.adjoin K (Set.range embeddingC)
  let F : IntermediateField K Omega :=
    IntermediateField.adjoin K ({embeddingC zeta} : Set Omega)
  have hCtop : Algebra.adjoin ℚ ({zeta} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hzeta
  have hembeddingC_le : Set.range embeddingC ⊆ (F : Set Omega) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Algebra.adjoin ℚ ({zeta} : Set C) := by
      rw [hCtop]
      exact mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
    | algebraMap x =>
        have hmap : embeddingC (algebraMap ℚ C x) =
            algebraMap K Omega (algebraMap ℚ K x) := by
          rw [embeddingC.commutes]
          exact (IsScalarTower.algebraMap_apply ℚ K Omega x).symm
        rw [hmap]
        exact F.algebraMap_mem _
    | add x y _ _ hx hy =>
        rw [map_add]
        exact F.add_mem hx hy
    | mul x y _ _ hx hy =>
        rw [map_mul]
        exact F.mul_mem hx hy
  have hDF : D = F := by
    apply le_antisymm
    · exact IntermediateField.adjoin_le_iff.mpr hembeddingC_le
    · apply IntermediateField.adjoin_le_iff.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact IntermediateField.subset_adjoin K _ ⟨zeta, rfl⟩
  have hzetaImage : IsPrimitiveRoot (embeddingC zeta) conductor :=
    hzeta.map_of_injective embeddingC.injective
  have hcyclotomicD : IsCyclotomicExtension {conductor} K D := by
    rw [hDF]
    exact hzetaImage.intermediateField_adjoin_isCyclotomicExtension K
  let M : IntermediateField K Omega :=
    IntermediateField.adjoin K (Set.range embeddingL)
  have hMleD : M ≤ D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rcases hy with ⟨x, rfl⟩
    apply IntermediateField.subset_adjoin K
    exact ⟨algebraMap data.L C x, rfl⟩
  letI : Algebra K D := D.algebra'
  letI : IsCyclotomicExtension {conductor} K D := hcyclotomicD
  letI : FiniteDimensional K D :=
    IsCyclotomicExtension.finiteDimensional {conductor} K D
  letI : NumberField D :=
    IsCyclotomicExtension.numberField {conductor} K D
  letI : IsAbelianGalois K D :=
    IsCyclotomicExtension.isAbelianGalois {conductor} K D
  let M0 : IntermediateField K D := M.restrict hMleD
  letI : FiniteDimensional K M0 := inferInstance
  have hGaloisM0 : IsGalois K M0 :=
    (InfiniteGalois.normal_iff_isGalois M0).mp inferInstance
  letI : IsGalois K M0 := hGaloisM0
  let eMM0 : M ≃ₐ[K] M0 :=
    IntermediateField.restrict_algEquiv hMleD
  letI : Algebra K M := M.algebra'
  letI : FiniteDimensional K M :=
    FiniteDimensional.of_surjective
      eMM0.symm.toLinearEquiv.toLinearMap eMM0.symm.surjective
  letI : NumberField M := NumberField.of_module_finite K M
  letI : IsGalois K M := IsGalois.of_algEquiv eMM0.symm
  let jL : data.L →ₐ[ℚ] M :=
    { toFun := fun x =>
        ⟨embeddingL x, IntermediateField.subset_adjoin K _ ⟨x, rfl⟩⟩
      map_one' := Subtype.ext embeddingL.map_one
      map_mul' := fun x y => Subtype.ext (embeddingL.map_mul x y)
      map_zero' := Subtype.ext embeddingL.map_zero
      map_add' := fun x y => Subtype.ext (embeddingL.map_add x y)
      commutes' := fun x => Subtype.ext (embeddingL.commutes x) }
  let B : IntermediateField ℚ M := jL.fieldRange
  letI : Algebra ℚ B := B.algebra'
  let eLB : data.L ≃ₐ[ℚ] B := by
    simpa [B, AlgHom.fieldRange_toSubalgebra jL] using
      (AlgEquiv.ofInjectiveField jL)
  letI : FiniteDimensional ℚ B :=
    FiniteDimensional.of_surjective
      eLB.toLinearEquiv.toLinearMap eLB.surjective
  letI : IsGalois ℚ B := IsGalois.of_algEquiv eLB
  letI : IsCyclic Gal(B/ℚ) :=
    isCyclic_of_surjective (AlgEquiv.autCongr eLB)
      (AlgEquiv.autCongr eLB).surjective
  let restrictionHom : Gal(M/K) →* Gal(B/ℚ) :=
    (AlgEquiv.restrictNormalHom B).comp
      (MulSemiringAction.toAlgAut Gal(M/K) ℚ M)
  have hrestrictionInjective : Function.Injective restrictionHom := by
    intro sigma tau hst
    apply AlgEquiv.coe_algHom_injective
    apply IntermediateField.adjoin_algHom_ext K
    intro x hx
    rcases hx with ⟨y, rfl⟩
    let yB : B := ⟨jL y, ⟨y, rfl⟩⟩
    have heval := congrArg (fun f : Gal(B/ℚ) => (f yB : B)) hst
    have hevalM := congrArg (fun z : B => (z : M)) heval
    simp only [restrictionHom, MonoidHom.comp_apply,
      AlgEquiv.restrictNormalHom_apply] at hevalM
    change sigma (jL y) = tau (jL y)
    change sigma (jL y) = tau (jL y) at hevalM
    exact hevalM
  letI : IsCyclic Gal(M/K) :=
    isCyclic_of_injective restrictionHom hrestrictionInjective
  letI : Algebra data.L M := jL.toRingHom.toAlgebra
  letI : NumberField.IsTotallyComplex data.L := hcomplex
  have htotallyComplexM : NumberField.IsTotallyComplex M :=
    NumberField.isTotallyComplex_of_algebra data.L M
  letI : Algebra M D :=
    (IntermediateField.inclusion hMleD).toRingHom.toAlgebra
  letI : IsScalarTower K M D := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let result : FEData K :=
    { L := M
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := inferInstance
      finiteDimensionalKL := inferInstance
      isGaloisKL := inferInstance }
  refine ⟨result, ?_, htotallyComplexM, ?_⟩
  · change IsCyclic Gal(M/K) ∧ _
    exact ⟨inferInstance, conductor, D, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩
  · rcases hdegrees with ⟨selectedPlaces, hselectedDegrees⟩
    let finalPlaces : ∀ P : S,
        CompletionPlacesAbove (L := M) (FinitePlace.mk P.1).val := fun P => by
      let v := (FinitePlace.mk P.1).val
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P.1⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P.1
      exact Classical.choice
        (absolute_value_extension (K := K) (L := M) v)
    refine ⟨finalPlaces, ?_⟩
    intro P
    let v := (FinitePlace.mk P.1).val
    let w := finalPlaces P
    have hv : v.IsNontrivial := absolute_value_nontrivial P.1
    have hvna : IsNonarchimedean v :=
      fun x y => (FinitePlace.mk P.1).add_le x y
    letI : Fact v.IsNontrivial := ⟨hv⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P.1
    let q : AbsoluteValue ℚ ℝ :=
      v.comp (algebraMap ℚ K).injective
    let hqv : AbsoluteValue.LiesOver v q := ⟨rfl⟩
    have hq : q.IsNontrivial :=
      number_restriction_nontrivial v hv
    have hqna : IsNonarchimedean q := by
      intro x y
      change v (algebraMap ℚ K (x + y)) ≤
        max (v (algebraMap ℚ K x)) (v (algebraMap ℚ K y))
      simpa only [map_add] using hvna (algebraMap ℚ K x) (algebraMap ℚ K y)
    letI : Fact q.IsNontrivial := ⟨hq⟩
    letI : IsUltrametricDist q.Completion :=
      absoluteUltrametricDist q hqna
    let p : finitePrime ℚ :=
      P.1.under (NumberField.RingOfIntegers ℚ)
    let selectedIndex : rationalPrimesBelow K S :=
      rational_primes_below K S P
    let selectedAbove := selectedPlaces selectedIndex
    let pv := (FinitePlace.mk p).val
    have hpv : pv.IsNontrivial := absolute_value_nontrivial p
    have hpvna : IsNonarchimedean pv :=
      fun x y => (FinitePlace.mk p).add_le x y
    letI : Fact pv.IsNontrivial := ⟨hpv⟩
    letI : IsUltrametricDist pv.Completion :=
      placeUltrametricDist p
    letI : NumberField B := NumberField.of_module_finite ℚ B
    letI : Algebra B M := B.toAlgebra
    letI : IsScalarTower ℚ B M := inferInstance
    letI : FiniteDimensional B M := FiniteDimensional.right ℚ B M
    let r : AbsoluteValue B ℝ :=
      w.1.comp (algebraMap B M).injective
    let hrq : AbsoluteValue.LiesOver r q := by
      constructor
      ext x
      change w.1 (algebraMap B M (algebraMap ℚ B x)) =
        v (algebraMap ℚ K x)
      calc
        w.1 (algebraMap B M (algebraMap ℚ B x)) =
            w.1 (algebraMap ℚ M x) := by
          rw [IsScalarTower.algebraMap_apply ℚ B M]
        _ = w.1 (algebraMap K M (algebraMap ℚ K x)) := by
          rw [IsScalarTower.algebraMap_apply ℚ K M]
        _ = v (algebraMap ℚ K x) :=
          DFunLike.congr_fun w.2.comp_eq (algebraMap ℚ K x)
    let hwr : AbsoluteValue.LiesOver w.1 r := ⟨rfl⟩
    let hqw : AbsoluteValue.LiesOver w.1 q := by
      constructor
      ext x
      change w.1 (algebraMap ℚ M x) = v (algebraMap ℚ K x)
      rw [IsScalarTower.algebraMap_apply ℚ K M]
      exact DFunLike.congr_fun w.2.comp_eq (algebraMap ℚ K x)
    let originalPlace : AbsoluteValue data.L ℝ :=
      pullbackAbsoluteValue eLB r
    let horiginalq : AbsoluteValue.LiesOver originalPlace q :=
      pullback_absolute_lies eLB q r hrq
    let originalAbove : CompletionPlacesAbove (L := data.L) q :=
      ⟨originalPlace, horiginalq⟩
    have hcenterV :
        nonarchimedeanHeightSpectrum v hv hvna = P.1 :=
      nonarchimedean_height_spectrum P.1
    have hcenterOver :
        (nonarchimedeanHeightSpectrum v hv hvna).asIdeal.LiesOver
          (nonarchimedeanHeightSpectrum q hq hqna).asIdeal :=
      nonarchimedean_spectrum_centered
        q v hqv hq hqna hv hvna
    have hcenterQ :
        nonarchimedeanHeightSpectrum q hq hqna = p := by
      apply HeightOneSpectrum.ext
      calc
        (nonarchimedeanHeightSpectrum q hq hqna).asIdeal =
            (nonarchimedeanHeightSpectrum v hv hvna).asIdeal.under
              (NumberField.RingOfIntegers ℚ) := hcenterOver.over
        _ = P.1.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
          rw [hcenterV]
        _ = p.asIdeal := rfl
    letI : Algebra q.Completion originalPlace.Completion :=
      (completionLies q originalPlace horiginalq).toAlgebra
    letI : Algebra pv.Completion selectedAbove.1.Completion :=
      (completionLies pv selectedAbove.1 selectedAbove.2).toAlgebra
    letI : Algebra q.Completion r.Completion :=
      (completionLies q r hrq).toAlgebra
    letI : Algebra r.Completion w.1.Completion :=
      (completionLies r w.1 hwr).toAlgebra
    letI : Algebra q.Completion w.1.Completion :=
      (completionLies q w.1 hqw).toAlgebra
    letI : Algebra q.Completion v.Completion :=
      (completionLies q v hqv).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    have hselectedFormula :=
      centered_ramification_deg
        pv hpvna selectedAbove
    have horiginalFormula :=
      centered_ramification_deg
        q hqna originalAbove
    have hcenterPv :
        nonarchimedeanHeightSpectrum pv hpv hpvna = p := by
      exact nonarchimedean_height_spectrum p
    have hselectedOriginal :
        Module.finrank pv.Completion selectedAbove.1.Completion =
          Module.finrank q.Completion originalPlace.Completion := by
      rw [hselectedFormula, horiginalFormula, hcenterPv, hcenterQ]
    have horiginalEmbedded :
        Module.finrank q.Completion originalPlace.Completion =
          Module.finrank q.Completion r.Completion := by
      simpa only [originalPlace] using
        completion_finrank_alg eLB q r hrq
    have hrationalTarget :
        m * (Module.finrank ℚ K).factorial ∣
          Module.finrank q.Completion r.Completion := by
      have hs := hselectedDegrees selectedIndex
      change m * (Module.finrank ℚ K).factorial ∣
        Module.finrank pv.Completion selectedAbove.1.Completion at hs
      rw [hselectedOriginal, horiginalEmbedded] at hs
      exact hs
    have hrationalDvdTotal :
        Module.finrank q.Completion r.Completion ∣
          Module.finrank q.Completion w.1.Completion :=
      dvd_tower_general
        (D := B) (L := M) q r w.1 hrq hwr hqw
    let vAboveQ : {v : AbsoluteValue K ℝ // AbsoluteValue.LiesOver v q} :=
      ⟨v, hqv⟩
    letI : FiniteDimensional q.Completion v.Completion :=
      placeCompletionDimensional q vAboveQ
    have hlocalBaseLe :
        Module.finrank q.Completion v.Completion ≤ Module.finrank ℚ K :=
      completion_finrank_global q vAboveQ
    have htotalTower :
        Module.finrank q.Completion w.1.Completion =
          Module.finrank v.Completion w.1.Completion *
            Module.finrank q.Completion v.Completion :=
      finrank_tower_general
        (D := K) (L := M) q v w.1 hqv w.2 hqw
    have hrationalIntoResult :
        Module.finrank q.Completion r.Completion ∣
          Module.finrank q.Completion v.Completion *
            Module.finrank v.Completion w.1.Completion := by
      rw [Nat.mul_comm, ← htotalTower]
      exact hrationalDvdTotal
    exact dvd_change_factorial
      m (Module.finrank ℚ K)
      (Module.finrank q.Completion v.Completion)
      (Module.finrank q.Completion r.Completion)
      (Module.finrank v.Completion w.1.Completion)
      Module.finrank_pos hlocalBaseLe hrationalTarget hrationalIntoResult

/-- **Lemma VII.7.3.**  The cyclic cyclotomic extension with prescribed
finite local degrees exists unconditionally. -/
theorem rationalChangeStatement : (∀ (K : Type u) [Field K] [NumberField K]
      (S : Finset (finitePrime K)) (m : ℕ),
      0 < m →
        ∃ data : FEData K,
          data.IsCyclicCyclotomic ∧
            data.IsTotallyComplex ∧
            data.LocalDegreesDvd S m) :=
  rational_compositum_change
    changeRationalsBridge

/-- Lemma VII.7.3 in the exact form consumed by Proposition VII.7.2. -/
theorem rationalBaseChange : FinitePrime.{u} :=
  rationalCompositum
    changeRationalsBridge

end

end Submission.CField.CBrauer
