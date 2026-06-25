import Towers.NumberTheory.Galois.FinitePlaceGroup
import Towers.NumberTheory.Completions.TensorDecomposition
import Mathlib.Analysis.Normed.Group.Uniform


/-!
# Local degree and the decomposition group at a finite place

For a finite Galois extension of number fields, the degree of one completed
factor is the order of its decomposition group.  This is the degree part of
Milne, Proposition 8.10, derived from the product decomposition in
Proposition 8.2 and transitivity on the places above the base place.
-/

namespace Towers.NumberTheory.Milne

open AbsoluteValue IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped Pointwise TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance completionDegreeRingOfIntegersGaloisAction :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 4000000 in
omit [NumberField L] in
/-- The degree of a completed factor in a finite Galois extension is the
order of the corresponding decomposition group, once transitivity of the
places above the base value has been supplied. -/
theorem completion_decomposition_card
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Module.finrank v.Completion w.1.Completion =
      Nat.card (absoluteValueDecomposition v w.1) := by
  let F := v.Completion
  let W := CompletionPlacesAbove (L := L) v
  letI : NontriviallyNormedField F :=
    NontriviallyNormedField.ofNormNeOne <| by
      rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
      refine ⟨completionEmbedding v x, ?_, ?_⟩
      · intro hx
        apply hx0
        apply RingHom.injective (completionEmbedding v)
        rw [map_zero]
        exact hx
      · rwa [norm_completionEmbedding]
  letI : Algebra K F := completionBaseAlgebra v
  letI : SMul K F := completionBaseSMul v
  letI : Module K F := completionBaseModule v
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
        (Module.finrank_pi_fintype (R := F) (M := fun z : W => z.1.Completion)).symm
      _ = Module.finrank F (L ⊗[K] F) := e.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank F (F ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K F L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
  have hall (z : W) :
      Module.finrank F z.1.Completion = Module.finrank F w.1.Completion := by
    obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) z w
    have hz : sigma⁻¹ • w = z := by
      calc
        sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
          congrArg (fun y : W => sigma⁻¹ • y) hsigma.symm
        _ = z := inv_smul_smul sigma z
    subst z
    exact (completionTransportAlg v sigma w).toLinearEquiv.finrank_eq
  have hsumCard :
      Nat.card W * Module.finrank F w.1.Completion = Nat.card Gal(L/K) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card W * Module.finrank F w.1.Completion =
          ∑ _z : W, Module.finrank F w.1.Completion := by simp
      _ = ∑ z : W, Module.finrank F z.1.Completion := by
        apply Finset.sum_congr rfl
        intro z _
        exact (hall z).symm
      _ = Module.finrank K L := hsum
      _ = Nat.card Gal(L/K) := (IsGalois.card_aut_eq_finrank K L).symm
  let H := MulAction.stabilizer Gal(L/K) w
  have hindex : H.index = Nat.card W :=
    MulAction.index_stabilizer_of_transitive Gal(L/K) w
  have hgroupCard : Nat.card W * Nat.card H = Nat.card Gal(L/K) := by
    rw [← hindex, mul_comm]
    exact H.card_mul_index
  have hlocal : Module.finrank F w.1.Completion = Nat.card H := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := W))
    exact hsumCard.trans hgroupCard.symm
  have hH : H = MulAction.stabilizer Gal(L/K) w.1 := by
    ext sigma
    change sigma • w = w ↔ sigma • w.1 = w.1
    exact Subtype.ext_iff
  change Module.finrank F w.1.Completion =
    Nat.card (absoluteValueDecomposition v w.1)
  rw [absolute_decomposition_stabilizer v w.1]
  rw [← hH]
  exact hlocal

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 2000000 in
/-- The local degree formula specialized to the normalized absolute value of
a finite prime. -/
theorem finrank_decomposition_card
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk p).val) :
    letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
    Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion =
      Nat.card (absoluteValueDecomposition (FinitePlace.mk p).val w.1) := by
  let v := (FinitePlace.mk p).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive p
  exact completion_decomposition_card v w

/-- A completed factor of a finite global extension is finite-dimensional
over the completed base field. -/
@[reducible]
noncomputable def placeCompletionDimensional
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
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

/-- The completed factor of a finite Galois global extension is Galois over
the completed base. -/
@[reducible]
noncomputable def placeCompletionGalois
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      placeCompletionDimensional v w
    IsGalois v.Completion w.1.Completion := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  apply IsGalois.of_card_aut_eq_finrank
  calc
    Nat.card Gal(w.1.Completion/v.Completion) =
        Nat.card (absoluteValueDecomposition v w.1) :=
      Nat.card_congr
        (decompositionCompletionExtension v w.1).symm.toEquiv
    _ = Module.finrank v.Completion w.1.Completion :=
      (completion_decomposition_card v w).symm

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 5000000 in
/-- If the chosen place is fixed by the whole Galois group, completion has a
single tensor factor: `L ⊗_K K_v` is the chosen completion `L_w`. -/
noncomputable def tensorDecompositionTop
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    [Finite (CompletionPlacesAbove (L := L) v)]
    [Nonempty (CompletionPlacesAbove (L := L) v)]
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (htop : absoluteValueDecomposition v w.1 = ⊤) :
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    (L ⊗[K] v.Completion) ≃ₐ[v.Completion] w.1.Completion := by
  let F := v.Completion
  letI : NontriviallyNormedField F :=
    absoluteNontriviallyNormed v
  letI : Algebra K F := completionBaseAlgebra v
  letI : SMul K F := completionBaseSMul v
  letI : Module K F := completionBaseModule v
  letI : Algebra F w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  letI : Module.Finite F (L ⊗[K] F) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K F L).toLinearEquiv
  letI : FiniteDimensional F w.1.Completion :=
    Module.Finite.of_surjective
      (completionTensorPlace v w).toLinearMap
      (completions_component_surjective v w)
  have hcodomain : Module.finrank F w.1.Completion = Module.finrank K L := by
    calc
      Module.finrank F w.1.Completion =
          Nat.card (absoluteValueDecomposition v w.1) :=
        completion_decomposition_card v w
      _ = Nat.card Gal(L/K) := by rw [htop]; simp
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hdomain : Module.finrank F (L ⊗[K] F) = Module.finrank K L := by
    calc
      Module.finrank F (L ⊗[K] F) = Module.finrank F (F ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K F L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
  have hsurj : Function.Surjective
      (completionTensorPlace v w) :=
    completions_component_surjective v w
  have hinj : Function.Injective
      (completionTensorPlace v w) := by
    change Function.Injective
      (completionTensorPlace v w).toLinearMap
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdomain.trans hcodomain.symm)).2
    exact hsurj
  exact AlgEquiv.ofBijective (completionTensorPlace v w)
    ⟨hinj, hsurj⟩

/-- When the decomposition group is the whole global Galois group, the
global group identifies with the Galois group of the chosen completion. -/
noncomputable def globalDecompositionTop
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v)
    (htop : absoluteValueDecomposition v w.1 = ⊤) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Gal(L/K) ≃* Gal(w.1.Completion/v.Completion) := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  let eTop : Gal(L/K) ≃* (⊤ : Subgroup Gal(L/K)) :=
    Subgroup.topEquiv.symm
  let eDecomposition : (⊤ : Subgroup Gal(L/K)) ≃*
      absoluteValueDecomposition v w.1 :=
    MulEquiv.subgroupCongr htop.symm
  exact (eTop.trans eDecomposition).trans
    (decompositionCompletionExtension v w.1)

omit [NumberField K] [NumberField L] in
/-- The full-decomposition-group equivalence extends each global
automorphism on the embedded global field. -/
@[simp]
theorem global_decomposition_embedding
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v)
    (htop : absoluteValueDecomposition v w.1 = ⊤)
    (sigma : Gal(L/K)) (x : L) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    globalDecompositionTop v w htop sigma
        (completionEmbedding w.1 x) =
      completionEmbedding w.1 (sigma x) := by
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  change decompositionCompletionEquiv v w.1 _
      (completionEmbedding w.1 x) = completionEmbedding w.1 (sigma x)
  rw [decomposition_alg_embedding]
  rfl

/-- The height-one prime singled out by a nonarchimedean completion place. -/
noncomputable def completionDecompositionPrime
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (_hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) :=
  nonarchimedeanHeightSpectrum w.1
    (absolute_extension_nontrivial v w)
    (absolute_extension_nonarchimedean v w)

/-- The decomposition group attached to the distinguished completion place. -/
abbrev completionDecompositionGroup
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) : Subgroup Gal(L/K) :=
  MulAction.stabilizer Gal(L/K) (completionDecompositionPrime v hvna w).asIdeal

/-- The fixed field of the decomposition group at a completion place. -/
abbrev completionDecompositionField
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) : IntermediateField K L :=
  FixedPoints.intermediateField (completionDecompositionGroup v hvna w)

/-- The place of the decomposition field obtained by restricting the chosen
upper place. -/
noncomputable def completionDecompositionPlace
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    AbsoluteValue (completionDecompositionField v hvna w) ℝ :=
  w.1.comp
    (algebraMap (completionDecompositionField v hvna w) L).injective

/-- The distinguished decomposition-field place lies above the base place. -/
theorem completion_decomposition_lies
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    AbsoluteValue.LiesOver (completionDecompositionPlace v hvna w) v := by
  constructor
  ext x
  change w.1
      (algebraMap (completionDecompositionField v hvna w) L
        (algebraMap K (completionDecompositionField v hvna w) x)) = v x
  calc
    w.1
        (algebraMap (completionDecompositionField v hvna w) L
          (algebraMap K (completionDecompositionField v hvna w) x)) =
      w.1 (algebraMap K L x) := by congr 1
    _ = v x := DFunLike.congr_fun w.2.comp_eq x

/-- The chosen upper place lies over its restriction to the decomposition
field. -/
theorem lies_decomposition_field
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    AbsoluteValue.LiesOver w.1
      (completionDecompositionPlace v hvna w) := by
  constructor
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The completion of the distinguished prime of the decomposition field is
the base completion: its local degree is one. -/
theorem decomposition_restricted_finrank
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let P := nonarchimedeanHeightSpectrum w.1 hw hwna
    let H := MulAction.stabilizer Gal(L/K) P.asIdeal
    let D := (FixedPoints.intermediateField H : IntermediateField K L)
    let u : AbsoluteValue D ℝ :=
      w.1.comp (algebraMap D L).injective
    let huv : AbsoluteValue.LiesOver u v := by
      constructor
      ext x
      change w.1 (algebraMap D L (algebraMap K D x)) = v x
      calc
        w.1 (algebraMap D L (algebraMap K D x)) =
            w.1 (algebraMap K L x) := by
          congr 1
        _ = v x := DFunLike.congr_fun w.2.comp_eq x
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    Module.finrank v.Completion u.Completion = 1 := by
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let P := nonarchimedeanHeightSpectrum w.1 hw hwna
  let H := MulAction.stabilizer Gal(L/K) P.asIdeal
  let D := (FixedPoints.intermediateField H : IntermediateField K L)
  let u : AbsoluteValue D ℝ :=
    w.1.comp (algebraMap D L).injective
  let huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change w.1 (algebraMap D L (algebraMap K D x)) = v x
    calc
      w.1 (algebraMap D L (algebraMap K D x)) =
          w.1 (algebraMap K L x) := by
        congr 1
      _ = v x := DFunLike.congr_fun w.2.comp_eq x
  let hwu : AbsoluteValue.LiesOver w.1 u := by
    constructor
    rfl
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let uAbove : CompletionPlacesAbove (K := K) (L := D) v := ⟨u, huv⟩
  have hu : u.IsNontrivial := absolute_extension_nontrivial v uAbove
  have huna : IsNonarchimedean u :=
    absolute_extension_nonarchimedean v uAbove
  letI : Fact u.IsNontrivial := ⟨hu⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u huna
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : SMul K v.Completion := completionBaseSMul v
  letI : Module K v.Completion := completionBaseModule v
  letI : Algebra D u.Completion := completionBaseAlgebra u
  letI : SMul D u.Completion := completionBaseSMul u
  letI : Module D u.Completion := completionBaseModule u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra u.Completion w.1.Completion :=
    (completionLies u w.1 hwu).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let Wv := CompletionPlacesAbove (L := L) v
  letI : Finite Wv := absolute_extensions_separable v
  letI : Nonempty Wv := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) Wv :=
    above_pretr_nonar v hvna
  have hKL := completion_decomposition_card v w
  have hPH : H = absoluteValueDecomposition v w.1 :=
    centered_stabilizer_decomposition v w.1 hw hwna
  have hKL' : Module.finrank v.Completion w.1.Completion = Nat.card H := by
    rw [hKL, ← hPH]
  let Wu := CompletionPlacesAbove (K := D) (L := L) u
  letI : Finite Wu := absolute_extensions_separable u
  letI : Nonempty Wu := absolute_value_extension (K := D) (L := L) u
  letI : MulAction.IsPretransitive Gal(L/D) Wu :=
    above_pretr_nonar u huna
  let wAbove : Wu := ⟨w.1, hwu⟩
  have hDecTop : absoluteValueDecomposition u w.1 = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro tau x
    let e : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
    let h : H := e.symm tau
    have hh : (h.1 : Gal(L/K)) ∈
        absoluteValueDecomposition v w.1 := by
      rw [← hPH]
      exact h.2
    change w.1 (tau x) = w.1 x
    rw [← e.apply_symm_apply tau]
    simpa [e] using hh x
  have hDL := completion_decomposition_card u wAbove
  have hDL' : Module.finrank u.Completion w.1.Completion = Nat.card H := by
    calc
      Module.finrank u.Completion w.1.Completion =
          Nat.card (absoluteValueDecomposition u w.1) := hDL
      _ = Nat.card Gal(L/D) := by rw [hDecTop]; simp
      _ = Nat.card H :=
        (Nat.card_congr
          (IsGaloisGroup.mulEquivAlgEquiv H D L).toEquiv).symm
  letI : IsScalarTower v.Completion u.Completion w.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa using (completion_lies_trans v u w.1 huv hwu w.2).symm
  letI : Module.Finite v.Completion
      (v.Completion ⊗[K] L) := Module.Finite.base_change K v.Completion L
  letI : Module.Finite v.Completion (L ⊗[K] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K v.Completion L).toLinearEquiv
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Module.Finite.of_surjective
      (completionTensorPlace v w).toLinearMap
      (completions_component_surjective v w)
  letI : Module.Finite u.Completion
      (u.Completion ⊗[D] L) := Module.Finite.base_change D u.Completion L
  letI : Module.Finite u.Completion (L ⊗[D] u.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight D u.Completion L).toLinearEquiv
  letI : FiniteDimensional u.Completion w.1.Completion :=
    Module.Finite.of_surjective
      (completionTensorPlace u wAbove).toLinearMap
      (completions_component_surjective u wAbove)
  letI : FiniteDimensional v.Completion u.Completion :=
    FiniteDimensional.left v.Completion u.Completion w.1.Completion
  have htower := Module.finrank_mul_finrank
    v.Completion u.Completion w.1.Completion
  rw [hDL', hKL'] at htower
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  simpa using htower

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The completion of the distinguished decomposition-field place is
canonically equivalent to the original base completion. -/
noncomputable def decompositionCompletionAlg
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let P := nonarchimedeanHeightSpectrum w.1 hw hwna
    let H := MulAction.stabilizer Gal(L/K) P.asIdeal
    let D := (FixedPoints.intermediateField H : IntermediateField K L)
    let u : AbsoluteValue D ℝ :=
      w.1.comp (algebraMap D L).injective
    let huv : AbsoluteValue.LiesOver u v := by
      constructor
      ext x
      change w.1 (algebraMap D L (algebraMap K D x)) = v x
      calc
        w.1 (algebraMap D L (algebraMap K D x)) =
            w.1 (algebraMap K L x) := by congr 1
        _ = v x := DFunLike.congr_fun w.2.comp_eq x
    letI : Algebra v.Completion u.Completion :=
      (completionLies v u huv).toAlgebra
    v.Completion ≃ₐ[v.Completion] u.Completion := by
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let P := nonarchimedeanHeightSpectrum w.1 hw hwna
  let H := MulAction.stabilizer Gal(L/K) P.asIdeal
  let D := (FixedPoints.intermediateField H : IntermediateField K L)
  let u : AbsoluteValue D ℝ :=
    w.1.comp (algebraMap D L).injective
  let huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change w.1 (algebraMap D L (algebraMap K D x)) = v x
    calc
      w.1 (algebraMap D L (algebraMap K D x)) =
          w.1 (algebraMap K L x) := by congr 1
      _ = v x := DFunLike.congr_fun w.2.comp_eq x
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact u.IsNontrivial :=
    ⟨absolute_extension_nontrivial v
      (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  have hdegree : Module.finrank v.Completion u.Completion = 1 :=
    decomposition_restricted_finrank v hvna w
  letI : FiniteDimensional v.Completion u.Completion :=
    FiniteDimensional.of_finrank_pos (by simp [hdegree])
  have hsurj : Function.Surjective (algebraMap v.Completion u.Completion) := by
    change Function.Surjective (Algebra.linearMap v.Completion u.Completion)
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [hdegree] :
        Module.finrank v.Completion v.Completion =
          Module.finrank v.Completion u.Completion)).1
    exact (algebraMap v.Completion u.Completion).injective
  exact AlgEquiv.ofBijective (Algebra.ofId v.Completion u.Completion)
    ⟨(algebraMap v.Completion u.Completion).injective, hsurj⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The distinguished decomposition field embeds into the base completion.
The embedding is obtained by identifying its distinguished completion with
the base completion via the local-degree-one theorem. -/
noncomputable def decompositionEmbeddingCompletion
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let P := nonarchimedeanHeightSpectrum w.1 hw hwna
    let H := MulAction.stabilizer Gal(L/K) P.asIdeal
    let D := (FixedPoints.intermediateField H : IntermediateField K L)
    letI : Algebra K v.Completion := completionBaseAlgebra v
    D →ₐ[K] v.Completion := by
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let P := nonarchimedeanHeightSpectrum w.1 hw hwna
  let H := MulAction.stabilizer Gal(L/K) P.asIdeal
  let D := (FixedPoints.intermediateField H : IntermediateField K L)
  let u : AbsoluteValue D ℝ :=
    w.1.comp (algebraMap D L).injective
  let huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change w.1 (algebraMap D L (algebraMap K D x)) = v x
    calc
      w.1 (algebraMap D L (algebraMap K D x)) =
          w.1 (algebraMap K L x) := by congr 1
      _ = v x := DFunLike.congr_fun w.2.comp_eq x
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact u.IsNontrivial :=
    ⟨absolute_extension_nontrivial v
      (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : SMul K v.Completion := completionBaseSMul v
  letI : Module K v.Completion := completionBaseModule v
  letI : Algebra D u.Completion := completionBaseAlgebra u
  letI : SMul D u.Completion := completionBaseSMul u
  letI : Module D u.Completion := completionBaseModule u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  let e : v.Completion ≃ₐ[v.Completion] u.Completion :=
    decompositionCompletionAlg v hvna w
  refine
    { toRingHom := e.symm.toRingEquiv.toRingHom.comp (completionEmbedding u)
      commutes' := ?_ }
  intro x
  change e.symm (completionEmbedding u (algebraMap K D x)) =
    completionEmbedding v x
  have hcomp :=
    RingHom.congr_fun (completion_lies_comp v u huv) x
  change completionLies v u huv (completionEmbedding v x) =
    completionEmbedding u (algebraMap K D x) at hcomp
  rw [← hcomp]
  change e.symm (e (completionEmbedding v x)) = completionEmbedding v x
  exact e.symm_apply_apply _

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The degree-one completion equivalence, regarded as an equivalence over
the decomposition field itself. -/
noncomputable def decompositionAlgEquiv
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let D := completionDecompositionField v hvna w
    let u := completionDecompositionPlace v hvna w
    let _huv := completion_decomposition_lies v hvna w
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : Algebra D u.Completion := completionBaseAlgebra u
    v.Completion ≃ₐ[D] u.Completion := by
  let D := completionDecompositionField v hvna w
  let u := completionDecompositionPlace v hvna w
  let huv := completion_decomposition_lies v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact u.IsNontrivial :=
    ⟨absolute_extension_nontrivial v
      (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra
  letI : Algebra D u.Completion := completionBaseAlgebra u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  let e : v.Completion ≃ₐ[v.Completion] u.Completion :=
    decompositionCompletionAlg v hvna w
  exact
    { toRingEquiv := e.toRingEquiv
      commutes' := fun x => by
        change e (e.symm (completionEmbedding u x)) = completionEmbedding u x
        exact e.apply_symm_apply _ }

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field embedding into the base completion is compatible
with the embedding of the global field into the chosen upper completion. -/
theorem comple_decom_embed
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let hw := absolute_extension_nontrivial v w
    let hwna := absolute_extension_nonarchimedean v w
    let P := nonarchimedeanHeightSpectrum w.1 hw hwna
    let H := MulAction.stabilizer Gal(L/K) P.asIdeal
    let D := (FixedPoints.intermediateField H : IntermediateField K L)
    ∀ x : D,
      completionLies v w.1 w.2
          (decompositionEmbeddingCompletion v hvna w x) =
        completionEmbedding w.1 (algebraMap D L x) := by
  dsimp only
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  let P := nonarchimedeanHeightSpectrum w.1 hw hwna
  let H := MulAction.stabilizer Gal(L/K) P.asIdeal
  let D := (FixedPoints.intermediateField H : IntermediateField K L)
  let u : AbsoluteValue D ℝ :=
    w.1.comp (algebraMap D L).injective
  let huv : AbsoluteValue.LiesOver u v := by
    constructor
    ext x
    change w.1 (algebraMap D L (algebraMap K D x)) = v x
    calc
      w.1 (algebraMap D L (algebraMap K D x)) =
          w.1 (algebraMap K L x) := by congr 1
      _ = v x := DFunLike.congr_fun w.2.comp_eq x
  let hwu : AbsoluteValue.LiesOver w.1 u := by
    constructor
    rfl
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fact u.IsNontrivial :=
    ⟨absolute_extension_nontrivial v
      (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D u.Completion := completionBaseAlgebra u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  let e : v.Completion ≃ₐ[v.Completion] u.Completion :=
    decompositionCompletionAlg v hvna w
  intro x
  change completionLies v w.1 w.2
      (e.symm (completionEmbedding u x)) =
    completionEmbedding w.1 (algebraMap D L x)
  calc
    completionLies v w.1 w.2
          (e.symm (completionEmbedding u x)) =
        completionLies u w.1 hwu
          (completionLies v u huv
            (e.symm (completionEmbedding u x))) :=
      (RingHom.congr_fun
        (completion_lies_trans v u w.1 huv hwu w.2)
        (e.symm (completionEmbedding u x))).symm
    _ = completionLies u w.1 hwu
          (e (e.symm (completionEmbedding u x))) := rfl
    _ = completionLies u w.1 hwu
          (completionEmbedding u x) := by rw [e.apply_symm_apply]
    _ = completionEmbedding w.1 (algebraMap D L x) :=
      RingHom.congr_fun (completion_lies_comp u w.1 hwu) x

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 3000000 in
/-- Scalar extension from the decomposition field directly to the original
base completion maps into the chosen upper completion. -/
noncomputable def decompositionTensorPlace
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let D := completionDecompositionField v hvna w
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    (L ⊗[D] v.Completion) →ₐ[v.Completion] w.1.Completion := by
  let D := completionDecompositionField v hvna w
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra
  letI : SMul D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra.toSMul
  letI : Module D v.Completion := Algebra.toModule
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : SMul v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra.toSMul
  letI : Module v.Completion w.1.Completion := Algebra.toModule
  letI : Algebra D w.1.Completion :=
    ((completionEmbedding w.1).comp (algebraMap D L)).toAlgebra
  letI : SMul D w.1.Completion :=
    ((completionEmbedding w.1).comp (algebraMap D L)).toAlgebra.toSMul
  letI : Module D w.1.Completion := Algebra.toModule
  letI : IsScalarTower D v.Completion w.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    exact (comple_decom_embed
      v hvna w x).symm
  let j : L →ₐ[D] w.1.Completion :=
    { toRingHom := completionEmbedding w.1
      commutes' := fun _ => rfl }
  exact (j.liftEquiv D v.Completion L w.1.Completion).comp
    (Algebra.TensorProduct.commRight D v.Completion L).symm.toAlgHom

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 1000000 in
@[simp]
theorem decomposition_tensor_tmul
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v)
    (a : L) (b : v.Completion) :
    let D := completionDecompositionField v hvna w
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    decompositionTensorPlace v hvna w (a ⊗ₜ[D] b) =
      completionEmbedding w.1 a *
        completionLies v w.1 w.2 b := by
  dsimp only
  let D := completionDecompositionField v hvna w
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : SMul v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra.toSMul
  letI : Module v.Completion w.1.Completion := Algebra.toModule
  simp only [completionEmbedding_apply, WithAbs.equiv_symm_apply]
  change b • completionEmbedding w.1 a =
    completionEmbedding w.1 a * completionLies v w.1 w.2 b
  rw [Algebra.smul_def]
  exact mul_comm _ _

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field scalar-extension map reaches the entire chosen
upper completion. -/
theorem decomposition_tensor_surjective
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let D := completionDecompositionField v hvna w
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Function.Surjective
      (decompositionTensorPlace v hvna w) := by
  dsimp only
  let D := completionDecompositionField v hvna w
  let H := completionDecompositionGroup v hvna w
  let u := completionDecompositionPlace v hvna w
  let huv := completion_decomposition_lies v hvna w
  let hwu := lies_decomposition_field v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let uAbove : CompletionPlacesAbove (K := D) (L := L) u := ⟨w.1, hwu⟩
  have hu : u.IsNontrivial := absolute_extension_nontrivial v
    (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)
  have huna : IsNonarchimedean u :=
    absolute_extension_nonarchimedean v
      (⟨u, huv⟩ : CompletionPlacesAbove (K := K) (L := D) v)
  letI : Fact u.IsNontrivial := ⟨hu⟩
  letI : NontriviallyNormedField v.Completion :=
    absoluteNontriviallyNormed v
  letI : NontriviallyNormedField u.Completion :=
    absoluteNontriviallyNormed u
  letI : IsUltrametricDist u.Completion :=
    absoluteUltrametricDist u huna
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra
  letI : Algebra D u.Completion := completionBaseAlgebra u
  letI : Algebra v.Completion u.Completion :=
    (completionLies v u huv).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra u.Completion w.1.Completion :=
    (completionLies u w.1 hwu).toAlgebra
  let eD : v.Completion ≃ₐ[D] u.Completion :=
    decompositionAlgEquiv v hvna w
  let pull : (L ⊗[D] u.Completion) →ₗ[D] (L ⊗[D] v.Completion) :=
    TensorProduct.map (LinearMap.id (R := D) (M := L)) eD.symm.toLinearMap
  have hmap (b : u.Completion) :
      completionLies v w.1 w.2 (eD.symm b) =
        completionLies u w.1 hwu b := by
    calc
      completionLies v w.1 w.2 (eD.symm b) =
          completionLies u w.1 hwu
            (completionLies v u huv (eD.symm b)) :=
        (RingHom.congr_fun
          (completion_lies_trans v u w.1 huv hwu w.2)
          (eD.symm b)).symm
      _ = completionLies u w.1 hwu (eD (eD.symm b)) := rfl
      _ = completionLies u w.1 hwu b := by rw [eD.apply_symm_apply]
  intro y
  obtain ⟨z, hz⟩ :=
    completions_component_surjective u uAbove y
  refine ⟨pull z, ?_⟩
  rw [← hz]
  clear hz y
  induction z with
  | zero => simp [pull]
  | add x y hx hy => simp [pull, hx, hy]
  | tmul a b =>
      rw [show pull (a ⊗ₜ[D] b) = a ⊗ₜ[D] eD.symm b by
        exact TensorProduct.map_tmul _ _ _ _]
      rw [decomposition_tensor_tmul,
        tensor_place_tmul, hmap]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- Scalar extension from the decomposition field to the base completion is
exactly the chosen upper completion. -/
noncomputable def decompositionTensorCompletion
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let D := completionDecompositionField v hvna w
    letI : Algebra K v.Completion := completionBaseAlgebra v
    letI : Algebra D v.Completion :=
      (decompositionEmbeddingCompletion v hvna w).toAlgebra
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    (L ⊗[D] v.Completion) ≃ₐ[v.Completion] w.1.Completion := by
  let D := completionDecompositionField v hvna w
  let H := completionDecompositionGroup v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  letI : Algebra K v.Completion := completionBaseAlgebra v
  letI : Algebra D v.Completion :=
    (decompositionEmbeddingCompletion v hvna w).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Module.Finite v.Completion (v.Completion ⊗[D] L) :=
    Module.Finite.base_change D v.Completion L
  letI : Module.Finite v.Completion (L ⊗[D] v.Completion) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight D v.Completion L).toLinearEquiv
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  have hsource : Module.finrank v.Completion (L ⊗[D] v.Completion) =
      Module.finrank D L := by
    calc
      Module.finrank v.Completion (L ⊗[D] v.Completion) =
          Module.finrank v.Completion (v.Completion ⊗[D] L) :=
        (Algebra.TensorProduct.commRight D v.Completion L).toLinearEquiv
          |>.finrank_eq.symm
      _ = Module.finrank D L := Module.finrank_baseChange
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  have hPH : H = absoluteValueDecomposition v w.1 :=
    centered_stabilizer_decomposition v w.1 hw hwna
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  have htarget : Module.finrank v.Completion w.1.Completion =
      Module.finrank D L := by
    calc
      Module.finrank v.Completion w.1.Completion =
          Nat.card (absoluteValueDecomposition v w.1) :=
        completion_decomposition_card v w
      _ = Nat.card H := by rw [← hPH]
      _ = Nat.card Gal(L/D) := Nat.card_congr eH.toEquiv
      _ = Module.finrank D L := IsGalois.card_aut_eq_finrank D L
  let f := decompositionTensorPlace v hvna w
  have hsurj : Function.Surjective f :=
    decomposition_tensor_surjective v hvna w
  have hinj : Function.Injective f := by
    change Function.Injective f.toLinearMap
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hsource.trans htarget.symm)).2 hsurj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The Galois group over the decomposition field is the Galois group of the
chosen completion over the original base completion. -/
noncomputable def decompositionGaloisCompletion
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let D := completionDecompositionField v hvna w
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Gal(L/D) ≃* Gal(w.1.Completion/v.Completion) := by
  let D := completionDecompositionField v hvna w
  let H := completionDecompositionGroup v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  have hPH : H = absoluteValueDecomposition v w.1 :=
    centered_stabilizer_decomposition v w.1 hw hwna
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  exact eH.symm.trans
    ((MulEquiv.subgroupCongr hPH).trans
      (decompositionCompletionExtension v w.1))

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
/-- The decomposition-field Galois equivalence extends the corresponding
global automorphism on the embedded global field. -/
@[simp]
theorem decomposition_galois_embedding
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v)
    (sigma : Gal(L/(completionDecompositionField v hvna w))) (x : L) :
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    decompositionGaloisCompletion v hvna w sigma
        (completionEmbedding w.1 x) =
      completionEmbedding w.1 (sigma x) := by
  let D := completionDecompositionField v hvna w
  let H := completionDecompositionGroup v hvna w
  letI : NumberField D := NumberField.of_module_finite K D
  letI : IsGaloisGroup H D L :=
    IsGaloisGroup.subgroup Gal(L/K) K L H
  letI : FiniteDimensional D L := IsGaloisGroup.finiteDimensional H D L
  letI : IsGalois D L := IsGaloisGroup.isGalois H D L
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  have hPH : H = absoluteValueDecomposition v w.1 :=
    centered_stabilizer_decomposition v w.1 hw hwna
  let eH : H ≃* Gal(L/D) := IsGaloisGroup.mulEquivAlgEquiv H D L
  change decompositionCompletionEquiv v w.1 _
      (completionEmbedding w.1 x) = completionEmbedding w.1 (sigma x)
  rw [decomposition_alg_embedding]
  have hs := eH.apply_symm_apply sigma
  have hsx := congrArg (fun tau : Gal(L/D) => tau x) hs
  exact congrArg (completionEmbedding w.1) hsx

end

end Towers.NumberTheory.Milne
