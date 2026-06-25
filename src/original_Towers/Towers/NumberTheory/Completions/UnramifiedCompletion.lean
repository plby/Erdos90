import Towers.NumberTheory.Locals.ArchimedeanPlaceClassification
import Towers.NumberTheory.Locals.NonarchimedeanClassification
import Towers.NumberTheory.Completions.CompletedValuationExtension
import Towers.NumberTheory.Galois.FinitePlaceGroup
import Towers.NumberTheory.Galois.FrobeniusElement
import Towers.NumberTheory.Locals.RamificationGroups
import Towers.ClassField.Ideles.FinitePlaceCompletion


namespace Towers.NumberTheory.Milne

open AbsoluteValue IsDedekindDomain NumberField
open Towers.CField.Ideles
open scoped Pointwise WithZero

noncomputable section

/-!
# Unramified global primes and completed local extensions

This file identifies the valuation integer ring of an absolute-value
completion with the corresponding adic completion, transports the local
unramified criterion across that identification, and proves cyclicity of the
completed Galois group at an unramified prime.
-/

set_option maxHeartbeats 6000000 in
-- Extra heartbeats are needed for the large search space in this proof.
set_option backward.isDefEq.respectTransparency false in
theorem completion_ring_one
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    [IsUltrametricDist v.Completion] [IsUltrametricDist u.Completion]
    (h : v.IsEquiv u) (x : v.Completion) :
    ‖completionRing h x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      let e := completionRing h
      have hright : IsClopen {x : v.Completion | ‖x‖ ≤ 1} := by
        rw [show {x : v.Completion | ‖x‖ ≤ 1} =
            Metric.closedBall 0 1 by
          ext y
          simp [Metric.mem_closedBall]]
        exact IsUltrametricDist.isClopen_closedBall
          (0 : v.Completion) one_ne_zero
      have hleft : IsClopen {x : v.Completion | ‖e x‖ ≤ 1} := by
        have hu : IsClopen {y : u.Completion | ‖y‖ ≤ 1} := by
          rw [show {y : u.Completion | ‖y‖ ≤ 1} =
              Metric.closedBall 0 1 by
            ext y
            simp [Metric.mem_closedBall]]
          exact IsUltrametricDist.isClopen_closedBall
            (0 : u.Completion) one_ne_zero
        exact hu.preimage (continuous_ring_equiv h)
      have hset :
          {x : v.Completion | ‖e x‖ ≤ 1 ↔ ‖x‖ ≤ 1} =
            ({x : v.Completion | ‖e x‖ ≤ 1} ∩
              {x : v.Completion | ‖x‖ ≤ 1}) ∪
            ({x : v.Completion | ‖e x‖ ≤ 1}ᶜ ∩
              {x : v.Completion | ‖x‖ ≤ 1}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        tauto
      rw [hset]
      exact ((hleft.inter hright).union
        (hleft.compl.inter hright.compl)).isClosed
  | ih a =>
      have he : completionRing h
          (↑a : v.Completion) =
          (↑(WithAbs.congr v u (.refl F) a) : u.Completion) := by
        have hc : Continuous (WithAbs.congr v u (.refl F)) :=
          ((AbsoluteValue.isEquiv_iff_isHomeomorph v u).1 h).continuous
        unfold completionRing
        rw [UniformSpace.Completion.mapRingEquiv_apply]
        exact UniformSpace.Completion.map_coe
          (uniformContinuous_addMonoidHom_of_continuous hc) a
      rw [he]
      rw [UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe]
      rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
      change u (WithAbs.equiv v a) ≤ 1 ↔ v (WithAbs.equiv v a) ≤ 1
      exact h.le_one_iff.symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem completion_ring_embedding
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) (x : F) :
    completionRing h (completionEmbedding v x) =
      completionEmbedding u x := by
  have hc : Continuous (WithAbs.congr v u (.refl F)) :=
    ((AbsoluteValue.isEquiv_iff_isHomeomorph v u).1 h).continuous
  rw [completionEmbedding_apply, completionEmbedding_apply]
  unfold completionRing
  rw [UniformSpace.Completion.mapRingEquiv_apply]
  exact UniformSpace.Completion.map_coe
    (uniformContinuous_addMonoidHom_of_continuous hc) _

noncomputable def completionIntegerEquiv
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    [IsUltrametricDist v.Completion] [IsUltrametricDist u.Completion]
    (h : v.IsEquiv u) :
    completionIntegerRing v ≃+* completionIntegerRing u where
  toFun x := ⟨completionRing h x,
    by
      change ‖completionRing h (x : v.Completion)‖₊ ≤ 1
      exact_mod_cast
        (completion_ring_one h (x : v.Completion)).2
          (by
            change ‖(x : v.Completion)‖₊ ≤ 1
            simpa only [NormedField.valuation_apply] using x.property)⟩
  invFun y := ⟨(completionRing h).symm y,
    by
      change ‖(completionRing h).symm
        (y : u.Completion)‖₊ ≤ 1
      have hy : ‖(y : u.Completion)‖ ≤ 1 := by
        exact_mod_cast y.property
      have he := completion_ring_one h
        ((completionRing h).symm (y : u.Completion))
      rw [(completionRing h).apply_symm_apply] at he
      exact_mod_cast he.mp hy⟩
  left_inv x := by
    apply Subtype.ext
    exact (completionRing h).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (completionRing h).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact (completionRing h).map_mul
      (x : v.Completion) (y : v.Completion)
  map_add' x y := by
    apply Subtype.ext
    exact (completionRing h).map_add
      (x : v.Completion) (y : v.Completion)

theorem isometry_place_adic
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Isometry (placeCompletionAdic P) := by
  let h := completion_universal (FinitePlace.mk P).val
    (FinitePlace.embedding P) (by
      intro x
      exact (FinitePlace.mk_apply P x).symm)
  change Isometry h.choose
  exact h.choose_spec.1.1

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
noncomputable def placeIntegerAdic
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
      placeUltrametricDist P
    completionIntegerRing (FinitePlace.mk P).val ≃+*
      P.adicCompletionIntegers K where
  toFun x := ⟨placeCompletionAdic P x, by
    change (Valued.v : Valuation (P.adicCompletion K) ℤᵐ⁰)
      (placeCompletionAdic P x) ≤ 1
    rw [← Valued.toNormedField.norm_le_one_iff]
    have hx : ‖(x : (FinitePlace.mk P).val.Completion)‖ ≤ 1 := by
      simpa only [Valuation.mem_integer_iff, NormedField.valuation_apply,
        NNReal.coe_le_coe] using x.property
    have hn : ‖placeCompletionAdic P
        (x : (FinitePlace.mk P).val.Completion)‖ =
        ‖(x : (FinitePlace.mk P).val.Completion)‖ :=
      by
        simpa only [dist_zero_right, map_zero] using
          (isometry_place_adic P).dist_eq
            (x : (FinitePlace.mk P).val.Completion) 0
    rw [hn]
    exact hx⟩
  invFun y := ⟨(placeCompletionAdic P).symm y, by
    change ‖(placeCompletionAdic P).symm
      (y : P.adicCompletion K)‖₊ ≤ 1
    have hy : ‖(y : P.adicCompletion K)‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]
      exact y.property
    have he : ‖(placeCompletionAdic P).symm
        (y : P.adicCompletion K)‖ = ‖(y : P.adicCompletion K)‖ := by
      calc
        _ = ‖placeCompletionAdic P
            ((placeCompletionAdic P).symm
              (y : P.adicCompletion K))‖ :=
          by
            have hn : ‖placeCompletionAdic P
                ((placeCompletionAdic P).symm
                  (y : P.adicCompletion K))‖ =
                ‖(placeCompletionAdic P).symm
                  (y : P.adicCompletion K)‖ :=
              by
                simpa only [dist_zero_right, map_zero] using
                  (isometry_place_adic P).dist_eq
                    ((placeCompletionAdic P).symm
                      (y : P.adicCompletion K)) 0
            exact hn.symm
        _ = _ := congrArg norm
          ((placeCompletionAdic P).apply_symm_apply _)
    exact_mod_cast he.le.trans hy⟩
  left_inv x := by
    apply Subtype.ext
    exact (placeCompletionAdic P).symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact (placeCompletionAdic P).apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact (placeCompletionAdic P).map_mul x y
  map_add' x y := by
    apply Subtype.ext
    exact (placeCompletionAdic P).map_add x y

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
noncomputable def centeredIntegerAdic
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
      ⟨absolute_value_nontrivial Q⟩
    letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
      placeUltrametricDist Q
    completionIntegerRing w ≃+* Q.adicCompletionIntegers K := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  exact (completionIntegerEquiv
    (place_centered_prime w hw hwna)).trans
      (placeIntegerAdic Q)

@[simp]
theorem centered_adic_embedding
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) [IsUltrametricDist w.Completion] (x : K)
    (z : completionIntegerRing w)
    (hz : (z : w.Completion) = completionEmbedding w x) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
      ⟨absolute_value_nontrivial Q⟩
    letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
      placeUltrametricDist Q
    ((centeredIntegerAdic w hw hwna z :
      Q.adicCompletionIntegers K) : Q.adicCompletion K) =
      FinitePlace.embedding Q x := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  change placeCompletionAdic Q
      (completionRing
        (place_centered_prime w hw hwna) z) = _
  rw [hz, completion_ring_embedding,
    finite_place_adic]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
noncomputable def integersCenteredInteger
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
      ⟨absolute_value_nontrivial Q⟩
    letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
      placeUltrametricDist Q
    NumberField.RingOfIntegers K →+* completionIntegerRing w := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  exact (centeredIntegerAdic w hw hwna).symm.toRingHom.comp
    (algebraMap (NumberField.RingOfIntegers K)
      (Q.adicCompletionIntegers K))

@[simp]
theorem integers_centered_coe
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w)
    (x : NumberField.RingOfIntegers K) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
      ⟨absolute_value_nontrivial Q⟩
    letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
      placeUltrametricDist Q
    (((integersCenteredInteger w hw hwna x :
      completionIntegerRing w) : w.Completion)) =
      completionEmbedding w (algebraMap (NumberField.RingOfIntegers K) K x) := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  let e := centeredIntegerAdic w hw hwna
  let z := integersCenteredInteger w hw hwna x
  have hez : e z = algebraMap (NumberField.RingOfIntegers K)
      (Q.adicCompletionIntegers K) x := by
    exact e.apply_symm_apply _
  let h := place_centered_prime w hw hwna
  apply (completionRing h).injective
  rw [completion_ring_embedding]
  apply (placeCompletionAdic Q).injective
  have hez' := congrArg Subtype.val hez
  rw [finite_place_adic]
  change placeCompletionAdic Q
      (completionRing h (z : w.Completion)) =
    FinitePlace.embedding Q
      (algebraMap (NumberField.RingOfIntegers K) K x) at hez'
  exact hez'

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem centered_maximal_ideal
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    Q.asIdeal.map
        (integersCenteredInteger w hw hwna) =
      IsLocalRing.maximalIdeal (completionIntegerRing w) := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  let e := centeredIntegerAdic w hw hwna
  change Q.asIdeal.map
      (e.symm.toRingHom.comp
        (algebraMap (NumberField.RingOfIntegers K)
          (Q.adicCompletionIntegers K))) = _
  rw [← Ideal.map_map,
    adic_integers_maximal (K := K) Q]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e.symm

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
noncomputable def centeredIntegerRing
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    Localization.AtPrime Q.asIdeal →+* completionIntegerRing w := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  exact (centeredIntegerAdic w hw hwna).symm.toRingHom.comp
    (primeAdicIntegers (K := K) Q)

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem centered_integer_comp
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    (centeredIntegerRing w hw hwna).comp
        (algebraMap (NumberField.RingOfIntegers K)
          (Localization.AtPrime Q.asIdeal)) =
      integersCenteredInteger w hw hwna := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  let e := centeredIntegerAdic w hw hwna
  apply DFunLike.ext _ _
  intro x
  apply e.injective
  have hx := adic_integers_algebra (K := K) Q x
  simp [e, centeredIntegerRing,
    integersCenteredInteger]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem maximal_centered_ring
    {K : Type*} [Field K] [NumberField K]
    (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w) :
    let Q := nonarchimedeanHeightSpectrum w hw hwna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal)).map
        (centeredIntegerRing w hw hwna) =
      IsLocalRing.maximalIdeal (completionIntegerRing w) := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Fact (FinitePlace.mk Q).val.IsNontrivial :=
    ⟨absolute_value_nontrivial Q⟩
  letI : IsUltrametricDist (FinitePlace.mk Q).val.Completion :=
    placeUltrametricDist Q
  let e := centeredIntegerAdic w hw hwna
  change (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q.asIdeal)).map
        (e.symm.toRingHom.comp
          (primeAdicIntegers (K := K) Q)) = _
  rw [← Ideal.map_map,
    maximal_completion_integers (K := K) Q]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e.symm

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem integer_maximal_ideal
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w)
    [hQP : (nonarchimedeanHeightSpectrum w hw hwna).asIdeal.LiesOver
      P.asIdeal]
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K)
      (nonarchimedeanHeightSpectrum w hw hwna).asIdeal) :
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    P.asIdeal.map
        ((integersCenteredInteger w hw hwna).comp
          (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L))) =
      IsLocalRing.maximalIdeal (completionIntegerRing w) := by
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  let f := centeredIntegerRing w hw hwna
  letI := Localization.AtPrime.algebraOfLiesOver P.asIdeal Q.asIdeal
  have hloc : P.asIdeal.map
      (algebraMap (NumberField.RingOfIntegers K)
        (Localization.AtPrime Q.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q.asIdeal) :=
    ((Algebra.isUnramifiedAt_iff_map_eq
      (NumberField.RingOfIntegers K) P.asIdeal Q.asIdeal).mp hQ).2
  have hcomp : f.comp
      (algebraMap (NumberField.RingOfIntegers K)
        (Localization.AtPrime Q.asIdeal)) =
      (integersCenteredInteger w hw hwna).comp
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) := by
    calc
      _ = f.comp
          ((algebraMap (NumberField.RingOfIntegers L)
              (Localization.AtPrime Q.asIdeal)).comp
            (algebraMap (NumberField.RingOfIntegers K)
              (NumberField.RingOfIntegers L))) := by
            rw [← IsScalarTower.algebraMap_eq
              (NumberField.RingOfIntegers K)
              (NumberField.RingOfIntegers L)
              (Localization.AtPrime Q.asIdeal)]
      _ = (f.comp
            (algebraMap (NumberField.RingOfIntegers L)
              (Localization.AtPrime Q.asIdeal))).comp
            (algebraMap (NumberField.RingOfIntegers K)
              (NumberField.RingOfIntegers L)) := by
            rw [RingHom.comp_assoc]
      _ = _ := by
            rw [centered_integer_comp
              w hw hwna]
  rw [← hcomp, ← Ideal.map_map, hloc,
    maximal_centered_ring w hw hwna]

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem comp_global_integers
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    (hvna : IsNonarchimedean v)
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hwna : IsNonarchimedean w)
    (hwv : AbsoluteValue.LiesOver w v) :
    letI : Fact v.IsNontrivial := ⟨hv⟩
    letI : Fact w.IsNontrivial := ⟨hw⟩
    letI : IsUltrametricDist v.Completion :=
      absoluteUltrametricDist v hvna
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    (integerLies v w hwv).comp
        (integersCenteredInteger v hv hvna) =
      (integersCenteredInteger w hw hwna).comp
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) := by
  letI : Fact v.IsNontrivial := ⟨hv⟩
  letI : Fact w.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist v.Completion :=
    absoluteUltrametricDist v hvna
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change completionLies v w hwv
      ((integersCenteredInteger v hv hvna x :
        completionIntegerRing v) : v.Completion) =
    ((integersCenteredInteger w hw hwna
      (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) x) : completionIntegerRing w) :
      w.Completion)
  rw [integers_centered_coe,
    integers_centered_coe]
  calc
    completionLies v w hwv
        (completionEmbedding v
          (algebraMap (NumberField.RingOfIntegers K) K x)) =
      completionEmbedding w
        (algebraMap K L
          (algebraMap (NumberField.RingOfIntegers K) K x)) :=
      RingHom.congr_fun (completion_lies_comp v w hwv)
        (algebraMap (NumberField.RingOfIntegers K) K x)
    _ = completionEmbedding w
        (algebraMap (NumberField.RingOfIntegers L) L
          (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L) x)) := by
      congr 1

theorem nonarchimedean_height_spectrum
    {K : Type*} [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    nonarchimedeanHeightSpectrum (FinitePlace.mk P).val
        (absolute_value_nontrivial P)
        (fun x y ↦ (FinitePlace.mk P).add_le x y) = P := by
  apply HeightOneSpectrum.ext
  ext x
  change (FinitePlace.mk P).val
      (algebraMap (NumberField.RingOfIntegers K) K x) < 1 ↔
    x ∈ P.asIdeal
  change ‖FinitePlace.embedding P
      (algebraMap (NumberField.RingOfIntegers K) K x)‖ < 1 ↔ _
  exact FinitePlace.norm_lt_one_iff_mem K P x

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
set_option maxHeartbeats 6000000 in
theorem completion_formally_unramified
    {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : AbsoluteValue L ℝ)
    (hwv : AbsoluteValue.LiesOver w (FinitePlace.mk P).val)
    (hw : w.IsNontrivial) (hwna : IsNonarchimedean w)
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K)
      (nonarchimedeanHeightSpectrum w hw hwna).asIdeal)
    (hFinite :
      letI : Algebra (FinitePlace.mk P).val.Completion w.Completion :=
        (completionLies (FinitePlace.mk P).val w hwv).toAlgebra
      FiniteDimensional (FinitePlace.mk P).val.Completion w.Completion)
    (hSeparable :
      letI : Algebra (FinitePlace.mk P).val.Completion w.Completion :=
        (completionLies (FinitePlace.mk P).val w hwv).toAlgebra
      Algebra.IsSeparable (FinitePlace.mk P).val.Completion w.Completion) :
    let v := (FinitePlace.mk P).val
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : Fact w.IsNontrivial := ⟨hw⟩
    letI : IsUltrametricDist v.Completion :=
      placeUltrametricDist P
    letI : IsUltrametricDist w.Completion :=
      absoluteUltrametricDist w hwna
    letI : Algebra (completionIntegerRing v) (completionIntegerRing w) :=
      completionIntegerLies v w hwv
    Algebra.FormallyUnramified
      (completionIntegerRing v) (completionIntegerRing w) := by
  let v := (FinitePlace.mk P).val
  let hv := absolute_value_nontrivial P
  let hvna : IsNonarchimedean v := fun x y ↦ (FinitePlace.mk P).add_le x y
  let Q := nonarchimedeanHeightSpectrum w hw hwna
  letI : Q.asIdeal.LiesOver P.asIdeal :=
    nonarchimedean_spectrum_lies P w hwv hw hwna
  letI : Fact v.IsNontrivial := ⟨hv⟩
  letI : Fact w.IsNontrivial := ⟨hw⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : IsUltrametricDist w.Completion :=
    absoluteUltrametricDist w hwna
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : FiniteDimensional v.Completion w.Completion := hFinite
  letI : Algebra.IsSeparable v.Completion w.Completion := hSeparable
  let A := completionIntegerRing v
  let B := completionIntegerRing w
  letI : Algebra A B := completionIntegerLies v w hwv
  let eA := centeredIntegerAdic v hv hvna
  letI : IsDiscreteValuationRing A :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm
  letI : Module.Finite A B :=
    completion_integer_module v w hwv hFinite hSeparable
  letI : IsLocalHom (algebraMap A B) :=
    completion_integer_lies v w hwv
  let eB := centeredIntegerAdic w hw hwna
  let Qv := nonarchimedeanHeightSpectrum v hv hvna
  letI : Finite (IsLocalRing.ResidueField A) := by
    letI : Finite
        (IsLocalRing.ResidueField (Qv.adicCompletionIntegers K)) :=
      adicResidueField Qv
    exact Finite.of_equiv
      (IsLocalRing.ResidueField (Qv.adicCompletionIntegers K))
      (IsLocalRing.ResidueField.mapEquiv eA).symm.toEquiv
  letI : Finite (IsLocalRing.ResidueField B) := by
    letI : Finite
        (IsLocalRing.ResidueField (Q.adicCompletionIntegers L)) :=
      adicResidueField Q
    exact Finite.of_equiv
      (IsLocalRing.ResidueField (Q.adicCompletionIntegers L))
      (IsLocalRing.ResidueField.mapEquiv eB).symm.toEquiv
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B) := by infer_instance
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  have hbase : P.asIdeal.map
      (integersCenteredInteger v hv hvna) =
      IsLocalRing.maximalIdeal A := by
    have h := centered_maximal_ideal
      v hv hvna
    rwa [nonarchimedean_height_spectrum P] at h
  have hupper : P.asIdeal.map
      ((integersCenteredInteger w hw hwna).comp
        (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L))) =
      IsLocalRing.maximalIdeal B :=
    integer_maximal_ideal
      P w hw hwna hQ
  have hcomp := comp_global_integers
    v hv hvna w hw hwna hwv
  calc
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
        (P.asIdeal.map
          (integersCenteredInteger v hv hvna)).map
            (algebraMap A B) := by rw [hbase]
    _ = P.asIdeal.map
        ((algebraMap A B).comp
          (integersCenteredInteger v hv hvna)) :=
      Ideal.map_map
        (integersCenteredInteger v hv hvna)
        (algebraMap A B)
    _ = P.asIdeal.map
        ((integersCenteredInteger w hw hwna).comp
          (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L))) := by
      change P.asIdeal.map
          ((integerLies v w hwv).comp
            (integersCenteredInteger v hv hvna)) = _
      rw [hcomp]
    _ = IsLocalRing.maximalIdeal B := hupper

universe u

local instance unramifiedCompletionRingOfIntegersGaloisAction
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L
    (NumberField.RingOfIntegers L)

/-- At an unramified prime, the decomposition group is the Galois group of
the finite residue-field extension, hence is cyclic. -/
theorem decomposition_cyclic_unramified
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [Q.asIdeal.LiesOver P.asIdeal]
    (hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers K) Q.asIdeal) :
    letI : MulSemiringAction Gal(L/K)
        (NumberField.RingOfIntegers L) :=
      IsIntegralClosure.MulSemiringAction
        (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)
    letI : MulSemiringAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      Ideal.pointwiseMulSemiringAction
    IsCyclic (MulAction.stabilizer Gal(L/K) Q.asIdeal) := by
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  letI : MulSemiringAction Gal(L/K) S :=
    unramifiedCompletionRingOfIntegersGaloisAction
  letI : MulSemiringAction Gal(L/K) (Ideal S) :=
    Ideal.pointwiseMulSemiringAction
  let H := MulAction.stabilizer Gal(L/K) Q.asIdeal
  let I := (Q.asIdeal.inertia Gal(L/K)).subgroupOf H
  letI : Finite Gal(L/K) := IsGaloisGroup.finite Gal(L/K) K L
  letI : IsGaloisGroup Gal(L/K) R S :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) R S K L
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Field (R ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : Field (S ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Finite (R ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : Finite (S ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsUnramifiedAt R Q.asIdeal := hQ
  have hInertia : Q.asIdeal.inertia Gal(L/K) = ⊥ :=
    inertia_bot_unramified (R := R) (G := Gal(L/K)) Q.asIdeal
  have hI : I = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subtype.ext
      exact hInertia.le hx
    · exact bot_le
  letI : I.Normal := by
    dsimp only [I]
    exact inertia_normal_decomposition Q.asIdeal
  let eResidue : H ⧸ I ≃* Gal((S ⧸ Q.asIdeal)/(R ⧸ P.asIdeal)) := by
    dsimp only [H, I, R, S]
    exact Ideal.Quotient.stabilizerQuotientInertiaEquiv Gal(L/K)
      P.asIdeal Q.asIdeal
  have hResidueCyclic :
      IsCyclic Gal((S ⧸ Q.asIdeal)/(R ⧸ P.asIdeal)) := inferInstance
  have hQuotientCyclic : IsCyclic (H ⧸ I) :=
    eResidue.isCyclic.mpr hResidueCyclic
  let eBot : H ⧸ I ≃* H ⧸ (⊥ : Subgroup H) :=
    QuotientGroup.quotientMulEquivOfEq hI
  exact QuotientGroup.quotientBot.isCyclic.mp
    (eBot.isCyclic.mp hQuotientCyclic)

end


end Towers.NumberTheory.Milne
