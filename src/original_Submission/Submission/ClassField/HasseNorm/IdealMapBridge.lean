import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.HasseNorm.ModulusUnitCofinality
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# The ideal-map bridge in Proposition V.4.6

This file supplies the arithmetic compatibility facts left abstract in
`IdealMapBridge`.  The key point is that the exponent of the
fractional ideal attached to an idèle is the normalized order of the
corresponding finite coordinate.
-/

namespace Submission.CField.HNorm

open Filter Ideal IsDedekindDomain NumberField Set
open Submission.NumberTheory.Milne
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.Ideles
open scoped nonZeroDivisors RestrictedProduct WithZero

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

variable {K : Type u} [Field K] [NumberField K]

/-- The prime exponent of the ideal attached to an idèle is the normalized
order of its coordinate at that prime. -/
theorem count_idele_ideal (a : IdeleGroup (OK K) K)
    (P : HeightOneSpectrum (OK K)) :
    FractionalIdeal.count K P
        ((ideleIdealMap (OK K) K a :
          (FractionalIdeal (OK K)⁰ K)ˣ) : FractionalIdeal (OK K)⁰ K) =
      -WithZero.log
        (Valued.v ((a.2.1 P : (P.adicCompletion K)ˣ) :
          P.adicCompletion K)) := by
  let e := ideleExponentHom (OK K) K a.2
  have h := congrArg (fun z : Multiplicative
      (HeightOneSpectrum (OK K) →₀ ℤ) ↦ z.toAdd P)
    ((fractionalIdealFactorization (OK K) K).symm_apply_apply e)
  change FractionalIdeal.count K P
      (((fractionalIdealFactorization (OK K) K e :
        (FractionalIdeal (OK K)⁰ K)ˣ) : FractionalIdeal (OK K)⁰ K)) =
        e.toAdd P at h
  rw [show ideleIdealMap (OK K) K a =
      fractionalIdealFactorization (OK K) K e by rfl]
  rw [h]
  exact idele_exponent_hom (OK K) K a.2 P

/-- A ray-principal local unit is, in particular, a unit in the completed
valuation ring. -/
theorem ray_idele_unit
    (P : HeightOneSpectrum (OK K)) (n : ℕ) :
    rayLocalSubgroup (K := K) P n ≤
      IdeleUnitSubgroup (OK K) K P := by
  intro x hx
  let A := P.adicCompletionIntegers K
  change x ∈ (P.adicCompletionIntegers K).units
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  rw [rayLocalSubgroup] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  change Valued.v
      (((A.unitGroup.subtype.comp A.unitGroupMulEquiv.symm.toMonoidHom) u :
        (P.adicCompletion K)ˣ) : P.adicCompletion K) = 1
  simpa only [A, ValuationSubring.coe_unitGroupMulEquiv_symm_apply] using
    (Valuation.Integers.valuation_unit
      (Valuation.integer.integers
        (Valued.v : Valuation (P.adicCompletion K) ℤᵐ⁰)) u)

set_option maxHeartbeats 800000 in
-- Unfolding the dependent completed-unit subgroups requires extra elaboration time.
/-- The ideal map sends the modulus idèles to ideals prime to the finite
part of the modulus. -/
theorem modulus_lands_prime (m : Modulus K) :
    ModulusLandsPrime m := by
  intro a P hP
  rw [count_idele_ideal]
  let A := P.adicCompletionIntegers K
  have hray := a.property.1 P hP
  rw [rayLocalSubgroup] at hray
  obtain ⟨u, hu, heq⟩ := hray
  have hval : Valued.v ((a.1.2.1 P : (P.adicCompletion K)ˣ) :
      P.adicCompletion K) = 1 := by
    rw [← heq]
    change Valued.v
      (((A.unitGroup.subtype.comp A.unitGroupMulEquiv.symm.toMonoidHom) u :
        (P.adicCompletion K)ˣ) : P.adicCompletion K) = 1
    simpa only [A, ValuationSubring.coe_unitGroupMulEquiv_symm_apply] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers
          (Valued.v : Valuation (P.adicCompletion K) ℤᵐ⁰)) u)
  rw [hval, WithZero.log_one, neg_zero]

/-- The normalized adic order of a global element is the exponent of its
principal fractional ideal. -/
theorem normalized_adic_singleton
    {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (x : Fˣ) :
    normalizedAdicOrder P x =
      FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton R⁰ (x : F)) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq R⁰ (x : F)
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, IsLocalization.mk'_zero] at hnd
    exact x.ne_zero hnd.symm
  have hd : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hvn : P.intValuation n ≠ 0 := P.intValuation_ne_zero n hn
  have hvd : P.intValuation (d : R) ≠ 0 :=
    P.intValuation_ne_zero (d : R) hd
  have hspanne : FractionalIdeal.spanSingleton R⁰
      (IsLocalization.mk' F n d) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div]
    exact div_ne_zero
      ((map_ne_zero_iff (algebraMap R F)
        (IsFractionRing.injective R F)).mpr hn)
      ((map_ne_zero_iff (algebraMap R F)
        (IsFractionRing.injective R F)).mpr hd)
  have hrepr : FractionalIdeal.spanSingleton R⁰
      (IsLocalization.mk' F n d) =
      FractionalIdeal.spanSingleton R⁰
          (algebraMap R F (d : R))⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [normalizedAdicOrder, ← hnd, P.valuation_of_mk',
    WithZero.log_div hvn hvd, P.intValuation_if_neg hn,
    P.intValuation_if_neg hd, WithZero.log_exp, WithZero.log_exp,
    FractionalIdeal.count_well_defined F P hspanne hrepr]
  ring

/-- The idèle ideal map sends a principal idèle to the corresponding
principal fractional ideal. -/
theorem idele_ideal_principal (x : Kˣ) :
    ideleIdealMap (OK K) K (principalIdele (OK K) K x) =
      toPrincipalIdeal (OK K) K x := by
  apply (fractionalIdealFactorization (OK K) K).symm.injective
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro P
  change FractionalIdeal.count K P
      ((ideleIdealMap (OK K) K (principalIdele (OK K) K x) :
        (FractionalIdeal (OK K)⁰ K)ˣ) : FractionalIdeal (OK K)⁰ K) =
    FractionalIdeal.count K P
      ((toPrincipalIdeal (OK K) K x :
        (FractionalIdeal (OK K)⁰ K)ˣ) : FractionalIdeal (OK K)⁰ K)
  rw [count_idele_ideal, principal_idele_finite]
  change -WithZero.log
      (Valued.v ((x : K) : P.adicCompletion K)) = _
  rw [P.valuedAdicCompletion_eq_valuation']
  change normalizedAdicOrder P x = _
  rw [normalized_adic_singleton]
  simp only [coe_toPrincipalIdeal]

set_option synthInstance.maxHeartbeats 200000 in
private theorem adic_maximal_pow
    (P : HeightOneSpectrum (OK K)) (n : ℕ)
    (z : P.adicCompletionIntegers K) (hz : z ≠ 0) :
    z ∈
      (IsLocalRing.maximalIdeal (P.adicCompletionIntegers K) :
        Ideal (P.adicCompletionIntegers K)) ^ n ↔
      (n : ℤ) ≤ -WithZero.log
        (Valued.v (z : P.adicCompletion K)) := by
  let C := P.adicCompletion K
  let A := P.adicCompletionIntegers K
  let v : Valuation C ℤᵐ⁰ := Valued.v
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible A
  letI : IsDiscreteValuationRing v.integer := by
    change IsDiscreteValuationRing A
    infer_instance
  have hpow :
      ((((IsLocalRing.maximalIdeal A : Ideal A) ^ n : Ideal A)) : Set A) =
        {y : A | v (y : C) ≤ v (pi : C) ^ n} := by
    simpa only [A, C, v, HeightOneSpectrum.adicCompletionIntegers] using
      hpi.maximalIdeal_pow_eq_setOf_le_v_coe_pow (v := v) n
  have hpiUniform : v.IsUniformizer (pi : C) := by
    apply Valuation.isUniformizer_of_maximalIdeal_eq_span (v := v)
    simpa only [A, v, HeightOneSpectrum.adicCompletionIntegers] using
      hpi.maximalIdeal_eq
  have hsurj : Function.Surjective v := by
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      (K := K) P
  have hpiVal : v (pi : C) = WithZero.exp (-1 : ℤ) := by
    rw [hpiUniform.val]
    exact congrArg Units.val
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hsurj)
  have hzval : v (z : C) ≠ 0 := by
    apply (Valuation.ne_zero_iff v).2
    exact Subtype.val_injective.ne hz
  have hpival : v (pi : C) ^ n ≠ 0 := by
    exact pow_ne_zero n hpiUniform.val_ne_zero
  have hmem : z ∈ (IsLocalRing.maximalIdeal A : Ideal A) ^ n ↔
      v (z : C) ≤ v (pi : C) ^ n := by
    exact Set.ext_iff.mp hpow z
  rw [hmem]
  rw [← WithZero.log_le_log hzval hpival, WithZero.log_pow, hpiVal,
    WithZero.log_exp]
  simp only [v, nsmul_eq_mul, mul_neg, mul_one]
  omega

/-- At a prime where a global element is a unit, the local ray condition is
equivalent to the usual lower bound on the order of `x - 1`. -/
theorem principal_ray_subgroup
    (P : HeightOneSpectrum (OK K)) (n : ℕ) (x : Kˣ)
    (hxunit : FractionalIdeal.count K P
      (FractionalIdeal.spanSingleton (OK K)⁰ (x : K)) = 0) :
    Units.map (algebraMap K (P.adicCompletion K)) x ∈
        rayLocalSubgroup (K := K) P n ↔
      x = 1 ∨ (n : ℤ) ≤ FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (OK K)⁰ ((x : K) - 1)) := by
  let C := P.adicCompletion K
  let A := P.adicCompletionIntegers K
  let xu : Cˣ := Units.map (algebraMap K C) x
  have hxval : Valued.v (xu : C) = 1 := by
    have hord := normalized_adic_singleton P x
    rw [hxunit] at hord
    change -WithZero.log (P.valuation K (x : K)) = 0 at hord
    have hlog : WithZero.log (P.valuation K (x : K)) = 0 :=
      neg_eq_zero.mp hord
    have hvne : P.valuation K (x : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact x.ne_zero
    change Valued.v ((x : K) : P.adicCompletion K) = 1
    rw [P.valuedAdicCompletion_eq_valuation']
    calc
      P.valuation K (x : K) =
          WithZero.exp (WithZero.log (P.valuation K (x : K))) :=
        (WithZero.exp_log hvne).symm
      _ = 1 := by simp [hlog]
  have hxu : xu ∈ A.unitGroup := by
    simpa only [A, HeightOneSpectrum.adicCompletionIntegers] using
      (Valuation.mem_unitGroup_iff
        (v := (Valued.v : Valuation (P.adicCompletion K) ℤᵐ⁰))
        (x := xu)).2 hxval
  let xuA : A.unitGroup := ⟨xu, hxu⟩
  let u : Aˣ := A.unitGroupMulEquiv xuA
  have huMap :
      (A.unitGroup.subtype.comp A.unitGroupMulEquiv.symm.toMonoidHom) u = xu := by
    change (A.unitGroupMulEquiv.symm u : Cˣ) = xu
    simp only [u, xuA, MulEquiv.symm_apply_apply]
  constructor
  · intro hray
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      rw [rayLocalSubgroup] at hray
      obtain ⟨u', hu', hu'Map⟩ := hray
      have hdiffCoerced : (((u' : A) - 1 : A) : C) =
          (((x : K) - 1 : K) : P.adicCompletion K) := by
        change ((u' : A) : C) - 1 = algebraMap K C ((x : K) - 1)
        rw [map_sub, map_one]
        have hval := congrArg Units.val hu'Map
        exact congrArg (fun z : C ↦ z - 1) hval
      have hdiffne : (u' : A) - 1 ≠ 0 := by
        intro hzero
        have hzeroC : ((((u' : A) - 1 : A) : C)) = 0 :=
          congrArg (fun z : A ↦ (z : C)) hzero
        have : (((x : K) - 1 : K) : P.adicCompletion K) = 0 := by
          rw [← hdiffCoerced]
          exact hzeroC
        have hxsub : (x : K) - 1 = 0 :=
          (map_eq_zero_iff (algebraMap K C)
            (algebraMap K C).injective).mp this
        exact hx1 (Units.ext (sub_eq_zero.mp hxsub))
      have hlocal :=
        (adic_maximal_pow P n ((u' : A) - 1) hdiffne).1 hu'
      have hvaldiff := congrArg
        (fun z : P.adicCompletion K ↦ Valued.v z) hdiffCoerced
      change Valued.v ((((u' : A) - 1 : A) : P.adicCompletion K)) =
        Valued.v ((((x : K) - 1 : K) : P.adicCompletion K)) at hvaldiff
      have hglobal : Valued.v ((((x : K) - 1 : K) : P.adicCompletion K)) =
          P.valuation K ((x : K) - 1) :=
        P.valuedAdicCompletion_eq_valuation' ((x : K) - 1)
      rw [hglobal] at hvaldiff
      rw [hvaldiff] at hlocal
      let xm1 : Kˣ := Units.mk0 ((x : K) - 1) (sub_ne_zero.mpr <| by
        intro h
        exact hx1 (Units.ext h))
      have horder := normalized_adic_singleton P xm1
      change -WithZero.log (P.valuation K ((x : K) - 1)) = _ at horder
      exact horder ▸ hlocal
  · rintro (rfl | hcount)
    · exact (rayLocalSubgroup (K := K) P n).one_mem
    · by_cases hx1 : x = 1
      · subst x
        exact (rayLocalSubgroup (K := K) P n).one_mem
      rw [rayLocalSubgroup]
      refine ⟨u, ?_, huMap⟩
      have hdiffCoerced : (((u : A) - 1 : A) : C) =
          (((x : K) - 1 : K) : P.adicCompletion K) := by
        change ((u : A) : C) - 1 = algebraMap K C ((x : K) - 1)
        rw [map_sub, map_one]
        have hval := congrArg Units.val huMap
        exact congrArg (fun z : C ↦ z - 1) hval
      have hdiffne : (u : A) - 1 ≠ 0 := by
        intro hzero
        have hzeroC : ((((u : A) - 1 : A) : C)) = 0 :=
          congrArg (fun z : A ↦ (z : C)) hzero
        have : (((x : K) - 1 : K) : P.adicCompletion K) = 0 := by
          rw [← hdiffCoerced]
          exact hzeroC
        have hxsub : (x : K) - 1 = 0 :=
          (map_eq_zero_iff (algebraMap K C)
            (algebraMap K C).injective).mp this
        exact hx1 (Units.ext (sub_eq_zero.mp hxsub))
      apply (adic_maximal_pow P n ((u : A) - 1) hdiffne).2
      have hvaldiff := congrArg
        (fun z : P.adicCompletion K ↦ Valued.v z) hdiffCoerced
      change Valued.v ((((u : A) - 1 : A) : P.adicCompletion K)) =
        Valued.v ((((x : K) - 1 : K) : P.adicCompletion K)) at hvaldiff
      have hglobal : Valued.v ((((x : K) - 1 : K) : P.adicCompletion K)) =
          P.valuation K ((x : K) - 1) :=
        P.valuedAdicCompletion_eq_valuation' ((x : K) - 1)
      rw [hglobal] at hvaldiff
      rw [hvaldiff]
      let xm1 : Kˣ := Units.mk0 ((x : K) - 1) (sub_ne_zero.mpr <| by
        intro h
        exact hx1 (Units.ext h))
      have horder := normalized_adic_singleton P xm1
      change -WithZero.log (P.valuation K ((x : K) - 1)) = _ at horder
      exact horder.symm ▸ hcount

/-- The archimedean condition on a principal idèle is exactly positivity
of the corresponding real embedding. -/
theorem principal_positive_real
    (w : RealInfinitePlace K) (x : Kˣ) :
    MulEquiv.piUnits (principalIdele (OK K) K x).1 w.1 ∈
        positiveRealSubgroup w ↔
      0 < InfinitePlace.embedding_of_isReal w.property (x : K) := by
  rw [principal_idele_infinite]
  simp only [positiveRealSubgroup, Subgroup.mem_comap,
    Units.mem_posSubgroup, Units.coe_map]
  change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.property
      (((WithAbs.equiv w.1.1).symm (x : K) : w.1.Completion)) ↔ _
  rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp only [RingEquiv.apply_symm_apply]

/-- The diagonal idèles in `I_m` are precisely the ray elements
`K_{m,1}`. -/
theorem principal_modulus_ideles (m : Modulus K) (x : Kˣ) :
    principalIdele (OK K) K x ∈ modulusIdeles m ↔
      ∃ xS : ElementsPrimeTo (OK K) K m.finiteSupport,
        xS.1 = x ∧ IsRayElement K m xS := by
  constructor
  · intro hx
    have hxprime : toPrincipalIdeal (OK K) K x ∈
        IdealsPrimeTo (OK K) K m.finiteSupport := by
      have hlands := modulus_lands_prime m
        ⟨principalIdele (OK K) K x, hx⟩
      rwa [idele_ideal_principal] at hlands
    let xS : ElementsPrimeTo (OK K) K m.finiteSupport := ⟨x, hxprime⟩
    refine ⟨xS, rfl, ?_, ?_⟩
    · by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        intro P hP
        have hlocal := hx.1 P hP
        rw [principal_idele_finite] at hlocal
        have hxunit : FractionalIdeal.count K P
            (FractionalIdeal.spanSingleton (OK K)⁰ (x : K)) = 0 := by
          simpa only [xS, coe_toPrincipalIdeal] using xS.property P hP
        exact (principal_ray_subgroup
          P (m.finite P) x hxunit).1 hlocal |>.resolve_left hx1
    · intro w hw
      exact (principal_positive_real w x).1
        (hx.2 w hw)
  · rintro ⟨xS, hxS, hxray⟩
    have hxSeq : xS.1 = x := hxS
    constructor
    · intro P hP
      rw [principal_idele_finite]
      have hxunit : FractionalIdeal.count K P
          (FractionalIdeal.spanSingleton (OK K)⁰ (x : K)) = 0 := by
        simpa only [← hxSeq, coe_toPrincipalIdeal] using xS.property P hP
      apply (principal_ray_subgroup
        P (m.finite P) x hxunit).2
      rcases hxray.1 with hone | hcount
      · exact Or.inl (hxSeq.symm.trans hone)
      · exact Or.inr (by simpa only [← hxSeq] using hcount P hP)
    · intro w hw
      apply (principal_positive_real w x).2
      simpa only [← hxSeq] using hxray.2 w hw

/-- Principal idèles in `I_m` map to exactly the ray-principal subgroup. -/
theorem modulus_ideles_image (m : Modulus K) :
    Subgroup.map
        (modulusIdeleIdeal m (modulus_lands_prime m))
        (modulusPrincipalIdeles m) =
      rayPrincipalSubgroup K m := by
  apply le_antisymm
  · rintro I ⟨a, ha, rfl⟩
    change a.1 ∈ principalIdeles (OK K) K at ha
    obtain ⟨x, hx⟩ := ha
    have hxmod : principalIdele (OK K) K x ∈ modulusIdeles m := by
      rw [hx]
      exact a.property
    obtain ⟨xS, hxS, hxray⟩ :=
      (principal_modulus_ideles m x).1 hxmod
    apply Subgroup.subset_closure
    refine ⟨xS, hxray, ?_⟩
    apply Subtype.ext
    change toPrincipalIdeal (OK K) K xS.1 =
      ideleIdealMap (OK K) K a.1
    rw [hxS, ← hx, idele_ideal_principal]
  · rw [rayPrincipalSubgroup]
    apply (Subgroup.closure_le
      (Subgroup.map
        (modulusIdeleIdeal m (modulus_lands_prime m))
        (modulusPrincipalIdeles m))).2
    rintro I ⟨xS, hxray, rfl⟩
    have hxmod : principalIdele (OK K) K xS.1 ∈ modulusIdeles m :=
      (principal_modulus_ideles m xS.1).2
        ⟨xS, rfl, hxray⟩
    let a : modulusIdeles m :=
      ⟨principalIdele (OK K) K xS.1, hxmod⟩
    refine ⟨a, ?_, ?_⟩
    · change principalIdele (OK K) K xS.1 ∈ principalIdeles (OK K) K
      exact ⟨xS.1, rfl⟩
    · apply Subtype.ext
      change ideleIdealMap (OK K) K (principalIdele (OK K) K xS.1) =
        toPrincipalIdeal (OK K) K xS.1
      exact idele_ideal_principal xS.1

/-- Every fractional ideal prime to the modulus has a representative in
`I_m`.  Starting with an arbitrary idèle representative, we cancel its
finitely many coordinates over the modulus by local units. -/
theorem modulus_idele_surjective (m : Modulus K) :
    Function.Surjective
      (modulusIdeleIdeal m (modulus_lands_prime m)) := by
  classical
  intro I
  obtain ⟨x, hx⟩ := idele_surjective (OK K) K I.1
  have hunit : ∀ P ∈ m.finiteSupport,
      x.2.1 P ∈ IdeleUnitSubgroup (OK K) K P := by
    intro P hP
    change x.2.1 P ∈ (P.adicCompletionIntegers K).units
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    have hcount : FractionalIdeal.count K P
        ((ideleIdealMap (OK K) K x :
          (FractionalIdeal (OK K)⁰ K)ˣ) : FractionalIdeal (OK K)⁰ K) = 0 := by
      rw [hx]
      exact I.property P hP
    rw [count_idele_ideal] at hcount
    have hlog : WithZero.log
        (Valued.v ((x.2.1 P : (P.adicCompletion K)ˣ) :
          P.adicCompletion K)) = 0 := neg_eq_zero.mp hcount
    have hvne : Valued.v ((x.2.1 P : (P.adicCompletion K)ˣ) :
        P.adicCompletion K) ≠ 0 := by simp
    calc
      Valued.v ((x.2.1 P : (P.adicCompletion K)ˣ) :
          P.adicCompletion K) =
          WithZero.exp (WithZero.log
            (Valued.v ((x.2.1 P : (P.adicCompletion K)ˣ) :
              P.adicCompletion K))) := (WithZero.exp_log hvne).symm
      _ = 1 := by simp [hlog]
  let correctionAt : ∀ P : HeightOneSpectrum (OK K),
      (P.adicCompletion K)ˣ := fun P ↦
    if hP : P ∈ m.finiteSupport then (x.2.1 P)⁻¹ else 1
  have hcorrectionRestricted : ∀ᶠ P in Filter.cofinite,
      correctionAt P ∈ IdeleUnitSubgroup (OK K) K P := by
    filter_upwards [m.finiteSupport.finite_toSet.compl_mem_cofinite] with P hP
    simp only [Set.mem_compl_iff, Finset.mem_coe] at hP
    rw [show correctionAt P = 1 by
      simp only [correctionAt, dif_neg hP]]
    exact (IdeleUnitSubgroup (OK K) K P).one_mem
  let correction : FiniteIdeles (OK K) K :=
    RestrictedProduct.mk correctionAt hcorrectionRestricted
  let y : IdeleGroup (OK K) K := (1, x.2 * correction)
  have hy : y ∈ modulusIdeles m := by
    constructor
    · intro P hP
      change x.2.1 P * correction.1 P ∈
        rayLocalSubgroup (K := K) P (m.finite P)
      have hcancel : x.2.1 P * correction.1 P = 1 := by
        rw [show correction.1 P = (x.2.1 P)⁻¹ by
          simp only [correction, correctionAt, dif_pos hP]]
        exact mul_inv_cancel _
      rw [hcancel]
      exact (rayLocalSubgroup (K := K) P (m.finite P)).one_mem
    · exact (modulusIdeles m).one_mem.2
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change finiteIdeleIdeal (OK K) K (x.2 * correction) = I.1
  rw [map_mul]
  have hcmap : finiteIdeleIdeal (OK K) K correction = 1 := by
    change (fractionalIdealFactorization (OK K) K)
      (ideleExponentHom (OK K) K correction) = 1
    rw [← map_one (fractionalIdealFactorization (OK K) K),
      (fractionalIdealFactorization (OK K) K).injective.eq_iff]
    apply Multiplicative.toAdd.injective
    change (ideleExponentHom (OK K) K correction).toAdd = 0
    apply Finsupp.ext
    intro P
    rw [idele_exponent_hom]
    by_cases hP : P ∈ m.finiteSupport
    · have hval := hunit P hP
      change x.2.1 P ∈ (P.adicCompletionIntegers K).units at hval
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
        at hval
      rw [show correction.1 P = (x.2.1 P)⁻¹ by
        simp only [correction, correctionAt, dif_pos hP]]
      simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one,
        WithZero.log_one, neg_zero, Finsupp.zero_apply]
    · rw [show correction.1 P = 1 by
        simp only [correction, correctionAt, dif_neg hP]]
      simp
  rw [hcmap, mul_one]
  exact hx

/-- The unconditional arithmetic bridge required by Proposition V.4.6(a). -/
theorem idealMapBridge (m : Modulus K) :
    IdealMapBridge m where
  landsPrimeTo := modulus_lands_prime m
  idealMap_surjective := modulus_idele_surjective m
  principal_image := modulus_ideles_image m

end

end Submission.CField.HNorm
