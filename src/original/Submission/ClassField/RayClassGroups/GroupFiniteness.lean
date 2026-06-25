import Submission.NumberTheory.ClassGroup.ClassNumberFinite
import Submission.ClassField.RayClassGroups.CountFiniteIdeal
import Submission.ClassField.RayClassGroups.ResidueSignFactors

/-!
# Finiteness of ray class groups

We encode a ray class by its ordinary ideal class and by finite residue and
sign data for a prime-to principal adjustment.  Equality of these finite
codes implies equality of ray classes by Proposition V.1.6.
-/

namespace Submission.CField.RCGroups

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.ARecip
open scoped nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private abbrev RayClassCode (m : Modulus K) :=
  ClassGroup (𝓞 K) ×
    (𝓞 K ⧸ m.finiteIdeal) ×
    (𝓞 K ⧸ m.finiteIdeal) ×
    (m.infinite → Bool) × (m.infinite → Bool)

private theorem ray_class_code (m : Modulus K) :
    Finite (RayClassCode K m) := by
  letI : Finite (ClassGroup (𝓞 K)) := classGroup_finite K
  letI : Finite (𝓞 K ⧸ m.finiteIdeal) := Modulus.finite_finiteQuotient K m
  infer_instance

private noncomputable def rayClassRepresentative (m : Modulus K)
    (C : RayClassGroup K m) :
    IdealsPrimeTo (𝓞 K) K m.finiteSupport :=
  Classical.choose
    (QuotientGroup.mk'_surjective (rayPrincipalSubgroup K m) C)

private theorem ray_representative_spec (m : Modulus K)
    (C : RayClassGroup K m) :
    QuotientGroup.mk' (rayPrincipalSubgroup K m)
      (rayClassRepresentative K m C) = C :=
  Classical.choose_spec
    (QuotientGroup.mk'_surjective (rayPrincipalSubgroup K m) C)

private noncomputable def ordinaryRepresentative (m : Modulus K)
    (c : ClassGroup (𝓞 K)) :
    IdealsPrimeTo (𝓞 K) K m.finiteSupport :=
  Classical.choose
    (ideal_class_surjective (𝓞 K) K m.finiteSupport c)

private theorem ordinaryRepresentative_spec (m : Modulus K)
    (c : ClassGroup (𝓞 K)) :
    idealClassPrime (𝓞 K) K m.finiteSupport
      (ordinaryRepresentative K m c) = c :=
  Classical.choose_spec
    (ideal_class_surjective (𝓞 K) K m.finiteSupport c)

private noncomputable def rayClassOrdinary (m : Modulus K)
    (C : RayClassGroup K m) : ClassGroup (𝓞 K) :=
  idealClassPrime (𝓞 K) K m.finiteSupport
    (rayClassRepresentative K m C)

private theorem ray_class_adjustment (m : Modulus K)
    (C : RayClassGroup K m) :
    ∃ x : ElementsPrimeTo (𝓞 K) K m.finiteSupport,
      principalIdealPrime (𝓞 K) K m.finiteSupport x =
        rayClassRepresentative K m C *
          (ordinaryRepresentative K m (rayClassOrdinary K m C))⁻¹ := by
  let J := rayClassRepresentative K m C *
    (ordinaryRepresentative K m (rayClassOrdinary K m C))⁻¹
  have hker : J ∈ (idealClassPrime (𝓞 K) K m.finiteSupport).ker := by
    rw [MonoidHom.mem_ker]
    change idealClassPrime (𝓞 K) K m.finiteSupport
      (rayClassRepresentative K m C *
        (ordinaryRepresentative K m (rayClassOrdinary K m C))⁻¹) = 1
    rw [map_mul, map_inv, ordinaryRepresentative_spec]
    simp [rayClassOrdinary]
  have hrange : J ∈
      (principalIdealPrime (𝓞 K) K m.finiteSupport).range := by
    rw [range_principal_class]
    exact hker
  exact hrange

private noncomputable def rayClassAdjustment (m : Modulus K)
    (C : RayClassGroup K m) :
    ElementsPrimeTo (𝓞 K) K m.finiteSupport :=
  Classical.choose (ray_class_adjustment K m C)

private theorem ray_adjustment_spec (m : Modulus K)
    (C : RayClassGroup K m) :
    principalIdealPrime (𝓞 K) K m.finiteSupport
        (rayClassAdjustment K m C) =
      rayClassRepresentative K m C *
        (ordinaryRepresentative K m (rayClassOrdinary K m C))⁻¹ :=
  Classical.choose_spec (ray_class_adjustment K m C)

private structure IntegralFractionData (m : Modulus K)
    (x : ElementsPrimeTo (𝓞 K) K m.finiteSupport) where
  numerator : 𝓞 K
  denominator : 𝓞 K
  numerator_ne : numerator ≠ 0
  denominator_ne : denominator ≠ 0
  value : (x.1 : K) =
    algebraMap (𝓞 K) K numerator / algebraMap (𝓞 K) K denominator
  numerator_away : ∀ p ∈ m.finiteSupport,
    FractionalIdeal.count K p
      (FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K numerator)) = 0
  denominator_away : ∀ p ∈ m.finiteSupport,
    FractionalIdeal.count K p
      (FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K denominator)) = 0

private theorem integral_fraction_data (m : Modulus K)
    (x : ElementsPrimeTo (𝓞 K) K m.finiteSupport) :
    Nonempty (IntegralFractionData K m x) := by
  obtain ⟨a, b, ha, hb, hvalue, hawayA, hawayB⟩ :=
    integral_fraction_prime (𝓞 K) K m.finiteSupport x
  exact ⟨⟨a, b, ha, hb, hvalue, hawayA, hawayB⟩⟩

private noncomputable def rayFractionData (m : Modulus K)
    (C : RayClassGroup K m) :
    IntegralFractionData K m (rayClassAdjustment K m C) :=
  Classical.choice (integral_fraction_data K m (rayClassAdjustment K m C))

private def integralSignCode (m : Modulus K) (a : 𝓞 K) :
    m.infinite → Bool := fun w ↦
  if 0 < NumberField.InfinitePlace.embedding_of_isReal w.1.property
      (algebraMap (𝓞 K) K a) then true else false

omit [NumberField K] in
private theorem pos_sign_code (m : Modulus K)
    {a c : 𝓞 K} (ha : a ≠ 0) (hc : c ≠ 0)
    (hcode : integralSignCode K m a = integralSignCode K m c) :
    ∀ w ∈ m.infinite,
      0 < NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K a) *
        NumberField.InfinitePlace.embedding_of_isReal w.property
          (algebraMap (𝓞 K) K c) := by
  intro w hw
  let f : 𝓞 K →+* ℝ :=
    (NumberField.InfinitePlace.embedding_of_isReal w.property).comp
      (algebraMap (𝓞 K) K)
  have hfinj : Function.Injective f :=
    (NumberField.InfinitePlace.embedding_of_isReal w.property).injective.comp
      NumberField.RingOfIntegers.coe_injective
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hfinj).mpr ha
  have hfc : f c ≠ 0 := (map_ne_zero_iff f hfinj).mpr hc
  have hpoint := congrFun hcode (⟨w, hw⟩ : m.infinite)
  change (if 0 < f a then true else false) =
    (if 0 < f c then true else false) at hpoint
  change 0 < f a * f c
  by_cases hpa : 0 < f a
  · have hpc : 0 < f c := by
      by_contra hn
      simp [hpa, hn] at hpoint
    exact mul_pos hpa hpc
  · have hpc : ¬0 < f c := by
      intro hcpos
      simp [hpa, hcpos] at hpoint
    exact mul_pos_of_neg_of_neg
      (lt_of_le_of_ne (le_of_not_gt hpa) hfa)
      (lt_of_le_of_ne (le_of_not_gt hpc) hfc)

private noncomputable def rayClassCode (m : Modulus K)
    (C : RayClassGroup K m) : RayClassCode K m :=
  let d := rayFractionData K m C
  (rayClassOrdinary K m C,
    Ideal.Quotient.mk m.finiteIdeal d.numerator,
    Ideal.Quotient.mk m.finiteIdeal d.denominator,
    integralSignCode K m d.numerator,
    integralSignCode K m d.denominator)

private theorem ray_code_injective (m : Modulus K) :
    Function.Injective (rayClassCode K m) := by
  intro C D hcode
  let dC := rayFractionData K m C
  let dD := rayFractionData K m D
  have hclass : rayClassOrdinary K m C =
      rayClassOrdinary K m D := by
    simpa [rayClassCode, dC, dD] using
      congrArg (fun z : RayClassCode K m ↦ z.1) hcode
  have hnum : Ideal.Quotient.mk m.finiteIdeal dC.numerator =
      Ideal.Quotient.mk m.finiteIdeal dD.numerator := by
    simpa [rayClassCode, dC, dD] using
      congrArg (fun z : RayClassCode K m ↦ z.2.1) hcode
  have hden : Ideal.Quotient.mk m.finiteIdeal dC.denominator =
      Ideal.Quotient.mk m.finiteIdeal dD.denominator := by
    simpa [rayClassCode, dC, dD] using
      congrArg (fun z : RayClassCode K m ↦ z.2.2.1) hcode
  have hsignNum : integralSignCode K m dC.numerator =
      integralSignCode K m dD.numerator := by
    simpa [rayClassCode, dC, dD] using
      congrArg (fun z : RayClassCode K m ↦ z.2.2.2.1) hcode
  have hsignDen : integralSignCode K m dC.denominator =
      integralSignCode K m dD.denominator := by
    simpa [rayClassCode, dC, dD] using
      congrArg (fun z : RayClassCode K m ↦ z.2.2.2.2) hcode
  have hnumSub : dC.numerator - dD.numerator ∈ m.finiteIdeal :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hnum
  have hdenSub : dC.denominator - dD.denominator ∈ m.finiteIdeal :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hden
  have hnumSign := pos_sign_code K m
    dC.numerator_ne dD.numerator_ne hsignNum
  have hdenSign := pos_sign_code K m
    dC.denominator_ne dD.denominator_ne hsignDen
  let xC := rayClassAdjustment K m C
  let xD := rayClassAdjustment K m D
  let z : ElementsPrimeTo (𝓞 K) K m.finiteSupport := xC * xD⁻¹
  have hzvalue : (z.1 : K) =
      (algebraMap (𝓞 K) K dC.numerator /
        algebraMap (𝓞 K) K dC.denominator) /
      (algebraMap (𝓞 K) K dD.numerator /
        algebraMap (𝓞 K) K dD.denominator) := by
    have hvalue : (xC.1 : K) * (xD.1 : K)⁻¹ =
        (algebraMap (𝓞 K) K dC.numerator /
          algebraMap (𝓞 K) K dC.denominator) /
        (algebraMap (𝓞 K) K dD.numerator /
          algebraMap (𝓞 K) K dD.denominator) := by
      rw [dC.value, dD.value]
      simp [div_eq_mul_inv]
    simpa [z] using hvalue
  have hzray : IsRayElement K m z :=
    ray_fraction_ratio K m z
      dC.numerator_ne dC.denominator_ne
      dD.numerator_ne dD.denominator_ne hzvalue
      dC.denominator_away dD.numerator_away hnumSub hdenSub
      hnumSign hdenSign
  have hzmem : principalIdealPrime (𝓞 K) K m.finiteSupport z ∈
      rayPrincipalSubgroup K m := by
    apply Subgroup.subset_closure
    exact ⟨z, hzray, rfl⟩
  have hprincipal :
      principalIdealPrime (𝓞 K) K m.finiteSupport z =
        rayClassRepresentative K m C * (rayClassRepresentative K m D)⁻¹ := by
    change principalIdealPrime (𝓞 K) K m.finiteSupport (xC * xD⁻¹) = _
    rw [map_mul, map_inv, ray_adjustment_spec,
      ray_adjustment_spec, hclass]
    group
  have hquotient : QuotientGroup.mk' (rayPrincipalSubgroup K m)
      (rayClassRepresentative K m C) =
      QuotientGroup.mk' (rayPrincipalSubgroup K m)
        (rayClassRepresentative K m D) := by
    apply (QuotientGroup.eq).mpr
    have hinv := (rayPrincipalSubgroup K m).inv_mem hzmem
    rw [hprincipal] at hinv
    simpa [mul_comm] using hinv
  calc
    C = QuotientGroup.mk' (rayPrincipalSubgroup K m)
        (rayClassRepresentative K m C) := (ray_representative_spec K m C).symm
    _ = QuotientGroup.mk' (rayPrincipalSubgroup K m)
        (rayClassRepresentative K m D) := hquotient
    _ = D := ray_representative_spec K m D

/-- The ray class group of every modulus of a number field is finite. -/
theorem ray_class_group (m : Modulus K) :
    Finite (RayClassGroup K m) := by
  letI : Finite (RayClassCode K m) := ray_class_code K m
  exact Finite.of_injective (rayClassCode K m)
    (ray_code_injective K m)

end

end Submission.CField.RCGroups
