import Submission.ClassField.RayClassGroups.ForbiddenIdeal

/-!
# Chapter V, Section 1, Lemma 1.5

Every element of `K^S` is a quotient of two integral elements whose
principal ideals are both prime to `S`.
-/

namespace Submission.CField.RCGroups

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
private theorem coe_coprime_forbidden
    {S : Finset (HeightOneSpectrum R)} {J : Ideal R}
    (hJ : J ≠ 0) (hcop : IsCoprime J (forbiddenIdeal R S))
    {p : HeightOneSpectrum R} (hp : p ∈ S) :
    FractionalIdeal.count K p (J : FractionalIdeal R⁰ K) = 0 := by
  have hcop' : IsCoprime J p.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
    have hle : J ⊔ forbiddenIdeal R S ≤ J ⊔ p.asIdeal :=
      sup_le_sup_left (forbidden_ideal R hp) J
    rw [hcop] at hle
    exact top_unique hle
  have hnotdvd : ¬p.asIdeal ∣ J := by
    intro hdvd
    exact p.isPrime.ne_top
      (Ideal.isUnit_iff.mp (hcop'.symm.isUnit_of_dvd hdvd))
  rw [FractionalIdeal.count_coe K p hJ]
  norm_cast
  rw [← not_ne_iff]
  rwa [Associates.count_ne_zero_iff_dvd hJ p.irreducible]

omit [IsDomain R] in
private theorem count_coe_coprime
    {A B : Ideal R} (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : IsCoprime A B) {p : HeightOneSpectrum R}
    (hcount : FractionalIdeal.count K p (A : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K p (B : FractionalIdeal R⁰ K)) :
    FractionalIdeal.count K p (A : FractionalIdeal R⁰ K) = 0 := by
  by_contra hne
  have hneA :
      (Associates.mk p.asIdeal).count (Associates.mk A).factors ≠ 0 := by
    simpa [FractionalIdeal.count_coe K p hA] using hne
  have hneB :
      (Associates.mk p.asIdeal).count (Associates.mk B).factors ≠ 0 := by
    have : FractionalIdeal.count K p (B : FractionalIdeal R⁰ K) ≠ 0 := by
      rwa [← hcount]
    simpa [FractionalIdeal.count_coe K p hB] using this
  have hpA : p.asIdeal ∣ A :=
    (Associates.count_ne_zero_iff_dvd hA p.irreducible).mp hneA
  have hpB : p.asIdeal ∣ B :=
    (Associates.count_ne_zero_iff_dvd hB p.irreducible).mp hneB
  exact p.isPrime.ne_top
    (Ideal.isUnit_iff.mp (hcop.isUnit_of_dvd' hpA hpB))

/-- Lemma 1.5: every element of `K^S` is an integral fraction `a / b`
with both `(a)` and `(b)` prime to `S`. -/
theorem integral_fraction_prime
    (S : Finset (HeightOneSpectrum R))
    (x : ElementsPrimeTo R K S) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧
      (x.1 : K) = algebraMap R K a / algebraMap R K b ∧
      (∀ p ∈ S,
        FractionalIdeal.count K p
          (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) = 0) ∧
      (∀ p ∈ S,
        FractionalIdeal.count K p
          (FractionalIdeal.spanSingleton R⁰ (algebraMap R K b)) = 0) := by
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective R⁰ (x.1 : K)
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp only [IsLocalization.mk'_zero] at hnd
    exact x.1.ne_zero hnd.symm
  have hd : (d : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  let A : Ideal R := Ideal.span {n}
  let B : Ideal R := Ideal.span {(d : R)}
  let C : Ideal R := A ⊔ B
  have hA : A ≠ 0 := by
    change Ideal.span {n} ≠ 0
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  have hB : B ≠ 0 := by
    change Ideal.span {(d : R)} ≠ 0
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  have hC : C ≠ 0 := by
    intro hC
    apply hA
    exact le_bot_iff.mp ((show A ≤ C from le_sup_left).trans hC.le)
  obtain ⟨A', hAfac⟩ : C ∣ A := Ideal.dvd_iff_le.mpr le_sup_left
  obtain ⟨B', hBfac⟩ : C ∣ B := Ideal.dvd_iff_le.mpr le_sup_right
  have hA' : A' ≠ 0 := by
    intro h
    apply hA
    simpa [h] using hAfac
  have hB' : B' ≠ 0 := by
    intro h
    apply hB
    simpa [h] using hBfac
  have hcopAB : IsCoprime A' B' := by
    rw [Ideal.isCoprime_iff_sup_eq]
    apply mul_left_cancel₀ hC
    rw [Ideal.mul_sup, ← hAfac, ← hBfac]
    simp [C]
  have hxspan :
      FractionalIdeal.spanSingleton R⁰ (x.1 : K) =
        (A : FractionalIdeal R⁰ K) / (B : FractionalIdeal R⁰ K) := by
    change IsLocalization.mk' K n d = (x.1 : K) at hnd
    rw [← hnd, IsFractionRing.mk'_eq_div,
      ← FractionalIdeal.spanSingleton_div_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_span_singleton]
  have hcountAB (p : HeightOneSpectrum R) (hp : p ∈ S) :
      FractionalIdeal.count K p (A : FractionalIdeal R⁰ K) =
        FractionalIdeal.count K p (B : FractionalIdeal R⁰ K) := by
    have hxcount : FractionalIdeal.count K p
        (FractionalIdeal.spanSingleton R⁰ (x.1 : K)) = 0 := by
      simpa only [coe_toPrincipalIdeal] using x.property p hp
    rw [hxspan, div_eq_mul_inv,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hA)
        (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hB)),
      FractionalIdeal.count_inv] at hxcount
    omega
  have hcountA'B' (p : HeightOneSpectrum R) (hp : p ∈ S) :
      FractionalIdeal.count K p (A' : FractionalIdeal R⁰ K) =
        FractionalIdeal.count K p (B' : FractionalIdeal R⁰ K) := by
    have h := hcountAB p hp
    rw [hAfac, hBfac, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hC)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hA'),
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hC)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hB')] at h
    omega
  have hAaway (p : HeightOneSpectrum R) (hp : p ∈ S) :
      FractionalIdeal.count K p (A' : FractionalIdeal R⁰ K) = 0 :=
    count_coe_coprime R K hA' hB' hcopAB
      (hcountA'B' p hp)
  have hBaway (p : HeightOneSpectrum R) (hp : p ∈ S) :
      FractionalIdeal.count K p (B' : FractionalIdeal R⁰ K) = 0 := by
    rw [← hcountA'B' p hp]
    exact hAaway p hp
  obtain ⟨D, hD, hDcop, hADprincipal⟩ :=
    Submission.NumberTheory.Milne.coprime_nonzero_principal
      hA' (forbidden_ne_zero R S)
  have hDaway (p : HeightOneSpectrum R) (hp : p ∈ S) :
      FractionalIdeal.count K p (D : FractionalIdeal R⁰ K) = 0 :=
    coe_coprime_forbidden R K hD hDcop hp
  let A0 : (Ideal R)⁰ := ⟨A', mem_nonZeroDivisors_iff_ne_zero.mpr hA'⟩
  let B0 : (Ideal R)⁰ := ⟨B', mem_nonZeroDivisors_iff_ne_zero.mpr hB'⟩
  let C0 : (Ideal R)⁰ := ⟨C, mem_nonZeroDivisors_iff_ne_zero.mpr hC⟩
  let D0 : (Ideal R)⁰ := ⟨D, mem_nonZeroDivisors_iff_ne_zero.mpr hD⟩
  have hCAclass : ClassGroup.mk0 C0 * ClassGroup.mk0 A0 = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (C0 * A0).property).mpr
    change Submodule.IsPrincipal (C * A')
    rw [← hAfac]
    infer_instance
  have hCBclass : ClassGroup.mk0 C0 * ClassGroup.mk0 B0 = 1 := by
    rw [← map_mul]
    apply (ClassGroup.mk0_eq_one_iff (C0 * B0).property).mpr
    change Submodule.IsPrincipal (C * B')
    rw [← hBfac]
    infer_instance
  have hABclass : ClassGroup.mk0 A0 = ClassGroup.mk0 B0 := by
    apply mul_left_cancel (a := ClassGroup.mk0 C0)
    rw [hCAclass, hCBclass]
  have hADclass : ClassGroup.mk0 (A0 * D0) = 1 := by
    apply (ClassGroup.mk0_eq_one_iff (A0 * D0).property).mpr
    simpa [A0, D0] using hADprincipal
  have hBDclass : ClassGroup.mk0 (B0 * D0) = 1 := by
    rw [map_mul, ← hABclass, ← map_mul]
    exact hADclass
  have hBDprincipal : Submodule.IsPrincipal (B' * D) := by
    have := (ClassGroup.mk0_eq_one_iff (B0 * D0).property).mp hBDclass
    simpa [B0, D0] using this
  obtain ⟨a0, ha0⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hADprincipal
  obtain ⟨b0, hb0⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hBDprincipal
  have haIdeal : A' * D = Ideal.span {a0} := by
    simpa only [Ideal.span, Set.singleton] using ha0
  have hbIdeal : B' * D = Ideal.span {b0} := by
    simpa only [Ideal.span, Set.singleton] using hb0
  have ha0ne : a0 ≠ 0 := by
    intro ha
    exact (mul_ne_zero hA' hD) (by simpa [ha] using haIdeal)
  have hb0ne : b0 ≠ 0 := by
    intro hb
    exact (mul_ne_zero hB' hD) (by simpa [hb] using hbIdeal)
  have hspan :
      FractionalIdeal.spanSingleton R⁰ (x.1 : K) =
        FractionalIdeal.spanSingleton R⁰
          (algebraMap R K a0 / algebraMap R K b0) := by
    rw [hxspan, hAfac, hBfac, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_mul,
      mul_div_mul_left _ _ (FractionalIdeal.coeIdeal_ne_zero.mpr hC),
      ← mul_div_mul_right
        (A' : FractionalIdeal R⁰ K) (B' : FractionalIdeal R⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hD),
      ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul,
      haIdeal, hbIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_div_spanSingleton]
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  let a : R := (↑(u⁻¹) : R) * a0
  have ha : a ≠ 0 := mul_ne_zero (Units.ne_zero u⁻¹) ha0ne
  refine ⟨a, b0, ha, hb0ne, ?_, ?_, ?_⟩
  · calc
      (x.1 : K) = u⁻¹ • (u • (x.1 : K)) := by simp
      _ = u⁻¹ • (algebraMap R K a0 / algebraMap R K b0) := by rw [hu]
      _ = algebraMap R K a / algebraMap R K b0 := by
        rw [Units.smul_def]
        rw [Algebra.smul_def]
        simp [a, div_eq_mul_inv, mul_assoc]
  · intro p hp
    have haSpan : Ideal.span {a} = Ideal.span {a0} := by
      simpa [a] using
        (Ideal.span_singleton_mul_left_unit (Units.isUnit (u⁻¹)) a0)
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      haSpan,
      ← haIdeal, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hA')
        (FractionalIdeal.coeIdeal_ne_zero.mpr hD),
      hAaway p hp, hDaway p hp, add_zero]
  · intro p hp
    rw [← FractionalIdeal.coeIdeal_span_singleton,
      ← hbIdeal, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K p
        (FractionalIdeal.coeIdeal_ne_zero.mpr hB')
        (FractionalIdeal.coeIdeal_ne_zero.mpr hD),
      hBaway p hp, hDaway p hp, add_zero]

end

end Submission.CField.RCGroups
