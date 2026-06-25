import Submission.NumberTheory.Cyclotomic.CyclotomicUnits


/-!
# Milne, Proposition 6.7 for powers of two

Milne states Proposition 6.7 for every prime power, but writes out only the odd-prime-power
case needed for Fermat's last theorem.  This file supplies the omitted power-of-two argument.
-/

namespace Submission.NumberTheory.Milne

open Algebra NumberField NumberField.Units
open scoped NumberField

namespace TCUnits

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] [NumberField K] [NumberField.IsCMField K]

private noncomputable def rootUnit {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (pow_ne_zero _ two_ne_zero)).unit

omit [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] [NumberField K] [IsCMField K] in
private theorem rootUnit_coe {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    ((rootUnit hζ : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := by
  exact (hζ.toInteger_isPrimitiveRoot.isUnit (pow_ne_zero _ two_ne_zero)).unit_spec

omit [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] in
private theorem complexConj_zeta {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    NumberField.IsCMField.ringOfIntegersComplexConj K hζ.toInteger =
      ((rootUnit hζ)⁻¹ : (𝓞 K)ˣ) := by
  let η : torsion K := ⟨rootUnit hζ, by
    rw [torsion, CommGroup.mem_torsion]
    exact (hζ.toInteger_isPrimitiveRoot.isUnit_unit
      (pow_ne_zero _ two_ne_zero)).isOfFinOrder (pow_ne_zero _ two_ne_zero)⟩
  have ht := NumberField.IsCMField.complexConj_torsion K η
  apply RingOfIntegers.ext
  simpa [η, rootUnit_coe] using ht

private theorem zeta_sq_complex
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    (hζ.toInteger - 1) ^ 2 ∣
      hζ.toInteger - NumberField.IsCMField.ringOfIntegersComplexConj K hζ.toInteger := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcycl : IsCyclotomicExtension {2 ^ ((k + 1) + 1)} ℚ K := by
    simpa [add_assoc] using
      (inferInstance : IsCyclotomicExtension {2 ^ (k + 2)} ℚ K)
  letI : IsCyclotomicExtension {2 ^ ((k + 1) + 1)} ℚ K := hcycl
  have hζ' : IsPrimitiveRoot ζ (2 ^ ((k + 1) + 1)) := by
    simpa [add_assoc] using hζ
  have hdTwo : hζ.toInteger - 1 ∣ (2 : 𝓞 K) := by
    simpa [add_assoc] using hζ'.toInteger_sub_one_dvd_prime
  obtain ⟨a, ha⟩ := hdTwo
  have hdPlus : hζ.toInteger - 1 ∣ hζ.toInteger + 1 := by
    refine ⟨1 + a, ?_⟩
    calc
      hζ.toInteger + 1 = (hζ.toInteger - 1) + 2 := by ring
      _ = (hζ.toInteger - 1) + (hζ.toInteger - 1) * a := by rw [ha]
      _ = (hζ.toInteger - 1) * (1 + a) := by ring
  obtain ⟨b, hb⟩ := hdPlus
  have hb' : (↑(rootUnit hζ) : 𝓞 K) + 1 =
      ((↑(rootUnit hζ) : 𝓞 K) - 1) * b := by
    simpa [rootUnit_coe] using hb
  refine ⟨((rootUnit hζ)⁻¹ : (𝓞 K)ˣ) * b, ?_⟩
  rw [complexConj_zeta hζ, ← rootUnit_coe hζ]
  have hu : (↑(rootUnit hζ) : 𝓞 K) * ↑((rootUnit hζ)⁻¹) = 1 := by simp
  calc
    (↑(rootUnit hζ) : 𝓞 K) - ↑((rootUnit hζ)⁻¹) =
        ↑((rootUnit hζ)⁻¹) * ((↑(rootUnit hζ) : 𝓞 K) ^ 2 - 1) := by
      rw [mul_sub, mul_one, pow_two, ← mul_assoc,
        mul_comm (↑((rootUnit hζ)⁻¹) : 𝓞 K), hu, one_mul]
    _ = ↑((rootUnit hζ)⁻¹) * ((↑(rootUnit hζ) : 𝓞 K) - 1) *
        ((↑(rootUnit hζ) : 𝓞 K) + 1) := by ring
    _ = ↑((rootUnit hζ)⁻¹) * ((↑(rootUnit hζ) : 𝓞 K) - 1) *
        (((↑(rootUnit hζ) : 𝓞 K) - 1) * b) := by rw [hb']
    _ = ((↑(rootUnit hζ) : 𝓞 K) - 1) ^ 2 *
        (↑((rootUnit hζ)⁻¹) * b) := by ring

/-- In a `2`-power cyclotomic integer ring, every integer is fixed by complex conjugation
modulo `(ζ - 1)²`. -/
theorem zeta_complex_conj
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) (x : 𝓞 K) :
    (hζ.toInteger - 1) ^ 2 ∣
      x - NumberField.IsCMField.ringOfIntegersComplexConj K x := by
  have hadjoin : Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 K)) = ⊤ := by
    rw [← hζ.integralPowerBasis.adjoin_gen_eq_top, hζ.integralPowerBasis_gen]
  have hx : x ∈ Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 K)) := by simp [hadjoin]
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact zeta_sq_complex hζ
  | algebraMap a => simp
  | add x y _ _ hx hy =>
      simpa [map_add, sub_add_sub_comm] using dvd_add hx hy
  | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨x * b + a * NumberField.IsCMField.ringOfIntegersComplexConj K y, ?_⟩
      rw [map_mul]
      calc
        x * y - NumberField.IsCMField.ringOfIntegersComplexConj K x *
            NumberField.IsCMField.ringOfIntegersComplexConj K y =
          x * (y - NumberField.IsCMField.ringOfIntegersComplexConj K y) +
            (x - NumberField.IsCMField.ringOfIntegersComplexConj K x) *
              NumberField.IsCMField.ringOfIntegersComplexConj K y := by ring
        _ = x * ((hζ.toInteger - 1) ^ 2 * b) +
            ((hζ.toInteger - 1) ^ 2 * a) *
              NumberField.IsCMField.ringOfIntegersComplexConj K y := by rw [ha, hb]
        _ = (hζ.toInteger - 1) ^ 2 *
            (x * b + a * NumberField.IsCMField.ringOfIntegersComplexConj K y) := by ring

include k

/-- The Hasse unit index of a `2^(k+2)`-th cyclotomic field is one. -/
theorem cyclotomic_real_units :
    NumberField.IsCMField.indexRealUnits K = 1 := by
  rcases NumberField.IsCMField.indexRealUnits_eq_one_or_two K with h | h
  · exact h
  exfalso
  obtain ⟨u, hu⟩ := (NumberField.IsCMField.indexRealUnits_eq_two_iff K).mp h
  let t : torsion K := NumberField.IsCMField.unitsMulComplexConjInv K u
  have htorder : orderOf t = torsionOrder K := by
    rw [← Nat.card_zpowers, hu, Nat.card_congr Subgroup.topEquiv.toEquiv, torsionOrder,
      Nat.card_eq_fintype_card]
  have hnEven : Even (2 ^ (k + 2)) := by
    refine ⟨2 ^ (k + 1), ?_⟩
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    ring
  have htorsion : torsionOrder K = 2 ^ (k + 2) := by
    simpa [hnEven] using
      (IsCyclotomicExtension.Rat.torsionOrder_eq (n := 2 ^ (k + 2)) (K := K))
  have htprimUnit : IsPrimitiveRoot (t : (𝓞 K)ˣ) (2 ^ (k + 2)) := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rw [← Subgroup.orderOf_mk (t : (𝓞 K)ˣ) t.property]
    exact htorder.trans htorsion
  have htprim : IsPrimitiveRoot ((((t : (𝓞 K)ˣ) : 𝓞 K) : K)) (2 ^ (k + 2)) := by
    let f : (𝓞 K)ˣ →* K :=
      (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))
    have hf : Function.Injective f := by
      intro a b hab
      exact (NumberField.Units.coe_injective (K := K)) hab
    simpa [f] using htprimUnit.map_of_injective hf
  let ζ := IsCyclotomicExtension.zeta_spec (2 ^ (k + 2)) ℚ K
  obtain ⟨r, -, hrCoprime, hζr⟩ := ζ.isPrimitiveRoot_iff.mp htprim
  let c : (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K u
  have huEq : (u : 𝓞 K) = ζ.toInteger ^ r * (c : 𝓞 K) := by
    have htEq : (((t : (𝓞 K)ˣ) : 𝓞 K) = ζ.toInteger ^ r) := by
      apply RingOfIntegers.ext
      exact hζr.symm
    change (u : 𝓞 K) * (↑(c⁻¹) : 𝓞 K) = ζ.toInteger ^ r at htEq
    have hmul := congrArg (fun z : 𝓞 K ↦ z * (c : 𝓞 K))
      htEq
    change ((u : 𝓞 K) * (↑(c⁻¹) : 𝓞 K)) * c = ζ.toInteger ^ r * c at hmul
    simpa [mul_assoc] using hmul
  have hdif := zeta_complex_conj ζ (u : 𝓞 K)
  have hdif0 : (ζ.toInteger - 1) ^ 2 ∣ (u : 𝓞 K) - (c : 𝓞 K) := by
    simpa [c] using hdif
  have hdif' : (ζ.toInteger - 1) ^ 2 ∣
      (ζ.toInteger ^ r - 1) * (c : 𝓞 K) := by
    rw [huEq] at hdif0
    convert hdif0 using 1 ; ring
  have hdiv : (ζ.toInteger - 1) ^ 2 ∣ ζ.toInteger ^ r - 1 :=
    (Units.isUnit c).dvd_mul_right.mp hdif'
  obtain ⟨q, hq⟩ := hdiv
  have hnormDvd : Algebra.norm ℤ ((ζ.toInteger - 1) ^ 2) ∣
      Algebra.norm ℤ (ζ.toInteger ^ r - 1) := by
    refine ⟨Algebra.norm ℤ q, ?_⟩
    rw [hq, map_mul]
  have hnormBase : Algebra.norm ℤ (ζ.toInteger - 1) = 2 :=
    ζ.norm_toInteger_sub_one_of_eq_two_pow
  have hζrInt : (ζ.pow_of_coprime r hrCoprime).toInteger = ζ.toInteger ^ r := by
    ext
    simp
  have hnormPow : Algebra.norm ℤ (ζ.toInteger ^ r - 1) = 2 := by
    rw [← hζrInt]
    exact (ζ.pow_of_coprime r hrCoprime).norm_toInteger_sub_one_of_eq_two_pow
  rw [map_pow, hnormBase, hnormPow] at hnormDvd
  norm_num at hnormDvd

/-- Proposition 6.7 for powers of two: every unit is a root of unity times a unit fixed by
complex conjugation. -/
theorem cyclotomic_torsion_fixed (u : (𝓞 K)ˣ) :
    ∃ ζ : torsion K, ∃ v : (𝓞 K)ˣ,
      NumberField.IsCMField.unitsComplexConj K v = v ∧ u = (ζ : (𝓞 K)ˣ) * v := by
  have htop : NumberField.IsCMField.realUnits K ⊔ torsion K = ⊤ := by
    apply Subgroup.index_eq_one.mp
    exact cyclotomic_real_units (k := k) (K := K)
  have hu : u ∈ NumberField.IsCMField.realUnits K ⊔ torsion K := by simp [htop]
  rw [Subgroup.mem_sup] at hu
  obtain ⟨v, hv, ζ, hζ, hvζ⟩ := hu
  exact ⟨⟨ζ, hζ⟩, v, (NumberField.IsCMField.unitsComplexConj_eq_self_iff K v).2 hv, by
    rw [← hvζ]
    exact mul_comm v ζ⟩

/-- Proposition 6.7 for powers of two, with the real unit in the maximal real subfield. -/
theorem two_real_subfield (u : (𝓞 K)ˣ) :
    ∃ ζ : torsion K, ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      u = (ζ : (𝓞 K)ˣ) *
        Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v := by
  obtain ⟨ζ, v, hv, hu⟩ :=
    cyclotomic_torsion_fixed (k := k) (K := K) u
  rw [NumberField.IsCMField.unitsComplexConj_eq_self_iff,
    NumberField.IsCMField.mem_realUnits_iff] at hv
  obtain ⟨w, hw⟩ := hv
  refine ⟨ζ, w, ?_⟩
  rw [hu]
  congr 1
  apply Units.ext
  simpa using hw.symm

end TCUnits

section TwoPowerCyclotomicUnitsUnconditional

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K] [NumberField K]

/-- A cyclotomic field of conductor `2^(k+2)` carries its CM-field
structure automa. -/
@[reducible] noncomputable def twoCyclotomicCM :
    NumberField.IsCMField K := by
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) _
  have hn2 : 2 < 2 ^ (k + 2) := by
    rw [show k + 2 = k + 1 + 1 by omega, pow_succ]
    omega
  exact IsCyclotomicExtension.Rat.isCMField K
    ⟨2 ^ (k + 2), Set.mem_singleton _, hn2⟩

include k
/-- Proposition 6.7 for powers of two, without exporting the automatic
CM-field instance as an extra hypothesis. -/
theorem torsion_real_subfield
    (u : (𝓞 K)ˣ) :
    letI : NumberField.IsCMField K :=
      twoCyclotomicCM (k := k)
    ∃ ζ : torsion K, ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      u = (ζ : (𝓞 K)ˣ) *
        Units.map
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v := by
  letI : NumberField.IsCMField K := twoCyclotomicCM (k := k)
  exact TCUnits.two_real_subfield
    (k := k) (K := K) u

end TwoPowerCyclotomicUnitsUnconditional

section PrimePowerCyclotomicUnitsUnconditional

variable {p r : ℕ} {K : Type*} [Field K] [CharZero K] [Fact p.Prime]
  [IsCyclotomicExtension {p ^ r} ℚ K] [NumberField K]

/-- The automatic CM-field structure for a nontrivial prime-power
cyclotomic extension. -/
@[reducible] noncomputable def cyclotomicCMField
    (hn : 2 < p ^ r) : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K
    ⟨p ^ r, Set.mem_singleton _, hn⟩

include r
/-- Milne, Proposition 6.7, for every prime-power conductor `p^r > 2`,
with the automatic CM-field structure discharged internally. -/
theorem cyclotomic_real_subfield
    (hn : 2 < p ^ r) (u : (𝓞 K)ˣ) :
    letI : NumberField.IsCMField K := cyclotomicCMField hn
    ∃ ζ : torsion K, ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      u = (ζ : (𝓞 K)ˣ) *
        Units.map
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v := by
  letI : NumberField.IsCMField K := cyclotomicCMField hn
  have hr : 0 < r := by
    by_contra hr
    have : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    norm_num at hn
  by_cases hp2 : p = 2
  · subst p
    have hr2 : 2 ≤ r := by
      by_contra h
      have hr1 : r = 1 := by omega
      subst r
      norm_num at hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr2
    rw [Nat.add_comm] at hk
    subst r
    exact TCUnits.two_real_subfield
      (k := k) (K := K) u
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    subst r
    exact odd_torsion_subfield
      (k := k) (K := K) hp2 u

end PrimePowerCyclotomicUnitsUnconditional

end Submission.NumberTheory.Milne
