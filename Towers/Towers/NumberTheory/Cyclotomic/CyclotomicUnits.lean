import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Milne, Algebraic Number Theory, Proposition 6.7

For an odd prime-power cyclotomic field, every unit is the product of a root of unity and a
unit fixed by complex conjugation.  Milne states the result for all prime powers and gives the
proof below only for odd prime powers, the case needed later in his notes.  This file formalizes
that proof.
-/

namespace Towers.NumberTheory.Milne

open NumberField NumberField.Units
open scoped NumberField

namespace CyclotomicUnits

variable {n : ℕ} {K : Type*} [Field K] [CharZero K] [NeZero n]
  [IsCyclotomicExtension {n} ℚ K]

private noncomputable def rootUnit {ζ : K} (hζ : IsPrimitiveRoot ζ n) : (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne n)).unit

omit [CharZero K] [IsCyclotomicExtension {n} ℚ K] in
private theorem rootUnit_coe {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ((rootUnit hζ : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := by
  exact (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne n)).unit_spec

omit [CharZero K] [IsCyclotomicExtension {n} ℚ K] in
private theorem root_unit_torsion {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    rootUnit hζ ∈ torsion K := by
  rw [torsion, CommGroup.mem_torsion]
  exact (hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne n)).isOfFinOrder (NeZero.ne n)

variable [NumberField K] [NumberField.IsCMField K]

/-- Reduction modulo `(ζ - 1)` is unchanged by complex conjugation. -/
private theorem mk_complex_conj {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (Ideal.Quotient.mkₐ ℤ (Ideal.span {hζ.toInteger - 1})).comp
        ((NumberField.IsCMField.ringOfIntegersComplexConj K).toAlgHom.restrictScalars ℤ) =
      Ideal.Quotient.mkₐ ℤ (Ideal.span {hζ.toInteger - 1}) := by
  let η : torsion K := ⟨rootUnit hζ, root_unit_torsion hζ⟩
  have hconj : NumberField.IsCMField.ringOfIntegersComplexConj K hζ.toInteger =
      ((rootUnit hζ)⁻¹ : (𝓞 K)ˣ) := by
    apply RingOfIntegers.ext
    have ht := NumberField.IsCMField.complexConj_torsion K η
    simpa [η, rootUnit_coe] using ht
  apply hζ.subOneIntegralPowerBasis.algHom_ext
  rw [IsPrimitiveRoot.subOneIntegralPowerBasis_gen]
  change Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1})
      (NumberField.IsCMField.ringOfIntegersComplexConj K (hζ.toInteger - 1)) =
    Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (hζ.toInteger - 1)
  rw [map_sub, map_one, hconj]
  calc
    Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1})
          (((rootUnit hζ)⁻¹ : (𝓞 K)ˣ) - 1) = 0 := by
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      rw [Ideal.mem_span_singleton]
      refine ⟨-((rootUnit hζ)⁻¹ : (𝓞 K)ˣ), ?_⟩
      rw [← rootUnit_coe hζ]
      calc
        ((↑((rootUnit hζ)⁻¹) : 𝓞 K) - 1) =
            ↑((rootUnit hζ)⁻¹) -
              (↑(rootUnit hζ) : 𝓞 K) * ↑((rootUnit hζ)⁻¹) := by rw [Units.mul_inv]
        _ = (↑(rootUnit hζ) - 1) * -↑((rootUnit hζ)⁻¹) := by ring
    _ = Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (hζ.toInteger - 1) := by
      symm
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      exact Ideal.subset_span (Set.mem_singleton _)

/-- Every algebraic integer is congruent to its complex conjugate modulo `(ζ - 1)`. -/
theorem zeta_dvd_complex {ζ : K} (hζ : IsPrimitiveRoot ζ n) (x : 𝓞 K) :
    hζ.toInteger - 1 ∣ x - NumberField.IsCMField.ringOfIntegersComplexConj K x := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
  have h := DFunLike.congr_fun (mk_complex_conj hζ) x
  exact sub_eq_zero.mpr h.symm

end CyclotomicUnits

section OddPrimePower

variable {p k : ℕ} {K : Type*} [Field K] [CharZero K] [Fact p.Prime]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] [NumberField K] [NumberField.IsCMField K]

include k

/-- The Hasse unit index of an odd prime-power cyclotomic field is one.  This is the
index formulation of Milne's Proposition 6.7. -/
theorem odd_real_units (hp : p ≠ 2) :
    NumberField.IsCMField.indexRealUnits K = 1 := by
  letI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rcases NumberField.IsCMField.indexRealUnits_eq_one_or_two K with h | h
  · exact h
  exfalso
  obtain ⟨u, hu⟩ := (NumberField.IsCMField.indexRealUnits_eq_two_iff K).mp h
  let t : torsion K := NumberField.IsCMField.unitsMulComplexConjInv K u
  have htorder : orderOf t = torsionOrder K := by
    rw [← Nat.card_zpowers, hu, Nat.card_congr Subgroup.topEquiv.toEquiv, torsionOrder,
      Nat.card_eq_fintype_card]
  have hnodd : Odd (p ^ (k + 1)) := (Fact.out : p.Prime).odd_of_ne_two hp |>.pow
  have htfinite : IsOfFinOrder ((((t : (𝓞 K)ˣ) : 𝓞 K) : K)) := by
    have htunit : IsOfFinOrder (t : (𝓞 K)ˣ) :=
      (CommGroup.mem_torsion ((𝓞 K)ˣ) (t : (𝓞 K)ˣ)).mp t.property
    simpa using
      ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).isOfFinOrder htunit
  obtain ⟨r, -, htr | htr⟩ :=
    (IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K).exists_pow_or_neg_mul_pow_of_isOfFinOrder
      hnodd htfinite
  · have htpow : t ^ (p ^ (k + 1)) = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply RingOfIntegers.ext
      change ((((t : (𝓞 K)ˣ) : 𝓞 K) : K) ^ (p ^ (k + 1))) = 1
      rw [htr]
      rw [← pow_mul, mul_comm r (p ^ (k + 1)), pow_mul,
        (IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K).pow_eq_one, one_pow]
    have hdvd : orderOf t ∣ p ^ (k + 1) := orderOf_dvd_of_pow_eq_one htpow
    rw [htorder] at hdvd
    have htors : torsionOrder K = 2 * p ^ (k + 1) := by
      simpa [if_neg (Nat.not_even_iff_odd.mpr hnodd)] using
        (IsCyclotomicExtension.Rat.torsionOrder_eq (n := p ^ (k + 1)) (K := K))
    rw [htors] at hdvd
    have hnpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
    exact (Nat.not_dvd_of_pos_of_lt hnpos
      (by omega : p ^ (k + 1) < 2 * p ^ (k + 1))) hdvd
  · let c : (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K u
    let ζ := IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K
    have htneg : ((t : (𝓞 K)ˣ) : 𝓞 K) =
        -ζ.toInteger ^ r := by
      apply RingOfIntegers.ext
      simp [htr]
    have hu_eq : (u : 𝓞 K) = -ζ.toInteger ^ r * (c : 𝓞 K) := by
      change (u : 𝓞 K) * (↑(c⁻¹) : 𝓞 K) = -ζ.toInteger ^ r at htneg
      have hmul := congrArg (fun z : 𝓞 K ↦ z * (c : 𝓞 K)) htneg
      change ((u : 𝓞 K) * (↑(c⁻¹) : 𝓞 K)) * c =
        (-ζ.toInteger ^ r) * c at hmul
      rw [mul_assoc, Units.inv_mul, mul_one] at hmul
      exact hmul
    have hminus : ζ.toInteger - 1 ∣ (u : 𝓞 K) - (c : 𝓞 K) := by
      simpa [c] using CyclotomicUnits.zeta_dvd_complex ζ (u : 𝓞 K)
    have hplus : ζ.toInteger - 1 ∣ (u : 𝓞 K) + (c : 𝓞 K) := by
      have hpow : ζ.toInteger - 1 ∣ ζ.toInteger ^ r - 1 :=
        sub_one_dvd_pow_sub_one ζ.toInteger r
      rw [hu_eq]
      obtain ⟨a, ha⟩ := hpow
      refine ⟨-a * (c : 𝓞 K), ?_⟩
      calc
        -ζ.toInteger ^ r * (c : 𝓞 K) + c =
            -(ζ.toInteger ^ r - 1) * c := by ring
        _ = -((ζ.toInteger - 1) * a) * c := by rw [ha]
        _ = (ζ.toInteger - 1) * (-a * c) := by ring
    have htwo_u : ζ.toInteger - 1 ∣ (2 : 𝓞 K) * (u : 𝓞 K) := by
      obtain ⟨a, ha⟩ := hminus
      obtain ⟨b, hb⟩ := hplus
      refine ⟨a + b, ?_⟩
      calc
        (2 : 𝓞 K) * (u : 𝓞 K) = ((u : 𝓞 K) - c) + ((u : 𝓞 K) + c) := by ring
        _ = (ζ.toInteger - 1) * a + (ζ.toInteger - 1) * b := by rw [ha, hb]
        _ = (ζ.toInteger - 1) * (a + b) := by ring
    have htwo : ζ.toInteger - 1 ∣ (2 : 𝓞 K) :=
      (Units.isUnit u).dvd_mul_right.mp htwo_u
    exact ζ.toInteger_sub_one_not_dvd_two hp htwo

/-- **Milne, Proposition 6.7 (odd prime-power case).** Every unit in an odd
prime-power cyclotomic field is a root of unity times a unit fixed by complex conjugation. -/
theorem odd_torsion_fixed (hp : p ≠ 2)
    (u : (𝓞 K)ˣ) :
    ∃ ζ : torsion K, ∃ v : (𝓞 K)ˣ,
      NumberField.IsCMField.unitsComplexConj K v = v ∧ u = (ζ : (𝓞 K)ˣ) * v := by
  have htop : NumberField.IsCMField.realUnits K ⊔ torsion K = ⊤ := by
    apply Subgroup.index_eq_one.mp
    have hi := odd_real_units (k := k) (K := K) hp
    change (NumberField.IsCMField.realUnits K ⊔ torsion K).index = 1 at hi
    exact hi
  have hu : u ∈ NumberField.IsCMField.realUnits K ⊔ torsion K := by
    rw [htop]
    trivial
  rw [Subgroup.mem_sup] at hu
  obtain ⟨v, hv, ζ, hζ, hvζ⟩ := hu
  exact ⟨⟨ζ, hζ⟩,
    v, (NumberField.IsCMField.unitsComplexConj_eq_self_iff K v).2 hv, by
      rw [← hvζ]
      exact mul_comm v ζ⟩

/-- Proposition 6.7 with the real unit exhibited in the ring of integers of the maximal real
subfield. -/
theorem odd_torsion_subfield (hp : p ≠ 2)
    (u : (𝓞 K)ˣ) :
    ∃ ζ : torsion K, ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      u = (ζ : (𝓞 K)ˣ) *
        Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v := by
  obtain ⟨ζ, v, hv, hu⟩ :=
    odd_torsion_fixed (k := k) hp u
  rw [NumberField.IsCMField.unitsComplexConj_eq_self_iff,
    NumberField.IsCMField.mem_realUnits_iff] at hv
  obtain ⟨w, hw⟩ := hv
  refine ⟨ζ, w, ?_⟩
  rw [hu]
  congr 1
  apply Units.ext
  simpa using hw.symm

end OddPrimePower

section OddPrimePowerUnconditional

variable {p k : ℕ} {K : Type*} [Field K] [CharZero K] [Fact p.Prime]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] [NumberField K]

/-- An odd prime-power cyclotomic field carries its CM-field structure
canonically from the cyclotomic extension. -/
@[reducible] noncomputable def oddCyclotomicCM (hp : p ≠ 2) :
    NumberField.IsCMField K := by
  have hp2 : 2 < p := by
    have hpge := (Fact.out : p.Prime).two_le
    omega
  have hnpos : 0 < p ^ (k + 1) :=
    pow_pos (Fact.out : p.Prime).pos _
  have hpdiv : p ∣ p ^ (k + 1) :=
    dvd_pow_self p (by omega)
  have hn2 : 2 < p ^ (k + 1) :=
    hp2.trans_le (Nat.le_of_dvd hnpos hpdiv)
  exact IsCyclotomicExtension.Rat.isCMField K
    ⟨p ^ (k + 1), Set.mem_singleton _, hn2⟩

include k
/-- Proposition 6.7 for odd prime powers, without exporting the automatic
CM-field instance as an extra hypothesis. -/
theorem odd_real_subfield
    (hp : p ≠ 2) (u : (𝓞 K)ˣ) :
    letI : NumberField.IsCMField K :=
      oddCyclotomicCM (k := k) hp
    ∃ ζ : torsion K, ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      u = (ζ : (𝓞 K)ˣ) *
        Units.map
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom v := by
  letI : NumberField.IsCMField K :=
    oddCyclotomicCM (k := k) hp
  exact odd_torsion_subfield
    (k := k) hp u

end OddPrimePowerUnconditional

end Towers.NumberTheory.Milne
