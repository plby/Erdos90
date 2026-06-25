import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Units
import Mathlib.Tactic.IntervalCases
import Submission.NumberTheory.Units.UnitTheorem

/-!
# Milne, Algebraic Number Theory, Example 5.3

The Pell-type equation describing the units in `ℤ[√d]`.
-/

namespace Submission.NumberTheory.Milne

open NumberField NumberField.InfinitePlace
open scoped NumberField

/-- **Milne, Example 5.3.** A quadratic number field with a real place has unit rank one. -/
theorem quadratic_real_place
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (hreal : 0 < nrRealPlaces K) :
    NumberField.Units.rank K = 1 := by
  have hsignature : nrRealPlaces K + 2 * nrComplexPlaces K = 2 :=
    (card_add_two_mul_card_eq_rank K).trans hdegree
  rw [real_places_complex K]
  omega

/-- **Milne, Example 5.3.** An imaginary quadratic number field has unit rank zero. -/
theorem quadratic_no_real
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (hreal : nrRealPlaces K = 0) :
    NumberField.Units.rank K = 0 := by
  have hsignature : nrRealPlaces K + 2 * nrComplexPlaces K = 2 :=
    (card_add_two_mul_card_eq_rank K).trans hdegree
  rw [real_places_complex K]
  omega

/-- **Milne, Example 5.3 (imaginary quadratic case).** Every unit of an
imaginary quadratic number field is torsion, hence a root of unity. -/
theorem imaginary_quadratic_torsion
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (hreal : nrRealPlaces K = 0)
    (u : (𝓞 K)ˣ) :
    u ∈ NumberField.Units.torsion K := by
  have hrank : NumberField.Units.rank K = 0 :=
    quadratic_no_real K hdegree hreal
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  have hprod : ∏ i, (NumberField.Units.fundSystem K i) ^ (e i) = 1 := by
    letI : IsEmpty (Fin (NumberField.Units.rank K)) :=
      ⟨fun i => by
        have hi : i.1 < 0 := by simpa [hrank] using i.2
        omega⟩
    exact Fintype.prod_empty _
  rw [hprod, mul_one] at hu
  rw [hu]
  exact ζ.property

/-- **Milne, Example 5.3 (imaginary quadratic case).** The unit group of an
imaginary quadratic number field is its full torsion subgroup. -/
theorem imaginary_torsion_top
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (hreal : nrRealPlaces K = 0) :
    NumberField.Units.torsion K = ⊤ := by
  ext u
  simp only [Subgroup.mem_top, iff_true]
  exact imaginary_quadratic_torsion K hdegree hreal u

set_option backward.isDefEq.respectTransparency false in
/-- **Milne, Example 5.3 (real quadratic case).** In a number field with a real
place and unit rank one, one fundamental unit generates every unit up to sign.
In particular, this applies to every real quadratic number field. -/
theorem fundamental_real_rank
    (K : Type*) [Field K] [NumberField K]
    (hreal : 0 < nrRealPlaces K) (hrank : NumberField.Units.rank K = 1) :
    ∃ ε : (𝓞 K)ˣ, ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
      u = ε ^ m ∨ u = (-1 : (𝓞 K)ˣ) * ε ^ m := by
  let i₀ : Fin (NumberField.Units.rank K) := ⟨0, by omega⟩
  letI : Unique (Fin (NumberField.Units.rank K)) :=
    ⟨⟨i₀⟩, fun i ↦ Fin.ext (by omega)⟩
  refine ⟨NumberField.Units.fundSystem K i₀, ?_⟩
  intro u
  obtain ⟨⟨ζ, e⟩, hu, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  have hζ : (ζ : (𝓞 K)ˣ) = 1 ∨ (ζ : (𝓞 K)ˣ) = -1 := by
    by_cases! hc : 2 < orderOf (ζ : (𝓞 K)ˣ)
    · rw [← orderOf_units, ← orderOf_submonoid] at hc
      linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
        (IsPrimitiveRoot.orderOf (ζ.1 : K))]
    · interval_cases hi : orderOf (ζ : (𝓞 K)ˣ)
      · have hpos : 0 < orderOf (ζ : (𝓞 K)ˣ) :=
          orderOf_pos_iff.mpr ((CommGroup.mem_torsion _ ζ.1).1 ζ.2)
        omega
      · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
      · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
        simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]
  refine ⟨e i₀, ?_⟩
  have hprod : ∏ i, (NumberField.Units.fundSystem K i) ^ (e i) =
      (NumberField.Units.fundSystem K i₀) ^ (e i₀) := by
    simpa only [Unique.eq_default i₀] using
      Fintype.prod_unique
        (fun i : Fin (NumberField.Units.rank K) ↦
          NumberField.Units.fundSystem K i ^ e i)
  rw [hprod] at hu
  rcases hζ with hζ | hζ
  · left
    simpa [hζ] using hu
  · right
    simpa [hζ] using hu

private theorem generates_up_sign
    {G : Type*} [CommGroup G] [HasDistribNeg G] (g : G)
    (hgen : ∀ u : G, ∃ m : ℤ, u = g ^ m ∨ u = -(g ^ m)) :
    ∀ u : G, ∃ m : ℤ, u = g⁻¹ ^ m ∨ u = -(g⁻¹ ^ m) := by
  intro u
  obtain ⟨m, hu | hu⟩ := hgen u
  · refine ⟨-m, Or.inl ?_⟩
    simpa [inv_zpow'] using hu
  · refine ⟨-m, Or.inr ?_⟩
    simpa [inv_zpow'] using hu

private theorem generates_up_neg
    {G : Type*} [CommGroup G] [HasDistribNeg G] (g : G)
    (hgen : ∀ u : G, ∃ m : ℤ, u = g ^ m ∨ u = -(g ^ m)) :
    ∀ u : G, ∃ m : ℤ, u = (-g) ^ m ∨ u = -((-g) ^ m) := by
  intro u
  obtain ⟨m, hu | hu⟩ := hgen u
  · refine ⟨m, ?_⟩
    by_cases hm : Even m
    · left
      simpa [hm.neg_zpow] using hu
    · right
      have hminus : (-1 : G) ^ m = -1 := by
        rw [neg_one_zpow_eq_ite, if_neg hm]
      have hpow : (-g) ^ m = -(g ^ m) := by
        rw [show -g = (-1 : G) * g by simp, mul_zpow, hminus]
        simp
      rw [hpow, neg_neg]
      exact hu
  · refine ⟨m, ?_⟩
    by_cases hm : Even m
    · right
      simpa [hm.neg_zpow] using hu
    · left
      have hminus : (-1 : G) ^ m = -1 := by
        rw [neg_one_zpow_eq_ite, if_neg hm]
      have hpow : (-g) ^ m = -(g ^ m) := by
        rw [show -g = (-1 : G) * g by simp, mul_zpow, hminus]
        simp
      rw [hpow]
      exact hu

private theorem fundamental_system_torsion
    (K : Type*) [Field K] [NumberField K]
    (i : Fin (NumberField.Units.rank K)) :
    NumberField.Units.fundSystem K i ∉ NumberField.Units.torsion K := by
  intro hi
  have hmk : QuotientGroup.mk (NumberField.Units.fundSystem K i) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hi
  have hfund := NumberField.Units.fundSystem_mk K i
  rw [hmk] at hfund
  have hbzero : NumberField.Units.basisModTorsion K i = 0 := by
    simpa using hfund.symm
  have hrepr := (NumberField.Units.basisModTorsion K).repr_self i
  rw [hbzero, map_zero] at hrepr
  have hcoord := congrArg (fun f => f i) hrepr
  simp at hcoord

set_option backward.isDefEq.respectTransparency false in
/-- A rank-one unit group can be oriented at any real embedding: there is a
fundamental unit whose image is greater than one, and it still generates every
unit up to sign. -/
theorem oriented_fundamental_real
    (K : Type*) [Field K] [NumberField K]
    (sigma : K →+* ℝ) (hreal : 0 < nrRealPlaces K)
    (hrank : NumberField.Units.rank K = 1) :
    ∃ epsilon : (𝓞 K)ˣ, 1 < sigma (epsilon : K) ∧
      ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
        u = epsilon ^ m ∨ u = (-1 : (𝓞 K)ˣ) * epsilon ^ m := by
  let hUnitsNeg : HasDistribNeg (𝓞 K)ˣ :=
    Units.val_injective.hasDistribNeg _ Units.val_neg Units.val_mul
  have hneg_eq (a : (𝓞 K)ˣ) : -a = (-1 : (𝓞 K)ˣ) * a :=
    @neg_eq_neg_one_mul _ _ hUnitsNeg a
  have toSigned (g : (𝓞 K)ˣ)
      (h : ∀ u : (𝓞 K)ˣ, ∃ m : ℤ, u = g ^ m ∨ u = -(g ^ m)) :
      ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
        u = g ^ m ∨ u = (-1 : (𝓞 K)ˣ) * g ^ m := by
    intro u
    obtain ⟨m, hu | hu⟩ := h u
    · exact ⟨m, Or.inl hu⟩
    · refine ⟨m, Or.inr ?_⟩
      rw [← hneg_eq]
      exact hu
  let i0 : Fin (NumberField.Units.rank K) := ⟨0, by omega⟩
  letI : Unique (Fin (NumberField.Units.rank K)) :=
    ⟨⟨i0⟩, fun i => Fin.ext (by omega)⟩
  let f : (𝓞 K)ˣ := NumberField.Units.fundSystem K i0
  have hgen : ∀ u : (𝓞 K)ˣ, ∃ m : ℤ, u = f ^ m ∨ u = -(f ^ m) := by
    intro u
    obtain ⟨⟨zeta, e⟩, hu, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
    have hzeta : (zeta : (𝓞 K)ˣ) = 1 ∨ (zeta : (𝓞 K)ˣ) = -1 := by
      by_cases! hc : 2 < orderOf (zeta : (𝓞 K)ˣ)
      · rw [← orderOf_units, ← orderOf_submonoid] at hc
        linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
          (IsPrimitiveRoot.orderOf (zeta.1 : K))]
      · interval_cases hi : orderOf (zeta : (𝓞 K)ˣ)
        · have hpos : 0 < orderOf (zeta : (𝓞 K)ˣ) :=
            orderOf_pos_iff.mpr ((CommGroup.mem_torsion _ zeta.1).1 zeta.2)
          omega
        · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
        · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
          simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]
    have hprod : ∏ i, (NumberField.Units.fundSystem K i) ^ (e i) = f ^ (e i0) := by
      simpa only [f, Unique.eq_default i0] using
        Fintype.prod_unique
          (fun i : Fin (NumberField.Units.rank K) =>
            NumberField.Units.fundSystem K i ^ e i)
    rw [hprod] at hu
    refine ⟨e i0, ?_⟩
    rcases hzeta with hzeta | hzeta
    · left
      simpa [hzeta] using hu
    · right
      simpa [hzeta] using hu
  have hfnot : f ∉ NumberField.Units.torsion K := by
    exact fundamental_system_torsion K i0
  let x : ℝ := sigma (f : K)
  have hx0 : x ≠ 0 := by
    intro hx
    have hfzero : (f : K) = 0 := sigma.injective (by simp [x] at hx)
    exact NumberField.Units.coe_ne_zero f hfzero
  have hx1 : x ≠ 1 := by
    intro hx
    have hfK : (f : K) = 1 := sigma.injective (by simpa [x] using hx)
    have hf : f = 1 := NumberField.Units.coe_injective K hfK
    apply hfnot
    rw [hf]
    exact (NumberField.Units.torsion K).one_mem
  have hxneg1 : x ≠ -1 := by
    intro hx
    have hfK : (f : K) = -1 := sigma.injective (by simpa [x] using hx)
    have hf : f = -1 := NumberField.Units.coe_injective K hfK
    apply hfnot
    rw [hf, NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by simp⟩
  have habs1 : |x| ≠ 1 := by
    intro hx
    rw [← abs_one, abs_eq_abs] at hx
    exact hx.elim hx1 hxneg1
  rcases lt_or_gt_of_ne habs1 with habslt | habsgt
  · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hnegxpos : 0 < -x := neg_pos.mpr hxneg
      have hnegxlt : -x < 1 := by simpa [abs_of_neg hxneg] using habslt
      refine ⟨-(f⁻¹), ?_, ?_⟩
      · simpa [x] using (one_lt_inv₀ hnegxpos).2 hnegxlt
      · exact toSigned (-(f⁻¹))
          (@generates_up_neg _ inferInstance hUnitsNeg f⁻¹
            (@generates_up_sign _ inferInstance hUnitsNeg f hgen))
    · refine ⟨f⁻¹, ?_, ?_⟩
      · have hxlt : x < 1 := by simpa [abs_of_pos hxpos] using habslt
        simpa [x] using (one_lt_inv₀ hxpos).2 hxlt
      · exact toSigned f⁻¹
          (@generates_up_sign _ inferInstance hUnitsNeg f hgen)
  · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · refine ⟨-f, ?_, ?_⟩
      · simpa [x, abs_of_neg hxneg] using habsgt
      · exact toSigned (-f)
          (@generates_up_neg _ inferInstance hUnitsNeg f hgen)
    · refine ⟨f, ?_, ?_⟩
      · simpa [x, abs_of_pos hxpos] using habsgt
      · exact toSigned f hgen

set_option backward.isDefEq.respectTransparency false in
/-- **Milne, Example 5.3 (real quadratic case).** Every unit of a real quadratic
number field is, up to sign, an integral power of one fundamental unit. -/
theorem fundamental_real_quadratic
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (hreal : 0 < nrRealPlaces K) :
    ∃ ε : (NumberField.RingOfIntegers K)ˣ,
      ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ m : ℤ,
        u = ε ^ m ∨ u = (-1 : (NumberField.RingOfIntegers K)ˣ) * ε ^ m := by
  exact fundamental_real_rank K hreal
    (quadratic_real_place K hdegree hreal)

/-- **Milne, Example 5.3.** The element `m + n√d` is a unit exactly when its norm
`m² - d n²` is `1` or `-1`. -/
theorem zsqrtd_pell_equation (d m n : ℤ) :
    IsUnit (⟨m, n⟩ : ℤ√d) ↔
      m ^ 2 - d * n ^ 2 = 1 ∨ m ^ 2 - d * n ^ 2 = -1 := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  simp only [Zsqrtd.norm_def]
  ring_nf

/-- The half-integral quadratic-order form of Example 5.3.  Writing
`d = 4A + 1`, the element `m + n(1 + √d)/2` is a unit exactly when
`(2m+n)² - d n² = ±4`. -/
theorem half_pell_equation (A m n : ℤ) :
    IsUnit (⟨m, n⟩ : QuadraticAlgebra ℤ A 1) ↔
      (2 * m + n) ^ 2 - (4 * A + 1) * n ^ 2 = 4 ∨
        (2 * m + n) ^ 2 - (4 * A + 1) * n ^ 2 = -4 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  simp only [QuadraticAlgebra.norm_def]
  constructor
  · rintro (h | h) <;> [left; right] <;> nlinarith
  · rintro (h | h) <;> [left; right] <;> nlinarith

/-- In the integral-basis case of an imaginary quadratic field other than `ℚ(i)`, the
only units are `1` and `-1`. -/
theorem zsqrtd_neg_two {d m n : ℤ} (hd : d ≤ -2) :
    IsUnit (⟨m, n⟩ : ℤ√d) ↔ n = 0 ∧ (m = 1 ∨ m = -1) := by
  rw [zsqrtd_pell_equation]
  constructor
  · rintro (h | h)
    · have hn : n = 0 := by
        by_contra hn
        have hnSqPos : 0 < n ^ 2 := sq_pos_of_ne_zero hn
        have hnSq : 1 ≤ n ^ 2 := by omega
        nlinarith [sq_nonneg m]
      subst n
      simp only [pow_two, mul_zero, sub_zero] at h
      have hfactor : (m - 1) * (m + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hm | hm <;> omega
    · nlinarith [sq_nonneg m, sq_nonneg n]
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

/-- The Gaussian order has exactly the four units `±1` and `±i`. -/
theorem gaussian_quadratic_unit (m n : ℤ) :
    IsUnit (⟨m, n⟩ : ℤ√(-1)) ↔
      (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
        (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by
  rw [zsqrtd_pell_equation]
  constructor
  · rintro (h | h)
    · have hmlo : -1 ≤ m := by nlinarith [sq_nonneg (m + 1), sq_nonneg n]
      have hmhi : m ≤ 1 := by nlinarith [sq_nonneg (m - 1), sq_nonneg n]
      have hnlo : -1 ≤ n := by nlinarith [sq_nonneg (n + 1), sq_nonneg m]
      have hnhi : n ≤ 1 := by nlinarith [sq_nonneg (n - 1), sq_nonneg m]
      interval_cases m <;> interval_cases n
      all_goals norm_num at h
      all_goals norm_num
    · nlinarith [sq_nonneg m, sq_nonneg n]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num

/-- The roots of unity in the Gaussian order are exactly `±1` and `±i`. -/
theorem gaussian_quadratic_fin (m n : ℤ) :
    IsOfFinOrder (⟨m, n⟩ : ℤ√(-1)) ↔
      (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
        (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by
  constructor
  · exact fun h => (gaussian_quadratic_unit m n).mp h.isUnit
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rw [isOfFinOrder_iff_pow_eq_one] <;>
      refine ⟨4, by norm_num, ?_⟩ <;>
      apply Zsqrtd.ext <;>
      norm_num [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]

/-- In the half-integral-basis case of an imaginary quadratic field other than
`ℚ(√-3)`, the only units are `1` and `-1`. -/
theorem half_quadratic_neg {A m n : ℤ} (hA : A ≤ -2) :
    IsUnit (⟨m, n⟩ : QuadraticAlgebra ℤ A 1) ↔
      n = 0 ∧ (m = 1 ∨ m = -1) := by
  rw [half_pell_equation]
  constructor
  · rintro (h | h)
    · have hn : n = 0 := by
        by_contra hn
        have hnSqPos : 0 < n ^ 2 := sq_pos_of_ne_zero hn
        have hnSq : 1 ≤ n ^ 2 := by omega
        nlinarith [sq_nonneg (2 * m + n)]
      subst n
      have hfactor : (m - 1) * (m + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hm | hm <;> omega
    · nlinarith [sq_nonneg (2 * m + n), sq_nonneg n]
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num

/-- The order `ℤ[(1 + √-3)/2]` has exactly its six roots of unity as units. -/
theorem sqrt_neg_unit (m n : ℤ) :
    IsUnit (⟨m, n⟩ : QuadraticAlgebra ℤ (-1) 1) ↔
      (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
        (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) ∨
          (m = -1 ∧ n = 1) ∨ (m = 1 ∧ n = -1) := by
  rw [half_pell_equation]
  constructor
  · rintro (h | h)
    · have hnlo : -1 ≤ n := by
        nlinarith [sq_nonneg (2 * m + n), sq_nonneg (n + 1)]
      have hnhi : n ≤ 1 := by
        nlinarith [sq_nonneg (2 * m + n), sq_nonneg (n - 1)]
      have hmlo : -1 ≤ m := by nlinarith [sq_nonneg (2 * m + n)]
      have hmhi : m ≤ 1 := by nlinarith [sq_nonneg (2 * m + n)]
      interval_cases n <;> interval_cases m
      all_goals norm_num at h
      all_goals norm_num
    · nlinarith [sq_nonneg (2 * m + n), sq_nonneg n]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- The roots of unity in `ℤ[(1 + √-3)/2]` are exactly its six listed units. -/
theorem sqrt_neg_fin (m n : ℤ) :
    IsOfFinOrder (⟨m, n⟩ : QuadraticAlgebra ℤ (-1) 1) ↔
      (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
        (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) ∨
          (m = -1 ∧ n = 1) ∨ (m = 1 ∧ n = -1) := by
  constructor
  · exact fun h => (sqrt_neg_unit m n).mp h.isUnit
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      rw [isOfFinOrder_iff_pow_eq_one] <;>
      refine ⟨6, by norm_num, ?_⟩ <;>
      apply QuadraticAlgebra.ext <;>
      norm_num [pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end Submission.NumberTheory.Milne
