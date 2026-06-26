import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Milne, Algebraic Number Theory, roots of unity in a number field

This file records the observations following Theorem 5.1: the torsion units are exactly the
roots of unity, and the presence of a primitive `m`-th root of unity forces `φ(m)` to divide
the degree of the number field.
-/

namespace Towers.NumberTheory.Milne

open NumberField NumberField.Units
open IntermediateField
open scoped NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The torsion subgroup of the unit group is the group of roots of unity in the field. -/
theorem unit_roots_unity :
    torsion K = rootsOfUnity (torsionOrder K) (𝓞 K) :=
  (rootsOfUnity_eq_torsion K).symm

/-- The roots of unity in a number field form a finite cyclic group. -/
theorem unit_torsion_cyclic : IsCyclic (torsion K) :=
  inferInstance

/-- If `K` contains a primitive `m`-th root of unity, then `φ(m)` divides `[K : ℚ]`. -/
theorem totient_primitive_root {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) : m.totient ∣ Module.finrank ℚ K := by
  let E : IntermediateField ℚ K := ℚ⟮ζ⟯
  letI : IsCyclotomicExtension {m} ℚ E :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hfinrank : Module.finrank ℚ E = m.totient :=
    IsCyclotomicExtension.Rat.finrank m E
  have hdvd : Module.finrank ℚ E ∣ Module.finrank ℚ (⊤ : IntermediateField ℚ K) :=
    IntermediateField.finrank_dvd_of_le_right le_top
  simpa [hfinrank] using hdvd

/-- The order of every root of unity in `K` divides the order of the full group of roots of
unity. -/
theorem dvd_torsion_fin {ζ : K} (hζ : IsOfFinOrder ζ) :
    orderOf ζ ∣ torsionOrder K := by
  letI : NeZero (orderOf ζ) := ⟨hζ.orderOf_pos.ne'⟩
  exact dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf ζ)

/-- The set of orders that actually occur among roots of unity in a number field is finite. -/
theorem root_unity_orders :
    {m : ℕ | ∃ ζ : K, IsOfFinOrder ζ ∧ orderOf ζ = m}.Finite := by
  apply (Set.finite_Iic (torsionOrder K)).subset
  rintro m ⟨ζ, hζ, rfl⟩
  exact Nat.le_of_dvd (torsionOrder_pos K)
    (dvd_torsion_fin K hζ)

/-- Milne, "Finding `μ(K)`": there are only finitely many positive integers `m` for which
`K` contains a primitive `m`-th root of unity. -/
theorem positive_primitive_orders :
    {m : ℕ | 0 < m ∧ ∃ ζ : K, IsPrimitiveRoot ζ m}.Finite := by
  apply root_unity_orders K |>.subset
  rintro m ⟨hm, ζ, hζ⟩
  exact ⟨ζ, hζ.isOfFinOrder hm.ne', hζ.eq_orderOf.symm⟩

set_option linter.style.nativeDecide false in
/-- A positive integer with Euler totient at most two divides `12`. -/
theorem dvd_twelve_totient {m : ℕ}
    (hm : 0 < m) (hphi : m.totient ≤ 2) :
    m ∣ 12 := by
  apply
    (Nat.factorization_le_iff_dvd hm.ne'
      (by norm_num : (12 : ℕ) ≠ 0)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      rw [show (12 : ℕ).factorization 2 = 2 by native_decide]
      by_contra h
      have hpow : 2 ^ 3 ∣ m :=
        Nat.prime_two.pow_dvd_iff_le_factorization hm.ne' |>.2 (by omega)
      have htot : (2 ^ 3).totient ∣ m.totient :=
        Nat.totient_dvd_of_dvd hpow
      have hfour : 4 ∣ m.totient := by
        norm_num at htot ⊢
        exact htot
      have := Nat.le_of_dvd (Nat.totient_pos.mpr hm) hfour
      omega
    · by_cases hp3 : p = 3
      · subst p
        rw [show (12 : ℕ).factorization 3 = 1 by native_decide]
        by_contra h
        have hp3prime : Nat.Prime 3 := hp
        have hpow : 3 ^ 2 ∣ m :=
          hp3prime.pow_dvd_iff_le_factorization hm.ne' |>.2 (by omega)
        have htot : (3 ^ 2).totient ∣ m.totient :=
          Nat.totient_dvd_of_dvd hpow
        have hsix : 6 ∣ m.totient := by
          norm_num at htot ⊢
          exact htot
        have := Nat.le_of_dvd (Nat.totient_pos.mpr hm) hsix
        omega
      · have hfac : m.factorization p = 0 := by
          by_contra h
          have hpos : 0 < m.factorization p := Nat.pos_of_ne_zero h
          have hpdvd : p ∣ m := by
            simpa using
              (hp.pow_dvd_iff_le_factorization hm.ne' (k := 1)).2 (by omega)
          have htot : p.totient ∣ m.totient :=
            Nat.totient_dvd_of_dvd hpdvd
          rw [Nat.totient_prime hp] at htot
          have hle : p - 1 ≤ 2 :=
            (Nat.le_of_dvd (Nat.totient_pos.mpr hm) htot).trans hphi
          have hpgt : 1 < p := hp.one_lt
          omega
        rw [hfac]
        exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- Milne's arithmetic classification from Example 5.3:
`φ(m) ≤ 2` exactly for the positive integers dividing `4` or `6`. -/
theorem totient_or_six {m : ℕ} (hm : 0 < m) :
    m.totient ≤ 2 ↔ m ∣ 4 ∨ m ∣ 6 := by
  constructor
  · intro h
    have hdvd := dvd_twelve_totient hm h
    have hle : m ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hmne12 : m ≠ 12 := by
      intro hm12
      subst m
      have ht : (12 : ℕ).totient = 4 := by decide
      omega
    interval_cases m
    all_goals omega
  · rintro (h | h)
    · have hdvd : m.totient ∣ (4 : ℕ).totient :=
        Nat.totient_dvd_of_dvd h
      norm_num at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    · have hdvd : m.totient ∣ (6 : ℕ).totient :=
        Nat.totient_dvd_of_dvd h
      norm_num at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd

/-- The cyclotomic field generated by a primitive `m`th root of unity has degree at most two
exactly for the orders that occur in Milne's quadratic-field classification. -/
theorem cyclotomic_or_six
    (m : ℕ) [NeZero m] :
    Module.finrank ℚ (CyclotomicField m ℚ) ≤ 2 ↔ m ∣ 4 ∨ m ∣ 6 := by
  letI : NeZero (m : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  letI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  rw [IsCyclotomicExtension.Rat.finrank m (CyclotomicField m ℚ)]
  exact totient_or_six (NeZero.pos m)

/-- If a quadratic number field contains a primitive `m`th root of unity, then `m`
divides `4` or `6`. This is the field-level restriction used in Example 5.3. -/
theorem primitive_six_quadratic
    (hdegree : Module.finrank ℚ K = 2)
    {m : ℕ} [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m) :
    m ∣ 4 ∨ m ∣ 6 := by
  have hdvd : m.totient ∣ 2 := by
    simpa [hdegree] using
      (totient_primitive_root K hζ)
  have hle : m.totient ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact (totient_or_six (NeZero.pos m)).mp hle

/-- A positive integer `m` occurs as the order of a root of unity in a quadratic number
field. The field is part of the assertion, so this also covers the degree-one cyclotomic
cases `m = 1, 2` by placing their roots in an auxiliary quadratic field. -/
def PrimitiveOccursQuadratic (m : ℕ) : Prop :=
  ∃ (L : Type) (fieldL : Field L),
    letI := fieldL
    ∃ numberFieldL : NumberField L,
      letI := numberFieldL
      Module.finrank ℚ L = 2 ∧ ∃ ζ : L, IsPrimitiveRoot ζ m

/-- Example 5.3: a primitive `m`-th root of unity occurs in some quadratic number field
exactly when `φ(m) ≤ 2` (equivalently, when `m` divides `4` or `6`). -/
theorem primitive_occurs_totient
    {m : ℕ} (hm : 0 < m) :
    PrimitiveOccursQuadratic m ↔ m.totient ≤ 2 := by
  constructor
  · rintro ⟨L, fieldL, numberFieldL, hdegree, ζ, hζ⟩
    letI := fieldL
    letI := numberFieldL
    letI : NeZero m := ⟨hm.ne'⟩
    have hdvd : m.totient ∣ 2 := by
      simpa [hdegree] using totient_primitive_root L hζ
    exact Nat.le_of_dvd (by norm_num) hdvd
  · intro htotient
    rcases (totient_or_six hm).mp htotient with hfour | hsix
    · letI : NeZero (4 : ℕ) := inferInstance
      letI : NeZero (4 : ℚ) := ⟨by norm_num⟩
      letI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
        CyclotomicField.isCyclotomicExtension 4 ℚ
      let ζ := IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ)
      have hζ : IsPrimitiveRoot ζ 4 :=
        IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)
      obtain ⟨a, ha⟩ := hfour
      refine ⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, ?_,
        ζ ^ a, hζ.pow (by norm_num) ?_⟩
      · simpa using
          (IsCyclotomicExtension.Rat.finrank 4 (CyclotomicField 4 ℚ))
      · simpa [Nat.mul_comm] using ha
    · letI : NeZero (6 : ℕ) := inferInstance
      letI : NeZero (6 : ℚ) := ⟨by norm_num⟩
      letI : IsCyclotomicExtension {6} ℚ (CyclotomicField 6 ℚ) :=
        CyclotomicField.isCyclotomicExtension 6 ℚ
      let ζ := IsCyclotomicExtension.zeta 6 ℚ (CyclotomicField 6 ℚ)
      have hζ : IsPrimitiveRoot ζ 6 :=
        IsCyclotomicExtension.zeta_spec 6 ℚ (CyclotomicField 6 ℚ)
      obtain ⟨a, ha⟩ := hsix
      refine ⟨CyclotomicField 6 ℚ, inferInstance, inferInstance, ?_,
        ζ ^ a, hζ.pow (by norm_num) ?_⟩
      · simpa using
          (IsCyclotomicExtension.Rat.finrank 6 (CyclotomicField 6 ℚ))
      · simpa [Nat.mul_comm] using ha

end

end Towers.NumberTheory.Milne
