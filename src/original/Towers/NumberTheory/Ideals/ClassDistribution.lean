import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

namespace Towers.NumberTheory

open Filter Ideal NumberField InfinitePlace Module Topology
open scoped nonZeroDivisors Real

namespace IDistri

variable (K : Type*) [Field K] [NumberField K]

/-- The number of nonzero integral ideals of norm at most `k` in the ideal
class `C`. -/
noncomputable def classIdealCount (C : ClassGroup (𝓞 K)) (k : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ //
    absNorm (I : Ideal (𝓞 K)) ≤ k ∧ ClassGroup.mk0 I = C}

/-- The number of all nonzero integral ideals of norm at most `k`. -/
noncomputable def nonzeroIdealCount (k : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ k}

/-- The common density constant in Wright's Theorem 106. -/
noncomputable def classDensity : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * Units.regulator K) /
    (Units.torsionOrder K * Real.sqrt |discr K|)

/-- Mathlib's classwise ideal-distribution limit, in Wright's notation. -/
theorem class_count_tendsto (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) ≤ s ∧ ClassGroup.mk0 I = C} : ℝ) / s)
      atTop (𝓝 (classDensity K)) := by
  simpa [classDensity] using
    NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K C

/-- The bounded ideals are the disjoint union of their ideal-class fibers. -/
theorem nonzero_count_class (k : ℕ) :
    nonzeroIdealCount K k =
      ∑ C : ClassGroup (𝓞 K), classIdealCount K C k := by
  classical
  haveI : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ k} :=
    @Fintype.ofFinite _ (finite_setOf_absNorm_le₀ k)
  let e := fun C : ClassGroup (𝓞 K) ↦ Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.1 ≤ k) (fun I ↦ ClassGroup.mk0 I = C)
  simp only [nonzeroIdealCount, classIdealCount]
  simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
  rw [Fintype.card, Finset.card_eq_sum_card_fiberwise
    (f := fun I ↦ ClassGroup.mk0 I.1) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]

/-- Wright's quantitative clause in Theorem 106, isolated from the already
formalized limit statement. -/
def ClasswiseRemainderBound (M : ℝ) : Prop :=
  ∀ (C : ClassGroup (𝓞 K)) (k : ℕ), 1 ≤ k →
    |(classIdealCount K C k : ℝ) / k - classDensity K| ≤
      M * (k : ℝ) ^ (-(1 / (finrank ℚ K : ℝ)))

/-- The error-bound clause of Theorem 107 follows by summing the classwise
error bounds from Theorem 106. -/
theorem total_remainder_classwise
    {M : ℝ} (hM : ClasswiseRemainderBound K M)
    (k : ℕ) (hk : 1 ≤ k) :
    |(nonzeroIdealCount K k : ℝ) / k -
        classDensity K * NumberField.classNumber K| ≤
      M * NumberField.classNumber K *
        (k : ℝ) ^ (-(1 / (finrank ℚ K : ℝ))) := by
  have hidentity :
      (nonzeroIdealCount K k : ℝ) / k -
          classDensity K * NumberField.classNumber K =
        ∑ C : ClassGroup (𝓞 K),
          ((classIdealCount K C k : ℝ) / k - classDensity K) := by
    rw [nonzero_count_class]
    push_cast
    rw [Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NumberField.classNumber]
    ring
  rw [hidentity]
  calc
    |∑ C : ClassGroup (𝓞 K),
        ((classIdealCount K C k : ℝ) / k - classDensity K)| ≤
        ∑ C : ClassGroup (𝓞 K),
          |(classIdealCount K C k : ℝ) / k - classDensity K| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _C : ClassGroup (𝓞 K),
        M * (k : ℝ) ^ (-(1 / (finrank ℚ K : ℝ))) := by
      exact Finset.sum_le_sum fun C _ ↦ hM C k hk
    _ = M * NumberField.classNumber K *
        (k : ℝ) ^ (-(1 / (finrank ℚ K : ℝ))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NumberField.classNumber]
      ring

end IDistri

end Towers.NumberTheory
