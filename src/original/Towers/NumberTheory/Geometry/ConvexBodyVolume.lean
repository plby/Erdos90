import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Milne, Algebraic Number Theory, Lemma 4.22

The weighted ball in the mixed real-complex space has volume
`2^r * (pi / 2)^s * t^n / n!`.
-/

namespace Towers.NumberTheory.Milne

open MeasureTheory NumberField NumberField.InfinitePlace Module

open scoped ENNReal NNReal

section ArbitrarySignature

open Fintype MeasureTheory.Measure Real

/-- The real vector space `R^r x C^s` appearing in Milne's Lemma 4.22, without
requiring `(r,s)` to arise as the signature of a number field. -/
abbrev milneMixedSpace (r s : ℕ) := (Fin r → ℝ) × (Fin s → ℂ)

/-- The weighted `l¹` norm `sum |x_i| + 2 * sum |z_j|` on `R^r x C^s`. -/
noncomputable def milneMixedWeighted {r s : ℕ} (x : milneMixedSpace r s) : ℝ :=
  ∑ i, ‖x.1 i‖ + 2 * ∑ j, ‖x.2 j‖

/-- Milne's weighted ball for an arbitrary pair `(r,s)`. -/
def milneMixedBall (r s : ℕ) (t : ℝ) : Set (milneMixedSpace r s) :=
  {x | milneMixedWeighted x ≤ t}

@[simp]
theorem milne_mixed_space (r s : ℕ) :
    finrank ℝ (milneMixedSpace r s) = r + 2 * s := by
  simp [milneMixedSpace, finrank_prod, finrank_pi_fintype,
    Complex.finrank_real_complex, Finset.sum_const, Fintype.card_fin,
    mul_comm]

private theorem milne_mixed_nonneg {r s : ℕ}
    (x : milneMixedSpace r s) :
    0 ≤ milneMixedWeighted x := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))

private theorem milne_mixed_neg {r s : ℕ}
    (x : milneMixedSpace r s) :
    milneMixedWeighted (-x) = milneMixedWeighted x := by
  simp [milneMixedWeighted]

private theorem milne_mixed_add {r s : ℕ}
    (x y : milneMixedSpace r s) :
    milneMixedWeighted (x + y) ≤
      milneMixedWeighted x + milneMixedWeighted y := by
  calc
    milneMixedWeighted (x + y) ≤
        (∑ i, (‖x.1 i‖ + ‖y.1 i‖)) +
          2 * ∑ j, (‖x.2 j‖ + ‖y.2 j‖) := by
      exact add_le_add
        (Finset.sum_le_sum fun _ _ ↦ norm_add_le _ _)
        (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun _ _ ↦ norm_add_le _ _) (by norm_num))
    _ = milneMixedWeighted x + milneMixedWeighted y := by
      simp_rw [Finset.sum_add_distrib]
      simp only [milneMixedWeighted]
      ring

private theorem milne_mixed_smul {r s : ℕ}
    (c : ℝ) (x : milneMixedSpace r s) :
    milneMixedWeighted (c • x) = |c| * milneMixedWeighted x := by
  change (∑ i, ‖c • x.1 i‖) + 2 * ∑ j, ‖c • x.2 j‖ =
    |c| * ((∑ i, ‖x.1 i‖) + 2 * ∑ j, ‖x.2 j‖)
  simp_rw [norm_smul, Real.norm_eq_abs, Finset.mul_sum]
  simp_rw [← Finset.mul_sum]
  ring

private theorem milne_mixed_weighted {r s : ℕ}
    (x : milneMixedSpace r s) :
    milneMixedWeighted x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hrNonneg : 0 ≤ ∑ i, ‖x.1 i‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hsNonneg : 0 ≤ ∑ j, ‖x.2 j‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    simp only [Real.norm_eq_abs] at hrNonneg
    simp only [milneMixedWeighted, Real.norm_eq_abs] at h
    have hr : ∑ i, |x.1 i| = 0 := by
      linarith
    have hs : ∑ j, ‖x.2 j‖ = 0 := by
      linarith
    apply Prod.ext
    · funext i
      exact abs_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ abs_nonneg _).mp hr i
          (Finset.mem_univ i))
    · funext j
      exact norm_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ norm_nonneg _).mp hs j
          (Finset.mem_univ j))
  · rintro rfl
    simp [milneMixedWeighted]

open scoped Classical in
/-- **Milne, Lemma 4.22**, for arbitrary nonnegative integers `r` and `s`:
the volume of the weighted ball in `R^r x C^s` is
`2^r * (pi/2)^s * t^(r+2s) / (r+2s)!`. -/
theorem volume_milne_mixed (r s : ℕ) (t : ℝ)
    (hn : 0 < r + 2 * s) (ht : 0 < t) :
    volume (milneMixedBall r s t) =
      (↑((2 : ℝ≥0) ^ r * (NNReal.pi / 2) ^ s /
          (r + 2 * s).factorial) : ℝ≥0∞) *
        (ENNReal.ofReal t) ^ (r + 2 * s) := by
  letI : Nontrivial (milneMixedSpace r s) :=
    nontrivial_of_finrank_pos (by rw [milne_mixed_space]; exact hn)
  letI : IsAddHaarMeasure (volume : Measure (milneMixedSpace r s)) :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let g : milneMixedSpace r s → ℝ := milneMixedWeighted
  have hg0 : g 0 = 0 := (milne_mixed_weighted (0 : milneMixedSpace r s)).mpr rfl
  have hgneg : ∀ x, g (-x) = g x := milne_mixed_neg
  have hgadd : ∀ x y, g (x + y) ≤ g x + g y := milne_mixed_add
  have hgeq : ∀ {x}, g x = 0 → x = 0 :=
    fun {_} hx ↦ (milne_mixed_weighted _).mp hx
  have hgsmul : ∀ c x, g (c • x) = |c| * g x := milne_mixed_smul
  have hunit : volume (milneMixedBall r s 1) =
      (↑((2 : ℝ≥0) ^ r * (NNReal.pi / 2) ^ s /
          (r + 2 * s).factorial) : ℝ≥0∞) := by
    change volume {x | g x ≤ 1} = _
    rw [MeasureTheory.measure_le_eq_lt _ hg0 hgneg hgadd hgeq
      (fun c x ↦ le_of_eq (hgsmul c x))]
    rw [measure_lt_one_eq_integral_div_gamma (g := g) volume hg0 hgneg hgadd hgeq
      (fun c x ↦ le_of_eq (hgsmul c x)) zero_lt_one]
    simp_rw [milne_mixed_space, div_one, Gamma_nat_eq_factorial,
      ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)),
      Real.rpow_one, ENNReal.ofReal_natCast]
    suffices ∫ x : milneMixedSpace r s, exp (-g x) =
        (2 : ℝ) ^ r * (Real.pi / 2) ^ s by
      rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos zero_lt_two,
        ENNReal.ofReal_ofNat, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal,
        ENNReal.coe_div (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
        ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_pow, ENNReal.coe_ofNat,
        ENNReal.coe_div two_ne_zero, ENNReal.coe_ofNat, ENNReal.coe_natCast]
    calc
      _ = (∫ x : Fin r → ℝ, ∏ i, exp (-‖x i‖)) *
          (∫ z : Fin s → ℂ, ∏ j, exp (-2 * ‖z j‖)) := by
        simp_rw [g, milneMixedWeighted, neg_add, ← neg_mul, Finset.mul_sum,
          ← Finset.sum_neg_distrib, exp_add, exp_sum, ← integral_prod_mul,
          volume_eq_prod]
      _ = (∫ x : ℝ, exp (-|x|)) ^ r *
          (∫ z : ℂ, exp (-2 * ‖z‖)) ^ s := by
        rw [integral_fintype_prod_volume_eq_pow (fun x ↦ exp (-‖x‖)),
          integral_fintype_prod_volume_eq_pow (fun z ↦ exp (-2 * ‖z‖))]
        simp_rw [Fintype.card_fin, norm_eq_abs]
      _ = (2 * Gamma (1 / 1 + 1)) ^ r *
          (Real.pi * (2 : ℝ) ^ (-(2 : ℝ) / 1) * Gamma (2 / 1 + 1)) ^ s := by
        rw [integral_comp_abs (f := fun x ↦ exp (-x)),
          ← integral_exp_neg_rpow zero_lt_one,
          ← Complex.integral_exp_neg_mul_rpow le_rfl zero_lt_two]
        simp_rw [Real.rpow_one]
      _ = (2 : ℝ) ^ r * (Real.pi / 2) ^ s := by
        simp_rw [div_one, one_add_one_eq_two, Gamma_add_one two_ne_zero, Gamma_two,
          mul_one, mul_assoc, ← Real.rpow_add_one two_ne_zero,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one,
          div_eq_mul_inv]
  rw [mul_comm]
  convert addHaar_smul volume t (milneMixedBall r s 1)
  · ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', milneMixedBall,
      Set.mem_setOf_eq, milneMixedBall, Set.mem_setOf_eq]
    change g x ≤ t ↔ g (t⁻¹ • x) ≤ 1
    rw [hgsmul, abs_inv, abs_eq_self.mpr ht.le, inv_mul_le_iff₀ ht, mul_one]
  · rw [abs_pow, ENNReal.ofReal_pow (abs_nonneg _), abs_eq_self.mpr ht.le,
      milne_mixed_space]
  · exact hunit.symm

open scoped Classical in
/-- Example 4.24(a), intrinsically on `R²`: the weighted ball has area `2t²`. -/
theorem volume_mixed_ball (t : ℝ) (ht : 0 < t) :
    volume (milneMixedBall 2 0 t) =
      2 * (ENNReal.ofReal t) ^ 2 := by
  rw [volume_milne_mixed 2 0 t (by norm_num) ht]
  norm_num

open scoped Classical in
/-- Example 4.24(b), intrinsically on `C`: the weighted ball is the disk of
radius `t/2` and has area `pi * t² / 4`. -/
theorem volume_milne_ball (t : ℝ) (ht : 0 < t) :
    volume (milneMixedBall 0 1 t) =
      (↑(NNReal.pi / 4) : ℝ≥0∞) * (ENNReal.ofReal t) ^ 2 := by
  rw [volume_milne_mixed 0 1 t (by norm_num) ht]
  norm_num
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp
  ring

end ArbitrarySignature

variable (K : Type*) [Field K] [NumberField K]

/-- Milne's weighted norm on the mixed real-complex embedding space. -/
noncomputable abbrev milneWeightedNorm (x : NumberField.mixedEmbedding.mixedSpace K) : ℝ :=
  NumberField.mixedEmbedding.convexBodySumFun x

/-- The weighted norm is nonnegative. -/
theorem milne_weighted_nonneg (x : NumberField.mixedEmbedding.mixedSpace K) :
    0 ≤ milneWeightedNorm K x :=
  NumberField.mixedEmbedding.convexBodySumFun_nonneg x

/-- The weighted norm vanishes only at the origin. -/
theorem milne_weighted_zero (x : NumberField.mixedEmbedding.mixedSpace K) :
    milneWeightedNorm K x = 0 ↔ x = 0 :=
  NumberField.mixedEmbedding.convexBodySumFun_eq_zero_iff x

/-- The weighted norm is absolutely homogeneous over `ℝ`. -/
theorem milne_weighted_smul (c : ℝ) (x : NumberField.mixedEmbedding.mixedSpace K) :
    milneWeightedNorm K (c • x) = |c| * milneWeightedNorm K x :=
  NumberField.mixedEmbedding.convexBodySumFun_smul c x

/-- The weighted norm satisfies the triangle inequality. -/
theorem milne_weighted_add
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    milneWeightedNorm K (x + y) ≤ milneWeightedNorm K x + milneWeightedNorm K y :=
  NumberField.mixedEmbedding.convexBodySumFun_add_le x y

/-- Milne's set `X(t)` in `R^r x C^s`, expressed in the canonical mixed space of a
number field. -/
abbrev milneWeightedBall (t : ℝ) : Set (NumberField.mixedEmbedding.mixedSpace K) :=
  NumberField.mixedEmbedding.convexBodySum K t

/-- The defining weighted `l1` inequality for Milne's `X(t)`. -/
theorem milne_weighted_ball (t : ℝ) (x : NumberField.mixedEmbedding.mixedSpace K) :
    x ∈ milneWeightedBall K t ↔
      NumberField.mixedEmbedding.convexBodySumFun x ≤ t := by
  rfl

open scoped Classical in
/-- **Milne, Lemma 4.22.** The volume of the weighted ball `X(t)` is
`2^r * (pi / 2)^s * t^n / n!`, with `r`, `s`, and `n` the real-place count,
complex-place count, and degree of the number field. -/
theorem volume_weighted_ball (t : ℝ) :
    volume (milneWeightedBall K t) =
      (↑((2 : ℝ≥0) ^ nrRealPlaces K * (NNReal.pi / 2) ^ nrComplexPlaces K /
          (finrank ℚ K).factorial) : ℝ≥0∞) *
        (ENNReal.ofReal t) ^ finrank ℚ K := by
  exact NumberField.mixedEmbedding.convexBodySum_volume K t

open scoped Classical in
/-- Example 4.24(a): with two real coordinates and no complex coordinates, the weighted ball
has volume `2 * t²` (expressed using `ENNReal.ofReal` for arbitrary real `t`). -/
theorem volume_ball_real (t : ℝ)
    (hr : nrRealPlaces K = 2) (hs : nrComplexPlaces K = 0)
    (hn : finrank ℚ K = 2) :
    volume (milneWeightedBall K t) =
      2 * (ENNReal.ofReal t) ^ 2 := by
  rw [volume_weighted_ball, hr, hs, hn]
  norm_num

open scoped Classical in
/-- Example 4.24(b): with one complex coordinate and no real coordinates, the weighted ball
has volume `π * t² / 4`. -/
theorem volume_ball_complex (t : ℝ)
    (hr : nrRealPlaces K = 0) (hs : nrComplexPlaces K = 1)
    (hn : finrank ℚ K = 2) :
    volume (milneWeightedBall K t) =
      (↑(NNReal.pi / 4) : ℝ≥0∞) * (ENNReal.ofReal t) ^ 2 := by
  rw [volume_weighted_ball, hr, hs, hn]
  norm_num
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp
  ring

end Towers.NumberTheory.Milne
