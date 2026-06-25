import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Towers.ClassField.EulerProducts.CoefficientPartialSum

/-!
# Chapter VI, Section 2, Proposition 2.1: the Abel estimate

This file supplies the partial-summation estimate proved by
`partial_abel_estimate`. In particular, it does not replace ordinary
convergence by absolute convergence.
-/

namespace Towers.CField.EProduc

open Complex Filter Finset Set Topology MeasureTheory

noncomputable section

/-- In a closed sector separated from the imaginary axis, modulus is bounded
by a fixed multiple of real part. -/
private theorem re_sin_region
    {b δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hε : 0 < ε)
    (hs : s ∈ dirichletRegion b δ ε) :
    ‖s - (b : ℂ)‖ ≤ (s.re - b) / Real.sin ε := by
  have hεpi : ε ≤ Real.pi / 2 :=
    sub_nonneg.mp ((abs_nonneg _).trans hs.2)
  have hsin : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε
      (hεpi.trans_lt (half_lt_self Real.pi_pos))
  have hzre : 0 < (s - (b : ℂ)).re := by
    simp only [sub_re, ofReal_re]
    linarith [hs.1]
  have hz : s - (b : ℂ) ≠ 0 := by
    intro h
    simp [h] at hzre
  have hcos : Real.sin ε ≤ Real.cos (arg (s - (b : ℂ))) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := |arg (s - (b : ℂ))|) (y := Real.pi / 2 - ε)
      (abs_nonneg _)
      ((sub_le_self _ hε.le).trans (half_le_self Real.pi_pos.le)) hs.2
    simpa [Real.cos_abs, Real.cos_pi_div_two_sub] using h
  have hmul : ‖s - (b : ℂ)‖ * Real.sin ε ≤ s.re - b := by
    calc
      ‖s - (b : ℂ)‖ * Real.sin ε
          ≤ ‖s - (b : ℂ)‖ * Real.cos (arg (s - (b : ℂ))) :=
            mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
      _ = (s - (b : ℂ)).re := Complex.norm_mul_cos_arg _
      _ = s.re - b := by simp
  exact (le_div_iff₀ hsin).2 hmul

/-- The factor `|s|` created by differentiating `x⁻ˢ` is absorbed by the
distance of `s` from the boundary line. -/
private theorem gap_sector_constant
    {b δ ε : ℝ} {s : ℂ} (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hs : s ∈ dirichletRegion b δ ε) :
    ‖s‖ ≤ (s.re - b) * (1 / Real.sin ε + b / δ) := by
  have hsin : 0 < Real.sin ε := by
    have hεpi : ε ≤ Real.pi / 2 :=
      sub_nonneg.mp ((abs_nonneg _).trans hs.2)
    exact Real.sin_pos_of_pos_of_lt_pi hε
      (hεpi.trans_lt (half_lt_self Real.pi_pos))
  have hgap : δ ≤ s.re - b := by linarith [hs.1]
  have hgap0 : 0 ≤ s.re - b := hδ.le.trans hgap
  have hnormadd : ‖s‖ ≤ ‖s - (b : ℂ)‖ + b := by
    calc
      ‖s‖ = ‖(s - (b : ℂ)) + (b : ℂ)‖ := by ring_nf
      _ ≤ ‖s - (b : ℂ)‖ + ‖(b : ℂ)‖ := norm_add_le _ _
      _ = ‖s - (b : ℂ)‖ + b := by simp [hb.le]
  calc
    ‖s‖ ≤ ‖s - (b : ℂ)‖ + b := hnormadd
    _ ≤ (s.re - b) / Real.sin ε + b :=
      by gcongr; exact re_sin_region hδ hε hs
    _ ≤ (s.re - b) / Real.sin ε + (s.re - b) * (b / δ) := by
      gcongr
      calc
        b = δ * (b / δ) := by field_simp
        _ ≤ (s.re - b) * (b / δ) := by
          gcongr
    _ = (s.re - b) * (1 / Real.sin ε + b / δ) := by ring

/-- The zeroth coefficient is irrelevant to an L-series, so we erase it when
using Mathlib's Abel formula (whose partial sums begin at zero). -/
private def coefficientsFromOne (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n

private theorem sum_coefficients_one (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 0 N, coefficientsFromOne a n = coefficientPartialSum a N := by
  classical
  rw [coefficientPartialSum]
  calc
    ∑ n ∈ Icc 0 N, coefficientsFromOne a n =
        ∑ n ∈ (Finset.Icc 0 N).filter (fun n ↦ n ≠ 0), a n := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n hn
      simp only [coefficientsFromOne]
      split_ifs <;> simp_all
    _ = ∑ n ∈ Icc 1 N, a n := by
      apply sum_congr
      · ext n
        simp only [mem_filter, Finset.mem_Icc]
        omega
      · intro n hn
        rfl

/-- On positive indices, `x⁻ˢ a(x)` is precisely the L-series term. -/
private theorem cpow_neg_term
    (a : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    ((n : ℂ) ^ (-s)) * coefficientsFromOne a n = LSeries.term a s n := by
  rw [coefficientsFromOne, if_neg hn.ne', LSeries.term_def, if_neg hn.ne']
  rw [div_eq_mul_inv, Complex.cpow_neg]
  ring

/-- Abel summation on an interval wholly to the right of zero. -/
private theorem abel_tail_identity
    (a : ℕ → ℂ) (s : ℂ) {l u : ℕ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : s ≠ 0) :
    ∑ k ∈ Ioc l u, LSeries.term a s k =
      ((u : ℂ) ^ (-s)) * coefficientPartialSum a u -
      ((l : ℂ) ^ (-s)) * coefficientPartialSum a l -
      ∫ t : ℝ in Set.Ioc (l : ℝ) u,
        ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊ := by
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s)
  have hdiff : ∀ t ∈ Set.Icc (l : ℝ) u, DifferentiableAt ℝ f t := by
    intro t ht
    exact DifferentiableAt.ofReal_cpow_const differentiableAt_id
      (ne_of_gt ((Nat.cast_pos.mpr hl).trans_le ht.1)) (neg_ne_zero.mpr hs)
  have hderiv : ∀ t ∈ Set.Icc (l : ℝ) u,
      deriv f t = (-s) * (t : ℂ) ^ (-s - 1) := by
    intro t ht
    exact Complex.deriv_ofReal_cpow_const
      (ne_of_gt ((Nat.cast_pos.mpr hl).trans_le ht.1)) (neg_ne_zero.mpr hs)
  have hcont : ContinuousOn (fun t : ℝ ↦ (-s) * (t : ℂ) ^ (-s - 1))
      (Set.Icc (l : ℝ) u) := by
    intro t ht
    exact (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
        (Or.inr (ne_of_gt ((Nat.cast_pos.mpr hl).trans_le ht.1))))).continuousWithinAt
  have hint : IntegrableOn (deriv f) (Set.Icc (l : ℝ) u) := by
    apply IntegrableOn.congr_fun hcont.integrableOn_Icc _ measurableSet_Icc
    intro t ht
    exact (hderiv t ht).symm
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (c := coefficientsFromOne a) (f := f) hlu hdiff hint
  calc
    ∑ k ∈ Ioc l u, LSeries.term a s k =
        ∑ k ∈ Ioc l u, f k * coefficientsFromOne a k := by
      apply sum_congr rfl
      intro k hk
      exact (cpow_neg_term a s
        (hl.trans (Finset.mem_Ioc.mp hk).1)).symm
    _ = f u * (∑ k ∈ Icc 0 u, coefficientsFromOne a k) -
          f l * (∑ k ∈ Icc 0 l, coefficientsFromOne a k) -
          ∫ t : ℝ in Set.Ioc (l : ℝ) u,
            deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, coefficientsFromOne a k := habel
    _ = ((u : ℂ) ^ (-s)) * coefficientPartialSum a u -
          ((l : ℂ) ^ (-s)) * coefficientPartialSum a l -
          ∫ t : ℝ in Set.Ioc (l : ℝ) u,
            ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊ := by
      simp only [f, sum_coefficients_one]
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hderiv t ⟨ht.1.le, ht.2⟩]

/-- The two boundary terms in Abel summation have the required decay. -/
private theorem norm_boundary_term
    (a : ℕ → ℂ) (A b δ : ℝ) (s : ℂ) {l x : ℕ}
    (hA : 0 < A) (hδ : 0 < δ) (hl : 0 < l) (hlx : l ≤ x)
    (hre : b + δ ≤ s.re)
    (hgrowth : ‖coefficientPartialSum a x‖ ≤ A * (x : ℝ) ^ b) :
    ‖((x : ℂ) ^ (-s)) * coefficientPartialSum a x‖ ≤
      A * (l : ℝ) ^ (-δ) := by
  have hx : 0 < (x : ℝ) := Nat.cast_pos.mpr (hl.trans_le hlx)
  have hlreal : 0 < (l : ℝ) := Nat.cast_pos.mpr hl
  have hxone : 1 ≤ (x : ℝ) := by exact_mod_cast hl.trans_le hlx
  have hexp : b - s.re ≤ -δ := by linarith
  calc
    ‖((x : ℂ) ^ (-s)) * coefficientPartialSum a x‖ =
        (x : ℝ) ^ (-s.re) * ‖coefficientPartialSum a x‖ := by
      rw [norm_mul, show (x : ℂ) = ((x : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    _ ≤ (x : ℝ) ^ (-s.re) * (A * (x : ℝ) ^ b) := by
      gcongr
    _ = A * (x : ℝ) ^ (b - s.re) := by
      rw [show b - s.re = -s.re + b by ring, Real.rpow_add hx]
      ring
    _ ≤ A * (x : ℝ) ^ (-δ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hxone hexp) hA.le
    _ ≤ A * (l : ℝ) ^ (-δ) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact Real.rpow_le_rpow_of_nonpos hlreal (by norm_cast) (neg_nonpos.mpr hδ.le)

/-- Pointwise majorant for the integral term in Abel summation. -/
private theorem norm_abel_integrand
    (a : ℕ → ℂ) (A b : ℝ) (s : ℂ) {l u : ℕ} {t : ℝ}
    (hA : 0 < A) (hb : 0 < b) (hl : 0 < l)
    (ht : t ∈ Set.Ioc (l : ℝ) u)
    (hgrowth : ∀ k ≥ l,
      ‖coefficientPartialSum a k‖ ≤ A * (k : ℝ) ^ b) :
    ‖((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ ≤
      ‖s‖ * A * t ^ (b - s.re - 1) := by
  have ht0 : 0 < t := (Nat.cast_pos.mpr hl).trans ht.1
  have hfloor : l ≤ ⌊t⌋₊ := Nat.le_floor ht.1.le
  have hfloor0 : 0 < (⌊t⌋₊ : ℝ) := Nat.cast_pos.mpr (hl.trans_le hfloor)
  have hfloor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
  have hpowfloor : (⌊t⌋₊ : ℝ) ^ b ≤ t ^ b :=
    Real.rpow_le_rpow hfloor0.le hfloor_le hb.le
  calc
    ‖((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ =
        ‖s‖ * t ^ (-s.re - 1) * ‖coefficientPartialSum a ⌊t⌋₊‖ := by
      rw [norm_mul, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp
    _ ≤ ‖s‖ * t ^ (-s.re - 1) * (A * (⌊t⌋₊ : ℝ) ^ b) := by
      gcongr
      exact hgrowth _ hfloor
    _ ≤ ‖s‖ * t ^ (-s.re - 1) * (A * t ^ b) := by
      gcongr
    _ = ‖s‖ * A * t ^ (b - s.re - 1) := by
      rw [show b - s.re - 1 = (-s.re - 1) + b by ring, Real.rpow_add ht0]
      ring

/-- The integral in Abel summation is bounded by the same power as the
boundary terms; the sector condition controls the derivative's factor
`|s|`. -/
private theorem norm_abel_integral
    (a : ℕ → ℂ) (A b δ ε : ℝ) (s : ℂ) {l u : ℕ}
    (hA : 0 < A) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hl : 0 < l) (_hlu : l ≤ u) (hs : s ∈ dirichletRegion b δ ε)
    (hgrowth : ∀ k ≥ l,
      ‖coefficientPartialSum a k‖ ≤ A * (k : ℝ) ^ b) :
    ‖∫ t : ℝ in Set.Ioc (l : ℝ) u,
        ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ ≤
      A * (1 / Real.sin ε + b / δ) * (l : ℝ) ^ (-δ) := by
  let p : ℝ := b - s.re - 1
  let K : ℝ := 1 / Real.sin ε + b / δ
  have hgap : 0 < s.re - b := by linarith [hs.1]
  have hp : p < -1 := by dsimp [p]; linarith [hs.1]
  have hlreal : 0 < (l : ℝ) := Nat.cast_pos.mpr hl
  have hsin : 0 < Real.sin ε := by
    have hεpi : ε ≤ Real.pi / 2 :=
      sub_nonneg.mp ((abs_nonneg _).trans hs.2)
    exact Real.sin_pos_of_pos_of_lt_pi hε
      (hεpi.trans_lt (half_lt_self Real.pi_pos))
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajorIoi : IntegrableOn (fun t : ℝ ↦ ‖s‖ * A * t ^ p)
      (Set.Ioi (l : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hp hlreal).const_mul (‖s‖ * A)
  have hmajorIoc : IntegrableOn (fun t : ℝ ↦ ‖s‖ * A * t ^ p)
      (Set.Ioc (l : ℝ) u) :=
    hmajorIoi.mono_set Set.Ioc_subset_Ioi_self
  have hnorm :
      ‖∫ t : ℝ in Set.Ioc (l : ℝ) u,
          ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ ≤
        ∫ t : ℝ in Set.Ioc (l : ℝ) u, ‖s‖ * A * t ^ p := by
    apply norm_integral_le_of_norm_le hmajorIoc
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [p] using norm_abel_integrand a A b s hA hb hl ht hgrowth
  have hmono :
      (∫ t : ℝ in Set.Ioc (l : ℝ) u, ‖s‖ * A * t ^ p) ≤
        ∫ t : ℝ in Set.Ioi (l : ℝ), ‖s‖ * A * t ^ p := by
    apply setIntegral_mono_set hmajorIoi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hA.le)
        (Real.rpow_nonneg (le_of_lt (hlreal.trans ht)) _)
    · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  have hnorms : ‖s‖ ≤ (s.re - b) * K := by
    simpa only [K] using gap_sector_constant hb hδ hε hs
  have hexp : b - s.re ≤ -δ := by linarith [hs.1]
  calc
    ‖∫ t : ℝ in Set.Ioc (l : ℝ) u,
        ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖
        ≤ ∫ t : ℝ in Set.Ioc (l : ℝ) u, ‖s‖ * A * t ^ p := hnorm
    _ ≤ ∫ t : ℝ in Set.Ioi (l : ℝ), ‖s‖ * A * t ^ p := hmono
    _ = ‖s‖ * A * (-((l : ℝ) ^ (p + 1)) / (p + 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hp hlreal]
    _ = ‖s‖ * A * ((l : ℝ) ^ (b - s.re) / (s.re - b)) := by
      dsimp [p]
      rw [show b - s.re - 1 + 1 = b - s.re by ring]
      rw [show b - s.re = -(s.re - b) by ring, div_neg]
      ring
    _ ≤ ((s.re - b) * K) * A * ((l : ℝ) ^ (b - s.re) / (s.re - b)) := by
      gcongr
    _ = A * K * (l : ℝ) ^ (b - s.re) := by
      field_simp
    _ ≤ A * K * (l : ℝ) ^ (-δ) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl) hexp)
      exact mul_nonneg hA.le hK
    _ = A * (1 / Real.sin ε + b / δ) * (l : ℝ) ^ (-δ) := by rfl

/-- Quantitative bound for a finite tail whose lower endpoint is positive. -/
private theorem norm_ioc_term
    (a : ℕ → ℂ) (A b δ ε : ℝ) (s : ℂ) {l u : ℕ}
    (hA : 0 < A) (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε)
    (hl : 0 < l) (hlu : l ≤ u) (hs : s ∈ dirichletRegion b δ ε)
    (hgrowth : ∀ k ≥ l,
      ‖coefficientPartialSum a k‖ ≤ A * (k : ℝ) ^ b) :
    ‖∑ k ∈ Ioc l u, LSeries.term a s k‖ ≤
      A * (2 + (1 / Real.sin ε + b / δ)) * (l : ℝ) ^ (-δ) := by
  have hsre : b + δ ≤ s.re := hs.1
  have hs0 : s ≠ 0 := by
    intro hszero
    have : s.re = 0 := by simp [hszero]
    linarith
  rw [abel_tail_identity a s hl hlu hs0]
  have hbu := norm_boundary_term a A b δ s hA hδ hl hlu hsre
    (hgrowth u hlu)
  have hbl := norm_boundary_term a A b δ s hA hδ hl le_rfl hsre
    (hgrowth l le_rfl)
  have hi := norm_abel_integral a A b δ ε s hA hb hδ hε hl hlu hs hgrowth
  calc
    ‖((u : ℂ) ^ (-s)) * coefficientPartialSum a u -
        ((l : ℂ) ^ (-s)) * coefficientPartialSum a l -
        ∫ t : ℝ in Set.Ioc (l : ℝ) u,
          ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖
        ≤ ‖((u : ℂ) ^ (-s)) * coefficientPartialSum a u‖ +
          ‖((l : ℂ) ^ (-s)) * coefficientPartialSum a l‖ +
          ‖∫ t : ℝ in Set.Ioc (l : ℝ) u,
            ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ := by
      calc
        _ ≤ ‖((u : ℂ) ^ (-s)) * coefficientPartialSum a u -
              ((l : ℂ) ^ (-s)) * coefficientPartialSum a l‖ +
              ‖∫ t : ℝ in Set.Ioc (l : ℝ) u,
                ((-s) * (t : ℂ) ^ (-s - 1)) * coefficientPartialSum a ⌊t⌋₊‖ :=
          norm_sub_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
    _ ≤ A * (l : ℝ) ^ (-δ) + A * (l : ℝ) ^ (-δ) +
          A * (1 / Real.sin ε + b / δ) * (l : ℝ) ^ (-δ) := by
      gcongr
    _ = A * (2 + (1 / Real.sin ε + b / δ)) * (l : ℝ) ^ (-δ) := by ring

private theorem ordered_ioc_pred
    (a : ℕ → ℂ) (s : ℂ) {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    dirichletPartialSum a m s - dirichletPartialSum a n s =
      ∑ k ∈ Ioc (n - 1) (m - 1), LSeries.term a s k := by
  rw [dirichletPartialSum, dirichletPartialSum,
    ← sum_Ico_eq_sub _ hnm]
  apply sum_congr
  · ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  · intro k hk
    rfl

/-- Moving the lower endpoint from `N - 1` to the source's convenient
`N + 1` costs only the fixed factor `3^δ`. -/
private theorem nat_rpow_neg
    (δ : ℝ) {N l : ℕ} (hδ : 0 < δ) (hN : 2 ≤ N) (hl : N - 1 ≤ l) :
    (l : ℝ) ^ (-δ) ≤ 3 ^ δ * ((N : ℝ) + 1) ^ (-δ) := by
  have hlpos : 0 < (l : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N - 1) hl)
  have hthirdpos : 0 < ((N : ℝ) + 1) / 3 := by positivity
  have hthirdle : ((N : ℝ) + 1) / 3 ≤ (l : ℝ) := by
    have hl' : ((N - 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    have hNm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      norm_num
    apply le_trans _ hl'
    rw [hNm1, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  calc
    (l : ℝ) ^ (-δ) ≤ (((N : ℝ) + 1) / 3) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hthirdpos hthirdle (neg_nonpos.mpr hδ.le)
    _ = 3 ^ δ * ((N : ℝ) + 1) ^ (-δ) := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      field_simp

/-- The quantitative Abel estimate required by Proposition VI.2.1. -/
theorem abelTailEstimate : AbelTailEstimate := by
  intro a A b δ ε hA hb hδ hε hgrowth
  rw [eventually_atTop] at hgrowth
  obtain ⟨N₁, hN₁⟩ := hgrowth
  let B : ℝ := 2 + (1 / Real.sin ε + b / δ)
  let C : ℝ := A * B * 3 ^ δ
  by_cases hregion : dirichletRegion b δ ε = ∅
  · refine ⟨0, le_rfl, 0, ?_⟩
    intro N hN m hm n hn s hs
    simp [hregion] at hs
  have hεpi : ε ≤ Real.pi / 2 := by
    obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hregion
    exact sub_nonneg.mp ((abs_nonneg _).trans hs.2)
  have hsin' : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε
      (hεpi.trans_lt (half_lt_self Real.pi_pos))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, max (N₁ + 1) 2, ?_⟩
  intro N hN m hm n hn s hs
  have hNtwo : 2 ≤ N := (le_max_right (N₁ + 1) 2).trans hN
  have hNN₁ : N₁ + 1 ≤ N := (le_max_left (N₁ + 1) 2).trans hN
  have hordered : ∀ {p q : ℕ}, N ≤ p → N ≤ q → p ≤ q →
      dist (dirichletPartialSum a q s)
          (dirichletPartialSum a p s) ≤
        C * ((N : ℝ) + 1) ^ (-δ) := by
    intro p q hp hq hpq
    have hp0 : 0 < p := by omega
    have hl0 : 0 < p - 1 := by omega
    have hlu : p - 1 ≤ q - 1 := Nat.sub_le_sub_right hpq 1
    have hlN₁ : N₁ ≤ p - 1 := by omega
    have htail := norm_ioc_term a A b δ ε s hA hb hδ hε
      hl0 hlu hs (fun k hk ↦ hN₁ k (hlN₁.trans hk))
    have hdecay := nat_rpow_neg δ hδ hNtwo
      (Nat.sub_le_sub_right hp 1 : N - 1 ≤ p - 1)
    rw [dist_eq_norm, ordered_ioc_pred a s hp0 hpq]
    calc
      ‖∑ k ∈ Ioc (p - 1) (q - 1), LSeries.term a s k‖
          ≤ A * B * (p - 1 : ℕ) ^ (-δ) := by simpa only [B] using htail
      _ ≤ A * B * (3 ^ δ * ((N : ℝ) + 1) ^ (-δ)) := by
        exact mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA.le hB)
      _ = C * ((N : ℝ) + 1) ^ (-δ) := by
        dsimp [C]
        ring
  rcases le_total n m with hnm | hmn
  · exact hordered hn hm hnm
  · rw [dist_comm]
    exact hordered hm hn hmn

/-- Consequently Proposition VI.2.1 is available without an analytic bridge
hypothesis. -/
theorem abelEstimateStatement : (∀ (a : ℕ → ℂ) (A b : ℝ),
      0 < A → 0 < b →
      (∀ᶠ x : ℝ in atTop,
        ‖coefficientPartialReal a x‖ ≤ A * x ^ b) →
      CoefficientPartialConclusion a b) :=
  partial_abel_estimate abelTailEstimate

end

end Towers.CField.EProduc
