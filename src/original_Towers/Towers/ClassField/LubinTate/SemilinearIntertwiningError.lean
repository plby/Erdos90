import Towers.ClassField.FormalGroups.CompositionalInverse
import Towers.ClassField.FormalGroups.SubstitutionCongruence

/-!
# Class Field Theory, Chapter I, Proposition 3.10

The construction of the semilinear isomorphism in Proposition 3.10 requires
the valuation ring of the completed maximal unramified extension, which is not
yet packaged.  This file formalizes the recursive algebra in Step 1 of Milne's
proof.  It also records the formal power-series cancellation used at the end
of the proof of Theorem 3.9: from `σθ = θ ∘ u` and `u ∘ v = X`, one gets
`(σθ) ∘ v = θ`.
-/

namespace Towers.CField.LTate

open PowerSeries

noncomputable section

/-- The error in the semilinear functional equation `σθ = θ ∘ u`. -/
def semilinearIntertwiningError
    {R : Type*} [CommRing R] (sigma : R →+* R)
    (u theta : PowerSeries R) : PowerSeries R :=
  PowerSeries.map sigma theta - PowerSeries.subst u theta

private theorem coeff_self_constant
    {R : Type*} [CommRing R] {u : PowerSeries R}
    (hu0 : constantCoeff u = 0) (n : ℕ) :
    coeff n (u ^ n) = coeff 1 u ^ n := by
  let v : PowerSeries R := PowerSeries.mk fun k ↦ coeff (k + 1) u
  have hu : u = X * v := by
    calc
      u = X * v + PowerSeries.C (constantCoeff u) :=
        PowerSeries.eq_X_mul_shift_add_const u
      _ = X * v := by rw [hu0]; simp
  rw [show u ^ n = (X * v) ^ n by rw [hu], mul_pow]
  have hcoeff := PowerSeries.coeff_X_pow_mul (v ^ n) n 0
  simp only [zero_add] at hcoeff
  rw [hcoeff, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  simp [v]

private theorem coeff_pow_self
    {R : Type*} [CommRing R] {u : PowerSeries R}
    (hu0 : constantCoeff u = 0) {k n : ℕ} (hk : k < n) :
    coeff k (u ^ n) = 0 := by
  let v : PowerSeries R := PowerSeries.mk fun d ↦ coeff (d + 1) u
  have hu : u = X * v := by
    calc
      u = X * v + PowerSeries.C (constantCoeff u) :=
        PowerSeries.eq_X_mul_shift_add_const u
      _ = X * v := by rw [hu0]; simp
  rw [show u ^ n = (X * v) ^ n by rw [hu], mul_pow,
    PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hk]

/-- Adding `bT^n` changes the degree-`n` semilinear error by
`σ(b) - b u'(0)^n`.  This is the coefficient calculation in Step 1 of
Proposition 3.10. -/
theorem semilinear_intertwining_error
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {u : PowerSeries R} (hu0 : constantCoeff u = 0)
    (theta : PowerSeries R) (b : R) (n : ℕ) :
    coeff n
        (semilinearIntertwiningError sigma u
          (theta + PowerSeries.C b * X ^ n)) =
      coeff n (semilinearIntertwiningError sigma u theta) +
        (sigma b - b * coeff 1 u ^ n) := by
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have hcoeffC : coeff n (PowerSeries.C b * u ^ n) =
      b * coeff n (u ^ n) := PowerSeries.coeff_C_mul n (u ^ n) b
  rw [semilinearIntertwiningError, semilinearIntertwiningError]
  rw [map_add, PowerSeries.subst_add hu]
  rw [map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X]
  rw [PowerSeries.subst_mul hu, PowerSeries.subst_pow hu]
  rw [PowerSeries.subst_C, PowerSeries.subst_X hu]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_self, mul_one]
  rw [show (MvPowerSeries.C b : PowerSeries R) = PowerSeries.C b by rfl]
  rw [hcoeffC]
  rw [coeff_self_constant hu0]
  ring

/-- A correction in degree `n` leaves all lower coefficients of the
semilinear error unchanged. -/
theorem semilinear_intertwining_c
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {u : PowerSeries R} (hu0 : constantCoeff u = 0)
    (theta : PowerSeries R) (b : R) {k n : ℕ} (hk : k < n) :
    coeff k
        (semilinearIntertwiningError sigma u
          (theta + PowerSeries.C b * X ^ n)) =
      coeff k (semilinearIntertwiningError sigma u theta) := by
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have hcoeffC : coeff k (PowerSeries.C b * u ^ n) =
      b * coeff k (u ^ n) := PowerSeries.coeff_C_mul k (u ^ n) b
  rw [semilinearIntertwiningError, semilinearIntertwiningError]
  rw [map_add, PowerSeries.subst_add hu]
  rw [map_mul, PowerSeries.map_C, map_pow, PowerSeries.map_X]
  rw [PowerSeries.subst_mul hu, PowerSeries.subst_pow hu]
  rw [PowerSeries.subst_C, PowerSeries.subst_X hu]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, if_neg (Nat.ne_of_lt hk), mul_zero]
  rw [show (MvPowerSeries.C b : PowerSeries R) = PowerSeries.C b by rfl]
  rw [hcoeffC]
  rw [coeff_pow_self hu0 hk]
  ring

/-- Twisting by an eigenunit converts surjectivity of `σ - 1` into the
surjectivity needed for the degree-`n` coefficient correction. -/
theorem surjective_twist_sub
    {R : Type*} [CommRing R] (sigma : R →+* R)
    (epsilon w : Rˣ)
    (hepsilon : sigma (epsilon : R) = ((epsilon * w : Rˣ) : R))
    (hsurj : Function.Surjective fun a : R ↦ sigma a - a)
    (n : ℕ) :
    Function.Surjective fun b : R ↦ sigma b - b * (w : R) ^ n := by
  intro t
  obtain ⟨a, ha⟩ := hsurj
    (t * ((((epsilon * w) ^ n)⁻¹ : Rˣ) : R))
  change sigma a - a = t * ((((epsilon * w) ^ n)⁻¹ : Rˣ) : R) at ha
  refine ⟨a * (epsilon : R) ^ n, ?_⟩
  change sigma (a * (epsilon : R) ^ n) -
      (a * (epsilon : R) ^ n) * (w : R) ^ n = t
  rw [map_mul, map_pow, hepsilon]
  change sigma a * ((epsilon : R) * (w : R)) ^ n -
      a * (epsilon : R) ^ n * (w : R) ^ n = t
  rw [mul_pow]
  calc
    sigma a * ((epsilon : R) ^ n * (w : R) ^ n) -
          a * (epsilon : R) ^ n * (w : R) ^ n =
        (sigma a - a) * ((epsilon : R) ^ n * (w : R) ^ n) := by ring
    _ = t * ((((epsilon * w) ^ n)⁻¹ : Rˣ) : R) *
        ((epsilon : R) ^ n * (w : R) ^ n) := by rw [ha]
    _ = t := by
      rw [show (epsilon : R) ^ n * (w : R) ^ n =
        (((epsilon * w) ^ n : Rˣ) : R) by
          norm_cast
          exact (mul_pow epsilon w n).symm]
      have hunit : ((((epsilon * w) ^ n)⁻¹ : Rˣ) : R) *
          (((epsilon * w) ^ n : Rˣ) : R) = 1 := by
        exact ((epsilon * w) ^ n).inv_mul
      rw [mul_assoc, hunit, mul_one]

/-- Milne's recursive Step 1: assuming `σ - 1` is surjective and an
eigenunit `ε` has been chosen, one can add a degree-`n` monomial which kills
the degree-`n` semilinear error without changing any lower coefficient. -/
theorem semilinear_intertwining_correction
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {u : PowerSeries R} (hu0 : constantCoeff u = 0)
    (epsilon w : Rˣ)
    (hepsilon : sigma (epsilon : R) = ((epsilon * w : Rˣ) : R))
    (hu1 : coeff 1 u = (w : R))
    (hsurj : Function.Surjective fun a : R ↦ sigma a - a)
    (theta : PowerSeries R) (n : ℕ) :
    ∃ b : R,
      coeff n
          (semilinearIntertwiningError sigma u
            (theta + PowerSeries.C b * X ^ n)) = 0 ∧
      ∀ k < n,
        coeff k
            (semilinearIntertwiningError sigma u
              (theta + PowerSeries.C b * X ^ n)) =
          coeff k (semilinearIntertwiningError sigma u theta) := by
  obtain ⟨b, hb⟩ :=
    surjective_twist_sub
      sigma epsilon w hepsilon hsurj n
      (-coeff n (semilinearIntertwiningError sigma u theta))
  refine ⟨b, ?_, fun k hk ↦
    semilinear_intertwining_c
      sigma hu0 theta b hk⟩
  rw [semilinear_intertwining_error sigma hu0,
    hu1]
  change sigma b - b * (w : R) ^ n = _ at hb
  rw [hb]
  abel

namespace SIStep

variable {R : Type*} [CommRing R]

private theorem eq_eq_le
    {U f g : PowerSeries R} (hU0 : constantCoeff U = 0) {n : ℕ}
    (hfg : ∀ d ≤ n, coeff d f = coeff d g) :
    coeff n (subst U f) = coeff n (subst U g) := by
  let hU : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  rw [coeff_subst' hU, coeff_subst' hU]
  apply finsum_congr
  intro d
  by_cases hdn : d ≤ n
  · rw [hfg d hdn]
  · have hnd : n < d := Nat.lt_of_not_ge hdn
    have hord : (d : ℕ∞) ≤ (U ^ d).order :=
      PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hU0
    have hz : coeff n (U ^ d) = 0 := by
      apply PowerSeries.coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hnd) hord
    simp [hz]

variable (sigma : R →+* R) (epsilon u : Rˣ) (U : PowerSeries R)
  (hsurj : Function.Surjective fun a : R ↦ sigma a - a)

private noncomputable def correction (p : PowerSeries R) (n : ℕ) : R :=
  let c := coeff n (subst U p - PowerSeries.map sigma p)
  let w : Rˣ := epsilon * u
  let a := Classical.choose
    (hsurj (c * (((w ^ n : Rˣ)⁻¹ : Rˣ) : R)))
  a * ((epsilon ^ n : Rˣ) : R)

private theorem correction_spec
    (hsigma_epsilon : sigma (epsilon : R) = (epsilon : R) * (u : R))
    (p : PowerSeries R) (n : ℕ) :
    sigma (correction sigma epsilon u U hsurj p n) -
        correction sigma epsilon u U hsurj p n * (u : R) ^ n =
      coeff n (subst U p - PowerSeries.map sigma p) := by
  let c := coeff n (subst U p - PowerSeries.map sigma p)
  let w : Rˣ := epsilon * u
  let a := Classical.choose
    (hsurj (c * (((w ^ n : Rˣ)⁻¹ : Rˣ) : R)))
  have ha : sigma a - a = c * (((w ^ n : Rˣ)⁻¹ : Rˣ) : R) :=
    Classical.choose_spec
      (hsurj (c * (((w ^ n : Rˣ)⁻¹ : Rˣ) : R)))
  have heps : sigma ((epsilon ^ n : Rˣ) : R) = ((w ^ n : Rˣ) : R) := by
    change sigma ((epsilon : R) ^ n) = (w : R) ^ n
    rw [map_pow, hsigma_epsilon]
    rfl
  change sigma (a * ((epsilon ^ n : Rˣ) : R)) -
      a * ((epsilon ^ n : Rˣ) : R) * (u : R) ^ n = _
  rw [map_mul, heps]
  have hprod : ((epsilon ^ n : Rˣ) : R) * (u : R) ^ n =
      ((w ^ n : Rˣ) : R) := by
    simp [w, mul_pow]
  rw [mul_assoc, hprod, ← sub_mul, ha]
  rw [mul_assoc]
  have hw : (↑((w ^ n)⁻¹) : R) * (↑(w ^ n) : R) = 1 := by
    have hw' : (w ^ n)⁻¹ * (w ^ n) = 1 := by simp
    exact congrArg (fun z : Rˣ ↦ (z : R)) hw'
  rw [hw, mul_one]

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => monomial 1 epsilon
  | n + 1 =>
      let p := approximation n
      let d := n + 2
      p + monomial d (correction sigma epsilon u U hsurj p d)

private theorem approximation_succ (n : ℕ) :
    approximation sigma epsilon u U hsurj (n + 1) =
      approximation sigma epsilon u U hsurj n +
        monomial (n + 2)
          (correction sigma epsilon u U hsurj
            (approximation sigma epsilon u U hsurj n) (n + 2)) := rfl

private theorem coeff_subst_monomial (hU0 : constantCoeff U = 0)
    (b : R) (n : ℕ) :
    coeff n (subst U (monomial n b)) = b * coeff 1 U ^ n := by
  let hU : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  rw [monomial_eq_C_mul_X_pow, subst_mul hU, subst_C, subst_pow hU,
    subst_X hU]
  change coeff n (PowerSeries.C b * U ^ n) = _
  rw [PowerSeries.coeff_C_mul]
  rw [coeff_self_constant hU0]

private theorem subst_of_lt (hU0 : constantCoeff U = 0)
    (b : R) {k n : ℕ} (hkn : k < n) :
    coeff k (subst U (monomial n b)) = 0 := by
  let hU : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  rw [monomial_eq_C_mul_X_pow, subst_mul hU, subst_C, subst_pow hU,
    subst_X hU]
  change coeff k (PowerSeries.C b * U ^ n) = _
  rw [PowerSeries.coeff_C_mul]
  have hord : (n : ℕ∞) ≤ (U ^ n).order :=
    PowerSeries.le_order_pow_of_constantCoeff_eq_zero n hU0
  have hz : coeff k (U ^ n) = 0 := by
    apply PowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hkn) hord
  rw [hz, mul_zero]

private theorem coeff_map_monomial (b : R) (n : ℕ) :
    coeff n (PowerSeries.map sigma (monomial n b)) = sigma b := by
  simp

private theorem approximation_coeff_stable {m n k : ℕ} (hmn : m ≤ n)
    (hk : k < m + 2) :
    coeff k (approximation sigma epsilon u U hsurj n) =
      coeff k (approximation sigma epsilon u U hsurj m) := by
  induction n with
  | zero =>
      have hm0 : m = 0 := by omega
      subst m
      rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [approximation_succ, map_add, coeff_monomial,
          if_neg (by omega : k ≠ n + 2), add_zero]
        exact ih hmn'
      · have hmn_eq : m = n + 1 := by omega
        subst m
        rfl

private theorem approximation_spec
    (hsigma_epsilon : sigma (epsilon : R) = (epsilon : R) * (u : R))
    (hU0 : constantCoeff U = 0) (hU1 : coeff 1 U = u) :
    ∀ n k, k < n + 2 →
      coeff k (PowerSeries.map sigma
        (approximation sigma epsilon u U hsurj n)) =
      coeff k (subst U (approximation sigma epsilon u U hsurj n)) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · change sigma (coeff 0 (monomial 1 (epsilon : R))) =
            coeff 0 (subst U (monomial 1 (epsilon : R)))
        rw [coeff_monomial, if_neg (by omega), map_zero,
          subst_of_lt U hU0 (epsilon : R) (by omega)]
      · simp only [approximation]
        rw [coeff_map_monomial, coeff_subst_monomial U hU0, hU1,
          hsigma_epsilon]
        simp
  | succ n ih =>
      intro k hk
      let p := approximation sigma epsilon u U hsurj n
      let d := n + 2
      let b := correction sigma epsilon u U hsurj p d
      rw [approximation_succ]
      by_cases hkd : k < d
      · have hstable : coeff k (p + monomial d b) = coeff k p := by
          rw [map_add, coeff_monomial, if_neg (by omega), add_zero]
        rw [PowerSeries.coeff_map, hstable]
        have hsubststable : coeff k (subst U (p + monomial d b)) =
            coeff k (subst U p) := by
          rw [subst_add (HasSubst.of_constantCoeff_zero' hU0), map_add,
            subst_of_lt U hU0 b hkd, add_zero]
        change sigma (coeff k p) = coeff k (subst U (p + monomial d b))
        rw [hsubststable]
        exact ih k hkd
      · have hkeq : k = d := by omega
        subst k
        rw [PowerSeries.coeff_map, map_add, coeff_monomial_same, map_add,
          subst_add (HasSubst.of_constantCoeff_zero' hU0), map_add,
          coeff_subst_monomial U hU0, hU1]
        have hcorr := correction_spec sigma epsilon u U hsurj hsigma_epsilon p d
        rw [map_sub, PowerSeries.coeff_map] at hcorr
        linear_combination hcorr

/-- The coefficientwise stable diagonal of the recursive approximants. -/
private noncomputable def semilinearTheta : PowerSeries R :=
  PowerSeries.mk fun k ↦
    coeff k (approximation sigma epsilon u U hsurj k)

@[simp]
private theorem coeff_semilinearTheta (k : ℕ) :
    coeff k (semilinearTheta sigma epsilon u U hsurj) =
      coeff k (approximation sigma epsilon u U hsurj k) := by
  simp [semilinearTheta]

private theorem semilinear_theta_approximation
    {k n : ℕ} (hk : k < n + 2) :
    coeff k (semilinearTheta sigma epsilon u U hsurj) =
      coeff k (approximation sigma epsilon u U hsurj n) := by
  rw [coeff_semilinearTheta]
  by_cases hkn : k ≤ n
  · exact (approximation_coeff_stable sigma epsilon u U hsurj
      hkn (by omega : k < k + 2)).symm
  · have hk_eq : k = n + 1 := by omega
    subst k
    exact approximation_coeff_stable sigma epsilon u U hsurj
      (Nat.le_succ n) (by omega)

/-- Proposition 3.10, Step 1, abstracted from the arithmetic construction of
the completed unramified valuation ring.  Surjectivity of `sigma - 1` and an
eigenunit produce a series with the exact semilinear functional equation. -/
theorem exists_semilinearTheta
    (hsigma_epsilon : sigma (epsilon : R) = (epsilon : R) * (u : R))
    (hsurj : Function.Surjective fun a : R ↦ sigma a - a)
    (hU0 : constantCoeff U = 0) (hU1 : coeff 1 U = (u : R)) :
    ∃ theta : PowerSeries R,
      constantCoeff theta = 0 ∧
      coeff 1 theta = (epsilon : R) ∧
      PowerSeries.map sigma theta = subst U theta := by
  let theta := semilinearTheta sigma epsilon u U hsurj
  refine ⟨theta, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    rw [semilinear_theta_approximation
      (sigma := sigma) (epsilon := epsilon) (u := u) (U := U)
      (hsurj := hsurj) (n := 0) (by omega)]
    change coeff 0 (monomial 1 (epsilon : R)) = 0
    rw [coeff_monomial]
    simp
  · rw [semilinear_theta_approximation
      (sigma := sigma) (epsilon := epsilon) (u := u) (U := U)
      (hsurj := hsurj) (n := 0) (by omega)]
    simp [approximation]
  · apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_map]
    have htheta : coeff n theta =
        coeff n (approximation sigma epsilon u U hsurj n) :=
      semilinear_theta_approximation
        (sigma := sigma) (epsilon := epsilon) (u := u) (U := U)
        (hsurj := hsurj) (by omega)
    rw [htheta]
    have hsubst : coeff n (subst U theta) =
        coeff n (subst U (approximation sigma epsilon u U hsurj n)) := by
      apply eq_eq_le hU0
      intro d hd
      exact semilinear_theta_approximation
        (sigma := sigma) (epsilon := epsilon) (u := u) (U := U)
        (hsurj := hsurj) (by omega)
    rw [hsubst]
    have hstage := approximation_spec sigma epsilon u U hsurj
      hsigma_epsilon hU0 hU1 n n (by omega)
    simpa only [PowerSeries.coeff_map] using hstage

end SIStep

/-- The formal-series identity behind Milne's calculation
`(σθ) ∘ [u⁻¹]_f = θ`. -/
theorem frobenius_twist_subst
    {R : Type*} [CommRing R]
    (sigma : R →+* R) {theta u v : PowerSeries R}
    (hu0 : constantCoeff u = 0)
    (hv0 : constantCoeff v = 0)
    (hsigma : PowerSeries.map sigma theta = PowerSeries.subst u theta)
    (huv : PowerSeries.subst v u = X) :
    PowerSeries.subst v (PowerSeries.map sigma theta) = theta := by
  rw [hsigma]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hu0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)]
  rw [huv]
  exact (PowerSeries.map_algebraMap_eq_subst_X
    (R := R) (S := R) theta).symm

end

end Towers.CField.LTate
