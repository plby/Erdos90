import Towers.NumberTheory.Discriminant.PolynomialExamples
import Towers.NumberTheory.ClassGroup.CubicNumberExample
import Towers.NumberTheory.ClassGroup.NoExtensionQ
import Towers.NumberTheory.Fields.CubicDiscriminantBound
import Towers.NumberTheory.Quadratic.QuadraticUnitExamples
import Mathlib


/-!
# Milne, Algebraic Number Theory, Example 5.14

The unit furnished by the cubic equation `X^3 + 10X + 1 = 0`.
-/

namespace Towers.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace Polynomial
open scoped NumberField

noncomputable section

/-- The cubic polynomial in Milne's Example 5.14. -/
def cubicTenPolynomial (R : Type*) [Ring R] : R[X] :=
  X ^ 3 + 10 * X + 1

/-- The polynomial `X³ + 10X + 1` is irreducible over `ℚ`. -/
theorem cubic_ten_irreducible : Irreducible (cubicTenPolynomial ℚ) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (cubicTenPolynomial ℚ).natDegree = 3 := by
      rw [show cubicTenPolynomial ℚ = X ^ 3 + (10 * X + 1) by
        simp only [cubicTenPolynomial]
        ring]
      exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
        compute_degree
        norm_num)).natDegree_eq
    simp [hnat]
  · intro x hx
    let f : ℤ[X] := cubicTenPolynomial ℤ
    have hf : f.Monic := by
      rw [show f = X ^ 3 + (10 * X + 1) by
        simp only [f, cubicTenPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    have hroot : Polynomial.aeval x f = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      simpa [f, cubicTenPolynomial, IsRoot.def, aeval_def] using hx
    obtain ⟨z, hxz, hz⟩ := exists_integer_of_is_root_of_monic hf hroot
    have hzunit : IsUnit z := by
      rw [isUnit_iff_dvd_one]
      simpa [f, cubicTenPolynomial] using hz
    rcases Int.isUnit_eq_one_or hzunit with rfl | rfl
    · have : x = 1 := by simpa using hxz
      subst x
      norm_num [cubicTenPolynomial, IsRoot.def, eval_add, eval_pow] at hx
    · have : x = -1 := by simpa using hxz
      subst x
      norm_num [cubicTenPolynomial, IsRoot.def, eval_add, eval_pow] at hx

/-- The polynomial discriminant of `X³ + 10X + 1` is `-4027`. -/
theorem ten_polynomial_discr : discr (cubicTenPolynomial ℤ) = -4027 := by
  simpa [cubicTenPolynomial] using
    (discr_cube_b (10 : ℤ) (1 : ℤ))

private theorem ten_companion_matrix :
    3 * (!![0, 0, -1; 1, 0, -10; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) ^ 2 + 10 =
      !![10, -3, 0; 0, -20, -3; 3, 0, -20] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.ofNat_fin_three, pow_two] <;>
    norm_num

private theorem ten_matrix_det :
    Matrix.det (!![10, -3, 0; 0, -20, -3; 3, 0, -20] : Matrix (Fin 3) (Fin 3) ℚ) =
      4027 := by
  simp [Matrix.det_fin_three]
  norm_num

private theorem cubic_ten_dim
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) : B.dim = 3 := by
  rw [← B.natDegree_minpoly, hmin]
  rw [show cubicTenPolynomial ℚ = X ^ 3 + (10 * X + 1) by
    simp only [cubicTenPolynomial]
    ring]
  exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
    compute_degree
    norm_num)).natDegree_eq

private theorem ten_reindexed_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    exists e : Fin B.dim ≃ Fin 3,
      Matrix.reindexAlgEquiv ℚ ℚ e (Algebra.leftMulMatrix B.basis B.gen) =
        !![0, 0, -1; 1, 0, -10; 0, 1, 0] := by
  classical
  have hdim := cubic_ten_dim B hmin
  let e : Fin B.dim ≃ Fin 3 := finCongr hdim
  refine ⟨e, ?_⟩
  rw [Matrix.reindexAlgEquiv_apply, B.leftMulMatrix]
  simp only [PowerBasis.minpolyGen_eq, hmin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, e, cubicTenPolynomial, hdim,
      Polynomial.coeff_one, Polynomial.coeff_X]

private theorem cubic_ten_derivative
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    Algebra.norm ℚ (3 * B.gen ^ 2 + 10) = 4027 := by
  rw [Algebra.norm_eq_matrix_det B.basis]
  obtain ⟨e, hM⟩ := ten_reindexed_gen B hmin
  rw [← Matrix.det_reindexAlgEquiv ℚ ℚ e]
  have hN : Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix B.basis (3 * B.gen ^ 2 + 10)) =
      !![10, -3, 0; 0, -20, -3; 3, 0, -20] := by
    let H : K →ₐ[ℚ] Matrix (Fin 3) (Fin 3) ℚ :=
      (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.comp
        (Algebra.leftMulMatrix B.basis)
    change H (3 * B.gen ^ 2 + 10) = !![10, -3, 0; 0, -20, -3; 3, 0, -20]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    change 3 * Matrix.reindexAlgEquiv ℚ ℚ e
        (Algebra.leftMulMatrix B.basis B.gen) ^ 2 + 10 =
      !![10, -3, 0; 0, -20, -3; 3, 0, -20]
    simpa [hM] using ten_companion_matrix
  rw [hN, ten_matrix_det]

/-- **Milne, Example 5.14.** The norm of the generating root is `-1`. -/
theorem ten_basis_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    Algebra.norm ℚ B.gen = -1 := by
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hmin,
    cubic_ten_dim B hmin]
  norm_num [cubicTenPolynomial, Polynomial.coeff_X, Polynomial.coeff_one]

/-- The rational power basis `(1, α, α²)` has discriminant `-4027`. -/
theorem ten_basis_discr
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    Algebra.discr ℚ B.basis = -4027 := by
  have hdim := cubic_ten_dim B hmin
  rw [Algebra.discr_powerBasis_eq_norm, B.finrank, hdim]
  norm_num
  rw [hmin]
  have hderiv : (cubicTenPolynomial ℚ).derivative = 3 * X ^ 2 + 10 := by
    simp only [cubicTenPolynomial, derivative_add, derivative_pow, Nat.cast_ofNat,
      Nat.add_one_sub_one, derivative_X, mul_one, derivative_mul, derivative_ofNat,
      zero_mul, zero_add, derivative_one, add_zero, add_left_inj, mul_eq_mul_right_iff,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_ne_zero, or_false]
    rw [Polynomial.C_ofNat]
  rw [hderiv]
  simp only [map_add, map_mul, map_pow, aeval_X, map_ofNat]
  linarith [cubic_ten_derivative B hmin]

/-- **Milne, Example 5.14.** The cubic field generated by a root of
`X³ + 10X + 1` has discriminant `-4027`. -/
theorem cubic_ten_discr
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    NumberField.discr K = -4027 := by
  have hpower : Algebra.discr ℚ B.basis = (-4027 : ℚ) :=
    ten_basis_discr B hmin
  have hgenIntegral : IsIntegral ℤ B.gen := by
    refine ⟨cubicTenPolynomial ℤ, ?_, ?_⟩
    · rw [show cubicTenPolynomial ℤ = X ^ 3 + (10 * X + 1) by
        simp only [cubicTenPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    · change Polynomial.aeval B.gen (cubicTenPolynomial ℤ) = 0
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      rw [show (cubicTenPolynomial ℤ).map (algebraMap ℤ ℚ) =
          cubicTenPolynomial ℚ by simp [cubicTenPolynomial]]
      rw [← hmin]
      exact minpoly.aeval ℚ B.gen
  have hIntegral : ∀ i, IsIntegral ℤ (B.basis i) := by
    intro i
    simpa only [PowerBasis.coe_basis] using hgenIntegral.pow i
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K B.basis hIntegral
  have hdZ : (-4027 : ℤ) = d ^ 2 * NumberField.discr K := by
    have hd' := hd
    rw [hpower] at hd'
    exact_mod_cast hd'
  have hdvd : d ^ 2 ∣ (4027 : ℤ) := by
    refine ⟨-NumberField.discr K, ?_⟩
    nlinarith [hdZ]
  have hsqfree : Squarefree (4027 : ℤ) :=
    (by norm_num : Prime (4027 : ℤ)).squarefree
  have hdunit : IsUnit d := hsqfree d (by simpa [pow_two] using hdvd)
  rcases Int.isUnit_eq_one_or hdunit with rfl | rfl
  · simpa using hdZ.symm
  · simpa using hdZ.symm

/-- **Milne, Example 5.14.** The cubic field has one real place and one pair of
complex places. -/
theorem cubicTen_signature
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    nrRealPlaces K = 1 ∧ nrComplexPlaces K = 1 := by
  have hdegree : finrank ℚ K = 3 := by
    rw [B.finrank, cubic_ten_dim B hmin]
  have hdiscr : NumberField.discr K < 0 := by
    rw [cubic_ten_discr B hmin]
    norm_num
  have hc : nrComplexPlaces K = 1 :=
    discr_nr_complex K hdegree hdiscr
  constructor
  · have hcard := card_add_two_mul_card_eq_rank K
    rw [hc, hdegree] at hcard
    omega
  · exact hc

/-- **Milne, Example 5.14.** The discriminant estimate from Lemma 5.13 forces a
fundamental unit for this field to be greater than `10`. -/
theorem ten_epsilon_discriminant {epsilon : ℝ}
    (hepsilon : 1 < epsilon)
    (hbound : (4027 : ℝ) < 4 * epsilon ^ 3 + 24) :
    10 < epsilon := by
  by_contra h
  have hepsilonNonneg : 0 ≤ epsilon := by linarith
  have hepsilonLe : epsilon ≤ 10 := le_of_not_gt h
  have hcubed : epsilon ^ 3 ≤ (10 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hepsilonNonneg hepsilonLe 3
  norm_num at hcubed
  nlinarith

/-- The real polynomial `x ↦ x³ + 10x + 1` is strictly increasing. -/
theorem cubic_ten_mono :
    StrictMono (fun x : ℝ => x ^ 3 + 10 * x + 1) := by
  intro x y hxy
  have hquad : 0 < y ^ 2 + y * x + x ^ 2 + 10 := by
    nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]
  have hfactor :
      (y ^ 3 + 10 * y + 1) - (x ^ 3 + 10 * x + 1) =
        (y - x) * (y ^ 2 + y * x + x ^ 2 + 10) := by
    ring
  nlinarith

/-- **Milne, Example 5.14.** The real root of `X³ + 10X + 1` lies between
`-0.1` and `-0.099`, a rational version of the decimal estimate in the text. -/
theorem ten_real_bounds (x : ℝ) (hx : x ^ 3 + 10 * x + 1 = 0) :
    -(1 / 10 : ℝ) < x ∧ x < -(99 / 1000 : ℝ) := by
  constructor
  · apply (cubic_ten_mono.lt_iff_lt).mp
    rw [hx]
    norm_num
  · apply (cubic_ten_mono.lt_iff_lt).mp
    rw [hx]
    norm_num

/-- **Milne, Example 5.14.** For the real root `α`, the positive unit candidate
`-α⁻¹` lies strictly between `10` and `11`. -/
theorem cubic_ten_bounds (x : ℝ)
    (hx : x ^ 3 + 10 * x + 1 = 0) : 10 < -x⁻¹ ∧ -x⁻¹ < 11 := by
  obtain ⟨hlo, hhi⟩ := ten_real_bounds x hx
  have hxneg : x < 0 := by linarith
  have hnegpos : 0 < -x := neg_pos.mpr hxneg
  constructor
  · rw [← inv_neg]
    rw [← one_mul (-x)⁻¹, lt_mul_inv_iff₀ hnegpos]
    nlinarith
  · rw [← inv_neg]
    rw [← one_mul (-x)⁻¹, mul_inv_lt_iff₀ hnegpos]
    nlinarith

/-- If a number between `10` and `11` is an integral power of a base greater
than `10`, then it is the first power. This is the final numerical deduction in
Milne's Example 5.14 once the unit-group structure is known. -/
theorem zpow_ten_eleven {epsilon beta : ℝ} {m : ℤ}
    (hepsilon : 10 < epsilon) (hbetaLower : 10 < beta) (hbetaUpper : beta < 11)
    (hpow : beta = epsilon ^ m) : m = 1 := by
  have hepsilonOne : 1 ≤ epsilon := by linarith
  have hmpos : 0 < m := by
    by_contra h
    have hm : m ≤ 0 := le_of_not_gt h
    have hle : epsilon ^ m ≤ 1 := zpow_le_one_of_nonpos₀ hepsilonOne hm
    rw [← hpow] at hle
    linarith
  have hmlt : m < 2 := by
    by_contra h
    have hm : (2 : ℤ) ≤ m := le_of_not_gt h
    have hle : epsilon ^ (2 : ℤ) ≤ epsilon ^ m :=
      zpow_le_zpow_right₀ hepsilonOne hm
    rw [← hpow] at hle
    norm_num [zpow_ofNat] at hle
    nlinarith
  omega

/-- **Milne, Example 5.14.** A root of `X^3 + 10X + 1` is a unit.  Its inverse is
explicitly `-x^2 - 10`. -/
theorem cubic_ten_root {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 3 + 10 * x + 1 = 0) : IsUnit x := by
  refine ⟨⟨x, -x ^ 2 - 10, ?_, ?_⟩, rfl⟩
  · linear_combination -hx
  · linear_combination -hx

/-- The power-basis generator satisfies its displayed cubic equation. -/
theorem ten_gen_root
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    B.gen ^ 3 + 10 * B.gen + 1 = 0 := by
  have hroot := minpoly.aeval ℚ B.gen
  rw [hmin] at hroot
  simpa [cubicTenPolynomial, map_ofNat] using hroot

/-- **Milne, Example 5.14.** The generating root is represented by a unit of
the ring of integers. -/
theorem cubic_ten_unit
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    ∃ alpha : (𝓞 K)ˣ, (alpha : K) = B.gen := by
  have hIntegral : IsIntegral ℤ B.gen := by
    refine ⟨cubicTenPolynomial ℤ, ?_, ?_⟩
    · rw [show cubicTenPolynomial ℤ = X ^ 3 + (10 * X + 1) by
        simp only [cubicTenPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    · change Polynomial.aeval B.gen (cubicTenPolynomial ℤ) = 0
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      simpa [cubicTenPolynomial, map_ofNat] using
        ten_gen_root B hmin
  let alphaO : 𝓞 K := ⟨B.gen, hIntegral⟩
  have hrootO : alphaO ^ 3 + 10 * alphaO + 1 = 0 := by
    apply Subtype.ext
    exact ten_gen_root B hmin
  let alpha : (𝓞 K)ˣ := (cubic_ten_root alphaO hrootO).unit
  refine ⟨alpha, ?_⟩
  simp [alpha, alphaO]

/-- **Milne, Example 5.14 (final numerical step).** If the unit `-α⁻¹` is an
integral power of a real unit `ε > 10`, then that power is the first power and
`-α⁻¹ = ε`. -/
theorem ten_inv_zpow (x epsilon : ℝ) (m : ℤ)
    (hx : x ^ 3 + 10 * x + 1 = 0) (hepsilon : 10 < epsilon)
    (hpow : -x⁻¹ = epsilon ^ m) : m = 1 ∧ -x⁻¹ = epsilon := by
  obtain ⟨hlower, hupper⟩ := cubic_ten_bounds x hx
  have hm := zpow_ten_eleven hepsilon hlower hupper hpow
  subst m
  simpa using hpow

/-- **Milne, Example 5.14.** At the real embedding, `-α⁻¹` is the
positive fundamental unit.  In particular it is greater than `10` and every
unit is, up to sign, an integral power of it. -/
theorem cubic_ten_fundamental
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ)
    (sigma : K →ₐ[ℚ] ℝ) :
    ∃ alpha : (𝓞 K)ˣ, (alpha : K) = B.gen ∧
      let beta : (𝓞 K)ˣ := (-1 : (𝓞 K)ˣ) * alpha⁻¹
      10 < sigma (beta : K) ∧
        ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
          u = beta ^ m ∨ u = (-1 : (𝓞 K)ˣ) * beta ^ m := by
  obtain ⟨alpha, halpha⟩ := cubic_ten_unit B hmin
  have hsignature := cubicTen_signature B hmin
  have hreal : 0 < nrRealPlaces K := by omega
  have hrank : NumberField.Units.rank K = 1 := by
    rw [real_places_complex K,
      hsignature.1, hsignature.2]
  obtain ⟨epsilon, hepsilon, hgen⟩ :=
    oriented_fundamental_real
      K sigma.toRingHom hreal hrank
  let beta : (𝓞 K)ˣ := (-1 : (𝓞 K)ˣ) * alpha⁻¹
  have hrootR : (sigma B.gen) ^ 3 + 10 * sigma B.gen + 1 = 0 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] using
      congrArg sigma (ten_gen_root B hmin)
  have hbetaImage : sigma (beta : K) = -(sigma B.gen)⁻¹ := by
    simp [beta, halpha]
  have hbetaLower :=
    (cubic_ten_bounds (sigma B.gen) hrootR).1
  have hbetaPos : 0 < sigma (beta : K) := by
    rw [hbetaImage]
    linarith
  obtain ⟨m, hbetaPower⟩ := hgen beta
  have hpowerImage : sigma (beta : K) = sigma (epsilon : K) ^ m := by
    rcases hbetaPower with hbetaPower | hbetaPower
    · calc
        sigma (beta : K) = sigma ((epsilon ^ m : (𝓞 K)ˣ) : K) :=
          congrArg (fun u : (𝓞 K)ˣ => sigma (u : K)) hbetaPower
        _ = sigma ((epsilon : K) ^ m) := by
          rw [NumberField.Units.coe_zpow]
        _ = sigma (epsilon : K) ^ m :=
          map_zpow₀ sigma (epsilon : K) m
    · have hnegative : sigma (beta : K) = -(sigma (epsilon : K) ^ m) := by
        calc
          sigma (beta : K) =
              sigma (((-1 : (𝓞 K)ˣ) * epsilon ^ m : (𝓞 K)ˣ) : K) :=
            congrArg (fun u : (𝓞 K)ˣ => sigma (u : K)) hbetaPower
          _ = -sigma ((epsilon : K) ^ m) := by
            rw [NumberField.Units.coe_mul, NumberField.Units.coe_neg_one,
              NumberField.Units.coe_zpow, map_mul, map_neg, map_one]
            simp
          _ = -(sigma (epsilon : K) ^ m) := by
            rw [map_zpow₀ sigma]
      have hpowPos : 0 < sigma (epsilon : K) ^ m :=
        zpow_pos (lt_trans (by norm_num) hepsilon) m
      linarith
  have hepsilonNontorsion :
      epsilon ∉ NumberField.Units.torsion K := by
    intro htorsion
    have hfinite : IsOfFinOrder epsilon :=
      (CommGroup.mem_torsion _ epsilon).mp htorsion
    obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
    have hpowImage : sigma (epsilon : K) ^ n = 1 := by
      calc
        sigma (epsilon : K) ^ n = sigma ((epsilon ^ n : (𝓞 K)ˣ) : K) := by
          rw [NumberField.Units.coe_pow, map_pow]
        _ = sigma ((1 : (𝓞 K)ˣ) : K) :=
          congrArg (fun u : (𝓞 K)ˣ => sigma (u : K)) hpow
        _ = 1 := by simp
    have honeLt : 1 < sigma (epsilon : K) ^ n :=
      one_lt_pow₀ hepsilon hn.ne'
    linarith
  have hdegree : finrank ℚ K = 3 := by
    rw [B.finrank, cubic_ten_dim B hmin]
  have hdiscr : NumberField.discr K < 0 := by
    rw [cubic_ten_discr B hmin]
    norm_num
  have hbound' := cubic_discr_nontorsion
    K hdegree hdiscr epsilon hepsilonNontorsion sigma hepsilon
  have hbound : (4027 : ℝ) < 4 * sigma (epsilon : K) ^ 3 + 24 := by
    rw [cubic_ten_discr B hmin] at hbound'
    norm_num at hbound' ⊢
    exact hbound'
  have hepsilonTen : 10 < sigma (epsilon : K) :=
    ten_epsilon_discriminant hepsilon hbound
  have hrealPower : -(sigma B.gen)⁻¹ = sigma (epsilon : K) ^ m := by
    rw [← hbetaImage]
    exact hpowerImage
  obtain ⟨-, hrealEq⟩ := ten_inv_zpow
    (sigma B.gen) (sigma (epsilon : K)) m hrootR hepsilonTen hrealPower
  have hbetaEpsilon : beta = epsilon := by
    apply NumberField.Units.coe_injective K
    apply sigma.injective
    exact hbetaImage.trans hrealEq
  refine ⟨alpha, halpha, ?_, ?_⟩
  · change 10 < sigma (beta : K)
    rw [hbetaEpsilon]
    exact hepsilonTen
  · change ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
        u = beta ^ m ∨ u = (-1 : (𝓞 K)ˣ) * beta ^ m
    simpa only [hbetaEpsilon] using hgen

/-- **Milne, Example 5.14.** Consequently the full unit group is
`{ ±α^m | m ∈ ℤ }`. -/
theorem cubic_ten_zpow
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ)
    (sigma : K →ₐ[ℚ] ℝ) :
    ∃ alpha : (𝓞 K)ˣ, (alpha : K) = B.gen ∧
      ∀ u : (𝓞 K)ˣ, ∃ m : ℤ,
        u = alpha ^ m ∨ u = (-1 : (𝓞 K)ˣ) * alpha ^ m := by
  obtain ⟨alpha, halpha, -, hgen⟩ :=
    cubic_ten_fundamental B hmin sigma
  refine ⟨alpha, halpha, ?_⟩
  intro u
  obtain ⟨m, hu | hu⟩ := hgen u
  · refine ⟨-m, ?_⟩
    by_cases hm : Even m
    · left
      calc
        u = ((-1 : (𝓞 K)ˣ) * alpha⁻¹) ^ m := hu
        _ = alpha ^ (-m) := by
          rw [mul_zpow, hm.neg_one_zpow, one_mul, inv_zpow']
    · right
      have hminus : (-1 : (𝓞 K)ˣ) ^ m = -1 := by
        rw [neg_one_zpow_eq_ite, if_neg hm]
      calc
        u = ((-1 : (𝓞 K)ˣ) * alpha⁻¹) ^ m := hu
        _ = (-1 : (𝓞 K)ˣ) * alpha ^ (-m) := by
          rw [mul_zpow, hminus, inv_zpow']
  · refine ⟨-m, ?_⟩
    by_cases hm : Even m
    · right
      calc
        u = (-1 : (𝓞 K)ˣ) * (((-1 : (𝓞 K)ˣ) * alpha⁻¹) ^ m) := hu
        _ = (-1 : (𝓞 K)ˣ) * alpha ^ (-m) := by
          rw [mul_zpow, hm.neg_one_zpow, one_mul, inv_zpow']
    · left
      have hminus : (-1 : (𝓞 K)ˣ) ^ m = -1 := by
        rw [neg_one_zpow_eq_ite, if_neg hm]
      calc
        u = (-1 : (𝓞 K)ˣ) * (((-1 : (𝓞 K)ˣ) * alpha⁻¹) ^ m) := hu
        _ = alpha ^ (-m) := by
          rw [mul_zpow, hminus, inv_zpow']
          simp

/-- **Milne, Example 5.14.** A complex root of `X^3 + 10X + 1` has infinite
multiplicative order. -/
theorem cubic_ten_order (x : ℂ)
    (hx : x ^ 3 + 10 * x + 1 = 0) : ¬IsOfFinOrder x := by
  intro hfin
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have hxnorm : ‖x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn.ne'
  have heq : 10 * x = -(x ^ 3 + 1) := by
    linear_combination hx
  have hle : ‖x ^ 3 + 1‖ ≤ 2 := by
    calc
      ‖x ^ 3 + 1‖ ≤ ‖x ^ 3‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hxnorm]; norm_num
  have hten : ‖10 * x‖ = 10 := by
    rw [norm_mul, hxnorm]
    norm_num
  have : (10 : ℝ) ≤ 2 := by
    rw [← hten, heq, norm_neg]
    exact hle
  norm_num at this

/-- **Milne, Example 5.14.** The generating root has infinite multiplicative order in its
cubic number field. -/
theorem cubic_ten_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicTenPolynomial ℚ) :
    ¬IsOfFinOrder B.gen := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty (K →+* ℂ))
  have hrootK : B.gen ^ 3 + 10 * B.gen + 1 = 0 := by
    have hroot := minpoly.aeval ℚ B.gen
    rw [hmin] at hroot
    simpa [cubicTenPolynomial, map_ofNat] using hroot
  have hrootC : (φ B.gen) ^ 3 + 10 * φ B.gen + 1 = 0 := by
    simpa only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] using
      congrArg φ hrootK
  intro hfin
  exact cubic_ten_order (φ B.gen) hrootC
    (φ.toMonoidHom.isOfFinOrder hfin)

end

end Towers.NumberTheory.Milne
