import Submission.NumberTheory.Discriminant.DiscriminantBasisCriterion
import Submission.NumberTheory.Discriminant.PolynomialExamples
import Submission.NumberTheory.ClassGroup.MinkowskiClassBound
import Submission.NumberTheory.ClassGroup.NoExtensionQ
import Mathlib.NumberTheory.NumberField.ClassNumber


/-!
# Milne, Algebraic Number Theory, Example 4.8

The noncomputational part of the example for `X^5 - X + 1`: its polynomial discriminant is
`19 * 151`, its root generates the ring of integers, its Minkowski bound is less than four,
and the absence of residue fields of cardinality two or three forces class number one.
-/

namespace Submission.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace Polynomial
open scoped NumberField Real

noncomputable section

/-- The polynomial in Example 4.8. -/
def quinticNumberPolynomial (R : Type*) [Ring R] : R[X] :=
  X ^ 5 - X + 1

private theorem quintic_number_monic (R : Type*) [CommRing R] :
    (quinticNumberPolynomial R).Monic := by
  rw [show quinticNumberPolynomial R = X ^ 5 + (-X + 1) by
    simp only [quinticNumberPolynomial]
    ring]
  apply monic_X_pow_add
  compute_degree
  norm_num

/-- `X^5 - X + 1` is irreducible over `ℚ`. -/
theorem quintic_number_irreducible :
    Irreducible (quinticNumberPolynomial ℚ) := by
  have h := irreducible_x_five.map
    (Polynomial.algEquivAevalNegX (R := ℚ))
  have hneg : Irreducible (-(quinticNumberPolynomial ℚ)) := by
    convert h using 1 ;
      simp [quinticNumberPolynomial, Polynomial.algEquivAevalNegX_apply] ; ring
  have hunit : IsUnit (-1 : ℚ[X]) := isUnit_neg_one
  exact (irreducible_isUnit_mul hunit).mp (by simpa using hneg)

/-- `X^5 - X + 1` is irreducible over `ℤ`. -/
theorem quintic_irreducible_int :
    Irreducible (quinticNumberPolynomial ℤ) := by
  have hprimitive : (quinticNumberPolynomial ℤ).IsPrimitive :=
    (quintic_number_monic ℤ).isPrimitive
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprimitive).mpr
  simpa [quinticNumberPolynomial] using quintic_number_irreducible

/-- The polynomial discriminant is `2869 = 19 * 151`. -/
theorem quintic_class_discr :
    discr (quinticNumberPolynomial ℚ) = 19 * 151 := by
  rw [show quinticNumberPolynomial ℚ = X ^ 5 + C (-1 : ℚ) * X + C 1 by
    simp [quinticNumberPolynomial]
    ring]
  rw [discr_x_b]
  norm_num

private theorem Polynomial_natDegree (R : Type*) [CommRing R] [Nontrivial R] :
    (quinticNumberPolynomial R).natDegree = 5 := by
  rw [show quinticNumberPolynomial R = X ^ 5 + (-X + 1) by
    simp only [quinticNumberPolynomial]
    ring]
  exact ((isMonicOfDegree_X_pow R 5).add_right (by
    compute_degree
    norm_num)).natDegree_eq

private theorem quintic_basis_dim
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) : B.dim = 5 := by
  rw [← B.natDegree_minpoly, hmin, Polynomial_natDegree]

private def CompanionMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, 0, 0, 0, -1;
     1, 0, 0, 0,  1;
     0, 1, 0, 0,  0;
     0, 0, 1, 0,  0;
     0, 0, 0, 1,  0]

private theorem quintic_reindexed_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    ∃ e : Fin B.dim ≃ Fin 5,
      Matrix.reindexAlgEquiv ℚ ℚ e (Algebra.leftMulMatrix B.basis B.gen) =
        CompanionMatrix := by
  classical
  have hdim := quintic_basis_dim B hmin
  let e : Fin B.dim ≃ Fin 5 := finCongr hdim
  refine ⟨e, ?_⟩
  rw [Matrix.reindexAlgEquiv_apply, B.leftMulMatrix]
  simp only [PowerBasis.minpolyGen_eq, hmin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, e, CompanionMatrix,
      quinticNumberPolynomial, hdim, Polynomial.coeff_one, Polynomial.coeff_X]

private def DerivativeMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  !![-1, -5, 0,  0,  0;
      0,   4, -5, 0,  0;
      0,   0, 4, -5,  0;
      0,   0, 0,  4, -5;
      5,   0, 0,  0,  4]

private theorem derivative_matrix :
    5 * CompanionMatrix ^ 4 - 1 = DerivativeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CompanionMatrix, DerivativeMatrix, pow_succ, Matrix.mul_apply,
      Matrix.ofNat_apply] <;>
    norm_num

private theorem quintic_matrix_det :
    Matrix.det DerivativeMatrix = 2869 := by
  simp [DerivativeMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove]
  norm_num

private theorem quintic_derivative_norm
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    Algebra.norm ℚ (5 * B.gen ^ 4 - 1) = 2869 := by
  rw [Algebra.norm_eq_matrix_det B.basis]
  obtain ⟨e, hM⟩ := quintic_reindexed_gen B hmin
  rw [← Matrix.det_reindexAlgEquiv ℚ ℚ e]
  have hN : Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix B.basis (5 * B.gen ^ 4 - 1)) =
      DerivativeMatrix := by
    let H : K →ₐ[ℚ] Matrix (Fin 5) (Fin 5) ℚ :=
      (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.comp
        (Algebra.leftMulMatrix B.basis)
    change H (5 * B.gen ^ 4 - 1) = DerivativeMatrix
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
    change 5 * Matrix.reindexAlgEquiv ℚ ℚ e
        (Algebra.leftMulMatrix B.basis B.gen) ^ 4 - 1 =
      DerivativeMatrix
    simpa [hM] using derivative_matrix
  rw [hN, quintic_matrix_det]

/-- The discriminant of the rational power basis is `2869`. -/
theorem quintic_basis_discr
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    Algebra.discr ℚ B.basis = 2869 := by
  have hdim := quintic_basis_dim B hmin
  rw [Algebra.discr_powerBasis_eq_norm, B.finrank, hdim]
  norm_num
  rw [hmin]
  have hderiv : (quinticNumberPolynomial ℚ).derivative = 5 * X ^ 4 - 1 := by
    simp only [quinticNumberPolynomial, derivative_add, derivative_sub, derivative_pow,
      Nat.cast_ofNat,
      Nat.add_one_sub_one, derivative_X, mul_one, derivative_one, add_zero, sub_left_inj,
        mul_eq_mul_right_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_ne_zero, or_false]
    rw [Polynomial.C_ofNat]
  rw [hderiv]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  exact quintic_derivative_norm B hmin

/-- The index-squared formula bounds the field discriminant by the polynomial discriminant. -/
theorem number_discr_abs
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    (NumberField.discr K).natAbs ≤ 2869 := by
  have hIntegral : ∀ i, IsIntegral ℤ (B.basis i) := by
    intro i
    rw [PowerBasis.coe_basis, hgen]
    change IsIntegral ℤ ((alpha : K) ^ (i : ℕ))
    exact alpha.isIntegral_coe.pow i
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K B.basis hIntegral
  have hdZ : (2869 : ℤ) = d ^ 2 * NumberField.discr K := by
    have hd' := hd
    rw [quintic_basis_discr B hmin] at hd'
    exact_mod_cast hd'
  have hdvd : NumberField.discr K ∣ (2869 : ℤ) := by
    refine ⟨d ^ 2, ?_⟩
    simpa [mul_comm] using hdZ
  simpa using Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (2869 : ℤ) ≠ 0)

/-- Since `2869 = 19 * 151` is squarefree, the power basis already has index one. -/
theorem quintic_number_discr
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    NumberField.discr K = 2869 := by
  have hIntegral : ∀ i, IsIntegral ℤ (B.basis i) := by
    intro i
    rw [PowerBasis.coe_basis, hgen]
    change IsIntegral ℤ ((alpha : K) ^ (i : ℕ))
    exact alpha.isIntegral_coe.pow i
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K B.basis hIntegral
  have hdZ : (2869 : ℤ) = d ^ 2 * NumberField.discr K := by
    have hd' := hd
    rw [quintic_basis_discr B hmin] at hd'
    exact_mod_cast hd'
  have hsquarefree : Squarefree (2869 : ℤ) := by
    rw [show (2869 : ℤ) = 19 * 151 by norm_num, squarefree_mul_iff]
    have h19 : Prime (19 : ℤ) := by norm_num
    have h151 : Prime (151 : ℤ) := by norm_num
    exact ⟨h19.irreducible.isRelPrime_iff_not_dvd.mpr (by norm_num),
      h19.squarefree, h151.squarefree⟩
  have hdunit : IsUnit d := by
    apply hsquarefree d
    refine ⟨NumberField.discr K, ?_⟩
    simpa [pow_two] using hdZ
  rcases Int.isUnit_eq_one_or hdunit with hd | hd
  · rw [hd] at hdZ
    norm_num at hdZ
    exact hdZ.symm
  · rw [hd] at hdZ
    norm_num at hdZ
    exact hdZ.symm

private theorem quintic_discr_coe
    {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → NumberField.RingOfIntegers K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) =
      Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K)) := by
  change algebraMap ℤ ℚ (Algebra.discr ℤ v) = _
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply]
  simpa only [map_mul] using Algebra.coe_trace_int (v i * v j)

/-- The powers `1, alpha, ..., alpha^4` form an integral basis. -/
theorem quintic_integers_adjoin
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ := by
  classical
  have hdim : B.dim = 5 := quintic_basis_dim B hmin
  let bQ : Basis (Fin 5) ℚ K := B.basis.reindex (finCongr hdim)
  have hbQ (i : Fin 5) : bQ i = B.gen ^ (i : ℕ) := by
    simp [bQ, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  let v : Fin 5 → NumberField.RingOfIntegers K := fun i => alpha ^ (i : ℕ)
  have hvQ : (fun i => ((v i : NumberField.RingOfIntegers K) : K)) = bQ := by
    funext i
    rw [hbQ i]
    simp only [v, map_pow]
    rw [hgen]
  have hvQdiscr : Algebra.discr ℚ
      (fun i => ((v i : NumberField.RingOfIntegers K) : K)) = (2869 : ℚ) := by
    rw [hvQ]
    dsimp [bQ]
    rw [Basis.coe_reindex, Algebra.discr_reindex]
    exact quintic_basis_discr B hmin
  have hvZdiscr : Algebra.discr ℤ v = (2869 : ℤ) := by
    apply Rat.intCast_injective
    rw [quintic_discr_coe]
    exact hvQdiscr
  have hfieldDiscr : NumberField.discr K = (2869 : ℤ) :=
    quintic_number_discr alpha B hgen hmin
  let eInt : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 5 :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]
      simpa [hdim] using B.finrank)
  let bInt : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
    (NumberField.RingOfIntegers.basis K).reindex eInt
  have hbIntDiscr : Algebra.discr ℤ bInt = (2869 : ℤ) := by
    rw [NumberField.discr_eq_discr K bInt]
    exact hfieldDiscr
  have hbIntDiscr_ne : Algebra.discr ℤ bInt ≠ 0 := by
    rw [hbIntDiscr]
    norm_num
  have hspan : Ideal.span ({Algebra.discr ℤ v} : Set ℤ) =
      Ideal.span ({Algebra.discr ℤ bInt} : Set ℤ) := by
    rw [hvZdiscr, hbIntDiscr]
  obtain ⟨bZ, hbZ⟩ :=
    (basis_span_discr bInt v hbIntDiscr_ne).mpr hspan
  let PB : PowerBasis ℤ (NumberField.RingOfIntegers K) :=
    { gen := alpha
      dim := 5
      basis := bZ
      basis_eq_pow := fun i => by rw [congr_fun hbZ i] }
  simpa [PB] using PB.adjoin_gen_eq_top

private theorem minkowski_floor_three
    {K : Type*} [Field K] [NumberField K]
    (hdegree : finrank ℚ K = 5)
    (hdiscr : (NumberField.discr K).natAbs ≤ 2869) :
    ⌊(4 / Real.pi) ^ nrComplexPlaces K *
      (Nat.factorial (finrank ℚ K) /
        (finrank ℚ K) ^ (finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)⌋₊ ≤ 3 := by
  let M : ℝ := (4 / Real.pi) ^ nrComplexPlaces K *
    (Nat.factorial (finrank ℚ K) /
      (finrank ℚ K) ^ (finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)
  have hcomplex : nrComplexPlaces K ≤ 2 := by
    have hcard := card_add_two_mul_card_eq_rank K
    omega
  have habs : (|(NumberField.discr K : ℝ)| : ℝ) ≤ 2869 := by
    calc
      |(NumberField.discr K : ℝ)| = ((|(NumberField.discr K)| : ℤ) : ℝ) :=
        Int.cast_abs.symm
      _ = ((NumberField.discr K).natAbs : ℝ) := by
        rw [Int.abs_eq_natAbs, Int.cast_natCast]
      _ ≤ 2869 := by exact_mod_cast hdiscr
  have hsqrt_sq : (Real.sqrt |(NumberField.discr K : ℝ)|) ^ 2 =
      |(NumberField.discr K : ℝ)| := by
    rw [Real.sq_sqrt (abs_nonneg _)]
  have hsqrt_nonneg : 0 ≤ Real.sqrt |(NumberField.discr K : ℝ)| := Real.sqrt_nonneg _
  have hsqrt_lt : Real.sqrt |(NumberField.discr K : ℝ)| < 54 := by
    nlinarith
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hM : M < 4 := by
    dsimp [M]
    rw [hdegree]
    norm_num [Nat.factorial]
    interval_cases hC : nrComplexPlaces K
    · norm_num
      nlinarith
    · norm_num
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpi_pos]
      nlinarith
    · rw [div_pow, div_mul_eq_mul_div, div_lt_iff₀ (sq_pos_of_pos hpi_pos)]
      nlinarith [sq_nonneg (Real.pi - 3)]
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hfloor : ⌊M⌋₊ < 4 := (Nat.floor_lt hMnonneg).mpr hM
  change ⌊M⌋₊ ≤ 3
  omega

private theorem root_relation
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    alpha ^ 5 - alpha + 1 = 0 := by
  have hrootK := minpoly.aeval ℚ B.gen
  rw [hmin] at hrootK
  have hrootK' : (alpha : K) ^ 5 - (alpha : K) + 1 = 0 := by
    simpa [quinticNumberPolynomial, hgen, map_ofNat] using hrootK
  apply NumberField.RingOfIntegers.ext
  simpa using hrootK'

private theorem abs_or_three
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (hroot : alpha ^ 5 - alpha + 1 = 0)
    (P : Ideal (NumberField.RingOfIntegers K))
    (p : ℕ) (hp : p = 2 ∨ p = 3) :
    Ideal.absNorm P ≠ p := by
  intro hnorm
  have hpPrime : p.Prime := by
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have hfinite : Finite (NumberField.RingOfIntegers K ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (by omega)
  letI : Fintype (NumberField.RingOfIntegers K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hnorm
  let e : ZMod p ≃+* (NumberField.RingOfIntegers K ⧸ P) :=
    ZMod.ringEquivOfPrime _ hpPrime hcard
  let q : NumberField.RingOfIntegers K ⧸ P := Ideal.Quotient.mk P alpha
  have hq : q ^ 5 - q + 1 = 0 := by
    have := congrArg (Ideal.Quotient.mk P) hroot
    simpa only [q, map_add, map_sub, map_pow, map_one, map_zero] using this
  let z : ZMod p := e.symm q
  have hz : z ^ 5 - z + 1 = 0 := by
    have := congrArg e.symm hq
    simpa only [z, map_add, map_sub, map_pow, map_one, map_zero] using this
  rcases hp with rfl | rfl
  · exact (show ∀ x : ZMod 2, x ^ 5 - x + 1 ≠ 0 by decide) z hz
  · exact (show ∀ x : ZMod 3, x ^ 5 - x + 1 ≠ 0 by decide) z hz

/-- The ring of integers in Example 4.8 is a principal ideal ring. -/
theorem quintic_principal_ring
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  have hdegree : finrank ℚ K = 5 :=
    B.finrank.trans (quintic_basis_dim B hmin)
  have hdiscr : (NumberField.discr K).natAbs ≤ 2869 :=
    number_discr_abs alpha B hgen hmin
  have hbound := minkowski_floor_three hdegree hdiscr
  have hroot := root_relation alpha B hgen hmin
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
  intro I hI hnorm
  have hnormLeFloor : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤
      ⌊(4 / Real.pi) ^ nrComplexPlaces K *
        (Nat.factorial (finrank ℚ K) /
          (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |NumberField.discr K|)⌋₊ := by
    exact Nat.le_floor hnorm
  have hnormLe : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ 3 :=
    hnormLeFloor.trans hbound
  have hnormNeZero : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≠ 0 :=
    Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  have hnormNeOne : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≠ 1 := by
    intro hone
    exact hI.ne_top' (Ideal.absNorm_eq_one_iff.mp hone)
  have hcases : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) = 2 ∨
      Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) = 3 := by
    omega
  exact False.elim <| (abs_or_three alpha hroot
    (I : Ideal (NumberField.RingOfIntegers K))
    (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)))
    (by omega)) rfl

/-- The number field in Example 4.8 has class number one. -/
theorem class_number_one
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    NumberField.classNumber K = 1 := by
  rw [NumberField.classNumber_eq_one_iff]
  exact quintic_principal_ring alpha B hgen hmin

/-- Milne, Example 4.8: `O_K = ℤ[alpha]` and the class number is one. -/
theorem quinticClassNumber
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = quinticNumberPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ ∧
      NumberField.classNumber K = 1 := by
  exact ⟨quintic_integers_adjoin alpha B hgen hmin,
    class_number_one alpha B hgen hmin⟩

end

end Submission.NumberTheory.Milne
