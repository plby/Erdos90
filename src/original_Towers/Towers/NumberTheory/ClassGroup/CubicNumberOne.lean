import Towers.NumberTheory.Discriminant.DiscriminantBasisCriterion
import Towers.NumberTheory.Discriminant.PolynomialExamples
import Towers.NumberTheory.Discriminant.Stickelberger
import Towers.NumberTheory.ClassGroup.CubicNumberExample
import Towers.NumberTheory.ClassGroup.NoExtensionQ
import Mathlib.NumberTheory.NumberField.ClassNumber


/-!
# Milne, Chapter 4, Exercise 6

For a root `alpha` of `X^3 - X + 2`, the cubic field `ℚ(alpha)` has ring of integers
`ℤ[alpha]` and class number one.
-/

namespace Towers.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace Polynomial
open scoped NumberField Real

noncomputable section

/-- The cubic polynomial in Exercise 4-6. -/
def cubicNumberPolynomial (R : Type*) [Ring R] : R[X] :=
  X ^ 3 - X + 2

/-- The polynomial in Exercise 4-6 is irreducible over `ℚ`. -/
theorem cubic_number_irreducible :
    Irreducible (cubicNumberPolynomial ℚ) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hnat : (cubicNumberPolynomial ℚ).natDegree = 3 := by
      rw [show cubicNumberPolynomial ℚ = X ^ 3 + (-X + 2) by
        simp only [cubicNumberPolynomial]
        ring]
      exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
        compute_degree
        norm_num)).natDegree_eq
    simp [hnat]
  · intro x hx
    let f : ℤ[X] := cubicNumberPolynomial ℤ
    have hf : f.Monic := by
      rw [show f = X ^ 3 + (-X + 2) by
        simp only [f, cubicNumberPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    have hroot : Polynomial.aeval x f = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      simpa [f, cubicNumberPolynomial, IsRoot.def, aeval_def] using hx
    obtain ⟨z, hxz, hz⟩ := exists_integer_of_is_root_of_monic hf hroot
    have hzdiv : z ∣ 2 := by
      simpa [f, cubicNumberPolynomial] using hz
    have hzabs : z.natAbs = 1 ∨ z.natAbs = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp (Int.dvd_natCast.mp hzdiv)
    rcases hzabs with hz1 | hz2
    · have hzsq : z ^ 2 = (1 : ℤ) ^ 2 := by
        exact Int.natAbs_eq_iff_sq_eq.mp (by simpa using hz1)
      have hz' : z = 1 ∨ z = -1 := sq_eq_sq_iff_eq_or_eq_neg.mp hzsq
      rcases hz' with rfl | rfl
      · have : x = 1 := by simpa using hxz
        subst x
        norm_num [cubicNumberPolynomial, IsRoot.def, eval_sub, eval_add, eval_pow] at hx
      · have : x = -1 := by simpa using hxz
        subst x
        norm_num [cubicNumberPolynomial, IsRoot.def, eval_sub, eval_add, eval_pow] at hx
    · have hzsq : z ^ 2 = (2 : ℤ) ^ 2 := by
        exact Int.natAbs_eq_iff_sq_eq.mp (by simpa using hz2)
      have hz' : z = 2 ∨ z = -2 := sq_eq_sq_iff_eq_or_eq_neg.mp hzsq
      rcases hz' with rfl | rfl
      · have : x = 2 := by simpa using hxz
        subst x
        norm_num [cubicNumberPolynomial, IsRoot.def, eval_sub, eval_add, eval_pow] at hx
      · have : x = -2 := by simpa using hxz
        subst x
        norm_num [cubicNumberPolynomial, IsRoot.def, eval_sub, eval_add, eval_pow] at hx

/-- The polynomial discriminant in Exercise 4-6 is `-104`. -/
theorem cubic_number_discr :
    discr (cubicNumberPolynomial ℤ) = -104 := by
  simpa [cubicNumberPolynomial, sub_eq_add_neg] using
    (discr_cube_b (-1 : ℤ) (2 : ℤ))

private theorem companion_derivative_matrix :
    3 * (!![0, 0, -2; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) ^ 2 - 1 =
      !![-1, -6, 0; 0, 2, -6; 3, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.ofNat_fin_three, pow_two] <;>
    norm_num

private theorem onederivative_matrix_det :
    Matrix.det (!![-1, -6, 0; 0, 2, -6; 3, 0, 2] : Matrix (Fin 3) (Fin 3) ℚ) = 104 := by
  simp [Matrix.det_fin_three]
  norm_num

private theorem cubic_onepower_dim
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) : B.dim = 3 := by
  rw [← B.natDegree_minpoly, hmin]
  rw [show cubicNumberPolynomial ℚ = X ^ 3 + (-X + 2) by
    simp only [cubicNumberPolynomial]
    ring]
  exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
    compute_degree
    norm_num)).natDegree_eq

private theorem onereindexed_matrix_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    exists e : Fin B.dim ≃ Fin 3,
      Matrix.reindexAlgEquiv ℚ ℚ e (Algebra.leftMulMatrix B.basis B.gen) =
        !![0, 0, -2; 1, 0, 1; 0, 1, 0] := by
  classical
  have hdim := cubic_onepower_dim B hmin
  let e : Fin B.dim ≃ Fin 3 := finCongr hdim
  refine ⟨e, ?_⟩
  rw [Matrix.reindexAlgEquiv_apply, B.leftMulMatrix]
  simp only [PowerBasis.minpolyGen_eq, hmin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, e, cubicNumberPolynomial, hdim,
      Polynomial.coeff_one, Polynomial.coeff_X]

private theorem cubic_number_onederivative
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.norm ℚ (3 * B.gen ^ 2 - 1) = 104 := by
  rw [Algebra.norm_eq_matrix_det B.basis]
  obtain ⟨e, hM⟩ := onereindexed_matrix_gen B hmin
  rw [← Matrix.det_reindexAlgEquiv ℚ ℚ e]
  have hN : Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix B.basis (3 * B.gen ^ 2 - 1)) =
      !![-1, -6, 0; 0, 2, -6; 3, 0, 2] := by
    let H : K →ₐ[ℚ] Matrix (Fin 3) (Fin 3) ℚ :=
      (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.comp
        (Algebra.leftMulMatrix B.basis)
    change H (3 * B.gen ^ 2 - 1) = !![-1, -6, 0; 0, 2, -6; 3, 0, 2]
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
    change 3 * Matrix.reindexAlgEquiv ℚ ℚ e
        (Algebra.leftMulMatrix B.basis B.gen) ^ 2 - 1 =
      !![-1, -6, 0; 0, 2, -6; 3, 0, 2]
    simpa [hM] using companion_derivative_matrix
  rw [hN, onederivative_matrix_det]

/-- The discriminant of the rational power basis `(1, alpha, alpha^2)` is `-104`. -/
theorem cubic_onepower_discr
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.discr ℚ B.basis = -104 := by
  have hdim := cubic_onepower_dim B hmin
  rw [Algebra.discr_powerBasis_eq_norm, B.finrank, hdim]
  norm_num
  rw [hmin]
  have hderiv : (cubicNumberPolynomial ℚ).derivative = 3 * X ^ 2 - 1 := by
    simp only [cubicNumberPolynomial, derivative_add, derivative_sub, derivative_pow,
      Nat.cast_ofNat,
      Nat.add_one_sub_one, derivative_X, mul_one, derivative_ofNat, add_zero, sub_left_inj,
        mul_eq_mul_right_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_ne_zero, or_false]
    rw [Polynomial.C_ofNat]
  rw [hderiv]
  simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat, map_one]
  linarith [cubic_number_onederivative B hmin]

private theorem onediscr_coe_integers
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

/-- Stickelberger's congruence rules out index two, so the field discriminant is `-104`. -/
theorem cubic_onenumber_discr
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    NumberField.discr K = -104 := by
  have hpower : Algebra.discr ℚ B.basis = (-104 : ℚ) :=
    cubic_onepower_discr B hmin
  have hgenIntegral : IsIntegral ℤ B.gen := by
    refine ⟨cubicNumberPolynomial ℤ, ?_, ?_⟩
    · rw [show cubicNumberPolynomial ℤ = X ^ 3 + (-X + 2) by
        simp only [cubicNumberPolynomial]
        ring]
      apply monic_X_pow_add
      compute_degree
      norm_num
    · change Polynomial.aeval B.gen (cubicNumberPolynomial ℤ) = 0
      rw [← Polynomial.aeval_map_algebraMap ℚ]
      rw [show (cubicNumberPolynomial ℤ).map (algebraMap ℤ ℚ) =
          cubicNumberPolynomial ℚ by simp [cubicNumberPolynomial]]
      rw [← hmin]
      exact minpoly.aeval ℚ B.gen
  have hIntegral : forall i, IsIntegral ℤ (B.basis i) := by
    intro i
    simpa only [PowerBasis.coe_basis] using
      hgenIntegral.pow i
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K B.basis hIntegral
  have hdZ : (-104 : ℤ) = d ^ 2 * NumberField.discr K := by
    have hd' := hd
    rw [hpower] at hd'
    exact_mod_cast hd'
  have hd_ne : d ≠ 0 := by
    intro hd0
    subst d
    norm_num at hdZ
  have hdvd : d ^ 2 ∣ (104 : ℤ) := by
    refine ⟨-NumberField.discr K, ?_⟩
    nlinarith [hdZ]
  have hd_sq_le : d ^ 2 ≤ (104 : ℤ) := by
    have hnat := Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (104 : ℤ) ≠ 0)
    have hnat' : d.natAbs ^ 2 ≤ 104 := by
      simpa [Int.natAbs_pow] using hnat
    have hcast : ((d.natAbs ^ 2 : ℕ) : ℤ) ≤ 104 := by
      exact_mod_cast hnat'
    calc
      d ^ 2 = |d| ^ 2 := by rw [sq_abs]
      _ = ((d.natAbs ^ 2 : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]
        norm_num
      _ ≤ 104 := hcast
  have hd_lower : (-10 : ℤ) ≤ d := by nlinarith [sq_nonneg d]
  have hd_upper : d ≤ (10 : ℤ) := by nlinarith [sq_nonneg d]
  have hsq : d ^ 2 = 1 ∨ d ^ 2 = 4 := by
    interval_cases d <;> norm_num at hdvd <;> norm_num
  rcases hsq with hsq | hsq
  · nlinarith
  · have hdisc : NumberField.discr K = -26 := by nlinarith
    have hmod := discr_emod_four K
    rw [hdisc] at hmod
    norm_num at hmod

/-- The powers `1, alpha, alpha^2` form an integral basis, hence `O_K = ℤ[alpha]`. -/
theorem onering_integers_adjoin
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ := by
  classical
  have hdim : B.dim = 3 := cubic_onepower_dim B hmin
  let bQ : Basis (Fin 3) ℚ K := B.basis.reindex (finCongr hdim)
  have hbQ (i : Fin 3) : bQ i = B.gen ^ (i : Nat) := by
    simp [bQ, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  let v : Fin 3 → NumberField.RingOfIntegers K := fun i => alpha ^ (i : Nat)
  have hvQ : (fun i => ((v i : NumberField.RingOfIntegers K) : K)) = bQ := by
    funext i
    rw [hbQ i]
    simp only [v, map_pow]
    rw [hgen]
  have hvQdiscr : Algebra.discr ℚ (fun i => ((v i : NumberField.RingOfIntegers K) : K)) =
      (-104 : ℚ) := by
    rw [hvQ]
    dsimp [bQ]
    rw [Basis.coe_reindex, Algebra.discr_reindex]
    exact cubic_onepower_discr B hmin
  have hvZdiscr : Algebra.discr ℤ v = (-104 : ℤ) := by
    apply Rat.intCast_injective
    rw [onediscr_coe_integers]
    exact hvQdiscr
  have hfieldDiscr : NumberField.discr K = (-104 : ℤ) :=
    cubic_onenumber_discr B hmin
  let eInt : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 3 :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank]
      simpa [hdim] using B.finrank)
  let bInt : Basis (Fin 3) ℤ (NumberField.RingOfIntegers K) :=
    (NumberField.RingOfIntegers.basis K).reindex eInt
  have hbIntDiscr : Algebra.discr ℤ bInt = (-104 : ℤ) := by
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
      dim := 3
      basis := bZ
      basis_eq_pow := fun i => by
        rw [congr_fun hbZ i] }
  simpa [PB] using PB.adjoin_gen_eq_top

private theorem norm_gen
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.norm ℚ B.gen = -2 := by
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hmin]
  have hdim := cubic_onepower_dim B hmin
  rw [hdim]
  norm_num [cubicNumberPolynomial, Polynomial.coeff_X, Polynomial.coeff_one]

private theorem companion_sub_matrix :
    (!![0, 0, -2; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) - 1 =
      !![-1, 0, -2; 1, -1, 1; 0, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp

private theorem norm_gen_sub
    {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.norm ℚ (B.gen - 1) = -2 := by
  rw [Algebra.norm_eq_matrix_det B.basis]
  obtain ⟨e, hM⟩ := onereindexed_matrix_gen B hmin
  rw [← Matrix.det_reindexAlgEquiv ℚ ℚ e]
  have hN : Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix B.basis (B.gen - 1)) =
      !![-1, 0, -2; 1, -1, 1; 0, 1, -1] := by
    let H : K →ₐ[ℚ] Matrix (Fin 3) (Fin 3) ℚ :=
      (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.comp
        (Algebra.leftMulMatrix B.basis)
    change H (B.gen - 1) = !![-1, 0, -2; 1, -1, 1; 0, 1, -1]
    simp only [map_sub, map_one]
    change Matrix.reindexAlgEquiv ℚ ℚ e
        (Algebra.leftMulMatrix B.basis B.gen) - 1 =
      !![-1, 0, -2; 1, -1, 1; 0, 1, -1]
    simpa [hM] using companion_sub_matrix
  rw [hN]
  simp [Matrix.det_fin_three]

private theorem alpha_prime
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Prime alpha := by
  have hnormQ : Algebra.norm ℚ (alpha : K) = -2 := by
    rw [← hgen]
    exact norm_gen B hmin
  have hnormZ : Algebra.norm ℤ alpha = -2 := by
    apply Rat.intCast_inj.mp
    rw [Algebra.coe_norm_int]
    exact hnormQ
  have halpha_ne : alpha ≠ 0 := by
    intro hzero
    subst alpha
    norm_num at hnormZ
  apply Ideal.prime_of_irreducible_absNorm_span halpha_ne
  rw [Ideal.absNorm_span_singleton, hnormZ]
  exact (Nat.irreducible_iff_nat_prime 2).mpr Nat.prime_two

private theorem alpha_sub_prime
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Prime (alpha - 1) := by
  have hnormQ : Algebra.norm ℚ ((alpha : K) - 1) = -2 := by
    rw [← hgen]
    exact norm_gen_sub B hmin
  have hnormZ : Algebra.norm ℤ (alpha - 1) = -2 := by
    apply Rat.intCast_inj.mp
    rw [Algebra.coe_norm_int]
    simpa using hnormQ
  have halpha_ne : alpha - 1 ≠ 0 := by
    intro hzero
    rw [hzero, Algebra.norm_zero] at hnormZ
    norm_num at hnormZ
  apply Ideal.prime_of_irreducible_absNorm_span halpha_ne
  rw [Ideal.absNorm_span_singleton, hnormZ]
  exact (Nat.irreducible_iff_nat_prime 2).mpr Nat.prime_two

private theorem minkowski_floor_two
    {K : Type*} [Field K] [NumberField K]
    (hdegree : finrank ℚ K = 3)
    (hcomplex : nrComplexPlaces K = 1)
    (hdiscr : NumberField.discr K = -104) :
    ⌊(4 / Real.pi) ^ nrComplexPlaces K *
      (Nat.factorial (finrank ℚ K) /
        (finrank ℚ K) ^ (finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)⌋₊ ≤ 2 := by
  let M : ℝ := (4 / Real.pi) ^ nrComplexPlaces K *
    (Nat.factorial (finrank ℚ K) /
      (finrank ℚ K) ^ (finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)
  have hsqrt_sq : (Real.sqrt (104 : ℝ)) ^ 2 = 104 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (104 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_lt : Real.sqrt (104 : ℝ) < (51 : ℝ) / 5 := by
    nlinarith
  have hpi : (157 : ℝ) / 50 < Real.pi := by
    convert Real.pi_gt_d2 using 1 ; norm_num
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hM : M < 3 := by
    dsimp [M]
    rw [hdegree, hcomplex, hdiscr]
    norm_num [Nat.factorial]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi_pos]
    nlinarith
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hfloor : ⌊M⌋₊ < 3 := (Nat.floor_lt hMnonneg).mpr hM
  change ⌊M⌋₊ ≤ 2
  omega

/-- The ring of integers in Exercise 4-6 is a principal ideal ring. -/
theorem cubicOneisRing
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  have hdegree : finrank ℚ K = 3 := by
    exact B.finrank.trans (cubic_onepower_dim B hmin)
  have hdiscr : NumberField.discr K = -104 :=
    cubic_onenumber_discr B hmin
  have hcomplex : nrComplexPlaces K = 1 :=
    discr_nr_complex K hdegree (by omega)
  have hbound := minkowski_floor_two hdegree hcomplex hdiscr
  have hrootK : (alpha : K) ^ 3 - (alpha : K) + 2 = 0 := by
    have hroot := minpoly.aeval ℚ B.gen
    rw [hmin] at hroot
    simpa [cubicNumberPolynomial, hgen, map_ofNat] using hroot
  have hroot : alpha ^ 3 - alpha + 2 = 0 := by
    apply NumberField.RingOfIntegers.ext
    simpa using hrootK
  have hprod : alpha * (alpha - 1) * (alpha + 1) = -2 := by
    linear_combination hroot
  have halphaPrime : Prime alpha :=
    alpha_prime alpha B hgen hmin
  have halphaSubPrime : Prime (alpha - 1) :=
    alpha_sub_prime alpha B hgen hmin
  have halpha_ne : alpha ≠ 0 := halphaPrime.ne_zero
  have halphaSub_ne : alpha - 1 ≠ 0 := halphaSubPrime.ne_zero
  have hspanAlphaPrime :
      (Ideal.span ({alpha} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    (Ideal.span_singleton_prime halpha_ne).mpr halphaPrime
  have hspanAlphaSubPrime :
      (Ideal.span ({alpha - 1} : Set (NumberField.RingOfIntegers K))).IsPrime :=
    (Ideal.span_singleton_prime halphaSub_ne).mpr halphaSubPrime
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpRange hpPrime P hP _
  have hpLe : p ≤ 2 := le_trans (Finset.mem_Icc.mp hpRange).2 hbound
  have hpEq : p = 2 := le_antisymm hpLe hpPrime.two_le
  subst p
  rcases hP with ⟨hPPrime, hPLies⟩
  letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPLies
  have hmapLe : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K))
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr
      (Ideal.over_def (P := P) (Ideal.span ({(2 : ℤ)} : Set ℤ))).le
  have hspanTwoLe :
      Ideal.span ({2} : Set (NumberField.RingOfIntegers K)) ≤ P := by
    simpa [Ideal.map_span] using hmapLe
  have htwoMem : (2 : NumberField.RingOfIntegers K) ∈ P :=
    hspanTwoLe (Ideal.subset_span (Set.mem_singleton 2))
  have hprodMem : alpha * (alpha - 1) * (alpha + 1) ∈ P := by
    rw [hprod]
    exact P.neg_mem htwoMem
  have hAlphaOrSub : alpha ∈ P ∨ alpha - 1 ∈ P := by
    rcases hPPrime.mem_or_mem hprodMem with hleft | hplus
    · exact hPPrime.mem_or_mem hleft
    · right
      have hnegTwo : (-2 : NumberField.RingOfIntegers K) ∈ P := P.neg_mem htwoMem
      convert P.add_mem hplus hnegTwo using 1 ; ring
  rcases hAlphaOrSub with halphaMem | halphaSubMem
  · have hle : Ideal.span ({alpha} : Set (NumberField.RingOfIntegers K)) ≤ P :=
      Ideal.span_le.mpr (by simpa using halphaMem)
    have hmax := hspanAlphaPrime.isMaximal (by simp [halpha_ne])
    have hEq : P = Ideal.span ({alpha} : Set (NumberField.RingOfIntegers K)) :=
      (hmax.eq_of_le hPPrime.ne_top' hle).symm
    rw [hEq]
    exact ⟨alpha, rfl⟩
  · have hle : Ideal.span ({alpha - 1} : Set (NumberField.RingOfIntegers K)) ≤ P :=
      Ideal.span_le.mpr (by simpa using halphaSubMem)
    have hmax := hspanAlphaSubPrime.isMaximal (by simp [halphaSub_ne])
    have hEq : P = Ideal.span ({alpha - 1} : Set (NumberField.RingOfIntegers K)) :=
      (hmax.eq_of_le hPPrime.ne_top' hle).symm
    rw [hEq]
    exact ⟨alpha - 1, rfl⟩

/-- Milne, Exercise 4-6: `O_K = ℤ[alpha]` and the class number is one. -/
theorem cubicNumber6
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = cubicNumberPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ ∧
      NumberField.classNumber K = 1 := by
  constructor
  · exact onering_integers_adjoin alpha B hgen hmin
  · rw [NumberField.classNumber_eq_one_iff]
    exact cubicOneisRing alpha B hgen hmin

end

end Towers.NumberTheory.Milne
