import Towers.NumberTheory.Fields.CubicPolynomial
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.ClassNumber


/-!
# Milne, Algebraic Number Theory, Exercise 6-1: the order argument

This file isolates the structural part of Milne's solution.  The key point is that the
discriminant calculation puts a power of `3` times the full ring of integers in `Z[alpha]`.
The equality `O_K = Z[alpha] + (alpha + 1) O_K` can then be iterated, and the relation
`(alpha + 1)^3 = 3 alpha (alpha + 2)` absorbs the final remainder.
-/

namespace Towers.NumberTheory.Milne

open Polynomial
open NumberField
open Module
open scoped NumberField

private theorem exercise_companion_matrix :
    3 * (!![0, 0, -1; 1, 0, 3; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) ^ 2 - 3 =
      !![-3, -3, 0; 0, 6, -3; 3, 0, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.ofNat_fin_three, pow_two] <;>
    norm_num

private theorem exercise_matrix_det :
    -Matrix.det (!![-3, -3, 0; 0, 6, -3; 3, 0, 6] : Matrix (Fin 3) (Fin 3) ℚ) = 81 := by
  simp [Matrix.det_fin_three]
  norm_num

section DiscriminantContainment

variable {K : Type*} [Field K] [NumberField K]

private theorem exercise_six_discr
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

private theorem exercise_six_minpoly
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    minpoly ℤ alpha = exerciseSixPolynomial ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Rat.intCast_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K alpha.isIntegral]
  change minpoly ℚ (alpha : K) =
    (exerciseSixPolynomial ℤ).map (algebraMap ℤ ℚ)
  rw [← hgen, hmin]
  simp [exerciseSixPolynomial]

private theorem exercise_six_dim
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) : B.dim = 3 := by
  rw [← B.natDegree_minpoly, hmin]
  rw [show exerciseSixPolynomial ℚ = X ^ 3 + (-3 * X + 1) by
    simp only [exerciseSixPolynomial]
    ring]
  exact ((isMonicOfDegree_X_pow ℚ 3).add_right (by
    compute_degree
    norm_num)).natDegree_eq

private theorem exercise_reindexed_gen
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    ∃ e : Fin B.dim ≃ Fin 3,
      Matrix.reindexAlgEquiv ℚ ℚ e (Algebra.leftMulMatrix B.basis B.gen) =
        !![0, 0, -1; 1, 0, 3; 0, 1, 0] := by
  classical
  have hdim := exercise_six_dim B hmin
  let e : Fin B.dim ≃ Fin 3 := finCongr hdim
  refine ⟨e, ?_⟩
  rw [Matrix.reindexAlgEquiv_apply, B.leftMulMatrix]
  simp only [PowerBasis.minpolyGen_eq, hmin]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, e, exerciseSixPolynomial, hdim,
      Polynomial.coeff_one, Polynomial.coeff_X]

private theorem exercise_six_derivative
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    Algebra.norm ℚ (3 * B.gen ^ 2 - 3) = -81 := by
  rw [Algebra.norm_eq_matrix_det B.basis]
  obtain ⟨e, hM⟩ := exercise_reindexed_gen B hmin
  rw [← Matrix.det_reindexAlgEquiv ℚ ℚ e]
  have hN : Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix B.basis (3 * B.gen ^ 2 - 3)) =
      !![-3, -3, 0; 0, 6, -3; 3, 0, 6] := by
    let H : K →ₐ[ℚ] Matrix (Fin 3) (Fin 3) ℚ :=
      (Matrix.reindexAlgEquiv ℚ ℚ e).toAlgHom.comp
        (Algebra.leftMulMatrix B.basis)
    change H (3 * B.gen ^ 2 - 3) = !![-3, -3, 0; 0, 6, -3; 3, 0, 6]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    change 3 * Matrix.reindexAlgEquiv ℚ ℚ e
        (Algebra.leftMulMatrix B.basis B.gen) ^ 2 - 3 =
      !![-3, -3, 0; 0, 6, -3; 3, 0, 6]
    simpa [hM] using exercise_companion_matrix
  rw [hN]
  linarith [exercise_matrix_det]

/-- The polynomial discriminant computation is the discriminant of the
corresponding cubic power basis. -/
theorem exercise_basis_discr
    (B : PowerBasis ℚ K)
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    Algebra.discr ℚ B.basis = 81 := by
  have hdim := exercise_six_dim B hmin
  rw [Algebra.discr_powerBasis_eq_norm, B.finrank, hdim]
  norm_num
  rw [hmin]
  have hderiv : (exerciseSixPolynomial ℚ).derivative = 3 * X ^ 2 - 3 := by
    simp only [exerciseSixPolynomial, derivative_add, derivative_sub,
      derivative_pow, Nat.cast_ofNat, Nat.add_one_sub_one, derivative_X,
      mul_one, derivative_mul, derivative_ofNat, zero_mul, zero_add,
      derivative_one, add_zero, sub_left_inj, mul_eq_mul_right_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, X_ne_zero,
      or_false]
    rw [Polynomial.C_ofNat]
  rw [hderiv]
  simp only [aeval_sub, map_mul, map_pow, aeval_X]
  have hthree : Polynomial.aeval B.gen (3 : ℚ[X]) = (3 : K) := by
    rw [← Polynomial.C_ofNat (R := ℚ) 3]
    simp
  rw [hthree]
  linarith [exercise_six_derivative B hmin]

/-- The discriminant computation implies that `81 O_K` is contained in `Z[alpha]`.
This is the concrete `m = 4` instance of the first order inclusion in Exercise 6-1. -/
theorem exercise_six_eighty
    (B : PowerBasis ℚ K) (hBint : IsIntegral ℤ B.gen)
    (hdiscr : Algebra.discr ℚ B.basis = 81) (z : NumberField.RingOfIntegers K) :
    (81 : K) * (z : K) ∈ Algebra.adjoin ℤ ({B.gen} : Set K) := by
  have h := Algebra.discr_mul_isIntegral_mem_adjoin
    (K := ℚ) (R := ℤ) (L := K) (B := B) hBint z.isIntegral_coe
  rw [Algebra.smul_def, hdiscr] at h
  norm_num at h ⊢
  exact h

/-- In particular the inclusions asserted in Exercise 6-1 hold with `m = 4`, stated
elementwise to avoid identifying the two concrete models of the order `Z[alpha]`. -/
theorem exercise_six_inclusions
    (B : PowerBasis ℚ K) (hBint : IsIntegral ℤ B.gen)
    (hdiscr : Algebra.discr ℚ B.basis = 81) :
    Algebra.adjoin ℤ ({B.gen} : Set K) ≤ integralClosure ℤ K ∧
      ∀ z : NumberField.RingOfIntegers K,
        ((3 : K) ^ 4) * (z : K) ∈ Algebra.adjoin ℤ ({B.gen} : Set K) := by
  constructor
  · rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact hBint
  · intro z
    norm_num
    exact exercise_six_eighty B hBint hdiscr z

/-- The order inclusions in Exercise 6-1, now requiring only the stated
minimal polynomial and integrality of the chosen root. -/
theorem exercise_inclusions_minpoly
    (B : PowerBasis ℚ K) (hBint : IsIntegral ℤ B.gen)
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    Algebra.adjoin ℤ ({B.gen} : Set K) ≤ integralClosure ℤ K ∧
      ∀ z : NumberField.RingOfIntegers K,
        ((3 : K) ^ 4) * (z : K) ∈ Algebra.adjoin ℤ ({B.gen} : Set K) :=
  exercise_six_inclusions B hBint (exercise_basis_discr B hmin)

end DiscriminantContainment

section OrderEquality

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Iterating `S = A + pi S` gives a remainder divisible by any prescribed power of `pi`. -/
theorem subalgebra_add_decompose
    (A : Subalgebra R S) (pi : S) (hpi : pi ∈ A)
    (hdecomp : ∀ x : S, ∃ a : S, a ∈ A ∧ ∃ y : S, x = a + pi * y)
    (n : ℕ) (x : S) :
    ∃ a : S, a ∈ A ∧ ∃ y : S, x = a + pi ^ n * y := by
  induction n generalizing x with
  | zero =>
      exact ⟨0, A.zero_mem, x, by simp⟩
  | succ n ih =>
      obtain ⟨a, ha, y, rfl⟩ := ih x
      obtain ⟨b, hb, z, rfl⟩ := hdecomp y
      refine ⟨a + pi ^ n * b, A.add_mem ha (A.mul_mem (A.pow_mem hpi n) hb), z, ?_⟩
      rw [pow_succ]
      ring

/-- Milne's order argument: if `q^m S` lies in `A`, every element is congruent modulo
`pi S` to an element of `A`, and `pi^d = q u`, then `A = S`. -/
theorem subalgebra_top_decompose
    (A : Subalgebra R S) (pi q u : S) (d m : ℕ)
    (hpi : pi ∈ A)
    (hdecomp : ∀ x : S, ∃ a : S, a ∈ A ∧ ∃ y : S, x = a + pi * y)
    (hscale : ∀ x : S, q ^ m * x ∈ A)
    (hpow : pi ^ d = q * u) : A = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, y, hxy⟩ :=
    subalgebra_add_decompose A pi hpi hdecomp (d * m) x
  rw [pow_mul, hpow, mul_pow] at hxy
  rw [hxy]
  exact A.add_mem ha (by
    rw [mul_assoc]
    exact hscale (u ^ m * y))

/-- The exact numerical specialization used in Exercise 6-1.  Twelve iterations suffice
because `(alpha + 1)^3 = 3u` and `3^4 O_K` is already in the order. -/
theorem exercise_six_subalgebra
    (A : Subalgebra ℤ S) (alpha : S)
    (halpha : alpha ∈ A)
    (hdecomp : ∀ x : S, ∃ a : S, a ∈ A ∧ ∃ y : S, x = a + (alpha + 1) * y)
    (hscale : ∀ x : S, (3 : S) ^ 4 * x ∈ A)
    (hroot : alpha ^ 3 - 3 * alpha + 1 = 0) : A = ⊤ := by
  apply subalgebra_top_decompose
    A (alpha + 1) 3 (alpha * (alpha + 2)) 3 4
  · exact A.add_mem halpha A.one_mem
  · exact hdecomp
  · exact hscale
  · simpa [mul_assoc] using exercise_six_cube alpha hroot

end OrderEquality

section Ideals

variable {R : Type*} [CommRing R]

/-- The relation in Exercise 6-1 gives the equality of principal ideals
`(alpha + 1)^3 = (3)`, because `alpha(alpha+2)` is a unit. -/
theorem exercise_six_three
    [IsDomain R] (alpha : R) (hroot : alpha ^ 3 - 3 * alpha + 1 = 0) :
    Ideal.span ({alpha + 1} : Set R) ^ 3 = Ideal.span ({3} : Set R) := by
  rw [Ideal.span_singleton_pow, exercise_six_cube alpha hroot]
  simpa [mul_assoc] using Ideal.span_singleton_mul_right_unit
    ((exercise_six_one alpha hroot).mul
      (exercise_six_unit alpha hroot)) (3 : R)

/-- A quotient-field identification proves that the principal ideal `(alpha + 1)` is prime. -/
theorem exercise_six_span
    (alpha : R)
    (e : (R ⧸ Ideal.span ({alpha + 1} : Set R)) ≃+* ZMod 3) :
    (Ideal.span ({alpha + 1} : Set R)).IsPrime := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfield : IsField (R ⧸ Ideal.span ({alpha + 1} : Set R)) :=
    e.toMulEquiv.isField (Field.toIsField (ZMod 3))
  have hmax : (Ideal.span ({alpha + 1} : Set R)).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient
      (Ideal.span ({alpha + 1} : Set R))).mpr hfield
  exact hmax.isPrime

/-- The quotient by `(alpha + 1)` is the three-element field.  Indeed, the
cube of this ideal is `(3)`, so its absolute norm is `3`. -/
noncomputable def exercise_six_root
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (hroot : alpha ^ 3 - 3 * alpha + 1 = 0)
    (hdegree : Module.finrank ℚ K = 3) :
    (NumberField.RingOfIntegers K ⧸
      Ideal.span ({alpha + 1} : Set (NumberField.RingOfIntegers K))) ≃+* ZMod 3 := by
  let I : Ideal (NumberField.RingOfIntegers K) :=
    Ideal.span ({alpha + 1} : Set (NumberField.RingOfIntegers K))
  have hpow : I ^ 3 = Ideal.span ({3} : Set (NumberField.RingOfIntegers K)) := by
    exact exercise_six_three alpha hroot
  have hnormPow := congrArg Ideal.absNorm hpow
  have hnormThree :
      Ideal.absNorm (Ideal.span ({3} : Set (NumberField.RingOfIntegers K))) = 27 := by
    rw [Ideal.absNorm_span_singleton]
    rw [show (3 : NumberField.RingOfIntegers K) =
      algebraMap ℤ (NumberField.RingOfIntegers K) 3 by norm_num,
      Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K),
      ← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
      NumberField.RingOfIntegers.rank, hdegree]
    norm_num
  have hnormCube : Ideal.absNorm I ^ 3 = 27 := by
    simpa [map_pow, hnormThree] using hnormPow
  have hnorm : Ideal.absNorm I = 3 := by
    apply Nat.pow_left_injective (by norm_num : 3 ≠ 0)
    norm_num [hnormCube]
  have hIne : I ≠ ⊥ := by
    intro hI
    rw [hI, Ideal.absNorm_bot] at hnorm
    norm_num at hnorm
  letI : Finite (NumberField.RingOfIntegers K ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I hIne
  letI : Fintype (NumberField.RingOfIntegers K ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card
      (NumberField.RingOfIntegers K ⧸ I) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hnorm
  exact (ZMod.ringEquivOfPrime _ (by norm_num) hcard).symm

/-- The principal ideal `(alpha + 1)` in the cubic ring of integers is prime. -/
theorem exercise_six_prime
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (hroot : alpha ^ 3 - 3 * alpha + 1 = 0)
    (hdegree : Module.finrank ℚ K = 3) :
    (Ideal.span ({alpha + 1} : Set (NumberField.RingOfIntegers K))).IsPrime := by
  exact exercise_six_span alpha
    (exercise_six_root alpha hroot hdegree)

/-- Surjectivity of the integer map to the quotient is exactly the assertion
`O_K = Z + (alpha+1) O_K`, written elementwise. -/
theorem exercise_six_surjective
    [Algebra ℤ R] (alpha : R)
    (hsurj : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span ({alpha + 1} : Set R))).comp
        (algebraMap ℤ R))) :
    ∀ x : R, ∃ z : ℤ, ∃ y : R, x = algebraMap ℤ R z + (alpha + 1) * y := by
  intro x
  obtain ⟨z, hz⟩ := hsurj (Ideal.Quotient.mk (Ideal.span ({alpha + 1} : Set R)) x)
  have hmem : x - algebraMap ℤ R z ∈ Ideal.span ({alpha + 1} : Set R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mk _ x -
      ((Ideal.Quotient.mk (Ideal.span ({alpha + 1} : Set R))).comp
        (algebraMap ℤ R)) z = 0
    rw [hz]
    exact sub_self _
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨z, y, by linear_combination hy⟩

/-- In the cubic from Exercise 6-1, every algebraic integer is congruent to
an ordinary integer modulo `(alpha + 1)`. -/
theorem exercise_six_int
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (hroot : alpha ^ 3 - 3 * alpha + 1 = 0)
    (hdegree : Module.finrank ℚ K = 3) :
    ∀ x : NumberField.RingOfIntegers K, ∃ z : ℤ,
      ∃ y : NumberField.RingOfIntegers K,
        x = algebraMap ℤ (NumberField.RingOfIntegers K) z + (alpha + 1) * y := by
  let I : Ideal (NumberField.RingOfIntegers K) :=
    Ideal.span ({alpha + 1} : Set (NumberField.RingOfIntegers K))
  let e : (NumberField.RingOfIntegers K ⧸ I) ≃+* ZMod 3 :=
    exercise_six_root alpha hroot hdegree
  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk I).comp
        (algebraMap ℤ (NumberField.RingOfIntegers K))) := by
    intro x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (e x)
    refine ⟨z, e.injective ?_⟩
    simpa using hz
  exact exercise_six_surjective alpha hsurj

end Ideals

section PrimeTwoAndPID

/-- The cubic from Exercise 6-1 remains irreducible modulo `2`. -/
theorem exercise_six_irreducible :
    Irreducible
      ((exerciseSixPolynomial ℤ).map (Int.castRingHom (ZMod 2))) := by
  have h : Irreducible (X ^ 3 + X + 1 : (ZMod 2)[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by
        rw [show (X ^ 3 + X + 1 : (ZMod 2)[X]) = X ^ 3 + (X + 1) by ring]
        exact ((isMonicOfDegree_X_pow (ZMod 2) 3).add_right (by
          compute_degree
          norm_num)).natDegree_eq
      simp [hdeg]
    · intro x hx
      fin_cases x <;>
        exact one_ne_zero (by simpa [IsRoot.def] using hx)
  have heq :
      (exerciseSixPolynomial ℤ).map (Int.castRingHom (ZMod 2)) = X ^ 3 + X + 1 := by
    simp only [exerciseSixPolynomial, sub_eq_add_neg, Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_one,
        add_left_inj, add_right_inj]
    calc
      -(3 * X : (ZMod 2)[X]) = (-3) * X := by rw [neg_mul]
      _ = 1 * X := by
        rw [show (-3 : (ZMod 2)[X]) = 1 by
          ext n
          by_cases hn : n = 0
          · subst n
            norm_num
            decide
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
            simp [Polynomial.coeff_one]]
      _ = X := one_mul X
  rw [heq]
  exact h

variable {K : Type*} [Field K] [NumberField K]

/-- Milne's congruence argument and the discriminant containment together show
that the full ring of integers is generated by `alpha`. -/
theorem exercise_integers_adjoin
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ := by
  let A : Subalgebra ℤ (NumberField.RingOfIntegers K) :=
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K))
  have hdegree : Module.finrank ℚ K = 3 := by
    rw [B.finrank, exercise_six_dim B hmin]
  have hrootK : (alpha : K) ^ 3 - 3 * (alpha : K) + 1 = 0 := by
    have hroot := minpoly.aeval ℚ B.gen
    rw [hmin] at hroot
    simpa [exerciseSixPolynomial, hgen, map_ofNat] using hroot
  have hroot : alpha ^ 3 - 3 * alpha + 1 = 0 := by
    apply NumberField.RingOfIntegers.ext
    simpa using hrootK
  apply exercise_six_subalgebra A alpha
  · exact Algebra.subset_adjoin (Set.mem_singleton alpha)
  · intro x
    obtain ⟨z, y, hxy⟩ := exercise_six_int alpha hroot hdegree x
    exact ⟨algebraMap ℤ (NumberField.RingOfIntegers K) z,
      A.algebraMap_mem z, y, hxy⟩
  · intro x
    let f : NumberField.RingOfIntegers K →ₐ[ℤ] K :=
      IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers K) K
    have hBint : IsIntegral ℤ B.gen := by
      rw [hgen]
      exact alpha.isIntegral_coe
    have hscaleK :=
      (exercise_inclusions_minpoly B hBint hmin).2 x
    have hmem : f ((3 : NumberField.RingOfIntegers K) ^ 4 * x) ∈ A.map f := by
      change f ((3 : NumberField.RingOfIntegers K) ^ 4 * x) ∈
        (Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K))).map f
      rw [AlgHom.map_adjoin_singleton]
      simpa [f, hgen] using hscaleK
    rw [Subalgebra.mem_map] at hmem
    obtain ⟨y, hy, heq⟩ := hmem
    have hyEq : y = (3 : NumberField.RingOfIntegers K) ^ 4 * x := by
      apply NumberField.RingOfIntegers.coe_injective
      exact heq
    simpa [hyEq] using hy
  · exact hroot

/-- Once the order argument is complete, the polynomial discriminant `81` is
the discriminant of the full ring of integers. -/
theorem exercise_number_discr
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    NumberField.discr K = 81 := by
  classical
  have hadjoin := exercise_integers_adjoin alpha B hgen hmin
  have hminZ := exercise_six_minpoly alpha B hgen hmin
  let PB : PowerBasis ℤ (NumberField.RingOfIntegers K) :=
    PowerBasis.ofAdjoinEqTop' alpha.isIntegral hadjoin
  have hPBdim : PB.dim = 3 := by
    change (PowerBasis.ofAdjoinEqTop' alpha.isIntegral hadjoin).dim = 3
    rw [PowerBasis.ofAdjoinEqTop'_dim, hminZ]
    rw [show exerciseSixPolynomial ℤ = X ^ 3 + (-3 * X + 1) by
      simp only [exerciseSixPolynomial]
      ring]
    exact ((isMonicOfDegree_X_pow ℤ 3).add_right (by
      compute_degree
      norm_num)).natDegree_eq
  let bZ : Basis (Fin 3) ℤ (NumberField.RingOfIntegers K) :=
    PB.basis.reindex (finCongr hPBdim)
  have hbZ (i : Fin 3) : bZ i = alpha ^ (i : ℕ) := by
    change (PB.basis.reindex (finCongr hPBdim)) i = alpha ^ (i : ℕ)
    rw [Basis.reindex_apply, PB.basis_eq_pow]
    have hPBgen : PB.gen = alpha := by
      simp [PB]
    rw [hPBgen]
    apply congrArg (fun n : ℕ => alpha ^ n)
    rfl
  have hBdim : B.dim = 3 := exercise_six_dim B hmin
  let bQ : Basis (Fin 3) ℚ K := B.basis.reindex (finCongr hBdim)
  have hbQ (i : Fin 3) : bQ i = B.gen ^ (i : ℕ) := by
    simp [bQ, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  have hcoe : (fun i => ((bZ i : NumberField.RingOfIntegers K) : K)) = bQ := by
    funext i
    rw [hbZ i, hbQ i]
    change (alpha : K) ^ (i : ℕ) = B.gen ^ (i : ℕ)
    rw [hgen]
  have hQ : Algebra.discr ℚ bQ = (81 : ℚ) := by
    dsimp [bQ]
    rw [Basis.coe_reindex, Algebra.discr_reindex]
    exact exercise_basis_discr B hmin
  have hZ : Algebra.discr ℤ bZ = (81 : ℤ) := by
    apply Rat.intCast_injective
    rw [exercise_six_discr, hcoe]
    exact hQ
  rw [← NumberField.discr_eq_discr K bZ]
  exact hZ

/-- The cubic has three real places and no complex places. -/
theorem exercise_six_nr
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    InfinitePlace.nrComplexPlaces K = 0 := by
  have hdegree : Module.finrank ℚ K = 3 := by
    rw [B.finrank, exercise_six_dim B hmin]
  have hcard := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcomplex_le : InfinitePlace.nrComplexPlaces K ≤ 1 := by
    omega
  interval_cases hcomplex : InfinitePlace.nrComplexPlaces K
  · rfl
  · have hsign := NumberField.sign_discr (K := K)
    rw [exercise_number_discr alpha B hgen hmin, hcomplex] at hsign
    norm_num at hsign

/-- For this totally real cubic of discriminant `81`, Minkowski's class bound
is exactly `2`. -/
theorem six_minkowski_floor
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    ⌊(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
      (Nat.factorial (Module.finrank ℚ K) /
        (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)⌋₊ = 2 := by
  have hdegree : Module.finrank ℚ K = 3 := by
    rw [B.finrank, exercise_six_dim B hmin]
  rw [hdegree, exercise_six_nr alpha B hgen hmin,
    exercise_number_discr alpha B hgen hmin]
  norm_num

/-- Once `O_K = Z[alpha]`, Kummer--Dedekind and irreducibility modulo `2` show that
the ideal `(2)` is prime in `O_K`. -/
theorem exercise_six_two
    (alpha : NumberField.RingOfIntegers K)
    (hadjoin : Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤)
    (hmin : minpoly ℤ alpha = exerciseSixPolynomial ℤ) :
    (Ideal.span ({2} : Set (NumberField.RingOfIntegers K))).IsPrime := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hexponent : RingOfIntegers.exponent alpha = 1 :=
    RingOfIntegers.exponent_eq_one_iff.mpr hadjoin
  have hnotdvd : ¬2 ∣ RingOfIntegers.exponent alpha := by
    rw [hexponent]
    norm_num
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan hnotdvd
  have hirr : Irreducible
      ((minpoly ℤ alpha).map (Int.castRingHom (ZMod 2))) := by
    simpa [hmin] using exercise_six_irreducible
  have hmaxPoly :
      (Ideal.span
        ({(minpoly ℤ alpha).map (Int.castRingHom (ZMod 2))} : Set (ZMod 2)[X])).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  have hfieldSource : IsField
      ((ZMod 2)[X] ⧸ Ideal.span
        ({(minpoly ℤ alpha).map (Int.castRingHom (ZMod 2))} : Set (ZMod 2)[X])) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxPoly
  have hfieldTarget : IsField
      (NumberField.RingOfIntegers K ⧸
        Ideal.span ({2} : Set (NumberField.RingOfIntegers K))) :=
    e.symm.toMulEquiv.isField hfieldSource
  exact ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfieldTarget).isPrime

/-- If the Minkowski bound has integer floor `2`, primality of `(2)` finishes Milne's
class-number-one argument. -/
theorem exercise_minkowski_floor
    (htwo : (Ideal.span ({2} : Set (NumberField.RingOfIntegers K))).IsPrime)
    (hbound : ⌊(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
      (Nat.factorial (Module.finrank ℚ K) /
        (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)⌋₊ = 2) :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpRange hpPrime P hP _
  have hpLe : p ≤ 2 := by
    have := (Finset.mem_Icc.mp hpRange).2
    simpa [hbound] using this
  have hpEq : p = 2 := le_antisymm hpLe hpPrime.two_le
  subst p
  rcases hP with ⟨hPPrime, hPLies⟩
  letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPLies
  have hmapLe : Ideal.map (algebraMap ℤ (NumberField.RingOfIntegers K))
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr
      (Ideal.over_def (P := P) (Ideal.span ({(2 : ℤ)} : Set ℤ))).le
  have hspanLe : Ideal.span ({2} : Set (NumberField.RingOfIntegers K)) ≤ P := by
    simpa [Ideal.map_span] using hmapLe
  have htwoMax : (Ideal.span ({2} : Set (NumberField.RingOfIntegers K))).IsMaximal :=
    htwo.isMaximal (by simp)
  have hEq : P = Ideal.span ({2} : Set (NumberField.RingOfIntegers K)) :=
    (htwoMax.eq_of_le hPPrime.ne_top' hspanLe).symm
  rw [hEq]
  exact ⟨2, rfl⟩

/-- **Milne, Exercise 6-1.** The full ring of integers is `ℤ[alpha]`, and it
is a principal ideal domain. -/
theorem exerciseSixOne
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (hmin : minpoly ℚ B.gen = exerciseSixPolynomial ℚ) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ ∧
      IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  have hadjoin := exercise_integers_adjoin alpha B hgen hmin
  have hminZ := exercise_six_minpoly alpha B hgen hmin
  have htwo := exercise_six_two alpha hadjoin hminZ
  exact ⟨hadjoin,
    exercise_minkowski_floor htwo
      (six_minkowski_floor alpha B hgen hmin)⟩

end PrimeTwoAndPID

end Towers.NumberTheory.Milne
