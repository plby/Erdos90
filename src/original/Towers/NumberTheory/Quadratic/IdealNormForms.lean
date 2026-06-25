import Towers.NumberTheory.Quadratic.ProperPrimitiveClasses
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: norm forms of ideals

This file constructs the integral binary norm form attached to a nonzero integral ideal in a
quadratic number field.  If `(u, v)` is a `Z`-basis of the ideal `I`, its value at `(x, y)` is

`N(xu + yv) / N(I)`.

The coefficients are integral because `N(I)` divides the norm of every element of `I`.  We also
prove that replacing the basis by a determinant-one integral change of basis transforms the form
by the corresponding proper change of variables.
-/

namespace Towers.NumberTheory.Milne

open scoped MatrixGroups
open scoped NumberField nonZeroDivisors
open Module

noncomputable section

namespace INForm

variable {K : Type*} [Field K] [NumberField K]

/-- The integral norm of an algebraic integer. -/
private def intNorm (z : 𝓞 K) : ℤ := Algebra.norm ℤ z

omit [NumberField K] in
/-- In rank two, the norm is a quadratic function.  This determinant identity is the
polarization formula used in the ideal norm-form construction. -/
theorem linear_combination_basis
    (B : Basis (Fin 2) ℤ (𝓞 K)) (u v : 𝓞 K) (x y : ℤ) :
    intNorm (x • u + y • v) =
      intNorm u * x ^ 2 + (intNorm (u + v) - intNorm u - intNorm v) * x * y +
        intNorm v * y ^ 2 := by
  simp_rw [intNorm, Algebra.norm_eq_matrix_det B]
  simp only [map_add, map_smul, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- For commuting two-by-two matrices, the discriminant of the determinant polarization is the
discriminant of the trace pairing.  Applied to multiplication matrices, this identifies the
discriminant of a quadratic norm form with the discriminant of its ordered pair of generators. -/
private theorem det_polar_discr (U V : Matrix (Fin 2) (Fin 2) ℤ)
    (hcomm : U * V = V * U) :
    (Matrix.det (U + V) - Matrix.det U - Matrix.det V) ^ 2 -
        4 * Matrix.det U * Matrix.det V =
      Matrix.trace (U * U) * Matrix.trace (V * V) - Matrix.trace (U * V) ^ 2 := by
  have h00 := congr_fun (congr_fun hcomm 0) 0
  have h01 := congr_fun (congr_fun hcomm 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.trace, Matrix.diag_apply,
    Fin.sum_univ_two, Matrix.mul_apply]
  linear_combination
    (2 * (U 0 1 * V 1 0 - U 1 0 * V 0 1)) * h00 -
    (2 * (U 0 0 * V 1 0 - U 1 0 * V 0 0 + U 1 0 * V 1 1 -
      U 1 1 * V 1 0)) * h01

omit [NumberField K] in
/-- In rank two, the discriminant of the (unnormalized) norm form on an ordered pair is its
trace-pairing discriminant. -/
theorem form_discriminant_discr (B : Basis (Fin 2) ℤ (𝓞 K)) (u v : 𝓞 K) :
    (intNorm (u + v) - intNorm u - intNorm v) ^ 2 - 4 * intNorm u * intNorm v =
      Algebra.discr ℤ (![u, v] : Fin 2 → 𝓞 K) := by
  let U := Algebra.leftMulMatrix B u
  let V := Algebra.leftMulMatrix B v
  have hcomm : U * V = V * U := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Algebra.trace_eq_matrix_trace B, intNorm,
    Algebra.norm_eq_matrix_det B]
  simpa [U, V, map_add, hcomm, pow_two] using det_polar_discr U V hcomm

/-- The first coefficient of the normalized ideal norm form. -/
noncomputable def coeffA (I : Ideal (𝓞 K)) (u : I) : ℤ :=
  intNorm (u : 𝓞 K) / (Ideal.absNorm I : ℤ)

/-- The mixed coefficient of the normalized ideal norm form. -/
noncomputable def coeffB (I : Ideal (𝓞 K)) (u v : I) : ℤ :=
  (intNorm ((u : 𝓞 K) + (v : 𝓞 K)) - intNorm (u : 𝓞 K) - intNorm (v : 𝓞 K)) /
    (Ideal.absNorm I : ℤ)

/-- The last coefficient of the normalized ideal norm form. -/
noncomputable def coeffC (I : Ideal (𝓞 K)) (v : I) : ℤ :=
  intNorm (v : 𝓞 K) / (Ideal.absNorm I : ℤ)

/-- The integral binary norm form associated to an ordered basis `(u, v)` of an ideal. -/
noncomputable def form (I : Ideal (𝓞 K)) (u v : I) : BQForm :=
  ⟨coeffA I u, coeffB I u v, coeffC I v⟩

/-- The normalized norm form attached to an ordered `Z`-basis of an integral ideal. -/
noncomputable def formOfBasis (I : Ideal (𝓞 K)) (b : Basis (Fin 2) ℤ I) :
    BQForm :=
  form I (b 0) (b 1)

theorem abs_norm_dvd (I : Ideal (𝓞 K)) (u : I) :
    (Ideal.absNorm I : ℤ) ∣ intNorm (u : 𝓞 K) :=
  Ideal.absNorm_dvd_norm_of_mem u.property

theorem abs_dvd_polarization (I : Ideal (𝓞 K)) (u v : I) :
    (Ideal.absNorm I : ℤ) ∣
      intNorm ((u : 𝓞 K) + (v : 𝓞 K)) - intNorm (u : 𝓞 K) - intNorm (v : 𝓞 K) := by
  exact (Ideal.absNorm_dvd_norm_of_mem (I.add_mem u.property v.property)).sub
    ((abs_norm_dvd I u).add (abs_norm_dvd I v)) |>.trans
      (by simp [intNorm, sub_sub])

theorem abs_norm_coeff (I : Ideal (𝓞 K)) (u : I) :
    (Ideal.absNorm I : ℤ) * coeffA I u = intNorm (u : 𝓞 K) := by
  rw [coeffA, mul_comm, Int.ediv_mul_cancel (abs_norm_dvd I u)]

theorem abs_coeff_b (I : Ideal (𝓞 K)) (u v : I) :
    (Ideal.absNorm I : ℤ) * coeffB I u v =
      intNorm ((u : 𝓞 K) + (v : 𝓞 K)) - intNorm (u : 𝓞 K) - intNorm (v : 𝓞 K) := by
  rw [coeffB, mul_comm, Int.ediv_mul_cancel (abs_dvd_polarization I u v)]

theorem abs_coeff_c (I : Ideal (𝓞 K)) (v : I) :
    (Ideal.absNorm I : ℤ) * coeffC I v = intNorm (v : 𝓞 K) := by
  rw [coeffC, mul_comm, Int.ediv_mul_cancel (abs_norm_dvd I v)]

/-- The defining evaluation identity for the normalized ideal norm form. -/
theorem abs_norm_form (B : Basis (Fin 2) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (u v : I) (x y : ℤ) :
    (Ideal.absNorm I : ℤ) * (form I u v).eval x y =
      intNorm (x • (u : 𝓞 K) + y • (v : 𝓞 K)) := by
  rw [linear_combination_basis B]
  simp only [form, BQForm.eval]
  calc
    (Ideal.absNorm I : ℤ) *
          (coeffA I u * x ^ 2 + coeffB I u v * x * y + coeffC I v * y ^ 2) =
        ((Ideal.absNorm I : ℤ) * coeffA I u) * x ^ 2 +
          ((Ideal.absNorm I : ℤ) * coeffB I u v) * x * y +
          ((Ideal.absNorm I : ℤ) * coeffC I v) * y ^ 2 := by ring
    _ = intNorm (u : 𝓞 K) * x ^ 2 +
          (intNorm ((u : 𝓞 K) + (v : 𝓞 K)) - intNorm (u : 𝓞 K) - intNorm (v : 𝓞 K)) *
            x * y + intNorm (v : 𝓞 K) * y ^ 2 := by
      rw [abs_norm_coeff, abs_coeff_b, abs_coeff_c]

/-- A nonzero ideal has positive absolute norm. -/
theorem absNorm_pos {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < Ideal.absNorm I :=
  Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
    (by simp [nonZeroDivisors, hI])

/-- For a nonzero ideal, the form really is the exact integral quotient of the element norm. -/
theorem eval_form (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (u v : I) (x y : ℤ) :
    (form I u v).eval x y =
      intNorm (x • (u : 𝓞 K) + y • (v : 𝓞 K)) / (Ideal.absNorm I : ℤ) := by
  symm
  apply Int.ediv_eq_of_eq_mul_left
  · exact_mod_cast (absNorm_pos hI).ne'
  · simpa [mul_comm] using (abs_norm_form B I u v x y).symm

/-- Evaluation of the norm form defined by an ordered ideal basis. -/
theorem eval_form_basis (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (b : Basis (Fin 2) ℤ I) (x y : ℤ) :
    (formOfBasis I b).eval x y =
      intNorm (x • (b 0 : 𝓞 K) + y • (b 1 : 𝓞 K)) / (Ideal.absNorm I : ℤ) := by
  exact eval_form B hI (b 0) (b 1) x y

/-- Apply a determinant-one matrix to an ordered pair in the same convention as
`BQForm.transform`. -/
def changeBasisPair (u v : 𝓞 K) (g : SL(2, ℤ)) : (𝓞 K) × (𝓞 K) :=
  (g 0 0 • u + g 1 0 • v, g 0 1 • u + g 1 1 • v)

/-- Proper change of an ideal basis gives the corresponding proper transform of its norm form. -/
theorem form_changeBasis (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (u v u' v' : I) (g : SL(2, ℤ))
    (hu' : (u' : 𝓞 K) = g 0 0 • (u : 𝓞 K) + g 1 0 • (v : 𝓞 K))
    (hv' : (v' : 𝓞 K) = g 0 1 • (u : 𝓞 K) + g 1 1 • (v : 𝓞 K)) :
    form I u' v' =
      (form I u v).transform g := by
  apply BQForm.ext
  · have h := abs_norm_form B I u' v' 1 0
    have h' := abs_norm_form B I u v (g 0 0) (g 1 0)
    simp only [one_smul, zero_smul, add_zero, hu'] at h
    simp only [BQForm.transform]
    apply mul_left_cancel₀ (show (Ideal.absNorm I : ℤ) ≠ 0 by exact_mod_cast (absNorm_pos hI).ne')
    simpa [BQForm.eval] using h.trans h'.symm
  · have h := abs_norm_form B I u' v' 1 1
    have h' := abs_norm_form B I u v (g 0 0 + g 0 1) (g 1 0 + g 1 1)
    simp only [one_smul, hu', hv'] at h
    simp only [BQForm.transform]
    apply mul_left_cancel₀ (show (Ideal.absNorm I : ℤ) ≠ 0 by exact_mod_cast (absNorm_pos hI).ne')
    have heq :
        (g 0 0 • (u : 𝓞 K) + g 1 0 • (v : 𝓞 K)) +
            (g 0 1 • (u : 𝓞 K) + g 1 1 • (v : 𝓞 K)) =
          (g 0 0 + g 0 1) • (u : 𝓞 K) + (g 1 0 + g 1 1) • (v : 𝓞 K) := by
      module
    rw [heq] at h
    have := h.trans h'.symm
    have ha :
        (Ideal.absNorm I : ℤ) * (form I u' v').a =
          (Ideal.absNorm I : ℤ) * ((form I u v).transform g).a := by
      have h0 := abs_norm_form B I u' v' 1 0
      have h0' := abs_norm_form B I u v (g 0 0) (g 1 0)
      simp only [one_smul, zero_smul, add_zero, hu', BQForm.eval,
        one_pow, mul_one, mul_zero] at h0 h0'
      simpa [BQForm.transform] using h0.trans h0'.symm
    have hc :
        (Ideal.absNorm I : ℤ) * (form I u' v').c =
          (Ideal.absNorm I : ℤ) * ((form I u v).transform g).c := by
      have h1 := abs_norm_form B I v' u' 1 0
      have h1' := abs_norm_form B I u v (g 0 1) (g 1 1)
      simp only [one_smul, zero_smul, add_zero, hv', BQForm.eval,
        one_pow, mul_one, mul_zero] at h1 h1'
      simpa [BQForm.transform] using h1.trans h1'.symm
    simp only [BQForm.eval] at this ⊢
    simp only [BQForm.transform] at ha hc
    ring_nf at this ha hc ⊢
    linarith
  · have h := abs_norm_form B I v' u' 1 0
    have h' := abs_norm_form B I u v (g 0 1) (g 1 1)
    simp only [one_smul, zero_smul, add_zero, hv'] at h
    simp only [BQForm.transform]
    apply mul_left_cancel₀ (show (Ideal.absNorm I : ℤ) ≠ 0 by exact_mod_cast (absNorm_pos hI).ne')
    simpa [BQForm.eval] using h.trans h'.symm

/-- Two ordered bases related by a determinant-one matrix yield properly equivalent norm forms. -/
theorem form_basis_change (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (b b' : Basis (Fin 2) ℤ I) (g : SL(2, ℤ))
    (h0 : (b' 0 : 𝓞 K) = g 0 0 • (b 0 : 𝓞 K) + g 1 0 • (b 1 : 𝓞 K))
    (h1 : (b' 1 : 𝓞 K) = g 0 1 • (b 0 : 𝓞 K) + g 1 1 • (b 1 : 𝓞 K)) :
    formOfBasis I b' = (formOfBasis I b).transform g := by
  exact form_changeBasis B hI (b 0) (b 1) (b' 0) (b' 1) g h0 h1

/-- In particular, determinant-one changes of ideal basis give equivalent forms. -/
theorem form_equivalent (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (b b' : Basis (Fin 2) ℤ I) (g : SL(2, ℤ))
    (h0 : (b' 0 : 𝓞 K) = g 0 0 • (b 0 : 𝓞 K) + g 1 0 • (b 1 : 𝓞 K))
    (h1 : (b' 1 : 𝓞 K) = g 0 1 • (b 0 : 𝓞 K) + g 1 1 • (b 1 : 𝓞 K)) :
    (formOfBasis I b).Equivalent (formOfBasis I b') := by
  exact ⟨g, form_basis_change B hI b b' g h0 h1⟩

/-- The discriminant of an ordered basis of an integral ideal is the field discriminant times
the square of the ideal norm. -/
theorem algebra_discr_basis (B : Basis (Fin 2) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (b : Basis (Fin 2) ℤ I) :
    Algebra.discr ℤ (fun i ↦ (b i : 𝓞 K)) =
      (Ideal.absNorm I : ℤ) ^ 2 * NumberField.discr K := by
  let f : Fin 2 → 𝓞 K := fun i ↦ (b i : 𝓞 K)
  let P : Matrix (Fin 2) (Fin 2) ℤ := B.toMatrix f
  have hdiscr := Algebra.discr_of_matrix_vecMul (B : Fin 2 → 𝓞 K) P
  have hvec : Matrix.vecMul B (P.map (algebraMap ℤ (𝓞 K))) = f := by
    exact B.toMatrix_map_vecMul f
  rw [hvec] at hdiscr
  have hnorm : P.det.natAbs = Ideal.absNorm I := by
    simpa [P, f, Basis.det_apply, Function.comp_def] using
      (Ideal.natAbs_det_basis_change B I b)
  have habs : |P.det| = (Ideal.absNorm I : ℤ) := by
    rw [← Int.natCast_natAbs, hnorm]
  have hsq : P.det ^ 2 = (Ideal.absNorm I : ℤ) ^ 2 := by
    rw [← habs, sq_abs]
  simpa [f, hsq, NumberField.discr_eq_discr K B] using hdiscr

/-- **Theorem 4.29 (discriminant part).**  The normalized norm form of an ordered basis of a
nonzero integral ideal in a quadratic number field has the field discriminant. -/
theorem form_basis_discriminant (B : Basis (Fin 2) ℤ (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (b : Basis (Fin 2) ℤ I) :
    (formOfBasis I b).discriminant = NumberField.discr K := by
  let n : ℤ := Ideal.absNorm I
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (absNorm_pos hI).ne'
  have ha := abs_norm_coeff I (b 0)
  have hb := abs_coeff_b I (b 0) (b 1)
  have hc := abs_coeff_c I (b 1)
  have hnormDiscr := form_discriminant_discr B
    (b 0 : 𝓞 K) (b 1 : 𝓞 K)
  have hidealDiscr := algebra_discr_basis B I b
  apply mul_left_cancel₀ (pow_ne_zero 2 hn)
  change n ^ 2 * (formOfBasis I b).discriminant = n ^ 2 * NumberField.discr K
  rw [← hidealDiscr]
  change n ^ 2 *
      (coeffB I (b 0) (b 1) ^ 2 - 4 * coeffA I (b 0) * coeffC I (b 1)) = _
  have hpair :
      Algebra.discr ℤ (fun i ↦ (b i : 𝓞 K)) =
        Algebra.discr ℤ (![b 0, b 1] : Fin 2 → 𝓞 K) := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hpair]
  rw [← hnormDiscr]
  change n * coeffA I (b 0) = _ at ha
  change n * coeffB I (b 0) (b 1) = _ at hb
  change n * coeffC I (b 1) = _ at hc
  calc
    n ^ 2 * (coeffB I (b 0) (b 1) ^ 2 - 4 * coeffA I (b 0) * coeffC I (b 1)) =
        (n * coeffB I (b 0) (b 1)) ^ 2 -
          4 * (n * coeffA I (b 0)) * (n * coeffC I (b 1)) := by ring
    _ = (intNorm ((b 0 : 𝓞 K) + (b 1 : 𝓞 K)) - intNorm (b 0 : 𝓞 K) -
          intNorm (b 1 : 𝓞 K)) ^ 2 -
        4 * intNorm (b 0 : 𝓞 K) * intNorm (b 1 : 𝓞 K) := by rw [ha, hb, hc]

end INForm

end

end Towers.NumberTheory.Milne
