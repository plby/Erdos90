import Towers.NumberTheory.Quadratic.FormNarrowEquivalence
import Towers.NumberTheory.Quadratic.IdealFormMap

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: ideal-to-form inverse

For a positively oriented basis `(u, v)` of a nonzero quadratic ideal `I`, put `n = N(I)` and
let `Q` be its normalized norm form.  If `b = B + 2r`, multiplication by the conjugate of `u`
identifies the two integral lattices

`(conj u) I = (n) (Z Q.a + Z (omega + r))`.

This is the integral principal-scaling identity proving that the form-to-ideal construction
returns the original ordinary ideal class.  In the imaginary case this is also the narrow class,
since there are no real embeddings.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField QuadraticAlgebra nonZeroDivisors
open Module

noncomputable section

namespace INForm

variable {A B : ℤ}

/-- The nontrivial conjugate in the coordinate quadratic order. -/
def orderConjugate (z : QOrd A B) : QOrd A B :=
  ⟨z.re + B * z.im, -z.im⟩

@[simp] theorem orderConjugate_re (z : QOrd A B) :
    (orderConjugate z).re = z.re + B * z.im :=
  rfl

@[simp] theorem orderConjugate_im (z : QOrd A B) :
    (orderConjugate z).im = -z.im :=
  rfl

/-- Multiplication by the conjugate gives the quadratic norm. -/
theorem orderConjugate_mul (z : QOrd A B) :
    orderConjugate z * z = ((QuadraticAlgebra.norm z : ℤ) : QOrd A B) := by
  apply QuadraticAlgebra.ext <;>
    simp [orderConjugate, QuadraticAlgebra.norm_def] <;> ring

/-- The imaginary coordinate of `conj(u) v` is the oriented coordinate determinant. -/
theorem order_conjugate_im (u v : QOrd A B) :
    (orderConjugate u * v).im = u.re * v.im - v.re * u.im := by
  simp [orderConjugate]
  ring

/-- The norm polarization is twice the real coordinate of `conj(u) v`, plus `B` times its
imaginary coordinate. -/
theorem polari_order_conju (u v : QOrd A B) :
    QuadraticAlgebra.norm (u + v) - QuadraticAlgebra.norm u - QuadraticAlgebra.norm v =
      2 * (orderConjugate u * v).re + B * (orderConjugate u * v).im := by
  simp [orderConjugate, QuadraticAlgebra.norm_def]
  ring

/-- The integral scaling identity, assuming the ordered coordinate determinant is the absolute
norm of the ideal.  The latter equality follows from positive orientation below. -/
theorem abs_mapped_form
    {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (b : Basis (Fin 2) ℤ I)
    (Q : BQForm) (hQ : Q = formOfBasis I b)
    (r : ℤ) (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (hdet : (e.symm (b 0 : 𝓞 K)).re * (e.symm (b 1 : 𝓞 K)).im -
      (e.symm (b 1 : 𝓞 K)).re * (e.symm (b 0 : 𝓞 K)).im = Ideal.absNorm I) :
    Ideal.span ({e (orderConjugate (e.symm (b 0 : 𝓞 K)))} : Set (𝓞 K)) * I =
      Ideal.span ({((Ideal.absNorm I : ℤ) : 𝓞 K)} : Set (𝓞 K)) *
        BQForm.mappedFormIdeal e Q r hb hdisc := by
  subst Q
  let Q := formOfBasis I b
  let n : ℤ := Ideal.absNorm I
  let u : QOrd A B := e.symm (b 0 : 𝓞 K)
  let v : QOrd A B := e.symm (b 1 : 𝓞 K)
  let ubar : QOrd A B := orderConjugate u
  let J : Ideal (𝓞 K) := BQForm.mappedFormIdeal e Q r hb hdisc
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (absNorm_pos hI).ne'
  have ha : n * Q.a = QuadraticAlgebra.norm u := by
    have h := abs_norm_coeff I (b 0)
    change n * Q.a = Algebra.norm ℤ (b 0 : 𝓞 K) at h
    rw [h]
    calc
      Algebra.norm ℤ (b 0 : 𝓞 K) = Algebra.norm ℤ (e u) := by simp [u]
      _ = QuadraticAlgebra.norm u :=
        BQForm.algebra_quadratic_order e u
  have hdelta : u.re * v.im - v.re * u.im = n := by
    simpa [u, v, n] using hdet
  have hmixed :
      n * Q.b = 2 * (ubar * v).re + B * (ubar * v).im := by
    have h := abs_coeff_b I (b 0) (b 1)
    change n * Q.b =
      Algebra.norm ℤ ((b 0 : 𝓞 K) + (b 1 : 𝓞 K)) -
        Algebra.norm ℤ (b 0 : 𝓞 K) - Algebra.norm ℤ (b 1 : 𝓞 K) at h
    rw [h]
    have hu : e u = (b 0 : 𝓞 K) := by simp [u]
    have hv : e v = (b 1 : 𝓞 K) := by simp [v]
    rw [← hu, ← hv, ← map_add,
      BQForm.algebra_quadratic_order,
      BQForm.algebra_quadratic_order,
      BQForm.algebra_quadratic_order]
    exact polari_order_conju u v
  have hu_im : (ubar * v).im = n := by
    rw [order_conjugate_im]
    exact hdelta
  have hu_re : (ubar * v).re = n * r := by
    rw [hu_im, hb] at hmixed
    nlinarith
  have huu : ubar * u = (n * Q.a : ℤ) := by
    rw [orderConjugate_mul, ← ha]
  have huv : ubar * v = n • (ω + (r : QOrd A B)) := by
    apply QuadraticAlgebra.ext
    · simp [hu_re]
    · simp [hu_im]
  have hscale0 : e ubar * (b 0 : 𝓞 K) =
      (n : 𝓞 K) * e (Q.a : QOrd A B) := by
    rw [← show e u = (b 0 : 𝓞 K) by simp [u], ← map_mul, huu]
    simp
  have hscale1 : e ubar * (b 1 : 𝓞 K) =
      (n : 𝓞 K) * e (ω + (r : QOrd A B)) := by
    rw [← show e v = (b 1 : 𝓞 K) by simp [v], ← map_mul, huv]
    simp [Algebra.smul_def]
  ext z
  simp only [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let xb := b.repr ⟨x, hx⟩
    have hxsum : x = xb 0 • (b 0 : 𝓞 K) + xb 1 • (b 1 : 𝓞 K) := by
      have h := b.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_two] at h
      exact congrArg Subtype.val h.symm
    refine ⟨xb 0 • e (Q.a : QOrd A B) +
      xb 1 • e (ω + (r : QOrd A B)), ?_, ?_⟩
    · change _ ∈ BQForm.mappedFormIdeal e Q r hb hdisc
      rw [BQForm.mappedFormIdeal]
      have hpre : xb 0 • (Q.a : QOrd A B) +
          xb 1 • (ω + (r : QOrd A B)) ∈ Q.toIdeal r hb hdisc := by
        apply (BQForm.lattice_ideal A B Q.a r Q.c
          (Q.lattice_relation r hb hdisc) _).mpr
        exact ⟨xb 0, xb 1, rfl⟩
      simpa using (Ideal.mem_map_of_mem e hpre)
    · have hscale0' := hscale0
      have hscale1' := hscale1
      dsimp only [n, ubar, u] at hscale0' hscale1'
      rw [hxsum]
      calc
        ((Ideal.absNorm I : ℤ) : 𝓞 K) *
              (xb 0 • e (Q.a : QOrd A B) +
                xb 1 • e (ω + (r : QOrd A B))) =
            xb 0 • (((Ideal.absNorm I : ℤ) : 𝓞 K) * e (Q.a : QOrd A B)) +
              xb 1 • (((Ideal.absNorm I : ℤ) : 𝓞 K) *
                e (ω + (r : QOrd A B))) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm]
        _ = xb 0 • (e (orderConjugate (e.symm (b 0 : 𝓞 K))) * (b 0 : 𝓞 K)) +
              xb 1 • (e (orderConjugate (e.symm (b 0 : 𝓞 K))) * (b 1 : 𝓞 K)) := by
          rw [hscale0', hscale1']
        _ = e (orderConjugate (e.symm (b 0 : 𝓞 K))) *
              (xb 0 • (b 0 : 𝓞 K) + xb 1 • (b 1 : 𝓞 K)) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm]
  · rintro ⟨x, hx, rfl⟩
    change x ∈ BQForm.mappedFormIdeal e Q r hb hdisc at hx
    rw [BQForm.mappedFormIdeal] at hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_of_equiv e x).mp hx
    obtain ⟨s, t, hst⟩ :=
      (BQForm.lattice_ideal A B Q.a r Q.c
        (Q.lattice_relation r hb hdisc) y).mp hy
    refine ⟨s • (b 0 : 𝓞 K) + t • (b 1 : 𝓞 K), ?_, ?_⟩
    · exact I.add_mem (I.toAddSubgroup.zsmul_mem (b 0).property s)
        (I.toAddSubgroup.zsmul_mem (b 1).property t)
    · have hmap : e y = s • e (Q.a : QOrd A B) +
          t • e (ω + (r : QOrd A B)) := by
        rw [hst]
        simp
      have hscale0' := hscale0
      have hscale1' := hscale1
      dsimp only [n, ubar, u] at hscale0' hscale1'
      calc
        e (orderConjugate (e.symm (b 0 : 𝓞 K))) *
              (s • (b 0 : 𝓞 K) + t • (b 1 : 𝓞 K)) =
            s • (e (orderConjugate (e.symm (b 0 : 𝓞 K))) * (b 0 : 𝓞 K)) +
              t • (e (orderConjugate (e.symm (b 0 : 𝓞 K))) * (b 1 : 𝓞 K)) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm]
        _ = s • (((Ideal.absNorm I : ℤ) : 𝓞 K) * e (Q.a : QOrd A B)) +
              t • (((Ideal.absNorm I : ℤ) : 𝓞 K) *
                e (ω + (r : QOrd A B))) := by
          rw [hscale0', hscale1']
        _ = ((Ideal.absNorm I : ℤ) : 𝓞 K) *
              (s • e (Q.a : QOrd A B) +
                t • e (ω + (r : QOrd A B))) := by
          rw [mul_add, mul_smul_comm, mul_smul_comm]
        _ = ((Ideal.absNorm I : ℤ) : 𝓞 K) * e y := by rw [hmap]

/-- Relative to the standard quadratic ring-of-integers basis, the coordinate matrix of an
ideal basis is the matrix of the explicit real and `omega` coordinates. -/
theorem basis_matrix_integers
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    {I : Ideal (𝓞 (QFModel d))} (b : Basis (Fin 2) ℤ I) :
    basisCoordinateMatrix (quadraticIntegersBasis hd hd1) b =
      !![(integersQuadraticOrder hd hd1 (b 0 : 𝓞 _)).re,
        (integersQuadraticOrder hd hd1 (b 1 : 𝓞 _)).re;
        (integersQuadraticOrder hd hd1 (b 0 : 𝓞 _)).im,
        (integersQuadraticOrder hd hd1 (b 1 : 𝓞 _)).im] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisCoordinateMatrix, quadraticIntegersBasis,
      Basis.toMatrix_apply, Basis.map_repr, QuadraticAlgebra.basis_repr_apply]

/-- Positive orientation chooses the positive sign in the determinant formula for ideal norm. -/
theorem det_positively_oriented
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (I : Ideal (𝓞 (QFModel d))) (b : Basis (Fin 2) ℤ I)
    (hb : IsPositivelyOriented (quadraticIntegersBasis hd hd1) b) :
    (integersQuadraticOrder hd hd1 (b 0 : 𝓞 _)).re *
          (integersQuadraticOrder hd hd1 (b 1 : 𝓞 _)).im -
        (integersQuadraticOrder hd hd1 (b 1 : 𝓞 _)).re *
          (integersQuadraticOrder hd hd1 (b 0 : 𝓞 _)).im =
      Ideal.absNorm I := by
  let M := basisCoordinateMatrix (quadraticIntegersBasis hd hd1) b
  have hM := basis_matrix_integers hd hd1 b
  change M = _ at hM
  have hnorm := Ideal.natAbs_det_basis_change
    (quadraticIntegersBasis hd hd1) I b
  rw [Basis.det_apply] at hnorm
  change M.det.natAbs = Ideal.absNorm I at hnorm
  have habs : |M.det| = (Ideal.absNorm I : ℤ) := by
    rw [← Int.natCast_natAbs, hnorm]
  have hpos : 0 < M.det := hb
  rw [abs_of_pos hpos] at habs
  rw [hM, Matrix.det_fin_two_of] at habs
  exact habs

/-- **Theorem 4.29, ideal-to-form-to-ideal inverse.**  For a positively oriented basis of a
nonzero integral ideal in the explicit quadratic field, the ideal reconstructed from its
normalized norm form represents the original ordinary ideal class. -/
theorem mapped_form_basis
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b : PositivelyOrientedBasis (quadraticIntegersBasis hd hd1) I)
    (r : ℤ)
    (hb : (formOfBasis I b.1).b = quadraticParameterB d + 2 * r)
    (hdisc : (formOfBasis I b.1).discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d) :
    ClassGroup.mk0
        ⟨BQForm.mappedFormIdeal
            (integersQuadraticOrder hd hd1).symm
            (formOfBasis I b.1) r hb hdisc,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            rw [BQForm.mappedFormIdeal]
            intro hbot
            have hb0 : (b.1 0 : 𝓞 (QFModel d)) ≠ 0 := by
              intro hz
              apply Basis.ne_zero b.1 (0 : Fin 2)
              exact Subtype.ext hz
            have hnorm : Algebra.norm ℤ (b.1 0 : 𝓞 (QFModel d)) ≠ 0 :=
              Algebra.norm_ne_zero_iff.mpr hb0
            have ha : (formOfBasis I b.1).a ≠ 0 := by
              intro ha
              have hmul := abs_norm_coeff I (b.1 0)
              change (Ideal.absNorm I : ℤ) * (formOfBasis I b.1).a =
                Algebra.norm ℤ (b.1 0 : 𝓞 (QFModel d)) at hmul
              rw [ha, mul_zero] at hmul
              exact hnorm hmul.symm
            apply (formOfBasis I b.1).ideal_ne r hb hdisc ha
            exact (Ideal.map_eq_bot_iff_of_injective
              (integersQuadraticOrder hd hd1).symm.injective).mp hbot)⟩ =
      ClassGroup.mk0
        ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ := by
  let e := (integersQuadraticOrder hd hd1).symm
  let Q := formOfBasis I b.1
  let u : QOrd (quadraticOrderParameter d) (quadraticParameterB d) :=
    e.symm (b.1 0 : 𝓞 (QFModel d))
  let ubar := orderConjugate u
  have hdet := det_positively_oriented hd hd1 I b.1 b.2
  have hscale :=
    abs_mapped_form
      e I hI b.1 Q rfl r hb hdisc (by simpa [e, u] using hdet)
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  have hn : ((Ideal.absNorm I : ℤ) : 𝓞 (QFModel d)) ≠ 0 := by
    exact_mod_cast (absNorm_pos hI).ne'
  have hu : u ≠ 0 := by
    intro hu
    have hb0 : (b.1 0 : 𝓞 (QFModel d)) ≠ 0 := by
      intro hz
      apply Basis.ne_zero b.1 (0 : Fin 2)
      exact Subtype.ext hz
    apply hb0
    rw [← e.apply_symm_apply (b.1 0 : 𝓞 (QFModel d)), show e.symm
      (b.1 0 : 𝓞 (QFModel d)) = u by rfl, hu, map_zero]
  have hubar : ubar ≠ 0 := by
    intro hzero
    apply hu
    have hre : u.re + quadraticParameterB d * u.im = 0 := by
      simpa [ubar, orderConjugate] using congrArg QuadraticAlgebra.re hzero
    have him : -u.im = 0 := by
      simpa [ubar, orderConjugate] using congrArg QuadraticAlgebra.im hzero
    have him0 : u.im = 0 := neg_eq_zero.mp him
    have hre0 : u.re = 0 := by simpa [him0] using hre
    apply QuadraticAlgebra.ext <;> simp [hre0, him0]
  have heubar : e ubar ≠ 0 := by
    intro hzero
    apply hubar
    apply e.injective
    simpa using hzero
  refine ⟨((Ideal.absNorm I : ℤ) : 𝓞 (QFModel d)), e ubar, hn, heubar, ?_⟩
  simpa [e, Q, u, ubar] using hscale.symm

/-- The invertible fractional ideal reconstructed from the norm form of a positive-leading
ordered ideal basis. -/
noncomputable def mappedFormBasis
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (I : Ideal (𝓞 (QFModel d)))
    (b : Basis (Fin 2) ℤ I) (ha : 0 < (formOfBasis I b).a)
    (r : ℤ) (hb : (formOfBasis I b).b = quadraticParameterB d + 2 * r)
    (hdisc : (formOfBasis I b).discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d) :
    (FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d))ˣ :=
  BQForm.mappedFormUnit
    (K := QFModel d)
    (A := quadraticOrderParameter d) (B := quadraticParameterB d)
    (integersQuadraticOrder hd hd1).symm
    (formOfBasis I b) r hb hdisc ha.ne'

/-- **Theorem 4.29, narrow ideal-to-form-to-ideal inverse.**  If the normalized norm form
of a positively oriented basis has positive leading coefficient, then the ideal reconstructed
from that form represents the original narrow ideal class. -/
theorem narrow_mapped_form
    {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    [Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r)]
    [Module.Finite ℚ (QFModel d)]
    [NumberField (QFModel d)]
    (I : Ideal (𝓞 (QFModel d))) (hI : I ≠ ⊥)
    (b : PositivelyOrientedBasis (quadraticIntegersBasis hd hd1) I)
    (ha : 0 < (formOfBasis I b.1).a)
    (r : ℤ)
    (hb : (formOfBasis I b.1).b = quadraticParameterB d + 2 * r)
    (hdisc : (formOfBasis I b.1).discriminant =
      quadraticParameterB d ^ 2 + 4 * quadraticOrderParameter d) :
    NCGroup.mk (QFModel d)
        (mappedFormBasis hd hd1 I b.1 ha r hb hdisc) =
      NCGroup.mk (QFModel d)
        (FractionalIdeal.mk0 (QFModel d)
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩) := by
  let e := (integersQuadraticOrder hd hd1).symm
  let Q := formOfBasis I b.1
  let n : ℤ := Ideal.absNorm I
  let u : QOrd (quadraticOrderParameter d) (quadraticParameterB d) :=
    e.symm (b.1 0 : 𝓞 (QFModel d))
  let ubar := orderConjugate u
  let nInt : 𝓞 (QFModel d) := (n : ℤ)
  let ubarInt : 𝓞 (QFModel d) := e ubar
  let J : Ideal (𝓞 (QFModel d)) :=
    BQForm.mappedFormIdeal e Q r hb hdisc
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast absNorm_pos hI
  have hdet := det_positively_oriented hd hd1 I b.1 b.2
  have hscale : Ideal.span ({ubarInt} : Set (𝓞 (QFModel d))) * I =
      Ideal.span ({nInt} : Set (𝓞 (QFModel d))) * J := by
    simpa [e, Q, n, u, ubar, ubarInt, nInt, J] using
      (abs_mapped_form
        e I hI b.1 Q rfl r hb hdisc (by simpa [e, u] using hdet))
  have hunorm : QuadraticAlgebra.norm u = n * Q.a := by
    have h := abs_norm_coeff I (b.1 0)
    change n * Q.a = Algebra.norm ℤ (b.1 0 : 𝓞 (QFModel d)) at h
    rw [h]
    symm
    calc
      Algebra.norm ℤ (b.1 0 : 𝓞 (QFModel d)) = Algebra.norm ℤ (e u) := by
        simp [u]
      _ = QuadraticAlgebra.norm u :=
        BQForm.algebra_quadratic_order e u
  have hubarNorm : QuadraticAlgebra.norm ubar = n * Q.a := by
    rw [show QuadraticAlgebra.norm ubar = QuadraticAlgebra.norm u by
      simp [ubar, orderConjugate, QuadraticAlgebra.norm_def]
      ring]
    exact hunorm
  have hnormUbarInt : Algebra.norm ℤ ubarInt = n * Q.a := by
    change Algebra.norm ℤ (e ubar) = _
    rw [BQForm.algebra_quadratic_order]
    exact hubarNorm
  have hnormNInt : Algebra.norm ℤ nInt = n ^ 2 := by
    have hnInt : nInt = e (n : QOrd
        (quadraticOrderParameter d) (quadraticParameterB d)) := by
      simp [nInt, e]
    rw [hnInt, BQForm.algebra_quadratic_order,
      QuadraticAlgebra.norm_intCast]
    norm_cast
  have hnormUbar : Algebra.norm ℚ (ubarInt : QFModel d) =
      ((n * Q.a : ℤ) : ℚ) := by
    calc
      Algebra.norm ℚ (ubarInt : QFModel d) =
          ((Algebra.norm ℤ ubarInt : ℤ) : ℚ) := (Algebra.coe_norm_int ubarInt).symm
      _ = ((n * Q.a : ℤ) : ℚ) := by rw [hnormUbarInt]
  have hnormN : Algebra.norm ℚ (nInt : QFModel d) = (n : ℚ) ^ 2 := by
    calc
      Algebra.norm ℚ (nInt : QFModel d) =
          ((Algebra.norm ℤ nInt : ℤ) : ℚ) := (Algebra.coe_norm_int nInt).symm
      _ = (n : ℚ) ^ 2 := by rw [hnormNInt]; norm_cast
  have hubarInt : ubarInt ≠ 0 := by
    intro hzero
    have hnormZero : Algebra.norm ℤ ubarInt = 0 := by rw [hzero]; simp
    rw [hnormUbarInt] at hnormZero
    exact (mul_pos hnpos ha).ne' hnormZero
  have hnInt : nInt ≠ 0 := by
    intro hzero
    have hnormZero : Algebra.norm ℤ nInt = 0 := by rw [hzero]; simp
    rw [hnormNInt] at hnormZero
    exact (pow_ne_zero 2 hnpos.ne') hnormZero
  let x : QFModel d :=
    (nInt : QFModel d) / (ubarInt : QFModel d)
  have hx : x ≠ 0 := div_ne_zero (by
      intro h
      exact hnInt (Subtype.ext h)) (by
      intro h
      exact hubarInt (Subtype.ext h))
  have hnormX : 0 < Algebra.norm ℚ x := by
    change 0 < Algebra.norm ℚ
      ((nInt : QFModel d) / (ubarInt : QFModel d))
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, hnormN, hnormUbar]
    exact mul_pos (sq_pos_of_pos (by exact_mod_cast hnpos))
      (inv_pos.mpr (by exact_mod_cast mul_pos hnpos ha))
  obtain ⟨epsilon, hepsilon, htotal⟩ :=
    QTPositi.sign_totally_positive x hx hnormX
  let numerator : 𝓞 (QFModel d) :=
    (epsilon : 𝓞 (QFModel d)) * nInt
  let t : QFModel d := (epsilon : QFModel d) * x
  have ht : ITPos (QFModel d) t := htotal
  have ht_ne : t ≠ 0 := by
    rcases hepsilon with rfl | rfl
    · simpa [t] using hx
    · simpa [t] using hx
  let tUnit : (QFModel d)ˣ := Units.mk0 t ht_ne
  have hnumeratorSpan :
      Ideal.span ({numerator} : Set (𝓞 (QFModel d))) =
        Ideal.span ({nInt} : Set (𝓞 (QFModel d))) := by
    rcases hepsilon with rfl | rfl
    · simp [numerator]
    · simpa only [numerator, Int.cast_neg, Int.cast_one, neg_mul, one_mul] using
        Ideal.span_singleton_neg nInt
  have hubarMem : ubarInt ∈ (𝓞 (QFModel d))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hubarInt
  have ht_fraction :
      t = IsLocalization.mk' (QFModel d) numerator ⟨ubarInt, hubarMem⟩ := by
    rw [IsFractionRing.mk'_eq_div]
    simp only [t, x, numerator, map_mul, map_intCast,
      NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [mul_div_assoc]
  have hIntegralScale :
      Ideal.span ({numerator} : Set (𝓞 (QFModel d))) * J =
        Ideal.span ({ubarInt} : Set (𝓞 (QFModel d))) * I := by
    rw [hnumeratorSpan]
    exact hscale.symm
  have hFractionalScale :
      FractionalIdeal.spanSingleton (𝓞 (QFModel d))⁰ t *
          (J : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) =
        (I : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) := by
    rw [ht_fraction]
    exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal
      (QFModel d) hubarMem).mpr hIntegralScale
  apply (QuotientGroup.mk'_eq_mk'
    (NarrowPrincipalIdeals (QFModel d))).mpr
  refine ⟨toPrincipalIdeal (𝓞 (QFModel d)) (QFModel d) tUnit, ?_, ?_⟩
  · exact ⟨⟨tUnit, by simpa [tUnit] using ht⟩, rfl⟩
  · apply Units.ext
    simp only [Units.val_mul, mappedFormBasis,
      BQForm.coe_mapped_form, coe_toPrincipalIdeal]
    change
      (J : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d)) *
          FractionalIdeal.spanSingleton (𝓞 (QFModel d))⁰ t =
        (I : FractionalIdeal (𝓞 (QFModel d))⁰ (QFModel d))
    simpa only [mul_comm] using hFractionalScale

end INForm

end

end Towers.NumberTheory.Milne
