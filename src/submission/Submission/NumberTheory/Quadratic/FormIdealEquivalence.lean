import Submission.NumberTheory.Quadratic.FormIdealClass

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: equivalent forms give equivalent ideals

This file proves the integral-ideal identity underlying descent of the explicit form-to-ideal
construction through proper equivalence.  Write `tau = omega + r` and let

`g = !![p, q; s, t] in SL(2, Z)`.

If `Q' = Q.transform g`, then its first coefficient is the normalized norm of
`alpha = p a + s tau`.  Multiplication by the conjugate of `alpha` carries the transformed
basis of the ideal of `Q` to `a` times the evident basis of the ideal of `Q'`.  Consequently

`(a) I(Q') = (conj alpha) I(Q)`.

This is the exact principal-scaling relation needed for the ideal-class part of Theorem 4.29.
-/

namespace Submission.NumberTheory.Milne

open scoped MatrixGroups NumberField QuadraticAlgebra

namespace BQForm

variable {A B : ℤ}

/-- The conjugate of the first vector in the basis obtained from the evident basis of the
form ideal by an `SL(2, Z)` change of variables. -/
def conjugateBasisVector (Q : BQForm) (r : ℤ)
    (g : SL(2, ℤ)) : QOrd A B :=
  g 0 0 • (Q.a : QOrd A B) +
    g 1 0 • (((B + r : ℤ) : QOrd A B) - ω)

/-- The first transformed basis vector times its conjugate is `a a'`, where `a'` is the
leading coefficient of the transformed form. -/
theorem conjugate_basis_vector
    (Q : BQForm) (r : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    conjugateBasisVector (A := A) (B := B) Q r g *
        (g 0 0 • (Q.a : QOrd A B) +
          g 1 0 • (ω + (r : QOrd A B))) =
      ((Q.a * (Q.transform g).a : ℤ) : QOrd A B) := by
  have hrel := Q.lattice_relation r hb hdisc
  have hA : A = r ^ 2 + B * r - Q.a * Q.c := by linarith
  apply QuadraticAlgebra.ext
  · simp only [conjugateBasisVector, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_intCast,
      BQForm.transform]
    norm_num
    rw [hb, hA]
    ring
  · simp [conjugateBasisVector]
    ring

/-- The conjugate first vector times the second transformed vector is `a` times the second
evident generator of the ideal belonging to the transformed form. -/
theorem conjugate_vector_second
    (Q : BQForm) (r r' : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hb' : (Q.transform g).b = B + 2 * r')
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    conjugateBasisVector (A := A) (B := B) Q r g *
        (g 0 1 • (Q.a : QOrd A B) +
          g 1 1 • (ω + (r : QOrd A B))) =
      Q.a • (ω + (r' : QOrd A B)) := by
  have hrel := Q.lattice_relation r hb hdisc
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hpt : g 0 0 * g 1 1 = 1 + g 0 1 * g 1 0 := by linarith
  have hr' :
      r' = Q.a * g 0 0 * g 0 1 + Q.b * g 0 1 * g 1 0 +
        Q.c * g 1 0 * g 1 1 + r := by
    simp only [BQForm.transform] at hb'
    rw [hb, hpt] at hb'
    rw [hb]
    ring_nf at hb' ⊢
    omega
  have hA : A = r ^ 2 + B * r - Q.a * Q.c := by linarith
  apply QuadraticAlgebra.ext
  · simp only [conjugateBasisVector, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      BQForm.transform] at hb' ⊢
    norm_num
    rw [hA, hr', hb]
    have hh := congrArg (fun z : ℤ => Q.a * r * z) hdet
    dsimp at hh
    linear_combination hh
  · simp only [conjugateBasisVector, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    norm_num
    linear_combination Q.a * hdet

/-- **Theorem 4.29 (proper-equivalence scaling identity).**  Ideals attached to forms related
by an `SL(2, Z)` change of variables differ by the explicitly displayed principal scaling.
The equality is stated integrally, so it does not require a fractional-ideal API or any choice
of ideal representatives. -/
theorem span_leading_transform
    (Q : BQForm) (r r' : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hb' : (Q.transform g).b = B + 2 * r')
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    Ideal.span ({(Q.a : QOrd A B)} : Set (QOrd A B)) *
        (Q.transform g).toIdeal r' hb'
          ((Q.discriminant_transform g).trans hdisc) =
      Ideal.span ({conjugateBasisVector (A := A) (B := B) Q r g} :
          Set (QOrd A B)) * Q.toIdeal r hb hdisc := by
  let Q' := Q.transform g
  let I := Q.toIdeal r hb hdisc
  let I' := Q'.toIdeal r' hb' ((Q.discriminant_transform g).trans hdisc)
  let alphaBar := conjugateBasisVector (A := A) (B := B) Q r g
  let alpha : QOrd A B :=
    g 0 0 • (Q.a : QOrd A B) +
      g 1 0 • (ω + (r : QOrd A B))
  let beta : QOrd A B :=
    g 0 1 • (Q.a : QOrd A B) +
      g 1 1 • (ω + (r : QOrd A B))
  have haa : alphaBar * alpha = ((Q.a * Q'.a : ℤ) : QOrd A B) := by
    exact conjugate_basis_vector Q r g hb hdisc
  have hab : alphaBar * beta = Q.a • (ω + (r' : QOrd A B)) := by
    exact conjugate_vector_second Q r r' g hb hb' hdisc
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hscale (x y : ℤ) :
      alphaBar * (x • alpha + y • beta) =
        (Q.a : QOrd A B) *
          (x • (Q'.a : QOrd A B) +
            y • (ω + (r' : QOrd A B))) := by
    calc
      alphaBar * (x • alpha + y • beta) =
          x • (alphaBar * alpha) + y • (alphaBar * beta) := by
        rw [mul_add, mul_smul_comm, mul_smul_comm]
      _ = x • (((Q.a * Q'.a : ℤ) : QOrd A B)) +
          y • (Q.a • (ω + (r' : QOrd A B))) := by rw [haa, hab]
      _ = (Q.a : QOrd A B) *
          (x • (Q'.a : QOrd A B) +
            y • (ω + (r' : QOrd A B))) := by
        simp [Algebra.smul_def, Int.cast_mul, mul_add,
          mul_comm, mul_left_comm, mul_assoc]
  ext z
  simp only [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨z', hz', rfl⟩
    obtain ⟨x, y, hxy⟩ :=
      (lattice_ideal A B Q'.a r' Q'.c
        (Q'.lattice_relation r' hb' ((Q.discriminant_transform g).trans hdisc)) z').mp hz'
    refine ⟨x • alpha + y • beta, ?_, ?_⟩
    · apply (lattice_ideal A B Q.a r Q.c
        (Q.lattice_relation r hb hdisc) _).mpr
      refine ⟨x * g 0 0 + y * g 0 1, x * g 1 0 + y * g 1 1, ?_⟩
      simp only [alpha, beta]
      module
    · rw [hxy]
      change alphaBar * (x • alpha + y • beta) =
        (Q.a : QOrd A B) *
          (x • (Q'.a : QOrd A B) + y • (ω + (r' : QOrd A B)))
      exact hscale x y
  · rintro ⟨z', hz', rfl⟩
    obtain ⟨x, y, hxy⟩ :=
      (lattice_ideal A B Q.a r Q.c
        (Q.lattice_relation r hb hdisc) z').mp hz'
    let X := g 1 1 * x - g 0 1 * y
    let Y := -(g 1 0) * x + g 0 0 * y
    have hX : X * g 0 0 + Y * g 0 1 = x := by
      dsimp [X, Y]
      linear_combination x * hdet
    have hY : X * g 1 0 + Y * g 1 1 = y := by
      dsimp [X, Y]
      linear_combination y * hdet
    refine ⟨X • (Q'.a : QOrd A B) +
      Y • (ω + (r' : QOrd A B)), ?_, ?_⟩
    · apply (lattice_ideal A B Q'.a r' Q'.c
        (Q'.lattice_relation r' hb' ((Q.discriminant_transform g).trans hdisc)) _).mpr
      exact ⟨X, Y, rfl⟩
    · rw [hxy]
      have hrecover : x • (Q.a : QOrd A B) +
          y • (ω + (r : QOrd A B)) =
          X • alpha + Y • beta := by
        calc
          x • (Q.a : QOrd A B) + y • (ω + (r : QOrd A B)) =
              (X * g 0 0 + Y * g 0 1) • (Q.a : QOrd A B) +
                (X * g 1 0 + Y * g 1 1) • (ω + (r : QOrd A B)) := by
            rw [hX, hY]
          _ = X • alpha + Y • beta := by
            simp only [alpha, beta]
            module
      rw [hrecover]
      change (Q.a : QOrd A B) *
          (X • (Q'.a : QOrd A B) + Y • (ω + (r' : QOrd A B))) =
        alphaBar * (X • alpha + Y • beta)
      exact (hscale X Y).symm

/-- The scaling identity after transporting both form ideals to the ring of integers of a
quadratic number field. -/
theorem leading_mapped_transform
    {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K)
    (Q : BQForm) (r r' : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hb' : (Q.transform g).b = B + 2 * r')
    (hdisc : Q.discriminant = B ^ 2 + 4 * A) :
    Ideal.span ({e Q.a} : Set (𝓞 K)) *
        mappedFormIdeal e (Q.transform g) r' hb'
          ((Q.discriminant_transform g).trans hdisc) =
      Ideal.span ({e (conjugateBasisVector (A := A) (B := B) Q r g)} :
          Set (𝓞 K)) * mappedFormIdeal e Q r hb hdisc := by
  have h := congrArg (Ideal.map e)
    (span_leading_transform Q r r' g hb hb' hdisc)
  simpa only [mappedFormIdeal, Ideal.map_mul, Ideal.map_span, Set.image_singleton] using h

/-- Properly equivalent positive-leading forms define the same ordinary ideal class.  The
stronger narrow-class statement additionally requires choosing the sign of the displayed
principal multiplier at the real embeddings. -/
theorem mapped_form_transform
    {K : Type*} [Field K] [NumberField K]
    (e : QOrd A B ≃+* 𝓞 K)
    (Q : BQForm) (r r' : ℤ) (g : SL(2, ℤ))
    (hb : Q.b = B + 2 * r)
    (hb' : (Q.transform g).b = B + 2 * r')
    (hdisc : Q.discriminant = B ^ 2 + 4 * A)
    (ha : Q.a ≠ 0) (ha' : (Q.transform g).a ≠ 0) :
    ClassGroup.mk0
        ⟨mappedFormIdeal e Q r hb hdisc,
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            rw [mappedFormIdeal]
            intro h
            apply Q.ideal_ne r hb hdisc ha
            exact (Ideal.map_eq_bot_iff_of_injective e.injective).mp h)⟩ =
      ClassGroup.mk0
        ⟨mappedFormIdeal e (Q.transform g) r' hb'
            ((Q.discriminant_transform g).trans hdisc),
          mem_nonZeroDivisors_iff_ne_zero.mpr (by
            rw [mappedFormIdeal]
            intro h
            apply (Q.transform g).ideal_ne r' hb'
              ((Q.discriminant_transform g).trans hdisc) ha'
            exact (Ideal.map_eq_bot_iff_of_injective e.injective).mp h)⟩ := by
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  let alphaBar := conjugateBasisVector (A := A) (B := B) Q r g
  let alpha : QOrd A B :=
    g 0 0 • (Q.a : QOrd A B) +
      g 1 0 • (ω + (r : QOrd A B))
  have haa : alphaBar * alpha =
      ((Q.a * (Q.transform g).a : ℤ) : QOrd A B) :=
    conjugate_basis_vector Q r g hb hdisc
  have hprod : ((Q.a * (Q.transform g).a : ℤ) : QOrd A B) ≠ 0 := by
    intro h
    have hre := congrArg QuadraticAlgebra.re h
    simp only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero] at hre
    exact (mul_ne_zero ha ha') hre
  have halphaBar : alphaBar ≠ 0 := by
    intro h
    apply hprod
    rw [← haa, h, zero_mul]
  have halphaBarMap : e alphaBar ≠ 0 := by
    simpa using e.injective.ne halphaBar
  have haOrder : (Q.a : QOrd A B) ≠ 0 := by
    intro h
    apply ha
    have hre := congrArg QuadraticAlgebra.re h
    simpa only [QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_zero] using hre
  have haMap : e Q.a ≠ 0 := by
    simpa using e.injective.ne haOrder
  refine ⟨e alphaBar, e Q.a, halphaBarMap, haMap, ?_⟩
  · exact (leading_mapped_transform e Q r r' g hb hb' hdisc).symm

end BQForm

end Submission.NumberTheory.Milne
