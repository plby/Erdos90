import Submission.NumberTheory.Quadratic.BinaryQuadraticForms

/-!
# Milne, Algebraic Number Theory, Theorem 4.29: the form-side target

Milne's printed target in Theorem 4.29 needs a sign convention when the
fundamental discriminant is negative: norm forms of imaginary quadratic ideals
are positive definite, whereas the negative of such a form is not properly
equivalent to it.  This file defines the corrected target.  For positive
discriminant no positivity condition is imposed, since those forms are
indefinite; orientation there is carried by proper (`SL₂(ℤ)`) equivalence and
the narrow ideal-class relation on the ideal side.
-/

namespace Submission.NumberTheory.Milne

open scoped MatrixGroups

namespace BQForm

/-- The coefficient criterion for a real binary quadratic form to be positive definite. -/
def IsPositiveDefinite (Q : BQForm) : Prop :=
  0 < Q.a ∧ Q.discriminant < 0

/-- Completing the square expresses a binary quadratic form in terms of its
leading coefficient and discriminant. -/
theorem four_mul_eval (Q : BQForm) (x y : ℤ) :
    4 * Q.a * Q.eval x y =
      (2 * Q.a * x + Q.b * y) ^ 2 - Q.discriminant * y ^ 2 := by
  simp only [eval, discriminant]
  ring

/-- A positive-definite integral binary quadratic form is positive at every
nonzero integral pair. -/
theorem pos_positive_definite {Q : BQForm}
    (hQ : Q.IsPositiveDefinite) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < Q.eval x y := by
  rcases hQ with ⟨ha, hdisc⟩
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by simpa using hxy
    simp only [eval, mul_zero, add_zero, pow_two]
    exact mul_pos ha (mul_self_pos.mpr hx)
  · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    have hsquare : 0 ≤ (2 * Q.a * x + Q.b * y) ^ 2 := sq_nonneg _
    have hrhs : 0 < (2 * Q.a * x + Q.b * y) ^ 2 - Q.discriminant * y ^ 2 := by
      nlinarith
    have hleft : 0 < 4 * Q.a * Q.eval x y := by
      rw [four_mul_eval]
      exact hrhs
    nlinarith

/-- The first column of a determinant-one matrix is nonzero. -/
private theorem special_column_ne (g : SL(2, ℤ)) :
    g 0 0 ≠ 0 ∨ g 1 0 ≠ 0 := by
  by_contra h
  push Not at h
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  rw [h.1, h.2] at hdet
  norm_num at hdet

/-- Positive definiteness is preserved by a proper integral change of variables. -/
theorem definite_transform (Q : BQForm)
    (g : SL(2, ℤ)) (hQ : Q.IsPositiveDefinite) :
    (Q.transform g).IsPositiveDefinite := by
  constructor
  · change 0 < Q.eval (g 0 0) (g 1 0)
    exact pos_positive_definite hQ (special_column_ne g)
  · rw [discriminant_transform]
    exact hQ.2

/-- Positive definiteness is invariant under a proper integral change of variables. -/
theorem positi_defin_trans (Q : BQForm)
    (g : SL(2, ℤ)) :
    Q.IsPositiveDefinite ↔ (Q.transform g).IsPositiveDefinite := by
  constructor
  · exact definite_transform Q g
  · intro hQg
    have hback : (Q.transform g).transform g⁻¹ = Q := by
      calc
        (Q.transform g).transform g⁻¹ = Q.transform (g * g⁻¹) :=
          (transform_mul Q g g⁻¹).symm
        _ = Q.transform 1 := by rw [mul_inv_cancel]
        _ = Q := transform_one Q
    rw [← hback]
    exact definite_transform (Q.transform g) g⁻¹ hQg

/-- Properly equivalent forms are positive definite simultaneously. -/
theorem positi_defin_equiv {Q Q' : BQForm}
    (h : Q.Equivalent Q') : Q.IsPositiveDefinite ↔ Q'.IsPositiveDefinite := by
  obtain ⟨g, rfl⟩ := h
  exact positi_defin_trans Q g

/-- A primitive form of discriminant `D` in the component relevant to Theorem 4.29.
For `D < 0` this selects the positive-definite component; for `D ≥ 0` it imposes
no positivity condition. -/
def ProperDiscriminant (D : ℤ) (Q : BQForm) : Prop :=
  Q.discriminant = D ∧ Q.IsPrimitive ∧ (D < 0 → Q.IsPositiveDefinite)

/-- Primitive forms of discriminant `D`, restricted to the positive-definite
component when `D < 0`. -/
def ProperPrimitive (D : ℤ) :=
  {Q : BQForm // ProperDiscriminant D Q}

/-- The corrected admissibility condition is invariant under proper equivalence. -/
theorem proper_discr_equiv
    {D : ℤ} {Q Q' : BQForm} (h : Q.Equivalent Q') :
    ProperDiscriminant D Q ↔ ProperDiscriminant D Q' := by
  constructor
  · rintro ⟨hdisc, hprimitive, hpositive⟩
    refine ⟨(discriminant_equivalent h).symm.trans hdisc,
      (primitive_equivalent h).mp hprimitive, ?_⟩
    intro hD
    exact (positi_defin_equiv h).mp (hpositive hD)
  · rintro ⟨hdisc, hprimitive, hpositive⟩
    refine ⟨(discriminant_equivalent h).trans hdisc,
      (primitive_equivalent h).mpr hprimitive, ?_⟩
    intro hD
    exact (positi_defin_equiv h).mpr (hpositive hD)

instance properDiscriminantSetoid (D : ℤ) :
    Setoid (ProperPrimitive D) where
  r Q Q' := Q.1.Equivalent Q'.1
  iseqv := ⟨fun Q ↦ equivalent_refl Q.1, equivalent_symm, equivalent_trans⟩

/-- The corrected form-side target of Theorem 4.29: proper equivalence classes
of primitive forms, with the positive-definite component selected for negative
discriminant. -/
abbrev ProperPrimitDiscri (D : ℤ) :=
  Quotient (properDiscriminantSetoid D)

theorem proper_discriminant
    (D : ℤ) (Q : BQForm) :
    ProperDiscriminant D Q ↔
      Q.discriminant = D ∧ Q.IsPrimitive ∧ (D < 0 → Q.IsPositiveDefinite) :=
  Iff.rfl

/-- The positive Gaussian norm form belongs to the corrected target for
discriminant `-4`. -/
theorem proper_primi_discr :
    ProperDiscriminant (-4) gaussianPositiveForm := by
  refine ⟨discri_gauss_posit, primit_gauss_posit, ?_⟩
  intro _
  norm_num [gaussianPositiveForm, IsPositiveDefinite, discriminant]

/-- The negative-definite Gaussian form is excluded from the corrected target
for discriminant `-4`. -/
theorem gaussi_prope_discr :
    ¬ProperDiscriminant (-4) gaussianNegativeForm := by
  intro h
  have hpos := h.2.2 (by norm_num)
  norm_num [gaussianNegativeForm, IsPositiveDefinite, discriminant] at hpos

end BQForm

end Submission.NumberTheory.Milne
