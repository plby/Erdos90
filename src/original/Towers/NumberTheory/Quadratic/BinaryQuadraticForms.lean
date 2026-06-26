import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Milne, Algebraic Number Theory, Binary quadratic forms

This file records the elementary algebra at the start of Milne's discussion preceding
Theorem 4.29.  An integral binary quadratic form is represented by its three integer
coefficients.  We define the usual change of variables by an element of `SL(2, Z)` and prove
that it preserves both evaluation and discriminant.
-/

namespace Towers.NumberTheory.Milne

open scoped MatrixGroups

/-- An integral binary quadratic form `a X^2 + b X Y + c Y^2`. -/
@[ext]
structure BQForm where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace BQForm

/-- Evaluation of an integral binary quadratic form. -/
def eval (Q : BQForm) (x y : ℤ) : ℤ :=
  Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- The discriminant `b^2 - 4ac` of an integral binary quadratic form. -/
def discriminant (Q : BQForm) : ℤ :=
  Q.b ^ 2 - 4 * Q.a * Q.c

/-- A binary quadratic form is nondegenerate when its discriminant is nonzero. -/
def IsNondegenerate (Q : BQForm) : Prop :=
  Q.discriminant ≠ 0

/-- Change variables in a binary quadratic form by an integral matrix of determinant one. -/
def transform (Q : BQForm) (g : SL(2, ℤ)) :
    BQForm where
  a := Q.a * g 0 0 ^ 2 + Q.b * g 0 0 * g 1 0 + Q.c * g 1 0 ^ 2
  b := 2 * Q.a * g 0 0 * g 0 1 +
    Q.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) +
    2 * Q.c * g 1 0 * g 1 1
  c := Q.a * g 0 1 ^ 2 + Q.b * g 0 1 * g 1 1 + Q.c * g 1 1 ^ 2

theorem eval_transform (Q : BQForm) (g : SL(2, ℤ)) (x y : ℤ) :
    (Q.transform g).eval x y =
      Q.eval (g 0 0 * x + g 0 1 * y) (g 1 0 * x + g 1 1 * y) := by
  simp only [transform, eval]
  ring

theorem discriminant_transform (Q : BQForm) (g : SL(2, ℤ)) :
    (Q.transform g).discriminant = Q.discriminant := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  calc
    (Q.transform g).discriminant =
        Q.discriminant * (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 := by
      simp only [transform, discriminant]
      ring
    _ = Q.discriminant := by rw [hdet]; ring

theorem transform_one (Q : BQForm) : Q.transform 1 = Q := by
  ext <;> simp [transform]

theorem transform_mul (Q : BQForm) (g h : SL(2, ℤ)) :
    Q.transform (g * h) = (Q.transform g).transform h := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with
  | h α β γ δ hg =>
      induction h using Matrix.SpecialLinearGroup.fin_two_induction with
      | h p q r s hh =>
          ext <;>
            simp [transform, Matrix.mul_apply, Fin.sum_univ_two] <;>
            ring

/-- Milne's equivalence relation: two forms differ by an `SL₂(ℤ)` change of variables. -/
def Equivalent (Q Q' : BQForm) : Prop :=
  ∃ g : SL(2, ℤ), Q' = Q.transform g

theorem equivalent_refl (Q : BQForm) : Q.Equivalent Q :=
  ⟨1, (transform_one Q).symm⟩

theorem equivalent_symm {Q Q' : BQForm} (h : Q.Equivalent Q') :
    Q'.Equivalent Q := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  calc
    Q = Q.transform 1 := (transform_one Q).symm
    _ = Q.transform (g * g⁻¹) := by simp
    _ = (Q.transform g).transform g⁻¹ := transform_mul Q g g⁻¹

theorem equivalent_trans {Q₁ Q₂ Q₃ : BQForm}
    (h₁₂ : Q₁.Equivalent Q₂) (h₂₃ : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ := by
  obtain ⟨g, rfl⟩ := h₁₂
  obtain ⟨h, rfl⟩ := h₂₃
  exact ⟨g * h, (transform_mul Q₁ g h).symm⟩

instance equivalentSetoid : Setoid BQForm where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Equivalence classes of integral binary quadratic forms under `SL₂(ℤ)`. -/
abbrev Class := Quotient equivalentSetoid

/-- Integral binary quadratic forms having a prescribed discriminant. -/
abbrev OfDiscriminant (D : ℤ) :=
  {Q : BQForm // Q.discriminant = D}

instance ofDiscriminantSetoid (D : ℤ) : Setoid (OfDiscriminant D) where
  r Q Q' := Q.1.Equivalent Q'.1
  iseqv := ⟨fun Q ↦ equivalent_refl Q.1, equivalent_symm, equivalent_trans⟩

/-- Equivalence classes of integral binary quadratic forms of discriminant `D`. -/
abbrev ClassOfDiscriminant (D : ℤ) := Quotient (ofDiscriminantSetoid D)

theorem discriminant_equivalent {Q Q' : BQForm}
    (h : Q.Equivalent Q') : Q.discriminant = Q'.discriminant := by
  obtain ⟨g, rfl⟩ := h
  exact (discriminant_transform Q g).symm

/-- An integral binary quadratic form is primitive when every common divisor of its
three coefficients is a unit. -/
def IsPrimitive (Q : BQForm) : Prop :=
  ∀ d : ℤ, d ∣ Q.a → d ∣ Q.b → d ∣ Q.c → IsUnit d

private theorem common_dvd_transform (Q : BQForm) (g : SL(2, ℤ))
    {d : ℤ} (ha : d ∣ Q.a) (hb : d ∣ Q.b) (hc : d ∣ Q.c) :
    d ∣ (Q.transform g).a ∧ d ∣ (Q.transform g).b ∧ d ∣ (Q.transform g).c := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  constructor
  · refine ⟨a * g 0 0 ^ 2 + b * g 0 0 * g 1 0 + c * g 1 0 ^ 2, ?_⟩
    simp only [transform, ha, hb, hc]
    ring
  constructor
  · refine ⟨2 * a * g 0 0 * g 0 1 +
        b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * c * g 1 0 * g 1 1, ?_⟩
    simp only [transform, ha, hb, hc]
    ring
  · refine ⟨a * g 0 1 ^ 2 + b * g 0 1 * g 1 1 + c * g 1 1 ^ 2, ?_⟩
    simp only [transform, ha, hb, hc]
    ring

/-- Primitivity is unchanged by an integral determinant-one change of variables. -/
theorem primitive_transform (Q : BQForm) (g : SL(2, ℤ)) :
    Q.IsPrimitive ↔ (Q.transform g).IsPrimitive := by
  constructor
  · intro hQ d hda hdb hdc
    have hback : (Q.transform g).transform g⁻¹ = Q := by
      calc
        (Q.transform g).transform g⁻¹ = Q.transform (g * g⁻¹) :=
          (transform_mul Q g g⁻¹).symm
        _ = Q.transform 1 := by rw [mul_inv_cancel]
        _ = Q := transform_one Q
    obtain ⟨ha, hb, hc⟩ := common_dvd_transform (Q.transform g) g⁻¹ hda hdb hdc
    apply hQ d
    · simpa [hback] using ha
    · simpa [hback] using hb
    · simpa [hback] using hc
  · intro h d hda hdb hdc
    obtain ⟨ha, hb, hc⟩ := common_dvd_transform Q g hda hdb hdc
    exact h d ha hb hc

/-- Equivalent integral binary quadratic forms are primitive simultaneously. -/
theorem primitive_equivalent {Q Q' : BQForm}
    (h : Q.Equivalent Q') : Q.IsPrimitive ↔ Q'.IsPrimitive := by
  obtain ⟨g, rfl⟩ := h
  exact primitive_transform Q g

/-- The square of every common divisor of the coefficients divides the discriminant. -/
theorem sq_discriminant_common (Q : BQForm) {d : ℤ}
    (ha : d ∣ Q.a) (hb : d ∣ Q.b) (hc : d ∣ Q.c) :
    d * d ∣ Q.discriminant := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  refine ⟨b ^ 2 - 4 * a * c, ?_⟩
  simp only [discriminant, ha, hb, hc]
  ring

/-- In particular, a binary quadratic form with squarefree discriminant is primitive. -/
theorem primit_squar_discr (Q : BQForm)
    (hQ : Squarefree Q.discriminant) : Q.IsPrimitive := by
  intro d ha hb hc
  exact hQ d (sq_discriminant_common Q ha hb hc)

private theorem sq_emod_four (x : ℤ) :
    x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hx0 : 0 ≤ x % 4 := Int.emod_nonneg _ (by norm_num)
  have hx4 : x % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hsq : x ^ 2 % 4 = (x % 4) ^ 2 % 4 :=
    ((Int.mod_modEq x 4).pow 2).symm.eq
  rw [hsq]
  interval_cases hx : x % 4 <;> norm_num [hx]

/-- If `d` is squarefree and congruent to `2` or `3` modulo `4`, then a form
of discriminant `4d` is primitive.  The even-common-divisor case would force
`d` to be a square modulo four; an odd common divisor has square dividing `d`. -/
theorem primit_discr_squar
    (Q : BQForm) {d : ℤ}
    (hsq : Squarefree d) (hmod : d % 4 = 2 ∨ d % 4 = 3)
    (hdisc : Q.discriminant = 4 * d) :
    Q.IsPrimitive := by
  intro z ha hb hc
  have hzsq : z * z ∣ 4 * d := by
    rw [← hdisc]
    exact sq_discriminant_common Q ha hb hc
  by_cases hzEven : (2 : ℤ) ∣ z
  · have h2a : (2 : ℤ) ∣ Q.a := hzEven.trans ha
    have h2b : (2 : ℤ) ∣ Q.b := hzEven.trans hb
    have h2c : (2 : ℤ) ∣ Q.c := hzEven.trans hc
    rcases h2a with ⟨a, ha'⟩
    rcases h2b with ⟨b, hb'⟩
    rcases h2c with ⟨c, hc'⟩
    have hd : d = b ^ 2 - 4 * a * c := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
      calc
        4 * d = Q.discriminant := hdisc.symm
        _ = 4 * (b ^ 2 - 4 * a * c) := by
          simp only [discriminant]
          rw [ha', hb', hc']
          ring
    have hdmod : d % 4 = 0 ∨ d % 4 = 1 := by
      rw [hd, Int.sub_emod, Int.mul_emod]
      simpa using sq_emod_four b
    omega
  · have hp2 : Prime (2 : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by simpa using Nat.prime_two)
    have hcop2 : IsCoprime z (2 : ℤ) :=
      ((Prime.coprime_iff_not_dvd hp2).mpr hzEven).symm
    have hcop4 : IsCoprime (z * z) (4 : ℤ) := by
      have hcop2' : IsCoprime (z * z) (2 : ℤ) := hcop2.mul_left hcop2
      convert hcop2'.mul_right hcop2' using 1
    exact hsq z (hcop4.dvd_of_dvd_mul_left hzsq)

/-- Milne's claim preceding Theorem 4.29: a form whose discriminant is the
fundamental discriminant attached to a squarefree integer is primitive. -/
theorem primit_funda_discr
    (Q : BQForm) {d : ℤ} (hsq : Squarefree d)
    (hmod : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3)
    (hdisc : Q.discriminant = if d % 4 = 1 then d else 4 * d) :
    Q.IsPrimitive := by
  by_cases hd1 : d % 4 = 1
  · apply primit_squar_discr Q
    rw [hdisc, if_pos hd1]
    exact hsq
  · apply primit_discr_squar Q hsq
    · rcases hmod with h | h | h
      · exact (hd1 h).elim
      · exact Or.inl h
      · exact Or.inr h
    · simpa [hd1] using hdisc

/-- The norm form `X² - dY²`, used when `d ≡ 2,3 (mod 4)`. -/
def integralBasisForm (d : ℤ) : BQForm :=
  ⟨1, 0, -d⟩

/-- Milne's norm form `X² - dY²` is primitive. -/
theorem primitive_basis_form (d : ℤ) :
    (integralBasisForm d).IsPrimitive := by
  intro m hm _ _
  exact isUnit_iff_dvd_one.mpr (by simpa [integralBasisForm] using hm)

@[simp]
theorem integral_basis_form (d x y : ℤ) :
    (integralBasisForm d).eval x y = x ^ 2 - d * y ^ 2 := by
  simp [integralBasisForm, eval]
  ring

@[simp]
theorem discriminant_basis_form (d : ℤ) :
    (integralBasisForm d).discriminant = 4 * d := by
  simp [integralBasisForm, discriminant]

/-- The norm form `X² + XY + cY²`; Milne takes `c = (1-d)/4`. -/
def halfBasisForm (c : ℤ) : BQForm :=
  ⟨1, 1, c⟩

/-- Milne's norm form `X² + XY + cY²` is primitive. -/
theorem primitive_half_form (c : ℤ) :
    (halfBasisForm c).IsPrimitive := by
  intro m hm _ _
  exact isUnit_iff_dvd_one.mpr (by simpa [halfBasisForm] using hm)

@[simp]
theorem half_basis_form (c x y : ℤ) :
    (halfBasisForm c).eval x y = x ^ 2 + x * y + c * y ^ 2 := by
  simp [halfBasisForm, eval]

@[simp]
theorem discriminant_half_form (c : ℤ) :
    (halfBasisForm c).discriminant = 1 - 4 * c := by
  simp [halfBasisForm, discriminant]

theorem discriminant_half_relation (d c : ℤ)
    (h : 4 * c = 1 - d) : (halfBasisForm c).discriminant = d := by
  simp only [discriminant_half_form]
  omega

theorem discriminant_half_div (d : ℤ) (h : (4 : ℤ) ∣ 1 - d) :
    (halfBasisForm ((1 - d) / 4)).discriminant = d := by
  apply discriminant_half_relation
  simpa [mul_comm] using Int.ediv_mul_cancel h

/-- The norm form `X² + XY + ((1-d)/4)Y²`, used when `d ≡ 1 (mod 4)`. -/
def quadraticIntegerForm (d : ℤ) : BQForm :=
  halfBasisForm ((1 - d) / 4)

@[simp]
theorem discri_quadr_form (d : ℤ) (h : d % 4 = 1) :
    (quadraticIntegerForm d).discriminant = d := by
  apply discriminant_half_relation
  dsimp [quadraticIntegerForm]
  omega

example : (integralBasisForm (-1)).discriminant = -4 := by norm_num

example : (halfBasisForm 1).discriminant = -3 := by norm_num

/-- The positive-definite Gaussian norm form `X² + Y²`. -/
def gaussianPositiveForm : BQForm :=
  ⟨1, 0, 1⟩

/-- The negative-definite form `-X² - Y²`.  It has the same discriminant as the
Gaussian norm form, but belongs to a different `SL₂(ℤ)`-equivalence class. -/
def gaussianNegativeForm : BQForm :=
  ⟨-1, 0, -1⟩

@[simp]
theorem discri_gauss_posit : gaussianPositiveForm.discriminant = -4 := by
  norm_num [gaussianPositiveForm, discriminant]

@[simp]
theorem discriminant_gaussian_form : gaussianNegativeForm.discriminant = -4 := by
  norm_num [gaussianNegativeForm, discriminant]

theorem primit_gauss_posit : gaussianPositiveForm.IsPrimitive := by
  intro d hda _ _
  exact isUnit_iff_dvd_one.mpr (by simpa [gaussianPositiveForm] using hda)

theorem primitive_gaussian_form : gaussianNegativeForm.IsPrimitive := by
  intro d hda _ _
  exact isUnit_iff_dvd_one.mpr (by
    have hdneg : d ∣ (-1 : ℤ) := by simpa [gaussianNegativeForm] using hda
    simpa using hdneg.neg_right)

/-- The unrestricted formulation of Theorem 4.29 cannot use all primitive forms of
negative discriminant: the positive- and negative-definite forms of discriminant `-4`
are not properly equivalent.  The classical theorem restricts to positive-definite forms. -/
theorem gaussi_equiv_negat :
    ¬ gaussianPositiveForm.Equivalent gaussianNegativeForm := by
  rintro ⟨g, hg⟩
  have ha : (-1 : ℤ) = g 0 0 ^ 2 + g 1 0 ^ 2 := by
    simpa [gaussianPositiveForm, gaussianNegativeForm, transform] using
      congrArg BQForm.a hg
  nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 1 0)]

/-- The principal positive-definite form of discriminant `-20`. -/
def sqrtFiveForm : BQForm :=
  ⟨1, 0, 5⟩

/-- The second standard positive-definite form of discriminant `-20`. -/
def sqrtNonprincipalForm : BQForm :=
  ⟨2, 2, 3⟩

@[simp]
theorem discriminant_sqrt_form :
    sqrtFiveForm.discriminant = -20 := by
  norm_num [sqrtFiveForm, discriminant]

@[simp]
theorem discri_nonpr_form :
    sqrtNonprincipalForm.discriminant = -20 := by
  norm_num [sqrtNonprincipalForm, discriminant]

theorem primitive_sqrt_form : sqrtFiveForm.IsPrimitive := by
  intro d hda _ _
  exact isUnit_iff_dvd_one.mpr (by simpa [sqrtFiveForm] using hda)

theorem primit_nonpr_form :
    sqrtNonprincipalForm.IsPrimitive := by
  intro d hda _ hdc
  apply isUnit_iff_dvd_one.mpr
  have htwo : d ∣ (2 : ℤ) := by simpa [sqrtNonprincipalForm] using hda
  have hthree : d ∣ (3 : ℤ) := by simpa [sqrtNonprincipalForm] using hdc
  simpa using hthree.sub htwo

/-- The two forms displayed in Milne's note on `ℚ(√-5)` are inequivalent. -/
theorem sqrt_equiv_nonpr :
    ¬ sqrtFiveForm.Equivalent sqrtNonprincipalForm := by
  rintro ⟨g, hg⟩
  have ha : (2 : ℤ) = g 0 0 ^ 2 + 5 * g 1 0 ^ 2 := by
    simpa [sqrtFiveForm, sqrtNonprincipalForm, transform] using
      congrArg BQForm.a hg
  have hv_lt : g 1 0 ^ 2 < (1 : ℤ) := by
    nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 1 0)]
  have hv_sq : g 1 0 ^ 2 = 0 := by
    nlinarith [sq_nonneg (g 1 0)]
  have hu_sq : g 0 0 ^ 2 = 2 := by
    nlinarith
  have hu_mod := sq_emod_four (g 0 0)
  rw [hu_sq] at hu_mod
  norm_num at hu_mod

end BQForm

end Towers.NumberTheory.Milne
