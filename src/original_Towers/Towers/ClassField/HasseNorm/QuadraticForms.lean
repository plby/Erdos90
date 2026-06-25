import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Class field theory, Chapter VIII, Section 3: quadratic forms

This file formalizes the purely algebraic part of Milne's discussion of the local-global
principle for quadratic forms.  The Hasse norm theorem and the Hasse--Minkowski theorem
themselves require a theory of all completions of a number field and their norm groups which is
developed separately in this project.  The arguments below are independent of that global input;
Proposition 3.7(d) and Lemma 3.8 are completed by `quadraticValueStatement`.

The source's convention is that a form represents a scalar only at a nonzero vector.  This
matters in Lemma 3.4: the additional square coefficient has to be nonzero for the augmented form
to remain nondegenerate, so this is made explicit below.
-/

open QuadraticMap

namespace Towers.CField.HNorm

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A quadratic form represents `c` if it takes the value `c` at a nonzero vector. -/
def Represents (Q : QuadraticForm k V) (c : k) : Prop :=
  ∃ v : V, v ≠ 0 ∧ Q v = c

/-- The diagonal extension `q - aY²` of a quadratic form `q`. -/
def adjoinNegativeSquare (Q : QuadraticForm k V) (a : k) : QuadraticForm k (V × k) :=
  Q.prod ((-a) • QuadraticMap.sq)

@[simp]
theorem adjoin_negative_square (Q : QuadraticForm k V) (a : k) (v : V × k) :
    adjoinNegativeSquare Q a v = Q v.1 - a * v.2 ^ 2 := by
  simp [adjoinNegativeSquare, pow_two, sub_eq_add_neg]

/-- Adjoining a nonzero diagonal square coefficient preserves
nondegeneracy. -/
theorem adjoin_square_nondegenerate [NeZero (2 : k)]
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate) {a : k} (ha : a ≠ 0) :
    (adjoinNegativeSquare Q a).Nondegenerate := by
  letI : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  have hpolar : Q.polarBilin.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hformula (v w : V × k) :
      (adjoinNegativeSquare Q a).polarBilin v w =
        Q.polarBilin v.1 w.1 - 2 * a * v.2 * w.2 := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      adjoin_negative_square, Prod.fst_add, Prod.snd_add]
    ring
  apply QuadraticMap.nondegenerate_polar_iff.mp
  constructor
  · intro v hv
    apply Prod.ext
    · apply hpolar.1 v.1
      intro w
      have h := hv (w, 0)
      rw [hformula] at h
      simpa using h
    · have h := hv (0, 1)
      rw [hformula] at h
      simpa [NeZero.ne (2 : k), ha] using h
  · intro w hw
    apply Prod.ext
    · apply hpolar.2 w.1
      intro v
      have h := hw (v, 0)
      rw [hformula] at h
      simpa using h
    · have h := hw (0, 1)
      rw [hformula] at h
      simpa [NeZero.ne (2 : k), ha] using h

/-- Milne, Lemma 3.3.  A nondegenerate isotropic quadratic form represents every scalar. -/
theorem represents_all_nondegenerate
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate)
    (hzero : Represents Q 0) (c : k) :
    Represents Q c := by
  obtain ⟨v, hv, hQv⟩ := hzero
  have hnall : ¬ ∀ w : V, Q.polarBilin v w = 0 := by
    intro hall
    apply hv
    have hvRadical : v ∈ Q.radical := by
      rw [QuadraticMap.mem_radical_iff']
      refine ⟨hQv, ?_⟩
      intro w
      rw [QuadraticMap.map_add Q, hQv]
      change 0 + Q w + Q.polarBilin v w = Q w
      rw [hall w]
      simp
    rw [hQ.radical_eq_bot] at hvRadical
    exact hvRadical
  obtain ⟨w, hw⟩ : ∃ w : V, Q.polarBilin v w ≠ 0 := by
    simpa only [not_forall] using hnall
  have hw' : QuadraticMap.polar Q v w ≠ 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using hw
  let t : k := (c - Q w) / Q.polarBilin v w
  refine ⟨t • v + w, ?_, ?_⟩
  · intro hsum
    have hw_eq : w = -(t • v) := by
      exact eq_neg_of_add_eq_zero_right hsum
    apply hw
    rw [hw_eq]
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hQv]
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQv]
    simp only [smul_eq_mul, mul_zero, zero_add, QuadraticMap.polar_smul_left]
    dsimp [t]
    rw [div_mul_cancel₀ _ hw']
    ring

/-- Milne, Lemma 3.4.  For a nonzero scalar `a`, `q` represents `a` if and only if
`q - aY²` is isotropic. -/
theorem represents_adjoin_anisotropic
    {Q : QuadraticForm k V} (hQ : Q.Nondegenerate) {a : k} (ha : a ≠ 0) :
    Represents Q a ↔ ¬ (adjoinNegativeSquare Q a).Anisotropic := by
  constructor
  · rintro ⟨v, hv, hval⟩
    rw [QuadraticMap.not_anisotropic_iff_exists]
    refine ⟨(v, 1), ?_, ?_⟩
    · simp
    · simp [hval, adjoin_negative_square]
  · rw [QuadraticMap.not_anisotropic_iff_exists]
    rintro ⟨⟨v, y⟩, hvy, hiso⟩
    rw [adjoin_negative_square] at hiso
    by_cases hy : y = 0
    · subst y
      have hv : v ≠ 0 := by simpa using hvy
      apply represents_all_nondegenerate hQ ⟨v, hv, by simpa using hiso⟩
    · refine ⟨y⁻¹ • v, ?_, ?_⟩
      · intro hscaled
        have hvzero : v = 0 := by
          exact (smul_eq_zero.mp hscaled).resolve_left (inv_ne_zero hy)
        subst v
        simp [ha, hy] at hiso
      · rw [QuadraticMap.map_smul]
        simp only [smul_eq_mul]
        have hQv : Q v = a * y ^ 2 := sub_eq_zero.mp hiso
        rw [hQv]
        field_simp

/-- The binary diagonal form `X² - aY²`. -/
def binaryNormForm (a : k) : QuadraticForm k (k × k) :=
  adjoinNegativeSquare QuadraticMap.sq a

@[simp]
theorem binary_norm_form (a : k) (v : k × k) :
    binaryNormForm a v = v.1 ^ 2 - a * v.2 ^ 2 := by
  simp [binaryNormForm, adjoin_negative_square, pow_two]

theorem binary_form_polar (a : k) (v w : k × k) :
    (binaryNormForm a).polarBilin v w =
      2 * v.1 * w.1 - 2 * a * v.2 * w.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    binary_norm_form, Prod.fst_add, Prod.snd_add]
  ring

/-- The binary form `X²-aY²` is nondegenerate when `a` and `2` are nonzero. -/
theorem binary_form_nondegenerate [NeZero (2 : k)] {a : k} (ha : a ≠ 0) :
    (binaryNormForm a).Nondegenerate := by
  letI : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne _)
  apply QuadraticMap.nondegenerate_polar_iff.mp
  constructor
  · intro v hv
    apply Prod.ext
    · have h : (binaryNormForm a).polarBilin v (1, 0) = 0 := hv (1, 0)
      rw [binary_form_polar] at h
      simpa [NeZero.ne (2 : k)] using h
    · have h : (binaryNormForm a).polarBilin v (0, 1) = 0 := hv (0, 1)
      rw [binary_form_polar] at h
      simpa [NeZero.ne (2 : k), ha] using h
  · intro w hw
    apply Prod.ext
    · have h : (binaryNormForm a).polarBilin (1, 0) w = 0 := hw (1, 0)
      rw [binary_form_polar] at h
      simpa [NeZero.ne (2 : k)] using h
    · have h : (binaryNormForm a).polarBilin (0, 1) w = 0 := hw (0, 1)
      rw [binary_form_polar] at h
      simpa [NeZero.ne (2 : k), ha] using h

/-- The ternary diagonal form `X² - aY² - bZ²`. -/
def ternaryNormForm (a b : k) : QuadraticForm k ((k × k) × k) :=
  adjoinNegativeSquare (binaryNormForm a) b

@[simp]
theorem ternary_norm_form (a b : k) (v : (k × k) × k) :
    ternaryNormForm a b v = v.1.1 ^ 2 - a * v.1.2 ^ 2 - b * v.2 ^ 2 := by
  simp [ternaryNormForm, adjoin_negative_square]

/-- Milne, Proposition 3.7(a): the one-variable form `X²` is anisotropic over a field. -/
theorem sq_anisotropic :
    (QuadraticMap.sq : QuadraticForm k k).Anisotropic := by
  intro x hx
  simpa using (mul_self_eq_zero.mp hx)

/-- Milne, Proposition 3.7(b): `X²-aY²` is isotropic exactly when `a` is a square. -/
theorem binary_isotropic_square (a : k) :
    ¬ (binaryNormForm a).Anisotropic ↔ IsSquare a := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, hform⟩
    rw [binary_norm_form, sub_eq_zero] at hform
    have hy : y ≠ 0 := by
      intro hy
      subst y
      simp only [pow_two, mul_zero] at hform
      have hx : x = 0 := mul_self_eq_zero.mp hform
      exact hxy (by simp [hx])
    refine ⟨x / y, ?_⟩
    field_simp
    simpa [pow_two, mul_assoc] using hform.symm
  · rintro ⟨z, rfl⟩
    refine ⟨(z, 1), by simp, ?_⟩
    simp [binary_norm_form, pow_two]

/-- The quadratic-algebra norm is the binary form `X²-aY²`. -/
theorem quadratic_binary_form (a : k) (z : QuadraticAlgebra k a 0) :
    z.norm = binaryNormForm a (z.re, z.im) := by
  simp [QuadraticAlgebra.norm_def, binary_norm_form, pow_two]
  ring

/-- Representing a nonzero scalar by `X²-aY²` is exactly being a norm from the
quadratic algebra with generator squared equal to `a`. -/
theorem binary_represents_quadratic {a b : k} :
    Represents (binaryNormForm a) b ↔
      ∃ z : QuadraticAlgebra k a 0, z ≠ 0 ∧ z.norm = b := by
  constructor
  · rintro ⟨⟨x, y⟩, hxy, hnorm⟩
    refine ⟨⟨x, y⟩, ?_, ?_⟩
    · simpa [QuadraticAlgebra.ext_iff] using hxy
    · simpa [quadratic_binary_form] using hnorm
  · rintro ⟨z, hz, hnorm⟩
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · intro hpair
      apply hz
      ext
      · exact congrArg Prod.fst hpair
      · exact congrArg Prod.snd hpair
    · simpa [quadratic_binary_form] using hnorm

/-- Milne, Proposition 3.7(c): `X²-aY²-bZ²` is isotropic exactly when `b` is a
norm from the quadratic algebra generated by a square root of `a`. -/
theorem ternary_isotropic_quadratic
    [NeZero (2 : k)] {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ (ternaryNormForm a b).Anisotropic ↔
      ∃ z : QuadraticAlgebra k a 0, z ≠ 0 ∧ z.norm = b := by
  rw [← binary_represents_quadratic]
  exact (represents_adjoin_anisotropic
    (binary_form_nondegenerate ha) hb).symm

end Towers.CField.HNorm
