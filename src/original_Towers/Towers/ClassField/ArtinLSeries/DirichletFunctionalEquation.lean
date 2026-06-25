import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Chapter VIII, Section 10: Dirichlet functional equations

Mathlib contains the analytic continuation and functional equation for the
completed L-function of a primitive complex Dirichlet character.  These
wrappers give the results source-local names.  The accompanying assertion
that the root number has absolute value one is derived below from Mathlib's
primitive Gauss-sum product formula.
-/

namespace Towers.CField.ALSeries

noncomputable section

open scoped ComplexConjugate ZMod

variable {N : ℕ} [NeZero N]

/-- The usual Dirichlet L-function is the completed L-function divided by its
Archimedean gamma factor, away from the exceptional modulus-one point. -/
theorem dirichlet_l_gamma
    (chi : DirichletCharacter ℂ N) (s : ℂ) (h : s ≠ 0 ∨ N ≠ 1) :
    DirichletCharacter.LFunction chi s =
      DirichletCharacter.completedLFunction chi s /
        DirichletCharacter.gammaFactor chi s :=
  DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi s h

/-- The functional equation for the completed L-function of a primitive
Dirichlet character. -/
theorem dirichlet_l_function
    {chi : DirichletCharacter ℂ N} (hchi : chi.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction chi (1 - s) =
      N ^ (s - 1 / 2) * DirichletCharacter.rootNumber chi *
        DirichletCharacter.completedLFunction chi⁻¹ s :=
  hchi.completedLFunction_one_sub s

/-- Complex conjugation sends a Gauss sum to the Gauss sum of the inverse
multiplicative and additive characters. -/
private theorem conj_gaussSum
    (chi : DirichletCharacter ℂ N) (psi : AddChar (ZMod N) ℂ) :
    conj (gaussSum chi psi) = gaussSum chi⁻¹ psi⁻¹ := by
  classical
  rw [gaussSum, gaussSum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_mul]
  change star (chi x) * star (psi x) = chi⁻¹ x * psi⁻¹ x
  rw [MulChar.star_apply']
  congr 1
  rw [AddChar.inv_apply]
  exact (AddChar.map_neg_eq_conj psi x).symm

/-- A primitive complex Dirichlet character has Gauss sum of norm `√N`. -/
theorem std_char_primitive
    {chi : DirichletCharacter ℂ N} (hchi : chi.IsPrimitive) :
    ‖gaussSum chi ZMod.stdAddChar‖ = Real.sqrt N := by
  rcases eq_or_ne N 1 with rfl | hN
  · have hvalue (x : ZMod 1) : chi x = 1 := by
      rw [show x = 1 by exact Subsingleton.elim _ _]
      exact map_one chi
    have hgauss : gaussSum chi ZMod.stdAddChar = 1 := by
      have hadd (x : ZMod 1) : ZMod.stdAddChar x = 1 := by
        rw [show x = 0 by exact Subsingleton.elim _ _]
        exact AddChar.map_zero_eq_one _
      simp only [gaussSum, Finset.univ_unique, Finset.sum_singleton]
      rw [hvalue _, hadd _, mul_one]
    rw [hgauss, norm_one]
    norm_num
  let g := gaussSum chi ZMod.stdAddChar
  have hdouble := congrFun (ZMod.dft_dft (Φ := fun x => chi x))
    (-1 : ZMod N)
  have hleft :
      ZMod.dft (ZMod.dft (fun x => chi x)) (-1) =
        gaussSum chi⁻¹ ZMod.stdAddChar⁻¹ * g := by
    rw [ZMod.dft_apply, gaussSum]
    simp only [smul_eq_mul]
    rw [Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun a => ?_
    simp only [Equiv.neg_apply,
      hchi.fourierTransform_eq_inv_mul_gaussSum, g]
    rw [mul_neg, mul_one, AddChar.inv_apply]
    ring
  have hprod' :
      gaussSum chi ZMod.stdAddChar *
          conj (gaussSum chi ZMod.stdAddChar) =
        (N : ℂ) := by
    rw [conj_gaussSum, mul_comm]
    rw [← hleft]
    simpa using hdouble
  have hsq : ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 = (N : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hprod'
    exact Complex.ofReal_injective hprod'
  have hsqrt : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  nlinarith [norm_nonneg (gaussSum chi ZMod.stdAddChar),
    Real.sqrt_nonneg (N : ℝ)]

/-- The global root number of a primitive complex Dirichlet character lies
on the unit circle. -/
theorem primitive_dirichlet_number
    {chi : DirichletCharacter ℂ N} (hchi : chi.IsPrimitive) :
    ‖DirichletCharacter.rootNumber chi‖ = 1 := by
  rcases eq_or_ne N 1 with rfl | hN
  · rw [DirichletCharacter.rootNumber_modOne]
    exact norm_one
  rw [DirichletCharacter.rootNumber, norm_div, norm_div,
    norm_pow, Complex.norm_I, one_pow, div_one,
    std_char_primitive hchi,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    Real.sqrt_eq_rpow]
  norm_num
  exact NeZero.ne N

/-- The full source-style assertion follows from the functional equation and
the Gauss-sum computation of the root-number norm. -/
theorem dirichletFunctionalEquation :
    ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    chi.IsPrimitive →
      (∀ s : ℂ,
        DirichletCharacter.completedLFunction chi (1 - s) =
          N ^ (s - 1 / 2) * DirichletCharacter.rootNumber chi *
            DirichletCharacter.completedLFunction chi⁻¹ s) ∧
      ‖DirichletCharacter.rootNumber chi‖ = 1
  := by
  intro N _ chi hchi
  exact ⟨hchi.completedLFunction_one_sub,
    primitive_dirichlet_number hchi⟩

/-- A nontrivial completed Dirichlet L-function is differentiable on the
whole complex plane. -/
theorem differentiable_l_function
    {chi : DirichletCharacter ℂ N} (hne : chi ≠ 1) :
    Differentiable ℂ (DirichletCharacter.completedLFunction chi) :=
  DirichletCharacter.differentiable_completedLFunction hne

end

end Towers.CField.ALSeries
