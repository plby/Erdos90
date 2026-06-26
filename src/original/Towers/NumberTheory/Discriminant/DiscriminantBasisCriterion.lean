import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.24

When the discriminant of a finite free algebra is nonzero, an indexed family is a basis exactly
when its discriminant generates the same principal ideal as the discriminant of a fixed basis.
-/

namespace Towers.NumberTheory.Milne

open scoped Matrix

/-- Let `b` be a basis of a finite free algebra with nonzero discriminant. A family `v` with the
same finite index type is a basis precisely when `discr A v` and `discr A b` generate the same
principal ideal. -/
theorem basis_span_discr
    {A B ι : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A B) (v : ι → B) (hdiscr : Algebra.discr A b ≠ 0) :
    (∃ b' : Module.Basis ι A B, (b' : ι → B) = v) ↔
      Ideal.span ({Algebra.discr A v} : Set A) =
        Ideal.span ({Algebra.discr A b} : Set A) := by
  let P : Matrix ι ι A := b.toMatrix v
  have hv : b ᵥ* P.map (algebraMap A B) = v := by
    exact b.toMatrix_map_vecMul v
  have hchange : Algebra.discr A v = P.det ^ 2 * Algebra.discr A b := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  constructor
  · rintro ⟨b', hb'⟩
    have hP : P = b.toMatrix b' := by simp [P, hb']
    have hdet : IsUnit P.det := by
      rw [hP, ← LinearMap.toMatrix_id_eq_basis_toMatrix]
      exact LinearEquiv.isUnit_det (LinearEquiv.refl A B) b' b
    rw [Ideal.span_singleton_eq_span_singleton, hchange]
    exact associated_unit_mul_left _ _ (hdet.pow 2)
  · intro hspan
    have hassoc : Associated (P.det ^ 2 * Algebra.discr A b) (Algebra.discr A b) := by
      rw [← hchange]
      exact Ideal.span_singleton_eq_span_singleton.mp hspan
    have hpow : IsUnit (P.det ^ 2) := by
      rw [← associated_one_iff_isUnit]
      apply Associated.of_mul_right (a := P.det ^ 2) (b := Algebra.discr A b)
        (c := 1) (d := Algebra.discr A b) ?_ (Associated.refl _) hdiscr
      simpa using hassoc
    have hdet : IsUnit P.det := (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpow
    let e : B ≃ₗ[A] B := P.toLinearEquiv b hdet
    let b' : Module.Basis ι A B := b.map e
    refine ⟨b', ?_⟩
    funext i
    change Matrix.toLin b b P (b i) = v i
    rw [Matrix.toLin_self]
    exact b.sum_toMatrix_smul_self v i

end Towers.NumberTheory.Milne
