import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.26

The discriminant of a basis of a finite separable field extension is the square of the
determinant of its embeddings matrix, and in particular is nonzero.
-/

namespace Towers.NumberTheory.Milne

/-- Let `L / K` be finite separable, let `b` be a basis, and enumerate the embeddings of `L`
into an algebraically closed extension `Ω`. The discriminant of `b` is the square of the
determinant of the matrix of embedding values, and it is nonzero. -/
theorem discr_embeddings_det
    (K L Ω ι : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed Ω]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (e : ι ≃ (L →ₐ[K] Ω)) :
    algebraMap K Ω (Algebra.discr K b) =
        (Algebra.embeddingsMatrixReindex K Ω b e).det ^ 2 ∧
      Algebra.discr K b ≠ 0 := by
  exact ⟨Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K Ω b e,
    Algebra.discr_not_zero_of_basis K b⟩

/-- If a finite free algebra becomes a finite separable field extension after localization, then
the discriminant of every basis before localization is nonzero. This is the localization form of
Corollary 2.27. -/
theorem discr_localization_separable
    (A B K L : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid B M) L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) :
    Algebra.discr A b ≠ 0 := by
  intro hdiscr
  have hlocal :
      Algebra.discr K (b.localizationLocalization K M L) ≠ 0 :=
    Algebra.discr_not_zero_of_basis K (b.localizationLocalization K M L)
  apply hlocal
  rw [Algebra.discr_localizationLocalization A M L b, hdiscr, map_zero]

end Towers.NumberTheory.Milne
