import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Milne, Algebraic Number Theory, Proposition 2.40

The sign formula for the discriminant and Stickelberger's congruence modulo four.
-/

namespace Submission.NumberTheory.Milne

open scoped BigOperators

open Equiv Finset Matrix Module NumberField

section PermutationSums

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

private def permTerm (M : Matrix n n R) (σ : Equiv.Perm n) : R :=
  ∏ i, M (σ i) i

private def evenPart (M : Matrix n n R) : R :=
  ∑ σ with Equiv.Perm.sign σ = 1, permTerm M σ

private def oddPart (M : Matrix n n R) : R :=
  ∑ σ with Equiv.Perm.sign σ ≠ 1, permTerm M σ

private theorem permanent_even_part (M : Matrix n n R) :
    M.permanent = evenPart M + oddPart M := by
  rw [Matrix.permanent, evenPart, oddPart,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Equiv.Perm n ↦ Equiv.Perm.sign σ = 1)]
  simp [permTerm]

private theorem det_even_part (M : Matrix n n R) :
    M.det = evenPart M - oddPart M := by
  rw [Matrix.det_apply', evenPart, oddPart,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : Equiv.Perm n ↦ Equiv.Perm.sign σ = 1)]
  rw [sub_eq_add_neg]
  apply congrArg₂ (fun x y : R ↦ x + y)
  · apply Finset.sum_congr rfl
    intro σ hσ
    simp only [Finset.mem_filter] at hσ
    simp [hσ.2, permTerm]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    simp only [Finset.mem_filter] at hσ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact (hσ.2 h).elim
    · simp [h, permTerm]

private theorem det_permanent_parts (M : Matrix n n R) :
    M.det ^ 2 = M.permanent ^ 2 - 4 * (evenPart M * oddPart M) := by
  rw [det_even_part, permanent_even_part]
  ring

private theorem integral_even_part {A : Type*} [CommRing A] [Algebra A R]
    (M : Matrix n n R) (hM : ∀ i j, IsIntegral A (M i j)) :
    IsIntegral A (evenPart M) := by
  apply IsIntegral.sum
  intro σ _
  apply IsIntegral.prod
  intro i _
  exact hM _ _

private theorem integral_odd_part {A : Type*} [CommRing A] [Algebra A R]
    (M : Matrix n n R) (hM : ∀ i j, IsIntegral A (M i j)) :
    IsIntegral A (oddPart M) := by
  apply IsIntegral.sum
  intro σ _
  apply IsIntegral.prod
  intro i _
  exact hM _ _

end PermutationSums

noncomputable section

private abbrev AlgQ := AlgebraicClosure ℚ

private noncomputable def integralBasisEmbedding
    (K : Type*) [Field K] [NumberField K] :
    Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →ₐ[ℚ] AlgQ) :=
  Fintype.equivOfCardEq <|
    (Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 K)).symm.trans <|
      (RingOfIntegers.rank K).trans <| (AlgHom.card ℚ K AlgQ).symm

private noncomputable def integralEmbeddingsMatrix
    (K : Type*) [Field K] [NumberField K] :
    Matrix (Free.ChooseBasisIndex ℤ (𝓞 K))
      (Free.ChooseBasisIndex ℤ (𝓞 K)) AlgQ :=
  Algebra.embeddingsMatrixReindex ℚ AlgQ (integralBasis K)
    (integralBasisEmbedding K)

private def postcompEmbeddingEquiv
    (K : Type*) [Field K] [NumberField K] (τ : AlgQ ≃ₐ[ℚ] AlgQ) :
    (K →ₐ[ℚ] AlgQ) ≃ (K →ₐ[ℚ] AlgQ) where
  toFun σ := τ.toAlgHom.comp σ
  invFun σ := τ.symm.toAlgHom.comp σ
  left_inv σ := by
    ext x
    simp
  right_inv σ := by
    ext x
    simp

private def embeddingIndexPerm
    (K : Type*) [Field K] [NumberField K] (τ : AlgQ ≃ₐ[ℚ] AlgQ) :
    Equiv.Perm (Free.ChooseBasisIndex ℤ (𝓞 K)) :=
  (integralBasisEmbedding K).trans
    ((postcompEmbeddingEquiv K τ).trans (integralBasisEmbedding K).symm)

private theorem integral_embeddings_matrix
    (K : Type*) [Field K] [NumberField K] (τ : AlgQ ≃ₐ[ℚ] AlgQ) :
    (integralEmbeddingsMatrix K).map τ =
      (integralEmbeddingsMatrix K).submatrix id (embeddingIndexPerm K τ) := by
  ext i j
  simp [integralEmbeddingsMatrix, Algebra.embeddingsMatrixReindex,
    embeddingIndexPerm, postcompEmbeddingEquiv]

private theorem permanent_embeddings_fixed
    (K : Type*) [Field K] [NumberField K] (τ : AlgQ ≃ₐ[ℚ] AlgQ) :
    τ (integralEmbeddingsMatrix K).permanent =
      (integralEmbeddingsMatrix K).permanent := by
  calc
    τ (integralEmbeddingsMatrix K).permanent =
        ((integralEmbeddingsMatrix K).map τ).permanent := by
          simp [Matrix.permanent]
    _ = ((integralEmbeddingsMatrix K).submatrix id
          (embeddingIndexPerm K τ)).permanent := by
          rw [integral_embeddings_matrix]
    _ = (integralEmbeddingsMatrix K).permanent :=
      Matrix.permanent_permute_rows (embeddingIndexPerm K τ)
        (integralEmbeddingsMatrix K)

private theorem embeddings_matrix_entry
    (K : Type*) [Field K] [NumberField K]
    (i j : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    IsIntegral ℤ (integralEmbeddingsMatrix K i j) := by
  change IsIntegral ℤ
    ((integralBasisEmbedding K j) (integralBasis K i))
  apply IsIntegral.map
  simpa only [integralBasis_apply] using
    (RingOfIntegers.basis K i).property

private theorem permanent_embeddings_matrix
    (K : Type*) [Field K] [NumberField K] :
    IsIntegral ℤ (integralEmbeddingsMatrix K).permanent := by
  rw [Matrix.permanent]
  apply IsIntegral.sum
  intro σ _
  apply IsIntegral.prod
  intro i _
  exact embeddings_matrix_entry K _ _

private theorem integral_parts_product
    (K : Type*) [Field K] [NumberField K] :
    IsIntegral ℤ
      (evenPart (integralEmbeddingsMatrix K) * oddPart (integralEmbeddingsMatrix K)) :=
  (integral_even_part _ (embeddings_matrix_entry K)).mul
    (integral_odd_part _ (embeddings_matrix_entry K))

private theorem discr_det_embeddings
    (K : Type*) [Field K] [NumberField K] :
    algebraMap ℤ AlgQ (NumberField.discr K) =
      (integralEmbeddingsMatrix K).det ^ 2 := by
  calc
    algebraMap ℤ AlgQ (NumberField.discr K) =
        algebraMap ℚ AlgQ (NumberField.discr K : ℚ) := by simp
    _ = algebraMap ℚ AlgQ (Algebra.discr ℚ (integralBasis K)) := by
      rw [NumberField.coe_discr]
    _ = (integralEmbeddingsMatrix K).det ^ 2 := by
      exact Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two
        ℚ AlgQ (integralBasis K) (integralBasisEmbedding K)

private theorem parts_product_fixed
    (K : Type*) [Field K] [NumberField K] (τ : AlgQ ≃ₐ[ℚ] AlgQ) :
    τ (evenPart (integralEmbeddingsMatrix K) * oddPart (integralEmbeddingsMatrix K)) =
      evenPart (integralEmbeddingsMatrix K) * oddPart (integralEmbeddingsMatrix K) := by
  let M := integralEmbeddingsMatrix K
  let q := evenPart M * oddPart M
  have hd : M.det ^ 2 = M.permanent ^ 2 - 4 * q :=
    det_permanent_parts M
  have hdet : τ (M.det ^ 2) = M.det ^ 2 := by
    rw [← discr_det_embeddings K]
    simp
  have hperm : τ M.permanent = M.permanent :=
    permanent_embeddings_fixed K τ
  have hdτ := congrArg τ hd
  simp only [map_pow, map_sub, map_mul, map_ofNat] at hdτ
  have hdet' : τ M.det ^ 2 = M.det ^ 2 := by
    simpa only [map_pow] using hdet
  rw [hdet', hperm] at hdτ
  have hmul : (4 : AlgQ) * τ q = 4 * q := by
    calc
      (4 : AlgQ) * τ q = M.permanent ^ 2 - M.det ^ 2 := by
        rw [hdτ]
        ring
      _ = 4 * q := by
        rw [hd]
        ring
  exact mul_left_cancel₀ (by norm_num : (4 : AlgQ) ≠ 0) hmul

private theorem int_fixed_integral
    {x : AlgQ} (hx : IsIntegral ℤ x)
    (hfix : ∀ τ : AlgQ ≃ₐ[ℚ] AlgQ, τ x = x) :
    ∃ z : ℤ, algebraMap ℤ AlgQ z = x := by
  letI : IsAlgClosure ℚ AlgQ :=
    AlgebraicClosure.instIsAlgClosure ℚ
  letI : Algebra.IsSeparable ℚ AlgQ :=
    IsAlgClosure.separable ℚ AlgQ
  letI : Normal ℚ AlgQ :=
    IsAlgClosure.normal ℚ AlgQ
  letI : IsGalois ℚ AlgQ :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  obtain ⟨r, hr⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hrint : IsIntegral ℤ r := by
    apply (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom ℤ ℚ AlgQ)
      (algebraMap ℚ AlgQ).injective).mp
    simpa only [IsScalarTower.toAlgHom_apply, hr] using hx
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrint
  refine ⟨z, ?_⟩
  rw [← hr, ← hz]
  simp

private theorem discr_sq_four
    (K : Type*) [Field K] [NumberField K] :
    ∃ p q : ℤ, NumberField.discr K = p ^ 2 - 4 * q := by
  let M := integralEmbeddingsMatrix K
  obtain ⟨p, hp⟩ := int_fixed_integral
    (permanent_embeddings_matrix K)
    (permanent_embeddings_fixed K)
  obtain ⟨q, hq⟩ := int_fixed_integral
    (integral_parts_product K) (parts_product_fixed K)
  refine ⟨p, q, ?_⟩
  apply (Int.cast_injective : Function.Injective (fun z : ℤ ↦ (z : AlgQ)))
  change algebraMap ℤ AlgQ (NumberField.discr K) =
    algebraMap ℤ AlgQ (p ^ 2 - 4 * q)
  rw [map_sub, map_pow, map_mul, map_ofNat, hp, hq,
    discr_det_embeddings]
  exact det_permanent_parts M

private theorem sq_emod_four (x : ℤ) :
    x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have hx0 : 0 ≤ x % 4 := Int.emod_nonneg _ (by norm_num)
  have hx4 : x % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hsq : x ^ 2 % 4 = (x % 4) ^ 2 % 4 :=
    ((Int.mod_modEq x 4).pow 2).symm.eq
  rw [hsq]
  interval_cases hx : x % 4 <;> norm_num [hx]

/-- Proposition 2.40(a): the sign of a number-field discriminant is determined by the
number of conjugate pairs of complex embeddings. -/
theorem sign_number_discr
    (K : Type*) [Field K] [NumberField K] :
    (NumberField.discr K).sign =
      (-1) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  exact NumberField.sign_discr K

/-- Proposition 2.40(b), Stickelberger's theorem: a number-field discriminant is congruent
to zero or one modulo four. -/
theorem discr_emod_four
    (K : Type*) [Field K] [NumberField K] :
    NumberField.discr K % 4 = 0 ∨ NumberField.discr K % 4 = 1 := by
  obtain ⟨p, q, hdisc⟩ := discr_sq_four K
  rw [hdisc, Int.sub_emod, Int.mul_emod]
  simpa using sq_emod_four p

end

end Submission.NumberTheory.Milne
