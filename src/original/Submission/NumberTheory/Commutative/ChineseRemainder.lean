import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder

/-!
# Milne, Chapter 1, Theorems 1.14 and 1.15

The Chinese remainder theorem for a finite pairwise-coprime family of
ideals, first for the ring and then for an arbitrary module.
-/

namespace Submission.NumberTheory.Milne

open Function

variable {R : Type*} [CommRing R]
variable {iota : Type*} [Finite iota]

attribute [local instance] Fintype.ofFinite

/-- The product of a finite pairwise-coprime family of ideals is its
intersection, as in Milne's Theorem 1.14. -/
theorem pairwise_i_inf (I : iota → Ideal R)
    (hI : Pairwise (IsCoprime on I)) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  simpa using
    (Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := I) (by
        intro i _ j _ hij
        exact hI hij))

/-- Milne, Theorem 1.14: simultaneous representatives exist for arbitrary
residue classes modulo pairwise-coprime ideals. -/
theorem chinese_remainder (I : iota → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (x : iota → R) :
    ∃ r : R, ∀ i, r - x i ∈ I i :=
  Ideal.exists_forall_sub_mem_ideal hI x

/-- **Milne, Theorem 1.14.** Once `x` is one simultaneous solution, `y` is
another exactly when `y - x` belongs to the product of the moduli. -/
theorem chinese_remainder_solution
    (I : iota → Ideal R) (hI : Pairwise (IsCoprime on I))
    (residue : iota → R) {x : R}
    (hx : ∀ i, x - residue i ∈ I i) (y : R) :
    (∀ i, y - residue i ∈ I i) ↔ y - x ∈ ∏ i, I i := by
  constructor
  · intro hy
    rw [pairwise_i_inf I hI, Ideal.mem_iInf]
    intro i
    have heq : y - x = (y - residue i) - (x - residue i) := by ring
    rw [heq]
    exact (I i).sub_mem (hy i) (hx i)
  · intro hy i
    have hprod_le : (∏ j, I j) ≤ I i := by
      rw [pairwise_i_inf I hI]
      exact iInf_le I i
    have heq : y - residue i = (y - x) + (x - residue i) := by ring
    rw [heq]
    exact (I i).add_mem (hprod_le hy) (hx i)

/-- The ring-isomorphism form of Milne's Theorem 1.14. -/
noncomputable def chineseRemainderEquiv (I : iota → Ideal R)
    (hI : Pairwise (IsCoprime on I)) :
    (R ⧸ ∏ i, I i) ≃+* (∀ i, R ⧸ I i) :=
  Ideal.quotEquivOfEq (pairwise_i_inf I hI) |>.trans
    (Ideal.quotientInfRingEquivPiQuotient I hI)

section Module

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Milne, Theorem 1.15: the natural module Chinese-remainder map is
surjective, and its kernel is the product ideal times the module. -/
theorem chinese_remainder_ker
    (I : iota → Ideal R) (hI : Pairwise (IsCoprime on I)) :
    Surjective (LinearMap.pi fun i ↦
        TensorProduct.mk R (R ⧸ I i) M 1) ∧
      LinearMap.ker (LinearMap.pi fun i ↦
        TensorProduct.mk R (R ⧸ I i) M 1) =
        (∏ i, I i) • (⊤ : Submodule R M) := by
  constructor
  · exact Ideal.pi_tensorProductMk_quotient_surjective M I hI
  · rw [Ideal.ker_tensorProductMk_quotient M I hI,
      pairwise_i_inf I hI]

end Module

/-- Milne, Lemma 1.17: the tensor product of two surjective linear maps is
surjective. -/
theorem tensor_product_surjective
    {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M →ₗ[R] N) (g : P →ₗ[R] Q)
    (hf : Surjective f) (hg : Surjective g) :
    Surjective (TensorProduct.map f g) :=
  TensorProduct.map_surjective hf hg

end Submission.NumberTheory.Milne
