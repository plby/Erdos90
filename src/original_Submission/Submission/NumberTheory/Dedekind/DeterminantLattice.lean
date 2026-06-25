import Submission.NumberTheory.Dedekind.DedekindModules
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Milne, Algebraic Number Theory, determinant lattices

We identify the easy inclusion in the determinant lattice of `A^n × I`: every determinant
of a tuple of lattice vectors belongs to the fractional ideal `I`.
-/

namespace Submission.NumberTheory.Milne

open scoped nonZeroDivisors

noncomputable def fractionalLatticeMap
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A)) :
    ((Fin n → A) × I) →ₗ[A] (Fin (n + 1) → FractionRing A) where
  toFun x := Fin.lastCases (x.2 : FractionRing A)
    (fun i ↦ algebraMap A (FractionRing A) (x.1 i))
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' a x := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [Algebra.smul_def]
    · simp only [Prod.smul_fst, Pi.smul_apply, RingHom.id_apply,
        Fin.lastCases_castSucc]
      simp [Algebra.smul_def, map_mul]

@[simp]
theorem fractional_lattice_cast
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A))
    (x : (Fin n → A) × I) (i : Fin n) :
    fractionalLatticeMap A n I x i.castSucc =
      algebraMap A (FractionRing A) (x.1 i) := by
  simp [fractionalLatticeMap]

@[simp]
theorem fractional_lattice_last
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A))
    (x : (Fin n → A) × I) :
    fractionalLatticeMap A n I x (Fin.last n) = x.2.1 := by
  simp [fractionalLatticeMap]

theorem fractional_lattice_det
    (A : Type*) [CommRing A] [IsDomain A]
    (n : ℕ) (I : FractionalIdeal A⁰ (FractionRing A))
    (v : Fin (n + 1) → ((Fin n → A) × I)) :
    (Pi.basisFun (FractionRing A) (Fin (n + 1))).det
        (fractionalLatticeMap A n I ∘ v) ∈ I := by
  rw [Pi.basisFun_det_apply, Matrix.det_apply]
  apply Submodule.sum_mem
  intro σ _
  rw [Fin.prod_univ_castSucc]
  simp only [Function.comp_apply, Matrix.of_apply,
    fractional_lattice_cast, fractional_lattice_last]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul (FractionRing A), smul_eq_mul]
  change ((σ.sign : ℤ) : FractionRing A) *
      ((∏ i : Fin n,
          algebraMap A (FractionRing A) ((v (σ i.castSucc)).1 i)) *
        (v (σ (Fin.last n))).2.1) ∈ I
  rw [show ((σ.sign : ℤ) : FractionRing A) =
      algebraMap A (FractionRing A) ((σ.sign : ℤ) : A) by simp]
  rw [← map_prod]
  rw [← mul_assoc, ← map_mul]
  rw [← Algebra.smul_def]
  exact I.val.smul_mem _ (v (σ (Fin.last n))).2.2

end Submission.NumberTheory.Milne
