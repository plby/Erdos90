import Towers.ClassField.BrauerGroups.BrauerGroup
import Towers.ClassField.BrauerGroups.ScalarExtensionCentral

/-!
# Chapter IV, Section 2: scalar extension on Brauer groups

Scalar extension of central simple algebras descends to a homomorphism of
Brauer groups.  The relative Brauer group is its kernel.
-/

namespace Towers.CField.BGroups

open scoped TensorProduct

noncomputable section

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance low] Algebra.TensorProduct.rightAlgebra

/-- Scalar extension of a central simple `k`-algebra, packaged as a central
simple `K`-algebra. -/
def scalarExtensionCSA (A : CSA.{u, u} k) : CSA.{u, u} K := by
  have hCSA := scalar_extension_simple k K A
  letI : IsSimpleRing (A ⊗[k] K) := hCSA.1
  letI : Algebra.IsCentral K (A ⊗[k] K) := hCSA.2
  letI : Module.Finite K (K ⊗[k] A) := Module.Finite.base_change k K A
  letI : Module.Finite K (A ⊗[k] K) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k K A).toLinearEquiv
  exact centralSimpleCSA K (A ⊗[k] K)

/-- An algebra equivalence remains an algebra equivalence after extending
scalars on the right. -/
def scalarExtensionAlg
    (A B : Type u) [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (e : A ≃ₐ[k] B) : A ⊗[k] K ≃ₐ[K] B ⊗[k] K :=
  { Algebra.TensorProduct.congr e AlgEquiv.refl with
    commutes' := by
      intro x
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply]
      simp }

/-- Scalar extension commutes with forming matrix algebras. -/
def scalarMatrixAlg
    (A : Type u) [Ring A] [Algebra k A] (n : ℕ) :
    Matrix (Fin n) (Fin n) A ⊗[k] K ≃ₐ[K]
      Matrix (Fin n) (Fin n) (A ⊗[k] K) :=
  (Algebra.TensorProduct.commRight k K (Matrix (Fin n) (Fin n) A)).symm |>.trans
    ({ tensorMatrixEquiv (k := k) (A := K) (D := A) (Fin n) with
      commutes' := by
        intro x
        change tensorMatrixEquiv
          (k := k) (A := K) (D := A) (Fin n) (x ⊗ₜ[k] 1) = _
        simp only [tensorMatrixEquiv, AlgEquiv.trans_apply,
          Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
          map_one, Algebra.TensorProduct.one_def,
          Algebra.TensorProduct.assoc_symm_tmul,
          matrixEquivTensor_apply_symm]
        ext i j
        simp [Matrix.one_apply, Matrix.algebraMap_matrix_apply,
          Algebra.TensorProduct.algebraMap_apply] } :
      K ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[K]
        Matrix (Fin n) (Fin n) (K ⊗[k] A)) |>.trans
      (AlgEquiv.mapMatrix (Algebra.TensorProduct.commRight k K A))

/-- A matrix-algebra equivalence extends to the corresponding matrix-algebra
equivalence after scalar extension. -/
def scalarMatrixCongr
    (A B : Type u) [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (n m : ℕ)
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k]
      Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A ⊗[k] K) ≃ₐ[K]
      Matrix (Fin m) (Fin m) (B ⊗[k] K) :=
  (scalarMatrixAlg k K A n).symm |>.trans
    (scalarExtensionAlg k K _ _ e) |>.trans
      (scalarMatrixAlg k K B m)

/-- Brauer equivalence is preserved by scalar extension. -/
theorem IsBrauerEquivalent.scalarExtension
    {A B : CSA.{u, u} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (scalarExtensionCSA k K A)
      (scalarExtensionCSA k K B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm,
    ⟨scalarMatrixCongr k K A B n m e⟩⟩

/-- Scalar extension as a function on Brauer classes. -/
def brauerChangeFn : BrauerGroup.{u, u} k → BrauerGroup.{u, u} K :=
  Quotient.lift
    (fun A ↦ brauerClass K (scalarExtensionCSA k K A))
    fun _ _ h ↦
      Quotient.sound (IsBrauerEquivalent.scalarExtension (k := k) (K := K) h)

/-- The right scalar extension of the base field is the larger field. -/
def scalarExtensionBase :
    k ⊗[k] K ≃ₐ[K] K :=
  { Algebra.TensorProduct.lid k K with
    commutes' := by
      intro x
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp }

/-- Scalar extension commutes with tensor products of algebras. -/
def scalarTensorAlg
    (A B : Type u) [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
    (A ⊗[k] B) ⊗[k] K ≃ₐ[K]
      (A ⊗[k] K) ⊗[K] (B ⊗[k] K) := by
  let e₁ := Algebra.TensorProduct.congr
      (Algebra.TensorProduct.commRight k K A).symm
      (Algebra.TensorProduct.commRight k K B).symm
  let e₂ := Algebra.TensorProduct.tensorTensorTensorComm k k K K K A K B
  let e₃ := by
    letI : Algebra K (K ⊗[K] K) := Algebra.TensorProduct.instAlgebra
    exact Algebra.TensorProduct.congr
      (Algebra.TensorProduct.lid K K)
      (AlgEquiv.refl : (A ⊗[k] B) ≃ₐ[k] (A ⊗[k] B))
  let e₄ := Algebra.TensorProduct.commRight k K (A ⊗[k] B)
  exact (e₁.trans (e₂.trans (e₃.trans e₄))).symm

/-- Scalar extension induces a homomorphism of Brauer groups. -/
def brauerBaseChange : BrauerGroup.{u, u} k →* BrauerGroup.{u, u} K where
  toFun := brauerChangeFn k K
  map_one' := by
    apply Quotient.sound
    exact brauer_equivalent_alg K _ _
      (scalarExtensionBase k K)
  map_mul' := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ A B =>
        apply Quotient.sound
        exact brauer_equivalent_alg K _ _
          (scalarTensorAlg k K A B)

/-- Milne's relative Brauer group `Br(K/k)`: the classes over `k` split by
scalar extension to `K`. -/
def relativeBrauerGroup : Subgroup (BrauerGroup.{u, u} k) :=
  (brauerBaseChange k K).ker

theorem relative_brauer_group (x : BrauerGroup.{u, u} k) :
    x ∈ relativeBrauerGroup k K ↔ brauerBaseChange k K x = 1 :=
  MonoidHom.mem_ker

end

end Towers.CField.BGroups
