import Submission.ClassField.BrauerGroups.BaseChangeBrauer

/-!
# Scalar extension from `Type 0` to an ambient universe

The standard `brauerBaseChange` API places both fields and all CSA carriers
in one universe.  Number-field completions in an arbitrary universe are
`Small.{0}`, so comparison with the categorical Type-0 local reciprocity map
needs the special case of scalar extension from a Type-0 field to a field in
`Type u`.  In this case every scalar-extended CSA carrier lies in `Type u`,
and the usual Brauer-group construction applies without resizing the target.
-/

namespace Submission.CField.BGroups

open scoped TensorProduct

noncomputable section

universe u

variable (k : Type) (K : Type u) [Field k] [Field K] [Algebra k K]

attribute [local instance low] Algebra.TensorProduct.rightAlgebra

/-- A Type-0 central simple algebra after scalar extension to an ambient
field. -/
def scalarCSAUniverse
    (A : CSA.{0, 0} k) : CSA.{u, u} K := by
  have hCSA := scalar_extension_simple k K A
  letI : IsSimpleRing (A ⊗[k] K) := hCSA.1
  letI : Algebra.IsCentral K (A ⊗[k] K) := hCSA.2
  letI : Module.Finite K (K ⊗[k] A) := Module.Finite.base_change k K A
  letI : Module.Finite K (A ⊗[k] K) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight k K A).toLinearEquiv
  exact centralSimpleCSA K (A ⊗[k] K)

/-- An equivalence of Type-0 algebras remains an equivalence after scalar
extension to the ambient field. -/
def scalarExtensionUniverse
    (A B : Type) [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (e : A ≃ₐ[k] B) : A ⊗[k] K ≃ₐ[K] B ⊗[k] K :=
  { Algebra.TensorProduct.congr e AlgEquiv.refl with
    commutes' := by
      intro x
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply]
      simp }

/-- Scalar extension from `Type 0` commutes with matrix algebras. -/
def scalarMatrixUniverse
    (A : Type) [Ring A] [Algebra k A] (n : ℕ) :
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

/-- A Type-0 matrix-algebra equivalence extends to the ambient field. -/
def matrixCongrUniverse
    (A B : Type) [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (n m : ℕ)
    (e : Matrix (Fin n) (Fin n) A ≃ₐ[k]
      Matrix (Fin m) (Fin m) B) :
    Matrix (Fin n) (Fin n) (A ⊗[k] K) ≃ₐ[K]
      Matrix (Fin m) (Fin m) (B ⊗[k] K) :=
  (scalarMatrixUniverse k K A n).symm |>.trans
    (scalarExtensionUniverse k K _ _ e) |>.trans
      (scalarMatrixUniverse k K B m)

/-- Brauer equivalence of Type-0 CSAs is preserved after extension to the
ambient field. -/
theorem IsBrauerEquivalent.scalar_ext_zerou
    {A B : CSA.{0, 0} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (scalarCSAUniverse k K A)
      (scalarCSAUniverse k K B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm,
    ⟨matrixCongrUniverse k K A B n m e⟩⟩

/-- Type-0-to-ambient scalar extension as a function on Brauer classes. -/
def brauerUniverseFn :
    BrauerGroup.{0, 0} k → BrauerGroup.{u, u} K :=
  Quotient.lift
    (fun A => brauerClass K (scalarCSAUniverse k K A))
    fun _ _ h => Quotient.sound
      (IsBrauerEquivalent.scalar_ext_zerou
        (k := k) (K := K) h)

/-- The right scalar extension of the Type-0 base field is the ambient
field. -/
def scalarAlgUniverse :
    k ⊗[k] K ≃ₐ[K] K :=
  { Algebra.TensorProduct.lid k K with
    commutes' := by
      intro x
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp }

/-- Type-0-to-ambient scalar extension commutes with tensor products. -/
def scalarTensorUniverse
    (A B : Type) [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
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

/-- Scalar extension from a Type-0 field to a field in `Type u` induces a
homomorphism on the corresponding same-carrier-universe Brauer groups. -/
def brauerChangeUniverse :
    BrauerGroup.{0, 0} k →* BrauerGroup.{u, u} K where
  toFun := brauerUniverseFn k K
  map_one' := by
    apply Quotient.sound
    exact brauer_equivalent_alg K _ _
      (scalarAlgUniverse k K)
  map_mul' := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ A B =>
        apply Quotient.sound
        exact brauer_equivalent_alg K _ _
          (scalarTensorUniverse k K A B)

/-- Scalar extension on a representative is represented by the literal
scalar-extended central simple algebra. -/
theorem brauer_base_universe
    (A : CSA.{0, 0} k) :
    brauerChangeUniverse k K (brauerClass k A) =
      brauerClass K (scalarCSAUniverse k K A) :=
  rfl

/-- In `Type 0`, the mixed-universe construction reduces to the original
same-universe scalar-extension homomorphism. -/
theorem brauer_change_universe
    (k K : Type) [Field k] [Field K] [Algebra k K] :
    brauerChangeUniverse k K = brauerBaseChange k K := by
  apply MonoidHom.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ A => rfl

end


end Submission.CField.BGroups
