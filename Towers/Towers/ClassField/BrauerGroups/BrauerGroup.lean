import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Towers.ClassField.BrauerGroups.TensorProductCentral
import Towers.ClassField.BrauerGroups.MulLeftBijective

/-!
# Chapter IV, Definition of the Brauer group

Mathlib defines `CSA k`, Brauer equivalence, and `BrauerGroup k`, the quotient
of central simple algebras by Brauer equivalence.  This file records the
quotient interface used below and packages the base field as the distinguished
trivial class.  We then supply the tensor-product abelian group structure in
the same-universe case used throughout the class-field-theory development.
-/

namespace Towers.CField.BGroups

universe u v

variable (k : Type u) [Field k]

/-- Package a finite-dimensional central simple algebra as a member of
Mathlib's type `CSA`. -/
def centralSimpleCSA (A : Type v) [Ring A] [Algebra k A]
    [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A] : CSA.{u, v} k where
  toAlgCat := AlgCat.of k A
  isCentral := inferInstance
  isSimple := inferInstance
  fin_dim := inferInstance

/-- The canonical algebra equivalence from one-by-one matrices.  This
specialized version uses the standard `Fin 1` matrix instances, which is
convenient when unfolding `IsBrauerEquivalent`. -/
def matrixFinAlg (A : Type v) [Semiring A] [Algebra k A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[k] A where
  toFun M := M 0 0
  invFun a _ _ := a
  left_inv M := by
    ext i j
    simp only
    congr 1 <;> exact Subsingleton.elim _ _
  right_inv a := rfl
  map_add' _ _ := rfl
  map_mul' M N := by simp [Matrix.mul_apply]
  commutes' r := rfl

/-- The base field, regarded as a finite-dimensional central simple algebra
over itself. -/
def baseFieldCSA : CSA.{u, u} k where
  toAlgCat := AlgCat.of k k
  isCentral := by
    change Algebra.IsCentral k k
    infer_instance
  isSimple := inferInstance
  fin_dim := inferInstance

/-- The similarity class of a central simple algebra in Mathlib's Brauer
quotient. -/
def brauerClass (A : CSA.{u, v} k) : BrauerGroup.{u, v} k :=
  Quotient.mk'' A

/-- Equality of Brauer classes is exactly Brauer equivalence. -/
theorem brauer_class (A B : CSA.{u, v} k) :
    brauerClass k A = brauerClass k B ↔ IsBrauerEquivalent A B := by
  constructor
  · exact Quotient.exact
  · intro h
    change Quotient.mk'' A = Quotient.mk'' B
    exact Quotient.sound h

/-- A central simple algebra which is a full matrix algebra over `k` represents
the base-field class. -/
theorem brauer_equivalent_matrix
    (A : CSA.{u, u} k) (n : ℕ) (hn : n ≠ 0)
    (e : A ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    IsBrauerEquivalent A (baseFieldCSA k) := by
  refine ⟨1, n, one_ne_zero, hn, ?_⟩
  change Nonempty (Matrix (Fin 1) (Fin 1) A ≃ₐ[k] Matrix (Fin n) (Fin n) k)
  exact ⟨(matrixFinAlg k A).trans e⟩

/-- Algebra-isomorphic central simple algebras are Brauer equivalent. -/
theorem brauer_equivalent_alg (A B : CSA.{u, u} k)
    (e : A ≃ₐ[k] B) : IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

noncomputable section

open scoped TensorProduct

/-- The tensor product of two central simple algebras, packaged as a central
simple algebra. -/
def tensorCSA (A B : CSA.{u, u} k) : CSA.{u, u} k := by
  letI : IsSimpleRing (A ⊗[k] B) :=
    tensor_simple_ring k A B
  letI : Algebra.IsCentral k (A ⊗[k] B) := tensor_product_central k A B
  exact centralSimpleCSA k (A ⊗[k] B)

/-- The opposite of a central simple algebra, packaged as a central simple
algebra. -/
def oppositeCSA (A : CSA.{u, u} k) : CSA.{u, u} k :=
  centralSimpleCSA k Aᵐᵒᵖ

/-- Matrices over two coefficient algebras tensor to matrices over the tensor
product. -/
def matrixTensorCoefficients
    (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (n p : ℕ) :
    Matrix (Fin n) (Fin n) A ⊗[k] Matrix (Fin p) (Fin p) B ≃ₐ[k]
      Matrix (Fin (n * p)) (Fin (n * p)) (A ⊗[k] B) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) k k A B).trans <|
    Matrix.reindexAlgEquiv k (A ⊗[k] B) finProdFinEquiv

/-- Brauer equivalence is compatible with tensor products. -/
theorem IsBrauerEquivalent.tensor
    {A A' B B' : CSA.{u, u} k}
    (hA : IsBrauerEquivalent A A') (hB : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (tensorCSA k A B) (tensorCSA k A' B') := by
  obtain ⟨n, m, hn, hm, ⟨eA⟩⟩ := hA
  obtain ⟨p, q, hp, hq, ⟨eB⟩⟩ := hB
  refine ⟨n * p, m * q, mul_ne_zero hn hp, mul_ne_zero hm hq, ?_⟩
  exact ⟨(matrixTensorCoefficients k A B n p).symm |>.trans
    ((Algebra.TensorProduct.congr eA eB).trans <|
      matrixTensorCoefficients k A' B' m q)⟩

/-- Brauer equivalence is compatible with passage to opposite algebras. -/
theorem IsBrauerEquivalent.opposite
    {A B : CSA.{u, u} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (oppositeCSA k A) (oppositeCSA k B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  let en : Matrix (Fin n) (Fin n) Aᵐᵒᵖ ≃ₐ[k]
      (Matrix (Fin n) (Fin n) A)ᵐᵒᵖ := AlgEquiv.mopMatrix
  let em : Matrix (Fin m) (Fin m) Bᵐᵒᵖ ≃ₐ[k]
      (Matrix (Fin m) (Fin m) B)ᵐᵒᵖ := AlgEquiv.mopMatrix
  exact ⟨en.trans ((AlgEquiv.op e).trans em.symm)⟩

/-- Tensor product on representatives descends to the Brauer quotient. -/
def brauerMul (x y : BrauerGroup.{u, u} k) : BrauerGroup.{u, u} k :=
  Quotient.liftOn₂ x y
    (fun A B ↦ brauerClass k (tensorCSA k A B))
    fun _ _ _ _ hA hB ↦
      Quotient.sound (IsBrauerEquivalent.tensor (k := k) hA hB)

/-- Passage to the opposite algebra descends to the Brauer quotient. -/
def brauerInv (x : BrauerGroup.{u, u} k) : BrauerGroup.{u, u} k :=
  Quotient.liftOn x (fun A ↦ brauerClass k (oppositeCSA k A))
    fun _ _ h ↦
      Quotient.sound (IsBrauerEquivalent.opposite (k := k) h)

/-- Milne's abelian group structure on similarity classes of central simple
algebras. -/
instance : CommGroup (BrauerGroup.{u, u} k) where
  mul := brauerMul k
  one := brauerClass k (baseFieldCSA k)
  inv := brauerInv k
  mul_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ A B C =>
        apply Quotient.sound
        exact brauer_equivalent_alg k _ _
          (Algebra.TensorProduct.assoc k k k A B C)
  one_mul := by
    intro x
    induction x using Quotient.inductionOn with
    | _ A =>
        apply Quotient.sound
        exact brauer_equivalent_alg k _ _
          (Algebra.TensorProduct.lid k A)
  mul_one := by
    intro x
    induction x using Quotient.inductionOn with
    | _ A =>
        apply Quotient.sound
        exact brauer_equivalent_alg k _ _
          (Algebra.TensorProduct.rid k k A)
  inv_mul_cancel := by
    intro x
    induction x using Quotient.inductionOn with
    | _ A =>
        apply Quotient.sound
        exact brauer_equivalent_matrix k _
          (Module.finrank k A) (Module.finrank_pos.ne')
          ((Algebra.TensorProduct.comm k Aᵐᵒᵖ A).trans (tensorEquivMatrix k A))
  mul_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ A B =>
        apply Quotient.sound
        exact brauer_equivalent_alg k _ _
          (Algebra.TensorProduct.comm k A B)

end

/-- If every central simple algebra is a full matrix algebra over the base
field, then the Brauer quotient has only one element. -/
theorem subsingleton_matrix_classification
    (h : ∀ A : CSA.{u, u} k, ∃ (n : ℕ), n ≠ 0 ∧
      Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k)) :
    Subsingleton (BrauerGroup.{u, u} k) := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | _ A =>
      induction y using Quotient.inductionOn with
      | _ B =>
          obtain ⟨n, hn, ⟨eA⟩⟩ := h A
          obtain ⟨m, hm, ⟨eB⟩⟩ := h B
          exact Quotient.sound <|
            (brauer_equivalent_matrix k A n hn eA).trans
              (brauer_equivalent_matrix k B m hm eB).symm

end Towers.CField.BGroups
