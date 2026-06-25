import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Submission.ClassField.BrauerGroups.RelativeBrauerGroup
import Submission.ClassField.CrossedProducts.LeCentralizer

/-!
# Chapter IV, Corollary 3.10

Every Brauer class is split by a finite Galois extension contained in a fixed
separable closure.  The relative Brauer groups are the kernels of scalar
extension on Brauer groups.
-/

namespace Submission.CField.CProduca

open scoped TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance high] Algebra.TensorProduct.leftAlgebra

private noncomputable def tensorRightCongr
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (e : A ≃ₐ[k] B) : A ⊗[k] L ≃ₐ[L] B ⊗[k] L :=
  { Algebra.TensorProduct.congr e AlgEquiv.refl with
    commutes' := by
      intro l
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply]
      simp }

private noncomputable def tensorMatrixAlg
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] (n : ℕ) :
    L ⊗[k] Matrix (Fin n) (Fin n) A ≃ₐ[L]
      Matrix (Fin n) (Fin n) (L ⊗[k] A) :=
  { BGroups.tensorMatrixEquiv (k := k) (A := L) (D := A) (Fin n) with
    commutes' := by
      intro l
      change BGroups.tensorMatrixEquiv
        (k := k) (A := L) (D := A) (Fin n) (l ⊗ₜ[k] 1) = _
      simp only [BGroups.tensorMatrixEquiv, AlgEquiv.trans_apply,
        Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one,
        Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_symm_tmul,
        matrixEquivTensor_apply_symm]
      ext i j
      simp [Matrix.one_apply, Matrix.algebraMap_matrix_apply,
        Algebra.TensorProduct.algebraMap_apply] }

private noncomputable def scalarMatrixEquiv
    (k L A : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] (n : ℕ) :
    Matrix (Fin n) (Fin n) A ⊗[k] L ≃ₐ[L]
      Matrix (Fin n) (Fin n) (A ⊗[k] L) :=
  (Algebra.TensorProduct.commRight k L (Matrix (Fin n) (Fin n) A)).symm |>.trans
    (tensorMatrixAlg k L A n) |>.trans
      (AlgEquiv.mapMatrix (Algebra.TensorProduct.commRight k L A))

private noncomputable def tensorLidRight
    (L M : Type u) [Field L] [Field M] [Algebra L M] :
    L ⊗[L] M ≃ₐ[M] M :=
  { Algebra.TensorProduct.lid L M with
    commutes' := by
      intro m
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp }

private noncomputable def tensorRidLeft
    (L M : Type u) [Field L] [Field M] [Algebra L M] :
    M ⊗[L] L ≃ₐ[M] M :=
  (Algebra.TensorProduct.commRight L M L).trans (tensorLidRight L M)

private noncomputable def cancelLeftChange
    (k L M A : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [Ring A] [Algebra k A] :
    (M ⊗[L] L) ⊗[k] A ≃ₐ[M] M ⊗[k] A :=
  { Algebra.TensorProduct.congr ((tensorRidLeft L M).restrictScalars k)
      AlgEquiv.refl with
    commutes' := by
      intro m
      simp [tensorRidLeft, tensorLidRight] }

private noncomputable def baseChangeTower
    (k L M A : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [Ring A] [Algebra k A] :
    (A ⊗[k] L) ⊗[L] M ≃ₐ[M] A ⊗[k] M :=
  (tensorRightCongr L M (A ⊗[k] L) (L ⊗[k] A)
      (Algebra.TensorProduct.commRight k L A).symm).trans
    (Algebra.TensorProduct.commRight L M (L ⊗[k] A)).symm |>.trans
      (Algebra.TensorProduct.assoc k L M M L A).symm |>.trans
        (cancelLeftChange k L M A) |>.trans
          (Algebra.TensorProduct.commRight k M A)

/-- If an extension splits a central simple algebra, every further field
extension also splits it. -/
theorem ISBy.tower
    (k L M A : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [Ring A] [Algebra k A]
    (h : BGroups.ISBy k L A) : BGroups.ISBy k M A := by
  obtain ⟨n, hn, ⟨e⟩⟩ := h
  refine ⟨n, hn, ⟨?_⟩⟩
  exact (baseChangeTower k L M A).symm |>.trans
    (tensorRightCongr L M (A ⊗[k] L) (Matrix (Fin n) (Fin n) L) e) |>.trans
      (scalarMatrixEquiv L M L n) |>.trans
        (AlgEquiv.mapMatrix (tensorLidRight L M))

/-- A finite-dimensional central division algebra is split by a finite Galois
extension in the fixed separable closure. -/
theorem galois_splitting_division
    (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k D] [Module.Finite k D] :
    ∃ L : FiniteGaloisIntermediateField k (SeparableClosure k),
      BGroups.ISBy k L D := by
  classical
  obtain ⟨E, hcomm, hmax, hsep⟩ := maximal_separable_subfield k D
  letI : IsSimpleRing E :=
    commutative_subalgebra_simple k D E hcomm
  letI : Field E :=
    fieldCommutativeSubalgebra k D E hcomm
  letI : Algebra.IsSeparable k E := hsep
  have hdim : Module.finrank k D = (Module.finrank k E) ^ 2 :=
    (maximal_subfield_sq k D E hcomm).1 hmax
  have hsplitE : BGroups.ISBy k E D :=
    embedding_split_sq k E D E.val hdim
  let i : E →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let E' : IntermediateField k (SeparableClosure k) := i.fieldRange
  let eE : E ≃ₐ[k] E' := AlgEquiv.ofInjectiveField i
  letI : Module.Finite k E' := Module.Finite.equiv eE.toLinearEquiv
  letI : Algebra.IsSeparable k E' := AlgEquiv.Algebra.isSeparable eE
  letI : Algebra E E' := eE.toRingHom.toAlgebra
  letI : IsScalarTower k E E' := IsScalarTower.of_algebraMap_eq fun r => by
    exact (eE.commutes r).symm
  have hsplitE' : BGroups.ISBy k E' D :=
    ISBy.tower k E E' D hsplitE
  let N : IntermediateField k (SeparableClosure k) :=
    IntermediateField.normalClosure k E' (SeparableClosure k)
  letI : FiniteDimensional k N :=
    normalClosure.is_finiteDimensional k E' (SeparableClosure k)
  letI : IsGalois k N := IsGalois.normalClosure k E' (SeparableClosure k)
  have hsplitN : BGroups.ISBy k N D :=
    ISBy.tower k E' N D hsplitE'
  let L : FiniteGaloisIntermediateField k (SeparableClosure k) :=
    { N with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  exact ⟨L, hsplitN⟩

/-- Every finite-dimensional central simple algebra is split by a finite
Galois extension in the fixed separable closure. -/
theorem galois_splitting_field
    (k : Type u) [Field k] (A : CSA.{u, u} k) :
    ∃ L : FiniteGaloisIntermediateField k (SeparableClosure k),
      BGroups.ISBy k L A := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨m, hm, D, hDdiv, hDalg, hDfin, ⟨eA⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  letI : NeZero m := hm
  letI : DivisionRing D := hDdiv
  letI : Algebra k D := hDalg
  letI : Module.Finite k D := hDfin
  letI : Algebra.IsCentral k (Matrix (Fin m) (Fin m) D) :=
    Algebra.IsCentral.of_algEquiv k A _ eA
  letI : Algebra.IsCentral k (D ⊗[k] Matrix (Fin m) (Fin m) k) :=
    Algebra.IsCentral.of_algEquiv k _ _ (matrixEquivTensor (Fin m) k D)
  letI : Algebra.IsCentral k D :=
    Algebra.IsCentral.left_of_tensor_of_field k D (Matrix (Fin m) (Fin m) k)
  have hAD : IsBrauerEquivalent (BGroups.centralSimpleCSA k A)
      (BGroups.centralDivisionCSA k D) := by
    refine ⟨1, m, one_ne_zero, NeZero.ne m, ?_⟩
    exact ⟨(BGroups.matrixFinAlg k A).trans eA⟩
  obtain ⟨L, hsplitD⟩ := galois_splitting_division k D
  exact ⟨L, split_equivalent k L A D hAD hsplitD⟩

/-- The underlying set of Milne's relative Brauer group `Br(L/k)`. -/
def relativeBrauerClasses
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :
    Set (BrauerGroup.{u, u} k) :=
  BGroups.relativeBrauerGroup k L

/-- Milne, Corollary IV.3.10: the Brauer quotient is the union of the
relative Brauer classes over the finite Galois extensions in a fixed
separable closure. -/
theorem brauer_i_classes
    (k : Type u) [Field k] :
    (Set.univ : Set (BrauerGroup.{u, u} k)) =
      ⋃ L : FiniteGaloisIntermediateField k (SeparableClosure k),
        relativeBrauerClasses k L := by
  ext x
  simp only [Set.mem_univ, true_iff]
  induction x using Quotient.inductionOn with
  | _ A =>
      obtain ⟨L, hsplit⟩ := galois_splitting_field k A
      exact Set.mem_iUnion.2 ⟨L,
        (BGroups.brauer_relative_split k L A).2 hsplit⟩

end

end Submission.CField.CProduca
