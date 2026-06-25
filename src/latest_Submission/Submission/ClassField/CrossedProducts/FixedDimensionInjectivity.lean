import Submission.ClassField.BrauerGroups.CentralDivisionCSA
import Submission.ClassField.CrossedProducts.CrossedProductBrauer
import Submission.ClassField.CrossedProducts.Classification

/-!
# Chapter IV, Section 3, Theorem 3.14: the fixed-dimension injectivity step

This file proves Milne's fixed-dimension injectivity step: Brauer-equivalent
central simple algebras of equal dimension are isomorphic.  It also proves
that every class split by `L` is represented by a crossed product.  The
cohomology quotient and the resulting surjective map to the relative Brauer
group are constructed in `Theorem314Cohomology`.
-/

namespace Submission.CField.CProduca

noncomputable section

open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k]
  [Ring A] [Algebra k A] [IsSimpleRing A] [Algebra.IsCentral k A]
  [Module.Finite k A]
  [Ring B] [Algebra k B] [IsSimpleRing B] [Algebra.IsCentral k B]
  [Module.Finite k B]

/-- Milne, Theorem IV.3.14, injectivity step: within a fixed dimension, a
Brauer class contains at most one isomorphism class of central simple
algebras. -/
theorem nonempty_equivalent_finrank
    (hAB : IsBrauerEquivalent
      (BGroups.centralSimpleCSA k A)
      (BGroups.centralSimpleCSA k B))
    (hdim : Module.finrank k A = Module.finrank k B) :
    Nonempty (A ≃ₐ[k] B) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨eA⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k A
  obtain ⟨m, hm, E, hEdiv, hEalg, hEfin, ⟨eB⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
  letI : NeZero n := hn
  letI : NeZero m := hm
  letI : DivisionRing D := hDdiv
  letI : DivisionRing E := hEdiv
  letI : Algebra k D := hDalg
  letI : Algebra k E := hEalg
  letI : Module.Finite k D := hDfin
  letI : Module.Finite k E := hEfin
  letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv k A _ eA
  letI : Algebra.IsCentral k (D ⊗[k] Matrix (Fin n) (Fin n) k) :=
    Algebra.IsCentral.of_algEquiv k _ _ (matrixEquivTensor (Fin n) k D)
  letI : Algebra.IsCentral k D :=
    Algebra.IsCentral.left_of_tensor_of_field k D (Matrix (Fin n) (Fin n) k)
  letI : Algebra.IsCentral k (Matrix (Fin m) (Fin m) E) :=
    Algebra.IsCentral.of_algEquiv k B _ eB
  letI : Algebra.IsCentral k (E ⊗[k] Matrix (Fin m) (Fin m) k) :=
    Algebra.IsCentral.of_algEquiv k _ _ (matrixEquivTensor (Fin m) k E)
  letI : Algebra.IsCentral k E :=
    Algebra.IsCentral.left_of_tensor_of_field k E (Matrix (Fin m) (Fin m) k)
  have hAD : IsBrauerEquivalent
      (BGroups.centralSimpleCSA k A)
      (BGroups.centralDivisionCSA k D) := by
    refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
    exact ⟨(BGroups.matrixFinAlg k A).trans eA⟩
  have hBE : IsBrauerEquivalent
      (BGroups.centralSimpleCSA k B)
      (BGroups.centralDivisionCSA k E) := by
    refine ⟨1, m, one_ne_zero, NeZero.ne m, ?_⟩
    exact ⟨(BGroups.matrixFinAlg k B).trans eB⟩
  have hDE : IsBrauerEquivalent
      (BGroups.centralDivisionCSA k D)
      (BGroups.centralDivisionCSA k E) :=
    hAD.symm.trans (hAB.trans hBE)
  obtain ⟨eDE⟩ :=
    (BGroups.division_brauer_equivalent
      k D E).1 hDE
  have hmatrix :
      Module.finrank k (Matrix (Fin n) (Fin n) D) =
        Module.finrank k (Matrix (Fin m) (Fin m) E) := by
    calc
      Module.finrank k (Matrix (Fin n) (Fin n) D) = Module.finrank k A :=
        eA.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k B := hdim
      _ = Module.finrank k (Matrix (Fin m) (Fin m) E) :=
        eB.toLinearEquiv.finrank_eq
  have hnm : n = m :=
    SAlgebr.matrix_size_finrank k D E n m ⟨eDE⟩ hmatrix
  subst m
  exact ⟨eA |>.trans (eDE.mapMatrix |>.trans eB.symm)⟩

/-- Equality of Brauer classes is equivalent to algebra isomorphism for
central simple algebras of the same dimension. -/
theorem brauer_nonempty_finrank
    (hdim : Module.finrank k A = Module.finrank k B) :
    BGroups.brauerClass k
        (BGroups.centralSimpleCSA k A) =
      BGroups.brauerClass k
        (BGroups.centralSimpleCSA k B) ↔
      Nonempty (A ≃ₐ[k] B) := by
  rw [BGroups.brauer_class]
  constructor
  · intro h
    exact nonempty_equivalent_finrank k A B h hdim
  · rintro ⟨e⟩
    exact ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- Milne, Theorem IV.3.14, surjectivity on representatives: every class split
by `L` is represented by a crossed product for a normalized cocycle on
`Gal(L/k)`. -/
theorem crossed_brauer_split
    (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (hsplit : BGroups.ISBy k L A) :
    ∃ c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ),
      CProduc.brauerClass k L c =
        BGroups.brauerClass k
          (BGroups.centralSimpleCSA k A) := by
  obtain ⟨B, i, _, hdim, hAB⟩ :=
    (split_similar_containing k L A).1 hsplit
  let c := galoisNormalizedCocycle k L B i hdim
  refine ⟨c, ?_⟩
  rw [CProduc.brauerClass, BGroups.brauer_class]
  have hBC : IsBrauerEquivalent B (CProduc.centralSimpleCSA k L c) := by
    refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
    exact ⟨(algCrossedEmbedding k L B i hdim).mapMatrix⟩
  exact hBC.symm.trans hAB.symm

end

end Submission.CField.CProduca
