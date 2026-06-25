import Towers.ClassField.BrauerGroups.CentralDivisionCSA
import Towers.ClassField.CrossedProducts.TensorEquivLeft

/-!
# Chapter IV, Corollary 3.7

A field of the degree of a central division algebra embeds in it exactly when
it splits it.
-/

namespace Towers.CField.CProduca

open scoped TensorProduct

universe u

variable (k L D : Type u) [Field k] [Field L] [Algebra k L]
  [DivisionRing D] [Algebra k D] [Algebra.IsCentral k D]
  [Module.Finite k D] [Module.Finite k L]

/-- Milne, Corollary IV.3.7: if `[D:k] = n^2` and `[L:k] = n`, then
`L` splits the central division algebra `D` exactly when `L` embeds in `D`. -/
theorem split_nonempty_alg (n : ℕ)
    (hD : Module.finrank k D = n ^ 2)
    (hL : Module.finrank k L = n) :
    BGroups.ISBy k L D ↔ Nonempty (L →ₐ[k] D) := by
  constructor
  · intro hsplit
    obtain ⟨B, i, _, hBdim, hDB⟩ :=
      (split_similar_containing k L D).1 hsplit
    letI : IsArtinianRing B := IsArtinianRing.of_finite k B
    obtain ⟨m, hm, E, hEdiv, hEalg, hEfin, ⟨eB⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
    letI : NeZero m := hm
    letI : DivisionRing E := hEdiv
    letI : Algebra k E := hEalg
    letI : Module.Finite k E := hEfin
    letI : Algebra.IsCentral k (Matrix (Fin m) (Fin m) E) :=
      Algebra.IsCentral.of_algEquiv k B _ eB
    letI : Algebra.IsCentral k (E ⊗[k] Matrix (Fin m) (Fin m) k) :=
      Algebra.IsCentral.of_algEquiv k _ _ (matrixEquivTensor (Fin m) k E)
    letI : Algebra.IsCentral k E :=
      Algebra.IsCentral.left_of_tensor_of_field k E (Matrix (Fin m) (Fin m) k)
    have hBE : IsBrauerEquivalent B (BGroups.centralDivisionCSA k E) := by
      refine ⟨1, m, one_ne_zero, NeZero.ne m, ?_⟩
      exact ⟨(BGroups.matrixFinAlg k B).trans eB⟩
    have hDE : IsBrauerEquivalent (BGroups.centralDivisionCSA k D)
        (BGroups.centralDivisionCSA k E) := by
      exact hDB.trans hBE
    obtain ⟨eDE⟩ :=
      (BGroups.division_brauer_equivalent k D E).1 hDE
    have hBDdim : Module.finrank k B = Module.finrank k D := by
      rw [hBdim, hD, hL]
    have hmatrix : Module.finrank k (Matrix (Fin m) (Fin m) E) =
        Module.finrank k (Matrix (Fin 1) (Fin 1) D) := by
      calc
        Module.finrank k (Matrix (Fin m) (Fin m) E) = Module.finrank k B :=
          eB.toLinearEquiv.finrank_eq.symm
        _ = Module.finrank k D := hBDdim
        _ = Module.finrank k (Matrix (Fin 1) (Fin 1) D) :=
          (BGroups.matrixFinAlg k D).toLinearEquiv.finrank_eq.symm
    have hm1 : m = 1 :=
      SAlgebr.matrix_size_finrank k E D m 1
        ⟨eDE.symm⟩ hmatrix
    subst m
    let eBD : B ≃ₐ[k] D :=
      eB.trans ((BGroups.matrixFinAlg k E).trans eDE.symm)
    exact ⟨eBD.toAlgHom.comp i⟩
  · rintro ⟨i⟩
    exact embedding_split_sq k L D i (by rw [hD, hL])

end Towers.CField.CProduca
