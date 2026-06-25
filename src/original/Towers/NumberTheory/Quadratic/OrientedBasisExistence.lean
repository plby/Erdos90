import Towers.NumberTheory.Quadratic.OrientedIdealBases
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Positive bases of quadratic ideals

Every nonzero ideal in a quadratic ring of integers has a basis indexed by `Fin 2`.
Reversing its two vectors reverses the determinant, so one of the two orders is positively
oriented.  This supplies the basis choice used in the ideal-to-form direction of Theorem 4.29.
-/

namespace Towers.NumberTheory.Milne

open Module
open scoped NumberField

noncomputable section

namespace INForm

variable {K : Type*} [Field K] [NumberField K]

/-- A `Fin 2`-indexed basis of every nonzero ideal in a quadratic ring of integers. -/
def basisFinTwo (B : Basis (Fin 2) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : Basis (Fin 2) ℤ I :=
  Module.finBasisOfFinrankEq ℤ I <| by
    calc
      Module.finrank ℤ I = Module.finrank ℤ (𝓞 K) :=
        Ideal.finrank_eq_finrank B I hI
      _ = Fintype.card (Fin 2) := Module.finrank_eq_card_basis B
      _ = 2 := Fintype.card_fin 2

omit [NumberField K] in
/-- Reversing a two-element ideal basis negates its coordinate determinant. -/
theorem matrix_reindex_det
    (B : Basis (Fin 2) ℤ (𝓞 K)) {I : Ideal (𝓞 K)}
    (b : Basis (Fin 2) ℤ I) :
    (basisCoordinateMatrix B (b.reindex (Equiv.swap 0 1))).det =
      -(basisCoordinateMatrix B b).det := by
  change (B.toMatrix (fun i => ((b.reindex (Equiv.swap 0 1)) i : 𝓞 K))).det =
    -(B.toMatrix fun i => (b i : 𝓞 K)).det
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]

/-- Every nonzero quadratic ideal admits a positively oriented ordered basis. -/
def positivelyOrientedBasis (B : Basis (Fin 2) ℤ (𝓞 K))
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : PositivelyOrientedBasis B I := by
  let b := basisFinTwo B I hI
  by_cases hb : 0 < (basisCoordinateMatrix B b).det
  · exact ⟨b, hb⟩
  · refine ⟨b.reindex (Equiv.swap 0 1), ?_⟩
    rw [IsPositivelyOriented, matrix_reindex_det]
    have hdet : (basisCoordinateMatrix B b).det ≠ 0 := by
      intro hzero
      have habs := Ideal.natAbs_det_basis_change B I b
      rw [Basis.det_apply] at habs
      change (basisCoordinateMatrix B b).det.natAbs = Ideal.absNorm I at habs
      rw [hzero, Int.natAbs_zero] at habs
      have hnorm : 0 < Ideal.absNorm I := absNorm_pos hI
      omega
    omega

end INForm

end

end Towers.NumberTheory.Milne
