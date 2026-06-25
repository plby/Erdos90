import Towers.ClassField.NormIndex.IdeleTowerFinite
import Towers.ClassField.NormIndex.IdeleTowerLocal

/-!
# Transitivity of the concrete idèle norm

This file combines transitivity at finite and infinite places into the
corresponding identity for the product idèle norm.
-/

namespace Towers.CField.NIndex

open NumberField
open Towers.CField.Ideles

noncomputable section

universe u

/-- Transitivity of the concrete idèle norm in a finite Galois tower. -/
theorem ideleNorm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · exact DFunLike.congr_fun
      (infinite_idele_trans (K := K) (E := E) (L := L)) x.1
  · exact idele_norm_trans (K := K) (E := E) (L := L) x.2

end

end Towers.CField.NIndex
