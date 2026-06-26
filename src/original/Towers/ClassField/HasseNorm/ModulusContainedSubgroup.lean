import Towers.ClassField.HasseNorm.IdeleOpenness
import Towers.ClassField.HasseNorm.ModulusUnitCofinality

/-! # Corollary V.4.13 from its two topological inputs -/

namespace Towers.CField.HNorm

open NumberField
open Towers.CField.Ideles
open Towers.CField.RCGroups

noncomputable section

universe u

/-- **Corollary V.4.13.** The idèle norm subgroup contains `W_m` for a
suitable modulus `m`. -/
theorem modulusContainedSubgroup
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    (∃ m : Modulus K,
          ideleModulusSubgroup m ≤
            ideleNormSubgroup (K := K) (L := L)) := by
  exact open_modulus_basis
    (idele_norm_open (K := K) (L := L))
    (modulusSubgroupsCofinal (K := K))

end

end Towers.CField.HNorm
