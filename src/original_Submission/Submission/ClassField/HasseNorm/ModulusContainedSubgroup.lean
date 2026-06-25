import Submission.ClassField.HasseNorm.IdeleOpenness
import Submission.ClassField.HasseNorm.ModulusUnitCofinality

/-! # Corollary V.4.13 from its two topological inputs -/

namespace Submission.CField.HNorm

open NumberField
open Submission.CField.Ideles
open Submission.CField.RCGroups

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

end Submission.CField.HNorm
