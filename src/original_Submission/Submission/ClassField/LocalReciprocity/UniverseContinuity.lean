import Submission.ClassField.NormCorrespondence.SubgroupOpenClosed
import Submission.ClassField.LocalReciprocity.UniverseNormResidue

/-!
# Continuity of the ambient-universe finite local Artin map

The `Small.{0}` norm-residue map has the norm subgroup as its kernel.  The
usual open-kernel proof of continuity therefore transports unchanged from
the Type-0 construction.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory

noncomputable section

universe u

variable (F E : Type u)
  [NontriviallyNormedField F] [IsUltrametricDist F]
  [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [CharZero F]
  [Field E] [Algebra F E] [FiniteDimensional F E]
  [IsGalois F E] [IsMulCommutative Gal(E/F)]
  [Small.{0} F] [Small.{0} E]

set_option maxHeartbeats 1000000 in
-- The transported equivalence supplies finiteness of the norm quotient.
set_option synthInstance.maxHeartbeats 100000 in
/-- The `Small.{0}`-transported finite abelian local Artin homomorphism is
continuous. -/
theorem abelian_small_continuous :
    Continuous (abelianLocalSmall F E) := by
  letI : Finite (Fˣ ⧸ normSubgroup F E) :=
    Finite.of_injective (abelianArtinSmall F E)
      (abelianArtinSmall F E).injective
  letI : (normSubgroup F E).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, nhds_discrete Gal(E/F), map_one,
    Filter.tendsto_pure]
  change ((abelianLocalSmall F E).ker : Set Fˣ) ∈ nhds 1
  have hopen : IsOpen
      ((abelianLocalSmall F E).ker : Set Fˣ) := by
    rw [abelian_small_ker]
    exact norm_subgroup F E
  exact hopen.mem_nhds (by simp)

end

end Submission.CField.LRecip
