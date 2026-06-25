import Submission.ClassField.NormIndex.CyclicSubextension
import Submission.ClassField.NormIndex.CanonicalTateFormula
import Submission.ClassField.HasseNorm.IdeleOpenness
import Submission.ClassField.BrauerLocalization.IdeleIdealSupport

/-!
# Lemma VII.4.5 assembly for Theorem VIII.4.2

The cyclic fixed-field construction and concrete idèle-norm transitivity are
proved in Chapter VII. Proposition VII.2.8 is supplied by the unconditional
openness theorem for the idèle norm range, leaving only the first inequality.
-/

namespace Submission.CField.BLoc

open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

/-- Lemma VII.4.5 follows from Corollary VII.4.4; its cyclic-subextension,
norm-transitivity, and norm-range openness inputs are now unconditional. -/
theorem localization_cokernel_assembly
    (hfirst : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index)) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1) := by
  apply previous_results_only
  · intro K L _ _ _ _ _ _
    exact norm_subgroup_open
      (idele_norm_open (K := K) (L := L))
  · exact hfirst

/-- **Lemma VII.4.5.**  A dense subgroup contained in the idèle norm
range forces a finite solvable Galois extension to have degree one. -/
theorem cyclicSubextensionDegree :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsSolvable Gal(L/K)],
      ∀ D : Subgroup (IK K),
        D ≤ ideleNormSubgroup (K := K) (L := L) →
        Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
          Subgroup (IK K)) : Set (IK K)) →
        Module.finrank K L = 1 :=
  localization_cokernel_assembly
    (natHerbrandStatement
      ideleHerbrandQuotient tateIndexBridge)

end


end Submission.CField.BLoc
