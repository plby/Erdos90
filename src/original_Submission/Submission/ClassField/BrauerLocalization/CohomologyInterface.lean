import Submission.ClassField.Reciprocity.FiniteIndependence
import Submission.ClassField.BrauerLocalization.FiniteCyclicCohomology
import Submission.ClassField.Ideles.Ideles

/-!
# Theorem VIII.4.2 from Theorem VII.8.1

The concrete Proposition V.5.2 construction supplies the global Artin-map
input to the existing final assembly.  Consequently Theorem VII.8.1 is the
only remaining mathematical input at this boundary.
-/

namespace Submission.CField.BLoc

open Submission.CField.Recip
open Submission.CField.LFTheory
open Submission.CField.RExist
open Submission.CField.GClass
open Submission.CField.Ideles

noncomputable section

universe u

/-- Once Theorem VII.8.1 is available, the concrete global Artin map closes
the final Theorem VIII.4.2 assembly. -/
theorem interface_global_fundamental
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L))) :
    GlobalLocalizationSequence.{u} := by
  apply global_artin_fundamental
  · intro K _ _
    exact global_artin_unique (K := K)
  · exact h81

end

end Submission.CField.BLoc
