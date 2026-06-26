import Submission.ClassField.CyclicIdeles.AlgebraicIdeleCohomology
import Submission.ClassField.BrauerLocalization.Injectivity

/-!
# The Brauer-group form of Theorem VII.7.1

The cohomological finite theorem, crossed-product comparison, and finite
splitting-field argument together give the canonical injection
`Br(K) → ⨁ v, Br(K_v)`.  Restricting this map to `Br(L/K)` proves Milne's
statement for finite or infinite extensions at once.
-/

namespace Submission.CField.CBrauer

open NumberField
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.CIdeles
open Submission.CField.RExist
open Submission.CField.BLoc

noncomputable section

universe u

/-- The canonical global Brauer localization package: its coordinates are
scalar extension to the actual finite and infinite completions, and every
class has finite support. -/
noncomputable def brauerData
    (K : Type u) [Field K] [NumberField K] : BData K :=
  Classical.choice (brauerConstructionBridge K)

/-- **Theorem VII.7.1, absolute Brauer form.**  The canonical map

`Br(K) → ⨁ v, Br(K_v)`

is injective. -/
theorem brauerLocalization_injective
    (K : Type u) [Field K] [NumberField K] :
    Function.Injective (brauerData K).localization.localization :=
  brauer_localization_cohomology
    ideleCohomologyClaims K (brauerData K)

/-- **Theorem VII.7.1, relative and possibly infinite form.**  For any
extension `L/K`, restriction of the canonical completion map to the relative
Brauer group `Br(L/K) = H²(L/K)` is injective.  For finite Galois `L/K`, its
coordinates factor through the usual local relative groups
`H²(Lᵛ/K_v)`; the ambient-Brauer formulation here is stronger and also
covers the direct-limit (possibly infinite) case without extra hypotheses. -/
theorem relative_localization_injective
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] :
    Function.Injective
      (relativeLocalization K (brauerData K) L) := by
  intro x y hxy
  have hsub :
      (MonoidHom.toAdditive (relativeBrauerGroup K L).subtype) x =
        (MonoidHom.toAdditive (relativeBrauerGroup K L).subtype) y := by
    apply brauerLocalization_injective K
    exact hxy
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg Additive.toMul hsub

end

end Submission.CField.CBrauer
