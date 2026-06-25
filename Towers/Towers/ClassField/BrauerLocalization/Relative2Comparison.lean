import Towers.ClassField.CrossedProducts.Cohomology
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison
import Towers.ClassField.HasseNorm.ResizedIdeleSequence
import Towers.ClassField.HasseNorm.LiftedH2

/-!
# Relative Brauer groups as degree-two cohomology

This file packages the already-proved crossed-product theorem and the two
multiplicative-to-categorical `H²` comparisons in the orientations needed by
the global Brauer localization argument.  The final declaration targets the
resized global-units representation occurring as the first term of the
idèle-class short exact sequence.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.HNorm

noncomputable section

universe u

section Ordinary

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- Theorem IV.3.14 followed by the ordinary categorical `H²` comparison,
in the orientation used by the cohomological proof of Theorem VII.7.1. -/
noncomputable def relativeBrauerCohomology :
    Additive (relativeBrauerGroup K L) ≃+
      H2 (Rep.ofAlgebraAutOnUnits K L) :=
  ((CProduc.hRelativeBrauer K L).symm.trans
    (multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ))).toAdditive

end Ordinary

section Resized

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- Universe-resized form of the relative Brauer/categorical `H²`
comparison. -/
noncomputable def relativeBrauer2 :
    Additive (relativeBrauerGroup K L) ≃+
      H2 (hasseGlobalRepresentation K L) :=
  ((CProduc.hRelativeBrauer K L).symm.trans
    (multiplicativeUCohomology
      (G := Gal(L/K)) (M := Lˣ))).toAdditive

variable [NumberField K] [NumberField L]

/-- Relative Brauer classes identified with `H²` of the exact global-units
representation used in the resized idèle-class short complex. -/
noncomputable def relativeBrauerResized :
    Additive (relativeBrauerGroup K L) ≃+
      H2 (resizedRepresentation K L) :=
  (relativeBrauer2 K L).trans
    (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
      (resizedIsoHasse K L)).toLinearEquiv.toAddEquiv).symm

end Resized

end

end Towers.CField.BLoc
