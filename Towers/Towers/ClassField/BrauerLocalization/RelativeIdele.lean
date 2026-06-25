import Towers.ClassField.BrauerLocalization.Relative2Comparison
import Towers.ClassField.HasseNorm.Class1Vanishing
import Towers.ClassField.HasseNorm.HCompletionProduct

/-!
# Relative Brauer localization through idèle cohomology

This file assembles the cohomological part of Theorem VII.7.1 in the resized
number-field universe.  It deliberately stops before the arithmetic
compatibility square: the coordinates constructed here are completion-product
`H²` classes, and a later theorem must identify their Shapiro/crossed-product
images with scalar extension of Brauer classes to completions.
-/

namespace Towers.CField.BLoc

open CategoryTheory CategoryTheory.Limits Representation groupCohomology
open IsDedekindDomain NumberField
open Towers.CField.BGroups
open Towers.CField.Ideles
open Towers.CField.CIdeles
open Towers.CField.CBrauer
open Towers.CField.HNorm

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The map from relative Brauer classes to idèle `H²` induced by the
principal-idèle embedding, after the canonical crossed-product comparison. -/
noncomputable def relativeResized2 :
    Additive (relativeBrauerGroup K L) →+
      H2 (resizedConcreteRepresentation K L) :=
  (groupCohomology.map (MonoidHom.id Gal(L/K))
      (resizedShortComplex K L).f 2).hom.toAddMonoidHom.comp
    (relativeBrauerResized K L).toAddMonoidHom

/-- The cohomological localization map with its actual direct-sum codomain. -/
noncomputable def relativeH2 :
    Additive (relativeBrauerGroup K L) →+
      DirectSum (NumberFieldPlace K)
        (fun v => H2 (resizedPlaceRepresentation
          (K := K) (L := L) v)) :=
  (resizedHDecomposition
      (K := K) (L := L)).toAddMonoidHom.comp
    (relativeResized2 K L)

/-- The cohomological localization of every relative Brauer class has finite
place support, because its target is a dependent direct sum. -/
theorem relative_brauer_support
    (x : Additive (relativeBrauerGroup K L)) :
    Set.Finite {v : NumberFieldPlace K |
      relativeH2 K L x v ≠ 0} :=
  DFinsupp.finite_support (relativeH2 K L x)

/-- Assuming VII.5.1, the map from relative Brauer classes into idèle `H²`
is injective. -/
theorem relative_resized_injective
    (h51 : IdeleCohomologyClaims.{u}) :
    Function.Injective (relativeResized2 K L) := by
  have hH1 : IsZero
      (H1 (resizedShortComplex K L).X₃) :=
    short_complex_3 h51 K L
  have hmap := h_1_third
    (resized_short_exact K L) hH1
  exact hmap.comp
    (relativeBrauerResized K L).injective

/-- The direct-sum completion-product form of the cohomological localization
is injective under VII.5.1. -/
theorem relative_brauer_injective
    (h51 : IdeleCohomologyClaims.{u}) :
    Function.Injective (relativeH2 K L) :=
  (resizedHDecomposition
      (K := K) (L := L)).injective.comp
    (relative_resized_injective K L h51)

end

end Towers.CField.BLoc
