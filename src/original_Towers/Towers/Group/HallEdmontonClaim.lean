import Towers.Group.HallBasic.StandardSequence
import Towers.Group.Zassenhaus.HallCoordinateDn

/-!
# Paper-facing Hall/Edmonton adapters

The file `docs/c.tex` imports Hall's Edmonton machinery as an external claim.
Most of that machinery is already present in this project, but under the
internal names used by the Hall-basis and free-nilpotent-truncation
developments.  This module exposes the concrete parts used by the
Hall--Zassenhaus argument under stable, claim-shaped names.
-/

namespace Towers
namespace Ctex

universe u

open scoped commutatorElement
open TCTex

/-- The concrete Hall commutators form the free-group lower-central
associated-graded basis in each positive weight. -/
theorem edmonton_forms_associated
    (d r : ℕ) (hr : 0 < r) :
    (concreteCommutatorsWeight.{u} d r).FormsfreeGroupassocGradedbasis :=
  TCTex.commutators_forms_basis
    d r hr

/-- Below the nilpotency cutoff, the concrete Hall commutators form the
associated-graded basis in the free nilpotent truncation. -/
theorem edmonton_forms_graded
    (d n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) :
    (concreteCommutatorsWeight.{u} d r).FormsAssocGradedbasis
      (n := n) :=
  TCTex.concrete_forms_associated
    d n r hr hrn

/-- Hall normal form for the concrete Hall basis in `F_d / γ_n(F_d)`. -/
theorem edmonton_concrete_form
    {d n : ℕ} (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : HEFam (concreteCommutatorsWeight.{u} d),
      collectedHallProduct
          (n := n) (concreteCommutatorsWeight.{u} d) e =
        y :=
  TCTex.hall_form_coordinates
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      edmonton_forms_graded d n s hs hsn)
    y

/-- The selected Hall normal-form coordinates collect back to the element. -/
theorem edmonton_form_collect
    {d n : ℕ} (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    collectedHallProduct
        (n := n) (concreteCommutatorsWeight.{u} d)
        (normalFormCoordinates
          hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            edmonton_forms_graded d n s hs hsn)
          y) =
      y :=
  TCTex.form_coordinates_collect
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      edmonton_forms_graded d n s hs hsn)
    y

/-- Uniqueness of concrete Hall normal-form coordinates. -/
theorem edmonton_form_coordinates
    {d n : ℕ} (hn : 2 ≤ n)
    (e f : HEFam (concreteCommutatorsWeight.{u} d))
    (hproduct :
      collectedHallProduct
          (n := n) (concreteCommutatorsWeight.{u} d) e =
        collectedHallProduct
          (n := n) (concreteCommutatorsWeight.{u} d) f) :
    ∀ r : ℕ,
      1 ≤ r →
        r < n →
          e r = f r :=
  collected_hall_coordinates
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      edmonton_forms_graded d n s hs hsn)
    e f hproduct

/-- Elements of `γ_r` have zero concrete Hall coordinates in all lower
ordinary weights. -/
theorem edmonton_coordinates_series
    {d n r : ℕ} (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∀ s : ℕ,
      1 ≤ s →
        s < r →
          s < n →
            normalFormCoordinates
              hn (concreteCommutatorsWeight.{u} d)
              (fun t ht htn =>
                edmonton_forms_graded d n t ht htn)
              y s =
              0 :=
  TCTex.form_coordinates_below
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      edmonton_forms_graded d n s hs hsn)
    y hy

/-- Triangularity of concrete Hall normal form: if two elements in `γ_r`
have the same weight-`r` Hall coordinates, their quotient lies in
`γ_(r+1)`. -/
theorem edmonton_triangular_series
    {d n r : ℕ}
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hcoordinates :
      normalFormCoordinates
          hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            edmonton_forms_graded d n s hs hsn)
          x r =
        normalFormCoordinates
          hn (concreteCommutatorsWeight.{u} d)
          (fun s hs hsn =>
            edmonton_forms_graded d n s hs hsn)
          y r) :
    x⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r :=
  TCTex.triangular_same_coordinates
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      edmonton_forms_graded d n s hs hsn)
    hr hrn x y hx hy hcoordinates

end Ctex
end Towers
