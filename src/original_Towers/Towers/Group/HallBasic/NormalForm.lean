import Mathlib.Algebra.Group.TransferInstance
import Towers.Group.HallBasic.StandardSequence

namespace Struik

open Towers
open Towers.TCTex

universe u

/-- The canonical Hall family of standard commutators in `d` free
generators, indexed separately in each ordinary weight. -/
noncomputable abbrev standardHallFamily (d : ℕ) :
    ∀ r : ℕ, BCWta.{u} d r :=
  concreteBasicCommutators.{u} d

/-- The canonical standard commutators form a basis in every positive
lower-central layer below the nilpotent truncation depth. -/
theorem standard_forms_associated
    (d n r : ℕ)
    (hr : 0 < r)
    (hrn : r < n) :
    (standardHallFamily.{u} d r).FormsAssocGradedbasis (n := n) :=
  concrete_forms_associated d n r hr hrn

/-- Integer coordinates on the canonical standard commutators. -/
abbrev StandardExponentFamily (d : ℕ) :=
  HEFam (standardHallFamily.{u} d)

/-- The ordered product of standard commutators of weights below `n`. -/
noncomputable def standardHallProduct
    (d n : ℕ)
    (e : StandardExponentFamily.{u} d) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  collectedHallProduct (n := n) (standardHallFamily.{u} d) e

/-- Chosen standard-commutator coordinates in the free nilpotent
truncation. The only numerical premise is the nondegenerate truncation range
used by the collection theorem. -/
noncomputable def standardHallCoordinates
    (d n : ℕ)
    (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    StandardExponentFamily.{u} d :=
  normalFormCoordinates hn (standardHallFamily.{u} d)
    (fun r _hr hrn =>
      standard_forms_associated d n r (by omega) hrn)
    y

/-- The chosen coordinates evaluate to the original element. -/
theorem standard_product_coordinates
    (d n : ℕ)
    (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    standardHallProduct d n (standardHallCoordinates d n hn y) = y :=
  collected_form_coordinates
    hn (standardHallFamily.{u} d)
    (fun r _hr hrn =>
      standard_forms_associated d n r (by omega) hrn)
    y

/-- Standard Hall coordinates below an element's lower-central depth vanish. -/
theorem standard_coordinates_series
    (d n r : ℕ)
    (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∀ s : ℕ,
      1 ≤ s →
        s < r →
          s < n →
            standardHallCoordinates d n hn y s = 0 := by
  intro s hs hsr hsn
  funext i
  exact lower_central_series
    hn (standardHallFamily.{u} d)
    (fun w hw hwn =>
      standard_forms_associated d n w hw hwn)
    y hy hs hsr hsn i

/-- Recollect an element of a lower-central term into one standard Hall
product, with all earlier weight blocks identically zero. -/
theorem standard_recollection_series
    (d n r : ℕ)
    (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∃ e : StandardExponentFamily.{u} d,
      standardHallProduct d n e = y ∧
        ∀ s : ℕ,
          1 ≤ s →
            s < r →
              s < n →
                e s = 0 := by
  refine ⟨standardHallCoordinates d n hn y,
    standard_product_coordinates d n hn y, ?_⟩
  exact
    standard_coordinates_series
      d n r hn y hy

/-- Any standard Hall coordinates for an element agree with the chosen
coordinates in every weight represented in the truncation. -/
theorem standard_coordinates_product
    (d n : ℕ)
    (hn : 2 ≤ n)
    (e : StandardExponentFamily.{u} d)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (he : standardHallProduct d n e = y) :
    ∀ r : ℕ,
      1 ≤ r →
        r < n →
          standardHallCoordinates d n hn y r = e r :=
  form_coordinates_collected
    hn (standardHallFamily.{u} d)
    (fun r _hr hrn =>
      standard_forms_associated d n r (by omega) hrn)
    e y he

/-- In the nondegenerate truncation range, every element has standard Hall
coordinates, unique in all weights below the truncation depth. -/
theorem unique_standard_coordinates
    (d n : ℕ)
    (hn : 2 ≤ n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : StandardExponentFamily.{u} d,
      standardHallProduct d n e = y ∧
        ∀ f : StandardExponentFamily.{u} d,
          standardHallProduct d n f = y →
            ∀ r : ℕ, 1 ≤ r → r < n → f r = e r := by
  refine ⟨standardHallCoordinates d n hn y,
    standard_product_coordinates d n hn y, ?_⟩
  intro f hf r hr hrn
  exact
    (standard_coordinates_product
      d n hn f y hf r hr hrn).symm

/-- Every element of the free nilpotent truncation has standard Hall
coordinates, unique in all weights below the truncation depth.

For `n < 2` the quotient is trivial and there are no positive weights below
`n`; for `2 ≤ n` this is the concrete Hall collection theorem. -/
theorem unique_hall_coordinates
    (d n : ℕ)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : StandardExponentFamily.{u} d,
      standardHallProduct d n e = y ∧
        ∀ f : StandardExponentFamily.{u} d,
          standardHallProduct d n f = y →
            ∀ r : ℕ, 1 ≤ r → r < n → f r = e r := by
  by_cases hn : 2 ≤ n
  · exact unique_standard_coordinates d n hn y
  · refine ⟨0, ?_, ?_⟩
    · have hn0 : n - 1 = 0 := by omega
      letI :
          Subsingleton
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) := by
        change Subsingleton
          (FreeGroup (FreeGenerator.{u} d) ⧸
            Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d)) (n - 1))
        rw [hn0, Subgroup.lowerCentralSeries_zero]
        exact QuotientGroup.subsingleton_quotient_top
      exact Subsingleton.elim _ _
    · intro f _hf r hr hrn
      omega

/-- Standard Hall exponent families supported exactly in the weights represented
in the truncation.  This is the infinite-function presentation of Struik's
finite coordinate tuples. -/
def StandardCoordinateTuple (d n : ℕ) :=
  { e : StandardExponentFamily.{u} d //
      ∀ r : ℕ, ¬ (1 ≤ r ∧ r < n) → e r = 0 }

/-- Discard the Hall coordinates outside the represented weights. -/
noncomputable def truncateStandardFamily
    (d n : ℕ)
    (e : StandardExponentFamily.{u} d) :
    StandardExponentFamily.{u} d :=
  fun r => if 1 ≤ r ∧ r < n then e r else 0

/-- Coordinates outside `1 ≤ r < n` do not contribute to the collected Hall
product. -/
theorem standard_truncate_family
    (d n : ℕ)
    (e : StandardExponentFamily.{u} d) :
    standardHallProduct d n (truncateStandardFamily d n e) =
      standardHallProduct d n e := by
  unfold standardHallProduct collectedHallProduct
  apply collected_product_coordinates
  intro r hr hrn
  have hrlt : r < n := by omega
  simp [truncateStandardFamily, hr, hrlt]

/-- The cutoff-supported standard Hall tuple chosen for an element of the free
nilpotent truncation. -/
noncomputable def standardHallTuple
    (d n : ℕ)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    StandardCoordinateTuple.{u} d n :=
  ⟨truncateStandardFamily d n
      (Classical.choose (unique_hall_coordinates d n y)),
    fun r hr => by
      simp [truncateStandardFamily, hr]⟩

/-- The chosen cutoff-supported tuple evaluates to its original element. -/
theorem standard_coordinate_tuple
    (d n : ℕ)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    standardHallProduct d n (standardHallTuple d n y).1 = y := by
  rw [standardHallTuple,
    standard_truncate_family]
  exact (Classical.choose_spec (unique_hall_coordinates d n y)).1

/-- Standard Hall coordinate tuples are canonically equivalent to the free
nilpotent truncation. -/
noncomputable def standardTupleEquiv
    (d n : ℕ) :
    StandardCoordinateTuple.{u} d n ≃
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n where
  toFun e := standardHallProduct d n e.1
  invFun := standardHallTuple d n
  left_inv e := by
    apply Subtype.ext
    funext r
    by_cases hr : 1 ≤ r ∧ r < n
    · rw [standardHallTuple]
      simp only [truncateStandardFamily, hr]
      exact
        ((Classical.choose_spec
            (unique_hall_coordinates d n
              (standardHallProduct d n e.1))).2
          e.1 rfl r hr.1 hr.2).symm
    · rw [standardHallTuple]
      simp [truncateStandardFamily, hr, e.2 r hr]
  right_inv y :=
    standard_coordinate_tuple d n y

/-- The group structure on standard Hall tuples obtained by transporting the
free nilpotent group law through their canonical evaluation equivalence. -/
noncomputable instance standardTupleGroup
    (d n : ℕ) :
    Group (StandardCoordinateTuple.{u} d n) :=
  (standardTupleEquiv d n).group

/-- Struik's standard Hall coordinate tuples, with their transported
multiplication, form a group isomorphic to the free nilpotent truncation. -/
noncomputable def standardCoordinateTuple
    (d n : ℕ) :
    StandardCoordinateTuple.{u} d n ≃*
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (standardTupleEquiv d n).mulEquiv

end Struik
