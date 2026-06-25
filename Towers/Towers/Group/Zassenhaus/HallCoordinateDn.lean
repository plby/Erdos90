import Towers.Group.Zassenhaus.TriangularGHLaw

/-!
# Hall-coordinate description of the Zassenhaus term

This file records the `c.tex` coordinate criterion for the free nilpotent
truncation in the notation used by the existing Hall/Zassenhaus development.
The substantial work is the already-proved subgroup equality
`zassenhaus_filtration_lattice`; the lemmas here expose it as
an iff on Hall normal-form coordinates.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
Hall normal form in the free nilpotent truncation: every element is an ordered
collected Hall product.
-/
theorem hall_form_coordinates
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    ∃ e : HEFam H,
      collectedHallProduct (n := n) H e = y :=
  collected_hall_product hn H hH y

/--
The chosen Hall normal-form coordinates collect back to the original element.
-/
theorem form_coordinates_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    collectedHallProduct (n := n) H (normalFormCoordinates hn H hH y) = y :=
  collected_form_coordinates hn H hH y

/--
An element of `γ_r` has no Hall coordinates in ordinary weights below `r`.
-/
theorem form_coordinates_below
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1)) :
    ∀ s : ℕ,
      1 ≤ s →
        s < r →
          s < n →
            normalFormCoordinates hn H hH y s = 0 := by
  exact
    imp_coordinates_below
      hn H hH (normalFormCoordinates hn H hH y)
      (by
        rw [collected_form_coordinates hn H hH y]
        exact hy)

/--
Triangular suffix step for Hall coordinates.  If two elements already lie in
`γ_r` and have the same Hall coordinates in weight `r`, then their quotient
lies in `γ_(r+1)`.
-/
theorem triangular_same_coordinates
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (x y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hcoordinates :
      normalFormCoordinates hn H hH x r =
        normalFormCoordinates hn H hH y r) :
    x⁻¹ * y ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r :=
  inv_form_coordinates
    hn H hH hr hrn x y hx hy hcoordinates

/--
Leading term of a labelled Hall commutator.  Freshening the leaves and
powering one distinguished leaf by `m` gives no lower-weight coordinates and
has the selected Hall coordinate equal to `m`.
-/
theorem labelled_leading_coordinate
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (H r).index)
    (m : ℤ) :
    ∃ a : Fin (((H r).commutator i).word.weight (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let y := (CWord.freshen ((H r).commutator i).word).eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (H s).index,
                hallCoordinate hn H hH y j = 0) ∧
        ∀ j : (H r).index,
          hallCoordinate hn H hH y j = if j = i then m else 0 :=
  BCWta.exists_evalp_leadh
    hn H hH hr hrn i m

/--
Leading coordinate of the normalized powered Hall word-value.  After applying
the least prime power whose Hall weight reaches `n`, the selected coordinate
is multiplied by that prime power, lower-weight coordinates still vanish, and
the value lies in the `n`th Zassenhaus term.
-/
theorem normalized_leading_coordinate
    {p d n r : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (H r).index)
    (m : ℤ) :
    ∃ a : Fin (((H r).commutator i).word.weight (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let S :=
        ((H r).commutator i).freshenleast_weightprime_powerscheme
          (p := p) (n := n) hr
      let y := S.eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (H s).index,
                hallCoordinate hn H hH y j = 0) ∧
        (∀ j : (H r).index,
          hallCoordinate hn H hH y j =
            if j = i then
              ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) * m
            else 0) ∧
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n :=
  BCWta.existsfreshen_primepower_evalprescoor
    hn H hH hr hrn i m

/--
Coordinate description of the `n`th Zassenhaus term in the free nilpotent
truncation.  This is the Lean form of the paper statement
`g ∈ D_n` iff every Hall coordinate of ordinary weight `s` is divisible by
the prime power assigned by `s * p^a ≥ n`.
-/
theorem form_coordinates_dvd
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ↔
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ i : (H s).index,
              ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣
                normalFormCoordinates hn H hH y s i := by
  change
    y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ↔
      y ∈ hallCoordinateLattice (p := p) hn H hH hproduct hinverse
  rw [zassenhaus_filtration_lattice
    hn H hH hpower hproduct hinverse]

/--
The same coordinate criterion expressed through the single Hall-coordinate
accessor.
-/
theorem zassenhaus_filtration_dvd
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ↔
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ i : (H s).index,
              ((p ^ leastWeightedExponent p n s : ℕ) : ℤ) ∣
                hallCoordinate hn H hH y i := by
  simpa [hallCoordinate] using
    form_coordinates_dvd
      (p := p) (d := d) (n := n) hn H hH hpower hproduct hinverse y

/--
Uniform bounded Hall--Zassenhaus collection in the free nilpotent truncation,
with the explicit bound equal to the number of Hall commutators of ordinary
weight below `n`, assuming the Hall basis and collection-polynomial data.
-/
theorem uniform_bound_data
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e) :
    TruncationCollectionBound.{u}
      p d n (commutatorCountBelow H n) :=
  free_truncation_data
    hn H hH hpower hproduct hinverse

/--
Existential form of the uniform bounded Hall--Zassenhaus collection theorem
for the free nilpotent truncation.
-/
theorem uniform_collection_data
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (hproduct :
      ∀ e : List (HEFam H),
        CollectedCoordinateData (n := n) H e)
    (hinverse :
      ∀ e : HEFam H,
        CollectedInverseData (n := n) H e) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow H n,
    uniform_bound_data
      hn H hH hpower hproduct hinverse⟩

end TCTex
end Towers
