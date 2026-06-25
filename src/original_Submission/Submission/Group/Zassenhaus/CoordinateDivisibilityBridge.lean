import Submission.Group.Zassenhaus.TriangularGHLaw

/-!
# Free-truncation collection from Hall-coordinate divisibility

The existing Claim 14 endpoint is proved from the full Hall collection
polynomial package by first showing that `D_n` is exactly the Hall-coordinate
lattice.  This file factors out the last step: once elements of `D_n` are
known to have the required Hall-coordinate divisibility, the bounded
normalized Zassenhaus list follows without any product, inverse, or power
polynomial inputs.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement


/--
Absorb one complete weight-`r` Hall layer using only the Hall-coordinate
divisibility of the element being absorbed.
-/
theorem bounded_normalized_divisibility
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
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hyZassenhaus :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n)
    (hyLower :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (hyCoordinates :
      HallCoordinateLattice (p := p) hn H hH y) :
    ∃ L : List
        (BSValue p d n
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)),
      L.length ≤ Fintype.card (H r).index ∧
        let z := (L.map BSValue.eval).prod⁻¹ * y
        z ∈ zassenhausFiltration
            p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ∧
          z ∈ Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) r := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  choose m hm using fun i : (H r).index => hyCoordinates r hr hrn i
  choose a _haBelow haWeight haZassenhaus using fun i : (H r).index =>
    BCWta.existsfreshen_primepower_evalprescoor
      (p := p) hn H hH hr hrn i (m i)
  let S : (H r).index → ZWScheme p n :=
    fun i =>
      ((H r).commutator i).freshenleast_weightprime_powerscheme
        (p := p) (n := n) hr
  choose z hz using fun i : (H r).index =>
    bounded_scheduled_scheme
      (p := p) (d := d) (by omega : 0 < n) (S i) (a i)
  let L :
      List
        (BSValue p d n
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)) :=
    (Finset.univ.sort fun i j : (H r).index => i ≤ j).map z
  let P : N := (L.map BSValue.eval).prod
  have hzLower :
      ∀ i : (H r).index,
        (z i).eval ∈ Subgroup.lowerCentralSeries N (r - 1) := by
    intro i
    rw [hz i]
    rw [ZWScheme.eval_def]
    apply (Subgroup.lowerCentralSeries N (r - 1)).pow_mem
    have hweight : (S i).word.weight (fun _ => 1) = r := by
      simp [S,
        BCWt.freshenleast_weightprime_powerscheme,
        ((H r).commutator i).word_weight]
    simpa [ZWScheme.lowerLevel, hweight] using
      (S i).word_lower_series (a i)
  have hzZassenhaus :
      ∀ i : (H r).index,
        (z i).eval ∈ zassenhausFiltration p N n := by
    intro i
    rw [hz i]
    exact haZassenhaus i
  have hPLower :
      P ∈ Subgroup.lowerCentralSeries N (r - 1) := by
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
    rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
    exact hzLower i
  have hPZassenhaus :
      P ∈ zassenhausFiltration p N n := by
    apply Subgroup.list_prod_mem
    intro x hx
    rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
    rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
    exact hzZassenhaus i
  have hzCoordinate :
      ∀ i j : (H r).index,
        hallCoordinate hn H hH (z i).eval j =
          if j = i then
            ((p ^ leastWeightedExponent p n r : ℕ) : ℤ) * m i
          else 0 := by
    intro i j
    rw [hz i]
    exact haWeight i j
  have hPCoordinates :
      normalFormCoordinates hn H hH P r =
        normalFormCoordinates hn H hH y r := by
    funext j
    change hallCoordinate hn H hH P j = hallCoordinate hn H hH y j
    rw [show P = (L.map BSValue.eval).prod by rfl,
      forall_lower_series
        hn H hH hr hrn
        (L.map BSValue.eval)
        (by
          intro x hx
          rcases List.mem_map.mp hx with ⟨zi, hzi, rfl⟩
          rcases List.mem_map.mp hzi with ⟨i, _hi, rfl⟩
          exact hzLower i)
        j]
    simp only [L, List.map_map]
    rw [list_sort_univ]
    simp only [Function.comp_apply, hzCoordinate]
    simp
    simpa [hallCoordinate] using (hm j).symm
  refine ⟨L, ?_, ?_, ?_⟩
  · simp [L]
  · exact
      (zassenhausFiltration p N n).mul_mem
        ((zassenhausFiltration p N n).inv_mem hPZassenhaus)
        hyZassenhaus
  · exact
      inv_form_coordinates
        hn H hH hr hrn P y hPLower hyLower hPCoordinates

/--
Claim 14 with the Hall-polynomial package replaced by the single consequence
needed from it: every element of `D_n` has divisible Hall coordinates.
-/
theorem normalized_filtration_divisibility
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hdiv :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
          HallCoordinateLattice (p := p) hn H hH y)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n) :
    BNZass
      p d n (commutatorCountBelow H n) y := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  have hcollect :
      ∀ t k : ℕ,
        k + t = n - 1 →
          ∀ z : N,
            z ∈ zassenhausFiltration p N n →
              z ∈ Subgroup.lowerCentralSeries N k →
                BNZass
                  p d n (hallCommutatorCount H k t) z := by
    intro t
    induction t with
    | zero =>
        intro k hk z _hzZassenhaus hzLower
        have hbot : Subgroup.lowerCentralSeries N (n - 1) = ⊥ := by
          simpa [N, LowerCentralTruncation] using
            (lower_last_bot
              (G := FreeGroup (FreeGenerator.{u} d)) (c := n))
        have hzOne : z = 1 := by
          apply eq_bot_iff.mp hbot
          have hk' : k = n - 1 := by omega
          simpa [hk'] using hzLower
        simpa [hallCommutatorCount, hzOne] using
          bounded_normalized_one p d n
    | succ t ih =>
        intro k hk z hzZassenhaus hzLower
        have hr : 1 ≤ k + 1 := by omega
        have hrn : k + 1 < n := by omega
        obtain ⟨L, hLlength, hLZassenhaus, hLLower⟩ :=
          bounded_normalized_divisibility
            hn H hH hr hrn z hzZassenhaus
              (by simpa using hzLower)
              (hdiv z hzZassenhaus)
        let residual : N :=
          (L.map BSValue.eval).prod⁻¹ * z
        have hresidual :
            BNZass
              p d n (hallCommutatorCount H (k + 1) t) residual :=
          ih (k + 1) (by omega) residual
            (by simpa [residual] using hLZassenhaus)
            (by simpa [residual] using hLLower)
        rcases hresidual with ⟨R, hRlength, hRprod⟩
        refine ⟨L ++ R, ?_, ?_⟩
        · simpa [hallCommutatorCount, List.length_append] using
            Nat.add_le_add hLlength hRlength
        · rw [List.map_append, List.prod_append, hRprod]
          simp [residual]
  simpa [commutatorCountBelow] using
    hcollect (n - 1) 0 (by simp) y hy (by simp)

/--
Free-truncation collection bound from a direct Hall-coordinate divisibility
criterion for `D_n`.
-/
theorem free_collection_divisibility
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hdiv :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
          HallCoordinateLattice (p := p) hn H hH y) :
    TruncationCollectionBound.{u}
      p d n (commutatorCountBelow H n) := by
  intro y hy
  exact
    normalized_filtration_divisibility
      hn H hH hdiv y hy

/--
Existential form of the direct-divisibility bridge.
-/
theorem free_truncation_divisibility
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hdiv :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
          HallCoordinateLattice (p := p) hn H hH y) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow H n,
    free_collection_divisibility
      hn H hH hdiv⟩

/--
It is enough to show that the Hall-coordinate lattice is the carrier of some
subgroup, together with the Hall power divisibility input for powered lower
central generators.  This isolates the product/inverse closure obligation from
the final bounded-collection argument.
-/
theorem free_truncation_lattice
    (p d n : ℕ)
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
    (L : Subgroup (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (hL :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ L ↔ HallCoordinateLattice (p := p) hn H hH y) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  apply
    free_truncation_divisibility
      p d n hn H hH
  intro y hy
  have hZassenhausLeL : zassenhausFiltration p N n ≤ L := by
    apply filtration_generator_set
    rintro y ⟨i, a, x, hx, hlevel, rfl⟩
    apply (hL (x ^ p ^ a)).mpr
    intro s hs hsn j
    exact
      least_weighted_exponent
        (r := i + 1) (s := s)
        hn H hH hpower x (by simpa using hx) (by omega) hs hsn a
        (by simpa using hlevel) j
  exact (hL y).mp (hZassenhausLeL hy)

/--
Concrete-Hall specialization of
`free_truncation_lattice`.
-/
theorem truncation_collection_lattice
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            BCWta.FormsAssocGradedbasis
              (n := n)
              (collectionConcreteCommutators.{u} d s))
    (hpower :
      ∀ (e :
          HEFam
            (collectionConcreteCommutators.{u} d))
        (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData
            (n := n)
            (collectionConcreteCommutators.{u} d)
            e t)
    (L : Subgroup (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n))
    (hL :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ L ↔
          HallCoordinateLattice
            (p := p) hn
            (collectionConcreteCommutators.{u} d)
            hH
            y) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  free_truncation_lattice
    p d n hn
      (collectionConcreteCommutators.{u} d)
      hH
      hpower
      L
      hL

/--
Internal concrete-Hall form of the direct-divisibility bridge.  The
associated-graded basis proof is kept explicit so this file stays independent
of the later concrete Hall triangular-law endpoint.
-/
theorem truncation_collection_divisibility
    (p d n : ℕ)
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            BCWta.FormsAssocGradedbasis
              (n := n)
              (collectionConcreteCommutators.{u} d s))
    (hdiv :
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
          HallCoordinateLattice
            (p := p) hn
            (collectionConcreteCommutators.{u} d)
            hH
            y) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  free_truncation_divisibility
    p d n hn
      (collectionConcreteCommutators.{u} d)
      hH
      hdiv

end TCTex
end Submission
