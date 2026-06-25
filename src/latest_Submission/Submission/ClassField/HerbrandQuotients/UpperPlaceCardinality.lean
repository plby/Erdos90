import Submission.ClassField.HerbrandQuotients.UnitLogKernel

/-!
# Counting the upper places in Proposition VII.3.1

When `S` contains every infinite place, its upper-place set is the disjoint
union of the finite primes of `L` above the finite members of `S` and all
infinite places of `L`.  This is the cardinal identity used in the
`T`-unit rank calculation.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Regard an archimedean completion place literally as its infinite place
of `L`. -/
noncomputable def upperInfinitePlace
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) : InfinitePlace L :=
  ⟨z.1, by
    obtain ⟨w, -, hw⟩ :=
      infinite_place_upper (K := K) (L := L) v z
    exact hw ▸ w.isInfinitePlace⟩

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem upper_infinite_val
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    (upperInfinitePlace (K := K) (L := L) v z).1 = z.1 :=
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The infinite place attached to an upper completion place lies over its
specified base place. -/
theorem upper_infinite_comap
    (v : InfinitePlace K)
    (z : CompletionPlacesAbove (L := L) v.1) :
    (upperInfinitePlace
      (K := K) (L := L) v z).comap (algebraMap K L) = v := by
  obtain ⟨w, hwv, hw⟩ :=
    infinite_place_upper (K := K) (L := L) v z
  have heq : upperInfinitePlace
      (K := K) (L := L) v z = w := Subtype.ext hw.symm
  exact congrArg (fun q : InfinitePlace L =>
    q.comap (algebraMap K L)) heq |>.trans hwv

/-- Send an upper completion place to its centered finite prime or literal
infinite place. -/
noncomputable def upperPlacesSum
    (S : Finset (NumberFieldPlace K)) :
    upperPlacesAt (K := K) (L := L) S →
      (primesAbovePlaces (K := K) (L := L) S) ⊕ InfinitePlace L
  | ⟨⟨.inl P, hP⟩, z⟩ =>
      let Q := placeAboveBase
        (K := K) (L := L) P z
      Sum.inl ⟨Q.1, by
        change (Sum.inl (Q.1.under (NumberField.RingOfIntegers K)) :
          NumberFieldPlace K) ∈ S
        rw [Q.2]
        exact hP⟩
  | ⟨⟨.inr v, _⟩, z⟩ =>
      Sum.inr (upperInfinitePlace (K := K) (L := L) v z)

private theorem upper_places_surjective
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Function.Surjective (upperPlacesSum (K := K) (L := L) S) := by
  intro q
  cases q with
  | inl Q =>
      let P : FinitePrime K := Q.1.under (NumberField.RingOfIntegers K)
      let vS : S := ⟨Sum.inl P, Q.2⟩
      let Qabove : PrimesAboveBase (K := K) (L := L) P := ⟨Q.1, rfl⟩
      let qFactor : UpperPrimeFactors (K := K) (L := L) P :=
        (upperAboveBase
          (K := K) (L := L) P).symm Qabove
      let z := (placesAboveFactors
        (K := K) (L := L) P).symm qFactor
      refine ⟨⟨vS, z⟩, ?_⟩
      dsimp only [upperPlacesSum]
      apply congrArg Sum.inl
      apply Subtype.ext
      have hfac := (placesAboveFactors
        (K := K) (L := L) P).apply_symm_apply qFactor
      have hcenter : placeAboveBase
          (K := K) (L := L) P z = Qabove := by
        apply (upperAboveBase
          (K := K) (L := L) P).symm.injective
        exact hfac
      exact congrArg (fun R : PrimesAboveBase
        (K := K) (L := L) P => R.1) hcenter
  | inr w =>
      let v : InfinitePlace K := w.comap (algebraMap K L)
      let vS : S := ⟨Sum.inr v, hSinf v⟩
      let z : CompletionPlacesAbove (L := L) v.1 :=
        ⟨w.1, infinite_lies_comap v w rfl⟩
      refine ⟨⟨vS, z⟩, ?_⟩
      dsimp only [upperPlacesSum]
      apply congrArg Sum.inr
      apply Subtype.ext
      rfl

private theorem upper_places_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective (upperPlacesSum (K := K) (L := L) S) := by
  rintro ⟨⟨v, hv⟩, z⟩ ⟨⟨v', hv'⟩, z'⟩ h
  cases v with
  | inl P =>
      cases v' with
      | inl P' =>
          let Q := placeAboveBase
            (K := K) (L := L) P z
          let Q' := placeAboveBase
            (K := K) (L := L) P' z'
          change Sum.inl _ = Sum.inl _ at h
          have hsub := Sum.inl_injective h
          have hQ : Q.1 = Q'.1 := congrArg Subtype.val hsub
          have hPP' : P = P' := by
            calc
              P = Q.1.under (NumberField.RingOfIntegers K) := Q.2.symm
              _ = Q'.1.under (NumberField.RingOfIntegers K) :=
                congrArg (fun R : FinitePrime L =>
                  R.under (NumberField.RingOfIntegers K)) hQ
              _ = P' := Q'.2
          subst P'
          have hcenter : Q = Q' := Subtype.ext hQ
          have hz : z = z' := by
            apply (placesAboveFactors
              (K := K) (L := L) P).injective
            change placeUpperFactor
                (K := K) (L := L) P z =
              placeUpperFactor
                (K := K) (L := L) P z'
            exact congrArg
              (upperAboveBase
                (K := K) (L := L) P).symm hcenter
          subst z'
          rfl
      | inr v' =>
          simp only [upperPlacesSum, reduceCtorEq] at h
  | inr v =>
      cases v' with
      | inl P' =>
          simp only [upperPlacesSum, reduceCtorEq] at h
      | inr v' =>
          change Sum.inr _ = Sum.inr _ at h
          have hw := Sum.inr_injective h
          have hvv' : v = v' := by
            rw [← upper_infinite_comap
              (K := K) (L := L) v z,
              ← upper_infinite_comap
                (K := K) (L := L) v' z', hw]
          subst v'
          have hz : z = z' := by
            apply Subtype.ext
            exact congrArg (fun w : InfinitePlace L => w.1) hw
          subst z'
          rfl

/-- The literal equivalence between Milne's upper-place index set and the
finite/infinite place decomposition of `L`. -/
noncomputable def upperPlacesInfinite
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    upperPlacesAt (K := K) (L := L) S ≃
      (primesAbovePlaces (K := K) (L := L) S) ⊕ InfinitePlace L :=
  Equiv.ofBijective (upperPlacesSum (K := K) (L := L) S)
    ⟨upper_places_injective (K := K) (L := L) S,
      upper_places_surjective (K := K) (L := L) S hSinf⟩

/-- Cardinal form of the finite/infinite decomposition of the upper-place
set. -/
theorem nat_upper_places
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Nat.card (upperPlacesAt (K := K) (L := L) S) =
      (primesAbovePlaces (K := K) (L := L) S).ncard +
        NumberField.InfinitePlace.nrRealPlaces L +
          NumberField.InfinitePlace.nrComplexPlaces L := by
  letI : Fintype (primesAbovePlaces (K := K) (L := L) S) :=
    (primes_above_places (K := K) (L := L) S).fintype
  have hInf : Nat.card (InfinitePlace L) =
      NumberField.InfinitePlace.nrRealPlaces L +
        NumberField.InfinitePlace.nrComplexPlaces L := by
    rw [Nat.card_eq_fintype_card,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [Nat.card_congr
    (upperPlacesInfinite
      (K := K) (L := L) S hSinf), Nat.card_sum,
    Nat.card_coe_set_eq, hInf]
  omega

/-- The logarithmic image has rank exactly one less than the number of
upper places. -/
theorem log_lattice_finrank
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Module.finrank ℤ
        (upperLogLattice (K := K) (L := L) S) =
      Nat.card (upperPlacesAt (K := K) (L := L) S) - 1 := by
  rw [upper_lattice_finrank (K := K) (L := L) S hSinf,
    nat_upper_places (K := K) (L := L) S hSinf]
  omega

/-- The ambient function space has one real dimension for each upper
place. -/
theorem upper_function_space
    (S : Finset (NumberFieldPlace K)) :
    Module.finrank ℝ
        (upperPlacesAt (K := K) (L := L) S → ℝ) =
      Nat.card (upperPlacesAt (K := K) (L := L) S) := by
  letI : Fintype (upperPlacesAt (K := K) (L := L) S) :=
    Fintype.ofFinite _
  rw [Module.finrank_pi, Nat.card_eq_fintype_card]

end

end Submission.CField.HQuotie
