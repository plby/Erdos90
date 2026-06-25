import Submission.ClassField.Ideles.IdeleNorm

/-!
# Reindexing places in a tower for idèle norms

The iterated norm over `L/E/K` is indexed by a place of `E` over a place of
`K`, followed by a place of `L` over that place of `E`.  The direct norm is
indexed by a place of `L` over the original place of `K`.  This file records
the two equivalences needed to compare those products.
-/

namespace Submission.CField.NIndex

open IsDedekindDomain NumberField
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Literal upper finite primes above a fixed lower prime. -/
abbrev PlacesAbovePrime
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (P : HeightOneSpectrum (OK K)) :=
  {Q : HeightOneSpectrum (OK L) // Q.under (OK K) = P}

/-- A prime factor of `P O_L` as a literal upper prime over `P`. -/
noncomputable def upperPlaceAbove
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) :
    UpperPrimeFactors (K := K) (L := L) P → PlacesAbovePrime K L P :=
  fun Q ↦ ⟨upperPrime (K := K) (L := L) P Q,
    upperPrime_under (K := K) (L := L) P Q⟩

private theorem upper_above_injective
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) :
    Function.Injective (upperPlaceAbove
      (K := K) (L := L) P) := by
  intro Q₁ Q₂ h
  apply Subtype.ext
  have h' := congrArg
    (fun Q : PlacesAbovePrime K L P ↦ Q.1.asIdeal) h
  exact h'

private theorem upper_above_surjective
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) :
    Function.Surjective (upperPlaceAbove
      (K := K) (L := L) P) := by
  intro Q
  let I : Ideal (OK L) :=
    P.asIdeal.map (algebraMap (OK K) (OK L))
  have hI : I ≠ 0 := Ideal.map_ne_bot_of_ne_bot P.ne_bot
  have hQtop : Q.1.asIdeal ≠ ⊤ := Q.1.isPrime.ne_top
  letI : P.asIdeal.IsMaximal := P.isMaximal
  have hlies : Q.1.asIdeal.LiesOver P.asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal Q.2).symm
  have hdiv : Q.1.asIdeal ∣ I :=
    (Ideal.liesOver_iff_dvd_map hQtop).mp hlies
  have hirr : Irreducible Q.1.asIdeal :=
    (Ideal.prime_of_isPrime Q.1.ne_bot Q.1.isPrime).irreducible
  obtain ⟨q, hqmem, hQq⟩ :=
    UniqueFactorizationMonoid.exists_mem_factors_of_dvd hI hirr hdiv
  let q' : UpperPrimeFactors (K := K) (L := L) P :=
    ⟨q, Multiset.mem_toFinset.mpr hqmem⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  exact associated_iff_eq.mp hQq.symm

/-- Prime factors of `P O_L` are equivalent to literal finite primes of `L`
contracting to `P`. -/
noncomputable def upperPlacesAbove
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) :
    UpperPrimeFactors (K := K) (L := L) P ≃ PlacesAbovePrime K L P :=
  Equiv.ofBijective (upperPlaceAbove
    (K := K) (L := L) P)
    ⟨upper_above_injective (K := K) (L := L) P,
      upper_above_surjective (K := K) (L := L) P⟩

noncomputable instance placesAboveFintype
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) :
    Fintype (PlacesAbovePrime K L P) :=
  Fintype.ofEquiv (UpperPrimeFactors (K := K) (L := L) P)
    (upperPlacesAbove (K := K) (L := L) P)

theorem height_one_spectrum
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (R : HeightOneSpectrum (OK L)) :
    (R.under (OK E)).under (OK K) = R.under (OK K) := by
  apply HeightOneSpectrum.ext
  change Ideal.under (OK K) (Ideal.under (OK E) R.asIdeal) =
    Ideal.under (OK K) R.asIdeal
  exact Ideal.under_under (A := OK K) (B := OK E) (C := OK L) R.asIdeal

/-- A finite prime of `L` over `P` is equivalently a prime of `E` over `P`
together with a prime of `L` above it. -/
noncomputable def placesAboveTower
    (K E L : Type u) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (P : HeightOneSpectrum (OK K)) :
    PlacesAbovePrime K L P ≃
      Σ Q : PlacesAbovePrime K E P,
        PlacesAbovePrime E L Q.1 where
  toFun R := by
    let Q : PlacesAbovePrime K E P :=
      ⟨R.1.under (OK E),
        (height_one_spectrum R.1).trans R.2⟩
    exact ⟨Q, ⟨R.1, rfl⟩⟩
  invFun QR := by
    let Q := QR.1
    let R := QR.2
    refine ⟨R.1, ?_⟩
    calc
      R.1.under (OK K) = (R.1.under (OK E)).under (OK K) :=
        (height_one_spectrum R.1).symm
      _ = Q.1.under (OK K) := congrArg (fun T ↦ T.under (OK K)) R.2
      _ = P := Q.2
  left_inv R := by
    apply Subtype.ext
    rfl
  right_inv QR := by
    rcases QR with ⟨Q, R⟩
    rcases Q with ⟨Q, hQ⟩
    rcases R with ⟨R, hR⟩
    dsimp at hR ⊢
    subst Q
    rfl

/-- An infinite place of `L` over `v` is equivalently an infinite place of
`E` over `v` together with an infinite place of `L` above it. -/
noncomputable def infiniteAboveTower
    (K E L : Type u) [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (v : InfinitePlace K) :
    InfinitePlacesAbove (K := K) (L := L) v ≃
      Σ u : InfinitePlacesAbove (K := K) (L := E) v,
        InfinitePlacesAbove (K := E) (L := L) u.1 where
  toFun w := by
    let u : InfinitePlacesAbove (K := K) (L := E) v :=
      ⟨w.1.comap (algebraMap E L), by
        calc
          (w.1.comap (algebraMap E L)).comap (algebraMap K E) =
              w.1.comap ((algebraMap E L).comp (algebraMap K E)) := rfl
          _ = w.1.comap (algebraMap K L) :=
            congrArg w.1.comap (IsScalarTower.algebraMap_eq K E L).symm
          _ = v := w.2⟩
    exact ⟨u, ⟨w.1, rfl⟩⟩
  invFun uw := by
    let u := uw.1
    let w := uw.2
    refine ⟨w.1, ?_⟩
    calc
      w.1.comap (algebraMap K L) =
          w.1.comap ((algebraMap E L).comp (algebraMap K E)) :=
        congrArg w.1.comap (IsScalarTower.algebraMap_eq K E L)
      _ = (w.1.comap (algebraMap E L)).comap (algebraMap K E) := rfl
      _ = u.1.comap (algebraMap K E) :=
        congrArg (fun z ↦ z.comap (algebraMap K E)) w.2
      _ = v := u.2
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv uw := by
    rcases uw with ⟨u, w⟩
    rcases u with ⟨u, hu⟩
    rcases w with ⟨w, hw⟩
    dsimp at hw ⊢
    subst u
    rfl

end

end Submission.CField.NIndex
