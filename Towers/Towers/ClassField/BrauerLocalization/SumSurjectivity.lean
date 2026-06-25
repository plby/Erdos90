import Towers.ClassField.GlobalClass.BrauerSequenceStatements

/-!
# Surjectivity of the invariant sum in Theorem VIII.4.2

The invariant sum is surjective for a reason independent of global
reciprocity: the invariant at any one finite place is already an additive
equivalence onto `LocalInvariant`.  This file supplies a finite place by
choosing a prime of the ring of integers above `(2)`.
-/

namespace Towers.CField.BLoc

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.RExist

noncomputable section

universe u v w

/-- A componentwise sum is surjective if one of its components is
surjective. -/
theorem direct_monoid_component
    {ι : Type u} {A : ι → Type v} [DecidableEq ι]
    [∀ i, AddCommMonoid (A i)]
    {B : Type w} [AddCommMonoid B]
    (f : ∀ i, A i →+ B) (i : ι) (hi : Function.Surjective (f i)) :
    Function.Surjective (DirectSum.toAddMonoid f) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := hi y
  exact ⟨DirectSum.of A i x, DirectSum.toAddMonoid_of f i x⟩

/-- The canonical carry-normalized invariant at a finite place is
surjective. -/
theorem place_invariant_surjective
    (K : Type u) [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective (finitePlaceInvariant K P) := by
  intro y
  letI : NontriviallyNormedField (FinitePlace.mk P).val.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel (FinitePlace.mk P).val.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := (FinitePlace.mk P).val.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := (FinitePlace.mk P).val.Completion))
  letI : IsNonarchimedeanLocalField (FinitePlace.mk P).val.Completion :=
    placeNonarchimedeanField P
  let x : BrauerGroup
      (Towers.CField.RExist.placeCompletion K (.inl P)) :=
    (carryBrauerInvariant
      ((FinitePlace.mk P).val.Completion)).symm (Multiplicative.ofAdd y)
  refine ⟨Additive.ofMul x, ?_⟩
  change (carryBrauerInvariant
    ((FinitePlace.mk P).val.Completion) x).toAdd = y
  simp [x]

/-- Surjectivity of the invariant sum after choosing any finite place. -/
theorem sum_invariant_place
    (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Surjective (BData.sumInvariant K data) := by
  classical
  change Function.Surjective
    (DirectSum.toAddMonoid data.placeInvariant.invariant)
  apply direct_monoid_component
      data.placeInvariant.invariant (.inl P)
  rw [data.placeInvariant.finite_eq P]
  exact place_invariant_surjective K P

/-- Every number field has a finite place; one may take a prime above `(2)`. -/
theorem height_spectrum_integers
    (K : Type u) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  let q : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : q.IsMaximal := by
    dsimp [q]
    exact Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨P, hPmax, hPlies⟩ :=
    q.exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K)
  have hq0 : q ≠ ⊥ := by
    simp [q]
  have hPmem : P ∈ q.primesOver (NumberField.RingOfIntegers K) :=
    ⟨hPmax.isPrime, hPlies⟩
  exact ⟨⟨P, hPmax.isPrime, Ideal.ne_bot_of_mem_primesOver hq0 hPmem⟩⟩

/-- The sum of the canonical local invariants is onto, independently of
global reciprocity: a single finite-place component is already onto. -/
theorem sumInvariant_surjective
    (K : Type u) [Field K] [NumberField K]
    (data : BData K) :
    Function.Surjective (BData.sumInvariant K data) := by
  obtain ⟨P⟩ := height_spectrum_integers K
  exact sum_invariant_place K data P

end

end Towers.CField.BLoc
