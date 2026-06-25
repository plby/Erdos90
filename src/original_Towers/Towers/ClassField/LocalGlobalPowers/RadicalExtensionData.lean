import Towers.ClassField.LocalGlobalPowers.PowerReduction
import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.ClassField.NormIndex.PlaceIndex
import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.NumberTheory.Galois.CompositumSplittingPrimes
import Towers.ClassField.Ideles.FinitePlaceCompletion

/-!
# Chapter VIII, Section 1, Theorem 1.1

An element of a number field containing the `n`th roots of unity is an
`n`th power globally if it is an `n`th power at all but finitely many finite
places.  The proof uses an actual radical extension and completion degrees.
-/

namespace Towers.CField.LGPowers

open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The radical extension `K[β]`, with `βⁿ = a`. -/
structure REData
    (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (a : Kˣ) where
  L : Type u
  fieldL : Field L
  numberFieldL : NumberField L
  algebraKL : Algebra K L
  finiteDimensionalKL : FiniteDimensional K L
  isGaloisKL : IsGalois K L
  isSolvableGal : IsSolvable Gal(L/K)
  root : L
  root_pow : root ^ n = algebraMap K L (a : K)
  adjoin_root_top : IntermediateField.adjoin K {root} = ⊤

/-- Complete splitting at `P`, expressed by degree one for every extension
of the normalized absolute value to `L`. -/
def REData.SplitsCompletelyAt
    {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {a : Kˣ} (data : REData K n a)
    (P : HeightOneSpectrum (OK K)) : Prop :=
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  ∀ w : CompletionPlacesAbove (L := data.L) (FinitePlace.mk P).val,
    letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk P).val w.1 w.2).toAlgebra
    Module.finrank (FinitePlace.mk P).val.Completion w.1.Completion = 1

set_option synthInstance.maxHeartbeats 500000 in
-- The proof transports between completion and ideal decomposition groups.
set_option maxHeartbeats 3000000 in
/-- Degree one for every completed factor implies the usual ideal-theoretic
complete-splitting predicate used in Proposition VII.4.6. -/
theorem splits_completely_completion
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : HeightOneSpectrum (OK K))
    (hlocal : ∀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk p).val,
      letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
        (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
      Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 1) :
    SplitsCompletelyAt K L p := by
  let v := (FinitePlace.mk p).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion := placeUltrametricDist p
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  let w : W := Classical.choice (inferInstance : Nonempty W)
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Q.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w.1 w.2 hw hwna
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : MulSemiringAction Gal(L/K) (OK L) :=
    IsIntegralClosure.MulSemiringAction (OK K) K L (OK L)
  letI : MulSemiringAction Gal(L/K) (Ideal (OK L)) :=
    Ideal.pointwiseMulSemiringAction
  letI : IsGaloisGroup Gal(L/K) (OK K) (OK L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (OK K) (OK L) K L
  letI : p.asIdeal.IsMaximal := p.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Field (OK K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Field (OK L ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Finite (OK K ⧸ p.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI : Finite (OK L ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsSeparable (OK K ⧸ p.asIdeal) (OK L ⧸ Q.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hstabilizer :
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) = 1 := by
    calc
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) =
          Nat.card (absoluteValueDecomposition v w.1) := by
        rw [centered_stabilizer_decomposition v w.1 hw hwna]
      _ = Module.finrank v.Completion w.1.Completion := by
        rw [finrank_decomposition_card p w]
      _ = 1 := hlocal w
  have hQmem : Q.asIdeal ∈ Ideal.primesOver p.asIdeal (OK L) :=
    ⟨Q.isPrime, inferInstance⟩
  apply (splits_completely_bot p Q.asIdeal hQmem).mpr
  exact (MulAction.stabilizer Gal(L/K) Q.asIdeal).eq_bot_of_card_eq hstabilizer

end

end Towers.CField.LGPowers
