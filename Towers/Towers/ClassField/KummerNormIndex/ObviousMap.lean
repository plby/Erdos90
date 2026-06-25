import Towers.ClassField.KummerNormIndex.FiniteLift
import Towers.ClassField.KummerNormIndex.FinitePrimePart
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# The local-unit map used in Lemma VII.6.9

This small module contains the construction shared by Lemma 6.9 and the
application of its surjectivity in Lemma 6.7.  Keeping it independent of
both source-statement files avoids a dependency cycle.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.HQuotie

noncomputable section

universe u

/-- The group `U_P / U_P^p` at one actual finite prime `P`. -/
abbrev localUnitClass
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (P : FinitePrime K) :=
  (P.adicCompletionIntegers K)ˣ ⧸
    pthPowerSubgroup p (P.adicCompletionIntegers K)ˣ

/-- The finite product `∏ P ∈ T, U_P / U_P^p` from Lemma 6.9. -/
abbrev localUnitClasses
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (T : Finset (FinitePrime K)) :=
  (P : T) → localUnitClass K p P.1

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent completion-integer unit equivalence needs extra elaboration.
set_option maxHeartbeats 1000000 in
/-- At a prime `P ∈ T` disjoint from `S`, an `S`-unit maps to a unit of the
completed valuation ring at `P`. -/
noncomputable def sUnitHom
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S)
    (P : T) :
    ArithmeticSUnits K (finitePrimePart K S) →*
      (P.1.adicCompletionIntegers K)ˣ :=
  (P.1.adicCompletionIntegers K).unitsEquivUnitsType.toMonoidHom.comp
    { toFun := fun x =>
        ⟨Units.map (FinitePlace.embedding (K := K) P.1) (x : Kˣ),
          by
            rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
            change Valued.v
              (FinitePlace.embedding (K := K) P.1 ((x : Kˣ) : K)) = 1
            rw [FinitePlace.embedding_apply,
              P.1.valuedAdicCompletion_eq_valuation']
            exact x.property P.1 (hDisjoint P.1 P.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }

/-- The actual "obvious map" in Lemma 6.9. -/
noncomputable def obviousMap
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S) :
    ArithmeticSUnits K (finitePrimePart K S) →*
      localUnitClasses K p T :=
  Pi.monoidHom fun P =>
    (QuotientGroup.mk'
      (pthPowerSubgroup p (P.1.adicCompletionIntegers K)ˣ)).comp
        (sUnitHom K S T hDisjoint P)

/-- Coordinate formula for the obvious map. -/
@[simp]
theorem obviousMap_apply
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S)
    (x : ArithmeticSUnits
      K (finitePrimePart K S)) (P : T) :
    obviousMap K p S T hDisjoint x P =
      QuotientGroup.mk'
        (pthPowerSubgroup p (P.1.adicCompletionIntegers K)ˣ)
        (sUnitHom K S T hDisjoint P x) :=
  rfl

end

end Towers.CField.KNIndex
