import Towers.ClassField.KummerNormIndex.LocalPowerIndex
import Towers.ClassField.KummerNormIndex.GeneratedPthRoots

/-!
# The local target cardinality in Lemma VII.6.9

Proposition VII.6.8 computes the power index in the local-unit subgroup of
the completed field.  This file transports that calculation to the literal
unit group of the completed valuation ring used in Lemma VII.6.9.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.Ideles
open ValuativeRel

noncomputable section

universe u

/-- Local units and units of the valuation integer ring are canonically
equivalent. -/
noncomputable def localUnitInteger
    (F : Type u) [Field F] [ValuativeRel F] :
    localUnitSubgroup F ≃* (Valuation.integer (valuation F))ˣ :=
  MonoidHom.toMulEquiv (localInteger F)
    (integerUnitLocal F)
    (by ext x; rfl)
    (by ext x; rfl)

set_option maxHeartbeats 4000000 in
-- Computing the local-unit quotient at the canonical finite completion
-- expands the power-index and residue-field cardinality comparisons.
set_option synthInstance.maxHeartbeats 1000000 in
/-- At a finite prime outside `S`, the quotient of local integer units by
`p`th powers has cardinality `p`. -/
theorem local_unit_card
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (hDividing : ∀ v : NumberFieldPlace K,
      normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S)
    (P : FinitePrime K)
    (hP : (Sum.inl P : NumberFieldPlace K) ∉ S) :
    Nat.card (localUnitClass K p P) = p := by
  let C := P.adicCompletion K
  let B := P.adicCompletionIntegers K
  letI : NontriviallyNormedField C :=
    completionNontriviallyNormed P
  letI : ValuativeRel C := completionValuativeRel P
  letI : IsNonarchimedeanLocalField C :=
    adicCompletionField P
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  letI : CharZero C :=
    charZero_of_injective_ringHom (FinitePlace.embedding (K := K) P).injective
  letI : NeZero p := ⟨hp.ne_zero⟩
  let eCB : Valuation.integer (valuation C) ≃+* B :=
    (integerEquivNormed C).trans
      (normedIntegerIntegers P)
  let eU : localUnitSubgroup C ≃* Bˣ :=
    (localUnitInteger C).trans
      (Units.mapEquiv eCB.toMulEquiv)
  have hindexTransport :
      (pthPowerSubgroup p (localUnitSubgroup C)).index =
        (pthPowerSubgroup p Bˣ).index :=
    power_index_equiv eU p
  have hplace :
      (FinitePlace.equivHeightOneSpectrum.symm P) (p : K) = 1 := by
    by_contra hne
    exact hP (hDividing (Sum.inl P) hne)
  obtain ⟨ζ, hζ⟩ := hroots
  have hprimitiveK : IsPrimitiveRoot ζ p :=
    (mem_primitiveRoots hp.pos).mp hζ
  have hprimitiveC :
      IsPrimitiveRoot (FinitePlace.embedding (K := K) P ζ) p :=
    hprimitiveK.map_of_injective
      (FinitePlace.embedding (K := K) P).injective
  have hcardRoots : Nat.card (rootsOfUnity p C) = p := by
    rw [Nat.card_eq_fintype_card]
    exact hprimitiveC.card_rootsOfUnity
  have hformula := complexAbsoluteStatement.2.2 C p hp.pos |>.2
  have hlocalIndex :
      (pthPowerSubgroup p (localUnitSubgroup C)).index = p := by
    have hreal :
        (((pthPowerSubgroup p (localUnitSubgroup C)).index : ℕ) : ℝ) =
          (p : ℝ) := by
      rw [normalized_absolute_value K P p hp.pos,
        hplace, mul_one, hcardRoots] at hformula
      exact hformula
    exact_mod_cast hreal
  change (pthPowerSubgroup p Bˣ).index = p
  rw [← hindexTransport]
  exact hlocalIndex

/-- The finite product of local unit power classes in Lemma VII.6.9 has
cardinality `p ^ |T|`. -/
theorem localTargetBridge : LocalTargetBridge.{u} := by
  intro p K _ _ hp hroots S T hDividing hDisjoint
  have hcard (P : T) : Nat.card (localUnitClass K p P.1) = p :=
    local_unit_card p K hp hroots S hDividing P.1
      (hDisjoint P.1 P.2)
  have hfinite (P : T) : Finite (localUnitClass K p P.1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard P]; exact hp.ne_zero)
  letI (P : T) : Finite (localUnitClass K p P.1) := hfinite P
  constructor
  · infer_instance
  · rw [Nat.card_pi]
    simp_rw [hcard]
    simp

end

end Towers.CField.KNIndex
