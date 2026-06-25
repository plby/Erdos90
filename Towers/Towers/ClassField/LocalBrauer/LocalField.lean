import Mathlib.NumberTheory.LocalField.Basic


/-!
# Chapter IV, Section 4: nonarchimedean local fields

Milne's local-field computation starts from the normalized discrete valuation,
the ring of integers, and the finite residue field.  Mathlib packages these
facts in `IsNonarchimedeanLocalField`; this file records the precise pieces
used at the start of the subsection.

The subsequent extension of the valuation to a finite-dimensional
*noncommutative* division algebra is not currently part of Mathlib's local
field API.  In particular, the division-algebra ring of integers and its
ramification and residue degrees require additional infrastructure.
-/

namespace Towers.CField.LBrauer

open ValuativeRel
open scoped Valued WithZero

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The residue field of a nonarchimedean local field is finite. -/
theorem local_field_residue : Finite 𝓀[K] :=
  inferInstance

/-- The number `q` of elements in the residue field. -/
noncomputable def fieldResidueCard : ℕ :=
  Nat.card 𝓀[K]

/-- A local residue field has at least two elements. -/
theorem local_residue_card : 1 < fieldResidueCard K := by
  exact Finite.one_lt_card

/-- The ring of integers of a nonarchimedean local field is a discrete
valuation ring. -/
theorem discrete_valuation_ring :
    IsDiscreteValuationRing 𝒪[K] :=
  inferInstance

/-- The value group of a nonarchimedean local field is the multiplicative
copy of the integers with an added zero. -/
noncomputable def local_value_int :
    ValueGroupWithZero K ≃*o ℤᵐ⁰ :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Multiplicativity of the normalized valuation. -/
theorem local_valuation_mul (x y : K) :
    valuation K (x * y) = valuation K x * valuation K y :=
  map_mul (valuation K) x y

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The ultrametric inequality for the normalized valuation. -/
theorem local_valuation_max (x y : K) :
    valuation K (x + y) ≤ max (valuation K x) (valuation K y) :=
  map_add_le_max (valuation K) x y

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The valuation vanishes exactly at zero. -/
theorem local_valuation_zero (x : K) :
    valuation K x = 0 ↔ x = 0 :=
  map_eq_zero (valuation K)

end Towers.CField.LBrauer
