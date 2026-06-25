import Submission.NumberTheory.Locals.LogarithmicValuation
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The valuation ring of a nonarchimedean absolute value

This file formalizes the algebraic assertions in Proposition 7.6 of Milne's
*Algebraic Number Theory*: the elements of absolute value at most one form a
valuation subring, its units have absolute value one, and its maximal ideal
consists of the elements of absolute value strictly less than one.
-/

namespace Submission.NumberTheory.Milne

section

variable {K : Type*} [Field K]

/-- A nonarchimedean real-valued absolute value, regarded as a valuation with
values in the nonnegative reals. -/
noncomputable def absoluteValueValuation (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) : Valuation K NNReal where
  toFun x := ⟨v x, v.nonneg x⟩
  map_one' := Subtype.ext v.map_one
  map_zero' := Subtype.ext v.map_zero
  map_mul' x y := Subtype.ext (v.map_mul x y)
  map_add_le_max' x y := by
    exact_mod_cast hv x y

@[simp]
theorem coe_absolute_valuation (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : K) :
    ((absoluteValueValuation v hv x : NNReal) : ℝ) = v x :=
  rfl

/-- Milne's ring `A = {x | |x| ≤ 1}`. -/
noncomputable def absoluteValueRing (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) : ValuationSubring K :=
  (absoluteValueValuation v hv).valuationSubring

/-- Membership in the valuation ring is exactly the bound `|x| ≤ 1`. -/
@[simp]
theorem absolute_ring (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : K) :
    x ∈ absoluteValueRing v hv ↔ v x ≤ 1 := by
  change (absoluteValueValuation v hv x : NNReal) ≤ 1 ↔ v x ≤ 1
  exact_mod_cast Iff.rfl

/-- The ring of elements of absolute value at most one is a local ring, hence
has a unique maximal ideal. -/
theorem absolute_ring_local (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) : IsLocalRing (absoluteValueRing v hv) :=
  inferInstance

/-- Milne, Proposition 7.6: the units in `A` are exactly the nonzero field
elements of absolute value one. -/
theorem absolute_value_ring (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : Kˣ) :
    x ∈ (absoluteValueRing v hv).unitGroup ↔ v (x : K) = 1 := by
  rw [absoluteValueRing, Valuation.mem_unitGroup_iff]
  rw [← coe_absolute_valuation v hv (x : K)]
  exact_mod_cast Iff.rfl

/-- Milne, Proposition 7.6: the unique maximal ideal of `A` consists of the
elements of absolute value strictly less than one. -/
theorem absolute_maximal_ideal (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : absoluteValueRing v hv) :
    x ∈ IsLocalRing.maximalIdeal (absoluteValueRing v hv) ↔ v (x : K) < 1 := by
  unfold absoluteValueRing at x ⊢
  rw [Valuation.mem_maximalIdeal_iff]
  rw [← coe_absolute_valuation v hv (x : K)]
  exact_mod_cast Iff.rfl

end


end Submission.NumberTheory.Milne
