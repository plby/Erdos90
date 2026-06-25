import Mathlib.GroupTheory.Index
import Submission.ClassField.Ramification.SubgroupEquivMap

/-!
# Class Field Theory, Chapter I, upper ramification numbering

This file introduces the integer-point Herbrand function used in Section 4,
together with the lower- and upper-jump predicates.  At an integer `i`, the
Herbrand function is the sum of the slopes on the intervals
`(0,1), ..., (i-1,i)`.
-/

namespace Submission.CField.Ramification

open scoped BigOperators NNReal

noncomputable section

/-- The value at a natural number of the Herbrand function associated to a
lower ramification filtration.  The summand on `(j,j+1)` is the reciprocal
of `(G₀ : G_{j+1})`. -/
def lowerHerbrandNat {G : Type*} [Group G]
    (lower : ℕ → Subgroup G) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range i,
    ((lower (j + 1)).relIndex (lower 0) : ℚ)⁻¹

@[simp]
theorem lower_herbrand_nat
    {G : Type*} [Group G] (lower : ℕ → Subgroup G) :
    lowerHerbrandNat lower 0 = 0 := by
  simp [lowerHerbrandNat]

/-- The increment over one unit interval is the reciprocal of the relevant
ramification-group index. -/
theorem lower_herbrand_succ
    {G : Type*} [Group G] (lower : ℕ → Subgroup G) (i : ℕ) :
    lowerHerbrandNat lower (i + 1) = lowerHerbrandNat lower i +
      ((lower (i + 1)).relIndex (lower 0) : ℚ)⁻¹ := by
  simp [lowerHerbrandNat, Finset.sum_range_succ]

/-- A jump in the lower numbering occurs when consecutive integral
ramification groups differ. -/
def LowerRamificationJump {G : Type*} [Group G]
    (lower : ℕ → Subgroup G) (i : ℕ) : Prop :=
  lower i ≠ lower (i + 1)

/-- Definition 4.5: `v` is a jump in an upper-numbered filtration when every
positive rightward displacement changes the group. -/
def UpperRamificationJump {G : Type*} [Group G]
    (upper : ℝ≥0 → Subgroup G) (v : ℝ≥0) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → upper v ≠ upper (v + ε)

/-- The integer-point formulation of the Hasse--Arf conclusion: every lower
jump is sent by the Herbrand function to an integer. -/
def IntegralHerbrandJumps {G : Type*} [Group G]
    (lower : ℕ → Subgroup G) : Prop :=
  ∀ i, LowerRamificationJump lower i →
    ∃ z : ℤ, lowerHerbrandNat lower i = z

/-- Quotient compatibility for a proposed upper numbering.  Proposition 4.4
asserts this property for upper ramification filtrations and the quotient map
of a normal subgroup. -/
def UNumber.IsQuotientCompatible
    {ι G Q : Type*} [Group G] [Group Q]
    (upperG : ι → Subgroup G) (upperQ : ι → Subgroup Q)
    (quotientMap : G →* Q) : Prop :=
  ∀ v, (upperG v).map quotientMap = upperQ v

/-- Pointwise form of quotient compatibility, matching the displayed formula
`(G/H)^v = im(G^v → G/H)` in Proposition 4.4. -/
theorem UNumber.image_eq_quotcompat
    {ι G Q : Type*} [Group G] [Group Q]
    {upperG : ι → Subgroup G} {upperQ : ι → Subgroup Q}
    {quotientMap : G →* Q}
    (h : UNumber.IsQuotientCompatible upperG upperQ quotientMap)
    (v : ι) :
    (upperG v).map quotientMap = upperQ v :=
  h v

end

end Submission.CField.Ramification
