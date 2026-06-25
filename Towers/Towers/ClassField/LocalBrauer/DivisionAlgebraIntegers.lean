import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Towers.ClassField.LocalBrauer.DivisionAbsoluteValue

/-!
# Chapter IV, Section 4: integers in a division algebra

For the canonical nonarchimedean absolute value on a finite-dimensional
division algebra, the elements of absolute value at most one form a subring.
The elements of absolute value strictly less than one form its maximal
two-sided ideal.  This is the noncommutative valuation ring used in Milne's
local-field calculation.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (D : Type u) [DivisionRing D] [Algebra K D] [Module.Finite K D]

private abbrev abv : AbsoluteValue D ℝ :=
  divisionAbsoluteValue K D

/-- The ring of integers in a finite-dimensional division algebra over a
complete nonarchimedean field. -/
def divisionIntegerSubring : Subring D where
  carrier := {x | abv K D x ≤ 1}
  zero_mem' := by simp [abv]
  one_mem' := by simp [abv]
  add_mem' := by
    intro x y hx hy
    exact (division_absolute_nonarchimedean K D x y).trans
      (max_le hx hy)
  neg_mem' := by
    intro x hx
    change abv K D (-x) ≤ 1
    change abv K D x ≤ 1 at hx
    simpa only [map_neg_eq_map] using hx
  mul_mem' := by
    intro x y hx hy
    change abv K D (x * y) ≤ 1
    change abv K D x ≤ 1 at hx
    change abv K D y ≤ 1 at hy
    rw [map_mul]
    nlinarith [abv K D |>.nonneg x, abv K D |>.nonneg y]

@[simp]
theorem division_subring (x : D) :
    x ∈ divisionIntegerSubring K D ↔ abv K D x ≤ 1 :=
  Iff.rfl

/-- The maximal ideal of the division-algebra ring of integers consists of
the elements of absolute value strictly less than one. -/
def divisionMaximalIdeal : TwoSidedIdeal (divisionIntegerSubring K D) :=
  TwoSidedIdeal.mk'
    {x | abv K D (x : D) < 1}
    (by simp [abv])
    (by
      intro x y hx hy
      exact (division_absolute_nonarchimedean K D (x : D) (y : D)).trans_lt
        (max_lt hx hy))
    (by
      intro x hx
      change abv K D (-(x : D)) < 1
      change abv K D (x : D) < 1 at hx
      simpa only [map_neg_eq_map] using hx)
    (by
      intro x y hy
      change abv K D ((x : D) * (y : D)) < 1
      change abv K D (y : D) < 1 at hy
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right x.2
        (abv K D |>.nonneg (y : D)) hy)
    (by
      intro x y hx
      change abv K D ((x : D) * (y : D)) < 1
      change abv K D (x : D) < 1 at hx
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left
        (abv K D |>.nonneg (x : D)) hx y.2)

@[simp]
theorem division_maximal
    (x : divisionIntegerSubring K D) :
    x ∈ divisionMaximalIdeal K D ↔ abv K D (x : D) < 1 := by
  simp [divisionMaximalIdeal]

/-- Membership in the division order restricts on every commutative
subfield to the usual spectral-norm integrality condition.  This is the
elementwise form of `O_D ∩ E = O_E`. -/
theorem coe_subring_spectral
    (E : Subalgebra K D) (hcomm : ∀ x y : E, x * y = y * x) (e : E) :
    letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
    letI : Module.Finite K E :=
      Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
    letI : IsDomain E :=
      Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
    letI : Field E := fieldOfFiniteDimensional K E
    (e : D) ∈ divisionIntegerSubring K D ↔ spectralNorm K E e ≤ 1 := by
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  rw [division_subring, division_algebra_absolute,
    regular_candidate_spectral K D E hcomm e]

/-- An integer of absolute value one has its inverse in the integer ring. -/
private theorem division_integer_subring
    (x : divisionIntegerSubring K D) (hx : abv K D (x : D) = 1) :
    (x : D)⁻¹ ∈ divisionIntegerSubring K D := by
  rw [division_subring, map_inv₀, hx, inv_one]

/-- Every integer outside the strict-valuation ideal is a unit of the ring of
integers. -/
theorem not_division_maximal
    (x : divisionIntegerSubring K D)
    (hx : x ∉ divisionMaximalIdeal K D) : IsUnit x := by
  have hxnot : ¬ abv K D (x : D) < 1 := by
    simpa only [division_maximal] using hx
  have hxval : abv K D (x : D) = 1 := le_antisymm x.2 (not_lt.mp hxnot)
  have hxzero : (x : D) ≠ 0 := by
    apply (abv K D).ne_zero_iff.mp
    rw [hxval]
    exact one_ne_zero
  let y : divisionIntegerSubring K D :=
    ⟨(x : D)⁻¹, division_integer_subring K D x hxval⟩
  refine ⟨⟨x, y, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hxzero
  · apply Subtype.ext
    exact inv_mul_cancel₀ hxzero

/-- A unit of the integer ring cannot lie in its strict-valuation ideal. -/
theorem division_maximal_unit
    (x : divisionIntegerSubring K D) (hx : IsUnit x) :
    x ∉ divisionMaximalIdeal K D := by
  obtain ⟨u, rfl⟩ := hx
  intro hu
  have huval : abv K D ((u : divisionIntegerSubring K D) : D) < 1 :=
    (division_maximal K D u).mp hu
  have huinv : abv K D (((u⁻¹ : (divisionIntegerSubring K D)ˣ) :
      divisionIntegerSubring K D) : D) ≤ 1 :=
    (((u⁻¹ : (divisionIntegerSubring K D)ˣ) :
      divisionIntegerSubring K D)).property
  have hmulD :
      ((u : divisionIntegerSubring K D) : D) *
          (((u⁻¹ : (divisionIntegerSubring K D)ˣ) :
            divisionIntegerSubring K D) : D) = 1 := by
    exact congrArg (fun z : divisionIntegerSubring K D ↦ (z : D)) (Units.mul_inv u)
  have hmul := congrArg (abv K D) hmulD
  rw [map_mul, map_one] at hmul
  have hlt :
      abv K D ((u : divisionIntegerSubring K D) : D) *
          abv K D (((u⁻¹ : (divisionIntegerSubring K D)ˣ) :
            divisionIntegerSubring K D) : D) < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left
      (abv K D |>.nonneg ((u : divisionIntegerSubring K D) : D)) huval huinv
  rw [hmul] at hlt
  exact (lt_irrefl 1 hlt)

/-- The units of the division-algebra ring of integers are exactly the
elements outside its maximal ideal. -/
theorem division_maximal_ideal
    (x : divisionIntegerSubring K D) :
    IsUnit x ↔ x ∉ divisionMaximalIdeal K D :=
  ⟨division_maximal_unit K D x,
    not_division_maximal K D x⟩

/-- The strict-valuation ideal is proper. -/
theorem division_maximal_top : divisionMaximalIdeal K D ≠ ⊤ := by
  intro h
  have hmem : (1 : divisionIntegerSubring K D) ∈ divisionMaximalIdeal K D := by
    rw [h]
    trivial
  have hone := (division_maximal K D 1).mp hmem
  simp at hone

/-- The strict-valuation ideal is maximal among two-sided ideals. -/
theorem division_maximal_coatom :
    IsCoatom (divisionMaximalIdeal K D) := by
  rw [SetLike.isCoatom_iff]
  refine ⟨division_maximal_top K D, ?_⟩
  intro J x hPJ hxP hxJ
  have hxunit : IsUnit x :=
    not_division_maximal K D x hxP
  obtain ⟨u, rfl⟩ := hxunit
  have hone : (1 : divisionIntegerSubring K D) ∈ J := by
    simpa using J.mul_mem_left
      (((u⁻¹ : (divisionIntegerSubring K D)ˣ) : divisionIntegerSubring K D))
      (u : divisionIntegerSubring K D) hxJ
  apply top_unique
  intro y hy
  simpa only [mul_one] using J.mul_mem_left y 1 hone

/-- The residue ring of the division-algebra ring of integers. -/
abbrev divisionResidueRing :=
  (divisionMaximalIdeal K D).ringCon.Quotient

private theorem division_residue_or
    (q : divisionResidueRing K D) : IsUnit q ∨ q = 0 := by
  obtain ⟨x, rfl⟩ := (divisionMaximalIdeal K D).ringCon.mk'_surjective q
  by_cases hx : x ∈ divisionMaximalIdeal K D
  · right
    exact (RingCon.eq (c := (divisionMaximalIdeal K D).ringCon)).mpr
      (((divisionMaximalIdeal K D).mem_iff x).mp hx)
  · left
    exact (not_division_maximal K D x hx).map
      (divisionMaximalIdeal K D).ringCon.mk'

/-- Milne's residue algebra `O_D / P` is a division ring. -/
@[implicit_reducible]
noncomputable def divisionResidue :
    DivisionRing (divisionResidueRing K D) := by
  letI : Nontrivial (divisionResidueRing K D) :=
    RingCon.nontrivial_quotient.mpr fun h ↦
      division_maximal_top K D
        (TwoSidedIdeal.ringCon_injective h)
  exact DivisionRing.ofIsUnitOrEqZero
    (division_residue_or K D)

end

end Towers.CField.LBrauer
