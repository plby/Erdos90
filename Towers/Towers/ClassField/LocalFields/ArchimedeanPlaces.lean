import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Complex

/-!
# Class Field Theory, Chapter I, 1.6

Milne's archimedean complement identifies the two norm subgroups of
`R^x`: the trivial extension has all of `R^x` as its norm image, whereas the
norm image from `C^x` is the subgroup of positive real numbers.
-/

namespace Towers.CField.LFTheory

open Set

/-- Every finite-index subgroup of `Rˣ` contains all positive real units. -/
theorem positive_real_index (H : Subgroup ℝˣ) [H.FiniteIndex] :
    Units.posSubgroup ℝ ≤ H := by
  intro u hu
  have hu_pos : 0 < (u : ℝ) := (Units.mem_posSubgroup u).mp hu
  have hindex : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  let r : ℝ := Real.rpow (u : ℝ) ((H.index : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hu_pos _
  let v : ℝˣ := Units.mk0 r hr.ne'
  have hv : v ^ H.index = u := by
    apply Units.ext
    change r ^ H.index = (u : ℝ)
    exact Real.rpow_inv_natCast_pow hu_pos.le hindex
  rw [← hv]
  exact H.pow_index_mem v

/-- Milne 1.6: the only finite-index subgroups of `Rˣ` are `Rˣ` itself
and the subgroup of positive real numbers. -/
theorem real_or_top
    (H : Subgroup ℝˣ) [H.FiniteIndex] :
    H = Units.posSubgroup ℝ ∨ H = ⊤ := by
  have hpos : Units.posSubgroup ℝ ≤ H := positive_real_index H
  by_cases hnegOne : (-1 : ℝˣ) ∈ H
  · right
    apply eq_top_iff.mpr
    intro u _
    by_cases hu : 0 < (u : ℝ)
    · exact hpos ((Units.mem_posSubgroup u).mpr hu)
    · have huneg : (u : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hu) (Units.ne_zero u)
      have hpositive : (-1 : ℝˣ) * u ∈ Units.posSubgroup ℝ :=
        (Units.mem_posSubgroup _).mpr (by
          change 0 < (-1 : ℝ) * (u : ℝ)
          simpa using neg_pos.mpr huneg)
      have hproduct : (-1 : ℝˣ) * u ∈ H := hpos hpositive
      simpa using H.mul_mem hnegOne hproduct
  · left
    apply le_antisymm
    · intro u hu
      rw [Units.mem_posSubgroup]
      by_contra hpositive
      have huneg : (u : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpositive) (Units.ne_zero u)
      have hnegMul : (-1 : ℝˣ) * u ∈ Units.posSubgroup ℝ :=
        (Units.mem_posSubgroup _).mpr (by
          change 0 < (-1 : ℝ) * (u : ℝ)
          simpa using neg_pos.mpr huneg)
      have hnegMul' : (-1 : ℝˣ) * u ∈ H := hpos hnegMul
      have := H.mul_mem hnegMul' (H.inv_mem hu)
      exact hnegOne (by simpa using this)
    · exact hpos

/-- The norm image of the nonzero complex numbers is exactly the positive
real numbers. -/
theorem range_complex_units :
    Set.range (fun z : ℂˣ ↦ Algebra.norm ℝ (z : ℂ)) = Set.Ioi 0 := by
  ext x
  simp only [Set.mem_range, Set.mem_Ioi]
  constructor
  · rintro ⟨z, rfl⟩
    have hnorm : Algebra.norm ℝ (z : ℂ) = Complex.normSq (z : ℂ) :=
      Algebra.norm_complex_apply (z : ℂ)
    rw [hnorm, Complex.normSq_pos]
    exact Units.ne_zero z
  · intro hx
    have hsqrt : Real.sqrt x ≠ 0 := by positivity
    let z : ℂˣ := Units.mk0 (Real.sqrt x : ℂ) (by exact_mod_cast hsqrt)
    refine ⟨z, ?_⟩
    have hnorm : Algebra.norm ℝ (z : ℂ) = Complex.normSq (z : ℂ) :=
      Algebra.norm_complex_apply (z : ℂ)
    rw [hnorm]
    simpa [z, Complex.normSq_ofReal] using Real.mul_self_sqrt hx.le

/-- The norm image for the trivial extension `R/R` is all nonzero real
numbers. -/
theorem range_real_units :
    Set.range (fun x : ℝˣ ↦ Algebra.norm ℝ (x : ℝ)) = {x : ℝ | x ≠ 0} := by
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, rfl⟩
    simp [Algebra.norm_self]
  · intro hx
    exact ⟨Units.mk0 x hx, by simp [Algebra.norm_self]⟩

end Towers.CField.LFTheory
