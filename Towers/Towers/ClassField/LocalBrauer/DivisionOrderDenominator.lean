import Towers.ClassField.LocalBrauer.DivisionSubfieldDegree
import Towers.ClassField.LocalBrauer.DivisionAlgebraOrder

/-!
# Chapter IV, Section 4: denominator of the division-algebra order

If a central division algebra has dimension `n ^ 2`, Milne observes that its
normalized order takes values in `(1 / n) * ℤ`.  For an element `x`, apply the
regular-norm formula to the commutative subfield `K[x]`; its degree divides
`n` by the centralizer dimension calculation.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open scoped WithZero

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [Module.Finite K D]

set_option synthInstance.maxHeartbeats 200000 in
-- The generated-field structure and its two scalar towers are active together.
/-- If `n` is the degree of a central division algebra, every value of its
normalized order on `Dˣ` is an integral multiple of `1 / n`. -/
theorem division_div_sqrt (x : Additive Dˣ) :
    ∃ z : ℤ,
      divisionUnitOrder K D x =
        (z : ℚ) / (Nat.sqrt (Module.finrank K D) : ℚ) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  let E : Subalgebra K D := Algebra.adjoin K ({(x.toMul : D)} : Set D)
  have hset : ∀ a ∈ ({(x.toMul : D)} : Set D),
      ∀ b ∈ ({(x.toMul : D)} : Set D), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    rfl
  have hcomm : ∀ a b : E, a * b = b * a :=
    by
      letI : IsMulCommutative E := Algebra.isMulCommutative_adjoin K hset
      exact mul_comm'
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  letI : Module.Finite E D :=
    Module.Finite.of_restrictScalars_finite K E D
  let e : E :=
    ⟨(x.toMul : D), Algebra.subset_adjoin (Set.mem_singleton (x.toMul : D))⟩
  have he : (e : D) ≠ 0 := x.toMul.ne_zero
  have hnormE : Algebra.norm K e ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := K) (S := E)).mpr (by
      intro he0
      apply he
      exact congrArg Subtype.val he0)
  let nx : Kˣ := Units.mk0 (Algebra.norm K e) hnormE
  have hnormUnits :
      Units.map (Algebra.norm K) x.toMul =
        nx ^ Module.finrank E D := by
    apply Units.ext
    change Algebra.norm K (x.toMul : D) =
      (Algebra.norm K e) ^ Module.finrank E D
    simpa [e] using regular_coe_pow K D E hcomm e
  have hregular :
      regularUnitOrder K D x =
        (Module.finrank E D : ℤ) *
          localUnitOrder K (Additive.ofMul nx) := by
    rw [regular_unit_order, hnormUnits]
    change localUnitOrder K
      (Module.finrank E D • Additive.ofMul nx) = _
    rw [map_nsmul]
    simp
  obtain ⟨t, ht⟩ := commutative_subalgebra_sqrt K D E hcomm
  refine ⟨localUnitOrder K (Additive.ofMul nx) * (t : ℤ), ?_⟩
  rw [division_unit_order, hregular]
  have hfinrank : Module.finrank K D =
      Module.finrank K E * Module.finrank E D :=
    (Module.finrank_mul_finrank K E D).symm
  have hm : (Module.finrank K E : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos.ne' : Module.finrank K E ≠ 0)
  have hr : (Module.finrank E D : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos.ne' : Module.finrank E D ≠ 0)
  have ht0 : t ≠ 0 := by
    intro htzero
    have hsqrt : Nat.sqrt (Module.finrank K D) ≠ 0 :=
      (Nat.sqrt_pos.2 Module.finrank_pos).ne'
    apply hsqrt
    rw [ht, htzero, mul_zero]
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht0
  push_cast
  rw [ht, hfinrank, Nat.cast_mul, Nat.cast_mul]
  field_simp [hm, hr, htQ]

/-- The same denominator statement for a nonzero element of `D`, phrased
using the additive valuation on the whole division algebra. -/
theorem division_algebra_div (x : D) (hx : x ≠ 0) :
    ∃ z : ℤ,
      divisionAlgebraOrder K (D := D) x =
        ((z : ℚ) / (Nat.sqrt (Module.finrank K D) : ℚ) : WithTop ℚ) := by
  obtain ⟨z, hz⟩ := division_div_sqrt K D
    (Additive.ofMul (Units.mk0 x hx))
  refine ⟨z, ?_⟩
  rw [division_ne_zero K (D := D) x hx, hz]

end

end Towers.CField.LBrauer
