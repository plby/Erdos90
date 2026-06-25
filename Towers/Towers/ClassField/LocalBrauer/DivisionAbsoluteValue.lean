import Towers.ClassField.LocalBrauer.DivisionAlgebraNorm
import Towers.ClassField.LocalBrauer.FieldNormExtension
import Towers.NumberTheory.Locals.CompleteDiscreteExtension

/-!
# Chapter IV, Section 4: the absolute value on a division algebra

This file identifies the determinant-based regular norm with the spectral
norm on every finite commutative subfield.  The one-generated subfield of a
quotient `x⁻¹y` then supplies the ultrametric inequality for arbitrary,
possibly noncommuting, elements of the division algebra.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open IntermediateField
open Towers.NumberTheory.Milne

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]

private theorem field_rpow_spectral
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] (x : E) :
    ‖Algebra.norm K x‖ ^ (1 / (Module.finrank K E : ℝ)) =
      spectralNorm K E x := by
  rw [← complete_absolute_value K E,
    complete_extension_rpow K E x]

variable (D : Type u) [DivisionRing D] [Algebra K D] [Module.Finite K D]

set_option synthInstance.maxHeartbeats 100000 in
-- The subalgebra field structure and both restricted-scalar module towers
-- are simultaneously active in this calculation.
/-- On every finite commutative subfield of `D`, the regular absolute-value
candidate is exactly the canonical spectral norm. -/
theorem regular_candidate_spectral
    (E : Subalgebra K D) (hcomm : ∀ x y : E, x * y = y * x) (e : E) :
    letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
    letI : Module.Finite K E :=
      Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
    letI : IsDomain E :=
      Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
    letI : Field E := fieldOfFiniteDimensional K E
    regularValueCandidate K D (e : D) = spectralNorm K E e := by
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  letI : Module.Finite E D :=
    Module.Finite.of_restrictScalars_finite K E D
  rw [regularValueCandidate,
    regular_coe_pow K D E hcomm e, norm_pow,
    ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg (Algebra.norm K e)),
    ← complete_absolute_value K E,
    complete_extension_rpow K E e]
  congr 1
  rw [← Module.finrank_mul_finrank K E D, Nat.cast_mul]
  have hKE : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  have hED : Module.finrank E D ≠ 0 := Module.finrank_pos.ne'
  field_simp [hKE, hED]

omit [IsUltrametricDist K] [CompleteSpace K] in
@[simp]
theorem regular_candidate_inv (x : D) :
    regularValueCandidate K D x⁻¹ =
      (regularValueCandidate K D x)⁻¹ := by
  change regularAbsoluteCandidate K D x⁻¹ =
    (regularAbsoluteCandidate K D x)⁻¹
  exact map_inv₀ (regularAbsoluteCandidate K D) x

set_option synthInstance.maxHeartbeats 100000 in
-- The generated subfield carries both its subtype algebra structure and the
-- field structure obtained from finite dimensionality.
/-- The ultrametric estimate for `1 + z` is already a commutative field
calculation, because both terms lie in the singly generated field `K[z]`. -/
theorem regular_candidate_max (z : D) :
    regularValueCandidate K D (1 + z) ≤
      max 1 (regularValueCandidate K D z) := by
  let E : Subalgebra K D := Algebra.adjoin K ({z} : Set D)
  have hset : ∀ x ∈ ({z} : Set D), ∀ y ∈ ({z} : Set D), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    rfl
  have hcomm : ∀ x y : E, x * y = y * x :=
    by
      letI : IsMulCommutative E := Algebra.isMulCommutative_adjoin K hset
      exact mul_comm'
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  let zE : E := ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩
  have hspec :=
    isNonarchimedean_spectralNorm (K := K) (L := E) (1 : E) zE
  rw [← regular_candidate_spectral K D E hcomm (1 + zE),
    ← regular_candidate_spectral K D E hcomm (1 : E),
    ← regular_candidate_spectral K D E hcomm zE] at hspec
  simpa [zE] using hspec

/-- The determinant-based candidate satisfies the ultrametric inequality on
the whole division algebra.  The proof divides by the larger summand and
uses the preceding commutative calculation for `1 + x⁻¹y`. -/
theorem regular_absolute_max (x y : D) :
    regularValueCandidate K D (x + y) ≤
      max (regularValueCandidate K D x)
        (regularValueCandidate K D y) := by
  have aux (a b : D)
      (hba : regularValueCandidate K D b ≤
        regularValueCandidate K D a) :
      regularValueCandidate K D (a + b) ≤
        regularValueCandidate K D a := by
    by_cases ha : a = 0
    · have hbval : regularValueCandidate K D b = 0 := by
        apply le_antisymm
        · simpa [ha] using hba
        · exact regular_candidate_nonneg K D b
      have hb : b = 0 :=
        (regular_absolute_candidate K D b).mp hbval
      simp [ha, hb]
    · let z : D := a⁻¹ * b
      have haval : 0 < regularValueCandidate K D a := by
        exact lt_of_le_of_ne
          (regular_candidate_nonneg K D a)
          (Ne.symm fun h => ha ((regular_absolute_candidate K D a).mp h))
      have hz : regularValueCandidate K D z ≤ 1 := by
        calc
          regularValueCandidate K D z =
                regularValueCandidate K D a⁻¹ *
                regularValueCandidate K D b := by
                  simpa only [z] using
                    regular_candidate_mul K D a⁻¹ b
          _ = (regularValueCandidate K D a)⁻¹ *
                regularValueCandidate K D b := by
                  rw [regular_candidate_inv]
          _ ≤ 1 := (inv_mul_le_one₀ haval).2 hba
      have hone : regularValueCandidate K D (1 + z) ≤ 1 :=
        (regular_candidate_max K D z).trans
          (max_le le_rfl hz)
      have hab : a + b = a * (1 + z) := by
        simp [z, mul_add, ha]
      calc
        regularValueCandidate K D (a + b) =
            regularValueCandidate K D (a * (1 + z)) := congrArg _ hab
        _ = regularValueCandidate K D a *
              regularValueCandidate K D (1 + z) :=
            regular_candidate_mul K D _ _
        _ ≤ regularValueCandidate K D a * 1 :=
            mul_le_mul_of_nonneg_left hone
              (regular_candidate_nonneg K D a)
        _ = regularValueCandidate K D a := mul_one _
  rcases le_total (regularValueCandidate K D y)
      (regularValueCandidate K D x) with h | h
  · exact (aux x y h).trans (le_max_left _ _)
  · simpa only [add_comm, max_comm] using
      (aux y x h).trans (le_max_left
        (regularValueCandidate K D y)
        (regularValueCandidate K D x))

/-- The unique absolute value on the finite-dimensional division algebra
obtained from the determinant of left multiplication. -/
def divisionAbsoluteValue : AbsoluteValue D ℝ where
  toFun := regularValueCandidate K D
  map_mul' := regular_candidate_mul K D
  nonneg' := regular_candidate_nonneg K D
  eq_zero' := regular_absolute_candidate K D
  add_le' x y :=
    (regular_absolute_max K D x y).trans
      (max_le_add_of_nonneg
        (regular_candidate_nonneg K D x)
        (regular_candidate_nonneg K D y))

@[simp]
theorem division_algebra_absolute (x : D) :
    divisionAbsoluteValue K D x =
      regularValueCandidate K D x :=
  rfl

/-- The division-algebra absolute value restricts to the original norm on
the base field. -/
@[simp]
theorem division_absolute_value (x : K) :
    divisionAbsoluteValue K D (algebraMap K D x) = ‖x‖ := by
  exact regular_candidate_algebra K D x

/-- Milne's nonarchimedean inequality for the extended absolute value. -/
theorem division_absolute_nonarchimedean :
    IsNonarchimedean (divisionAbsoluteValue K D) := by
  intro x y
  exact regular_absolute_max K D x y

set_option synthInstance.maxHeartbeats 100000 in
-- For each element, uniqueness is checked after installing the field
-- structure on its singly generated commutative subalgebra.
/-- Any real-valued absolute value on `D` extending the norm on `K` is the
determinant-based absolute value constructed above. -/
theorem division_absolute_unique
    (f : AbsoluteValue D ℝ)
    (hf : ∀ x : K, f (algebraMap K D x) = ‖x‖) :
    f = divisionAbsoluteValue K D := by
  ext x
  let E : Subalgebra K D := Algebra.adjoin K ({x} : Set D)
  have hset : ∀ a ∈ ({x} : Set D), ∀ b ∈ ({x} : Set D), a * b = b * a := by
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
  let xE : E := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  let fE : AbsoluteValue E ℝ :=
    f.comp (f := E.val.toRingHom) Subtype.val_injective
  have hfE : ∀ a : K, fE (algebraMap K E a) = ‖a‖ := by
    intro a
    change f (algebraMap K D a) = ‖a‖
    exact hf a
  have hfield : fE xE = spectralNorm K E xE :=
    spectralNorm_unique_field_norm_ext hfE xE
  have hcandidate :=
    regular_candidate_spectral K D E hcomm xE
  change regularValueCandidate K D x = spectralNorm K E xE at hcandidate
  change f x = regularValueCandidate K D x
  exact hfield.trans hcandidate.symm

/-- Existence and uniqueness of the nonarchimedean absolute value extending
the norm of the complete base field. -/
theorem unique_division_value :
    ∃! f : AbsoluteValue D ℝ,
      ∀ x : K, f (algebraMap K D x) = ‖x‖ := by
  refine ⟨divisionAbsoluteValue K D,
    division_absolute_value K D, ?_⟩
  intro f hf
  exact division_absolute_unique K D f hf

end

end Towers.CField.LBrauer
