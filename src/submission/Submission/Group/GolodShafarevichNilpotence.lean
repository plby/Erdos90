import Submission.Group.FinitePGS


open scoped BigOperators AlgebraMonoidAlgebra

noncomputable section

namespace Submission
namespace GShafar

/--
In a finite group algebra, the augmentation-one unit criterion implies that
the augmentation ideal is a nil ideal.

This is the Jacobson-radical bridge used in the finite `p`-group argument:
if every element with augmentation `1` is a unit, then every augmentation-zero
element lies in the Jacobson radical; in a finite ring the radical is nilpotent.
-/
theorem augmentation_nil_units
    (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]
    (hunit :
      ∀ a : MonoidAlgebra (ZMod p) G,
        (augmentationHom (ZMod p) G).toRingHom a = 1 → IsUnit a) :
    ∀ x : MonoidAlgebra (ZMod p) G,
      x ∈ augmentationIdeal (ZMod p) G → ∃ N : ℕ, x ^ N = 0 := by
  classical
  let A := MonoidAlgebra (ZMod p) G
  haveI : Finite A :=
    zmod_group_algebra p (Fact.out : Nat.Prime p) G
  haveI : IsArtinianRing A := isArtinian_of_finite
  have hI_le_jac :
      augmentationIdeal (ZMod p) G ≤ Ring.jacobson A := by
    rw [← Ideal.jacobson_bot]
    intro x hx
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hyxaug :
        (augmentationHom (ZMod p) G).toRingHom (y * x) = 0 :=
      RingHom.mem_ker.mp
        ((augmentationIdeal (ZMod p) G).mul_mem_left y hx)
    have haug_one :
        (augmentationHom (ZMod p) G).toRingHom (y * x + 1) = 1 := by
      rw [map_add, hyxaug, map_one, zero_add]
    rcases hunit (y * x + 1) haug_one with ⟨u, hu⟩
    refine ⟨↑u⁻¹, ?_⟩
    rw [Submodule.mem_bot]
    have hinv : (↑u⁻¹ : A) * (y * x + 1) = 1 := by
      rw [← hu]
      exact Units.inv_mul u
    have hsum : (↑u⁻¹ : A) * y * x + ↑u⁻¹ = 1 := by
      simpa [mul_add, mul_assoc] using hinv
    exact sub_eq_zero.mpr hsum
  rcases IsArtinianRing.isNilpotent_jacobson_bot (R := A) with ⟨N, hN⟩
  intro x hx
  refine ⟨N, ?_⟩
  have hJN : (Ring.jacobson A) ^ N = ⊥ := by
    simpa [← Ideal.jacobson_bot] using hN
  have hxpow_mem : x ^ N ∈ (Ring.jacobson A) ^ N :=
    Ideal.pow_mem_pow (hI_le_jac hx) N
  have hxbot : x ^ N ∈ (⊥ : Ideal A) := by
    simpa [hJN] using hxpow_mem
  simpa using hxbot

/--
Left multiplication by an augmentation-one element cannot kill a nonzero
scalar multiple of the norm element.
-/
theorem left_multiple_ne
    (R G : Type*) [CommSemiring R] [Group G] [Fintype G]
    (a : MonoidAlgebra R G) {r : R} (hr : r ≠ 0)
    (ha : (augmentationHom R G).toRingHom a = 1) :
    a * (MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G) ≠ 0 := by
  intro hzero
  have hfixed :
      a * (MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G) =
        MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G :=
    single_element_augmentation R G a r ha
  have hnorm_zero :
      MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G = 0 := by
    rw [← hfixed]
    exact hzero
  exact (single_element_ne R G hr) hnorm_zero

/--
Right multiplication by an augmentation-one element cannot kill a nonzero
scalar multiple of the norm element.
-/
theorem norm_multiple_ne
    (R G : Type*) [CommSemiring R] [Group G] [Fintype G]
    (a : MonoidAlgebra R G) {r : R} (hr : r ≠ 0)
    (ha : (augmentationHom R G).toRingHom a = 1) :
    (MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G) * a ≠ 0 := by
  intro hzero
  have hfixed :
      (MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G) * a =
        MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G :=
    single_algebra_element R G a r ha
  have hnorm_zero :
      MonoidAlgebra.single (1 : G) r * groupAlgebraElement R G = 0 := by
    rw [← hfixed]
    exact hzero
  exact (single_element_ne R G hr) hnorm_zero

end GShafar
end Submission
