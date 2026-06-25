import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Milne, Chapter 4, Exercise 5

Every ideal of the ring of integers of a number field becomes principal after passing to the
ring of integers of a suitable finite extension.  Following Milne's hint, we choose one ideal in
each ideal class, adjoin a class-number-th root of a generator of its class-number-th power, and
use torsion-freeness of the monoid of ideals in a Dedekind domain.
-/

namespace Submission.NumberTheory.Milne

open scoped nonZeroDivisors NumberField

noncomputable section

universe u

private theorem generator_pow_number
    (K : Type u) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      Ideal.span {a} = I ^ NumberField.classNumber K := by
  let I0 : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  have hclass : (ClassGroup.mk0 I0) ^ NumberField.classNumber K = 1 :=
    pow_card_eq_one
  have hpow0 : I ^ NumberField.classNumber K ≠
      (0 : Ideal (NumberField.RingOfIntegers K)) :=
    pow_ne_zero _ hI
  have hprincipal : Submodule.IsPrincipal (I ^ NumberField.classNumber K) := by
    apply (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hpow0)).mp
    change ClassGroup.mk0 (I0 ^ NumberField.classNumber K) = 1
    simpa only [map_pow] using hclass
  letI : Submodule.IsPrincipal (I ^ NumberField.classNumber K) := hprincipal
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal
    (I ^ NumberField.classNumber K)
  refine ⟨a, ?_, ha.symm⟩
  intro ha0
  subst a
  rw [Submodule.span_zero_singleton] at ha
  exact hpow0 ha

private theorem principal_same_after
    {A B : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.IsTorsionFree A B]
    (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hclass : ClassGroup.mk0
        ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ =
      ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩)
    (hJprincipal : (J.map (algebraMap A B)).IsPrincipal) :
    (I.map (algebraMap A B)).IsPrincipal := by
  let I0 : (Ideal A)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let J0 : (Ideal A)⁰ := ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    ClassGroup.mk0_eq_mk0_iff.mp (show ClassGroup.mk0 I0 = ClassGroup.mk0 J0 from hclass)
  have hmapI : I.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  have hmapJ : J.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ
  let mapI0 : (Ideal B)⁰ :=
    ⟨I.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr hmapI⟩
  let mapJ0 : (Ideal B)⁰ :=
    ⟨J.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr hmapJ⟩
  have hmappedClass : ClassGroup.mk0 mapI0 = ClassGroup.mk0 mapJ0 := by
    apply ClassGroup.mk0_eq_mk0_iff.mpr
    refine ⟨algebraMap A B x, algebraMap A B y, ?_, ?_, ?_⟩
    · exact (map_eq_zero_iff (algebraMap A B)
        (FaithfulSMul.algebraMap_injective A B)).not.mpr hx
    · exact (map_eq_zero_iff (algebraMap A B)
        (FaithfulSMul.algebraMap_injective A B)).not.mpr hy
    · simpa [I0, J0, mapI0, mapJ0, Ideal.map_mul, Ideal.map_span,
        Set.image_singleton] using congrArg (Ideal.map (algebraMap A B)) hxy
  apply (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hmapI)).mp
  calc
    ClassGroup.mk0 mapI0 = ClassGroup.mk0 mapJ0 := hmappedClass
    _ = 1 := (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hmapJ)).mpr hJprincipal

/-- Milne, Exercise 4-5: all ideals of `𝒪_K` become principal in `𝒪_L` for some finite
extension `L/K`. -/
theorem principalizationprincipalization
    (K : Type u) [Field K] [NumberField K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : NumberField L),
      ∀ I : Ideal (NumberField.RingOfIntegers K),
        (I.map (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L))).IsPrincipal := by
  let A := NumberField.RingOfIntegers K
  let rep : ClassGroup A → (Ideal A)⁰ := fun C =>
    Classical.choose (ClassGroup.mk0_surjective C)
  have hrep (C : ClassGroup A) : ClassGroup.mk0 (rep C) = C :=
    Classical.choose_spec (ClassGroup.mk0_surjective C)
  let generator : ClassGroup A → A := fun C =>
    Classical.choose (generator_pow_number K (rep C)
      (mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property))
  have hgenerator_ne (C : ClassGroup A) : generator C ≠ 0 :=
    (Classical.choose_spec (generator_pow_number K (rep C)
      (mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property))).1
  have hgenerator (C : ClassGroup A) :
      Ideal.span {generator C} =
        (rep C : Ideal A) ^ NumberField.classNumber K :=
    (Classical.choose_spec (generator_pow_number K (rep C)
      (mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property))).2
  let root : ClassGroup A → AlgebraicClosure K := fun C =>
    Classical.choose (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K)
        (algebraMap A K (generator C))) (NumberField.classNumber_pos K))
  have hroot (C : ClassGroup A) :
      root C ^ NumberField.classNumber K =
        algebraMap K (AlgebraicClosure K) (algebraMap A K (generator C)) :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K)
        (algebraMap A K (generator C))) (NumberField.classNumber_pos K))
  let L : Type u := IntermediateField.adjoin K (Set.range root)
  letI : Finite (Set.range root) := Set.finite_range root
  letI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  letI : NumberField L := NumberField.of_module_finite K L
  let rootL : ClassGroup A → L := fun C =>
    ⟨root C, IntermediateField.subset_adjoin K (Set.range root) (Set.mem_range_self C)⟩
  have hrootL (C : ClassGroup A) :
      rootL C ^ NumberField.classNumber K =
        algebraMap K L (algebraMap A K (generator C)) := by
    apply Subtype.ext
    exact hroot C
  have hrootL_integral (C : ClassGroup A) : IsIntegral ℤ (rootL C) := by
    apply IsIntegral.of_pow (NumberField.classNumber_pos K)
    rw [hrootL C]
    exact (NumberField.RingOfIntegers.isIntegral_coe (generator C)).map
      (Algebra.ofId K L)
  let beta : ClassGroup A → NumberField.RingOfIntegers L := fun C =>
    ⟨rootL C, hrootL_integral C⟩
  have hbeta_pow (C : ClassGroup A) :
      beta C ^ NumberField.classNumber K =
        algebraMap A (NumberField.RingOfIntegers L) (generator C) := by
    apply NumberField.RingOfIntegers.ext
    exact hrootL C
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  intro I
  by_cases hI : I = ⊥
  · subst I
    have hbot : (⊥ : Ideal (NumberField.RingOfIntegers L)).IsPrincipal :=
      bot_isPrincipal
    simpa using hbot
  let I0 : (Ideal A)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let C : ClassGroup A := ClassGroup.mk0 I0
  have hrep_ne : (rep C : Ideal A) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp (rep C).property
  have hrep_map_ne : (rep C : Ideal A).map
      (algebraMap A (NumberField.RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hrep_ne
  have hrep_map_pow :
      ((rep C : Ideal A).map (algebraMap A (NumberField.RingOfIntegers L))) ^
          NumberField.classNumber K =
        Ideal.span {beta C} ^ NumberField.classNumber K := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, hbeta_pow C, ← hgenerator C,
      Ideal.map_span, Set.image_singleton]
  have hrep_map :
      (rep C : Ideal A).map (algebraMap A (NumberField.RingOfIntegers L)) =
        Ideal.span {beta C} :=
    pow_left_injective (NumberField.classNumber_ne_zero K) hrep_map_pow
  have hrep_principal :
      ((rep C : Ideal A).map
        (algebraMap A (NumberField.RingOfIntegers L))).IsPrincipal :=
    ⟨⟨beta C, hrep_map⟩⟩
  apply principal_same_after I (rep C) hI hrep_ne
  · simpa [I0, C] using (hrep C).symm
  · exact hrep_principal

end

end Submission.NumberTheory.Milne
