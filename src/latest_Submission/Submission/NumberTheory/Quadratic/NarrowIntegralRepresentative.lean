import Submission.NumberTheory.Quadratic.OrientedBasisExistence
import Submission.NumberTheory.Quadratic.FieldFormSetup
import Submission.NumberTheory.ClassGroup.NarrowClassGroup

/-!
# Integral representatives of narrow ideal classes

A fractional ideal can be written as `a⁻¹ J` with `J` integral.  Multiplication by the
totally positive square `a²` replaces it by the integral ideal `(a) J` without changing its
narrow class.  In a quadratic field, a nonzero such ideal also admits a positively oriented
ordered basis.
-/

namespace Submission.NumberTheory.Milne

open scoped NumberField nonZeroDivisors

noncomputable section

namespace NCGroup

variable {K : Type*} [Field K] [NumberField K]

/-- A chosen invertible fractional-ideal representative of a narrow ideal class. -/
def fractionalRepresentative (C : NCGroup K) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Classical.choose (QuotientGroup.mk_surjective C)

@[simp]
theorem mk_fraction (C : NCGroup K) :
    NCGroup.mk K (fractionalRepresentative C) = C :=
  Classical.choose_spec (QuotientGroup.mk_surjective C)

/-- A denominator clearing a chosen fractional-ideal representative. -/
def representativeDenominator (C : NCGroup K) : 𝓞 K :=
  Classical.choose
    (FractionalIdeal.exists_eq_spanSingleton_mul
      (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K))

/-- The integral numerator after clearing the chosen denominator. -/
def representativeNumerator (C : NCGroup K) : Ideal (𝓞 K) :=
  Classical.choose (Classical.choose_spec
    (FractionalIdeal.exists_eq_spanSingleton_mul
      (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K)))

theorem repres_denom_ne (C : NCGroup K) :
    representativeDenominator C ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec
    (FractionalIdeal.exists_eq_spanSingleton_mul
      (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K)))).1

theorem fractiona_eq (C : NCGroup K) :
    (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          ((algebraMap (𝓞 K) K) (representativeDenominator C))⁻¹ *
        (representativeNumerator C : FractionalIdeal (𝓞 K)⁰ K) :=
  (Classical.choose_spec (Classical.choose_spec
    (FractionalIdeal.exists_eq_spanSingleton_mul
      (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K)))).2

/-- The integral ideal obtained by multiplying `a⁻¹ J` by the square `a²`. -/
def integralRepresentative (C : NCGroup K) : Ideal (𝓞 K) :=
  Ideal.span {representativeDenominator C} * representativeNumerator C

theorem integr_repre_bot (C : NCGroup K) :
    integralRepresentative C ≠ ⊥ := by
  change ¬Ideal.span {representativeDenominator C} * representativeNumerator C = ⊥
  rw [Ideal.mul_eq_bot, not_or]
  constructor
  · simpa [Ideal.span_singleton_eq_bot] using repres_denom_ne C
  · intro hnum
    have hrep := fractiona_eq C
    rw [hnum, FractionalIdeal.coeIdeal_bot, mul_zero] at hrep
    exact (fractionalRepresentative C).ne_zero hrep

/-- The nonzero integral ideal underlying `integralRepresentative`. -/
def integr_repre_nonze (C : NCGroup K) : (Ideal (𝓞 K))⁰ :=
  ⟨integralRepresentative C,
    mem_nonZeroDivisors_iff_ne_zero.mpr (integr_repre_bot C)⟩

/-- The denominator square used to pass from the chosen fractional ideal to its integral
representative. -/
def denominatorSquareUnit (C : NCGroup K) : Kˣ :=
  Units.mk0 ((algebraMap (𝓞 K) K (representativeDenominator C)) ^ 2) (by
    exact pow_ne_zero 2
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr (repres_denom_ne C))))

theorem denomi_total_posit (C : NCGroup K) :
    ITPos K (denominatorSquareUnit C : K) := by
  intro phi
  change 0 < phi ((algebraMap (𝓞 K) K (representativeDenominator C)) ^ 2)
  rw [map_pow]
  exact sq_pos_of_ne_zero (by
    intro h
    have haK : algebraMap (𝓞 K) K (representativeDenominator C) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr (repres_denom_ne C))
    exact haK (phi.injective (by simpa using h)))

/-- Clearing denominators by the denominator square gives exactly the chosen integral ideal. -/
theorem repres_denom_squar
    (C : NCGroup K) :
    (FractionalIdeal.mk0 K (integr_repre_nonze C) :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (denominatorSquareUnit C : K) *
        (fractionalRepresentative C : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.coe_mk0, fractiona_eq]
  simp only [integr_repre_nonze, integralRepresentative,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
    denominatorSquareUnit, Units.val_mk0]
  rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
  congr 1
  field_simp

/-- Every narrow ideal class has a nonzero integral representative in the same narrow class. -/
@[simp]
theorem mk_integralRepresentative (C : NCGroup K) :
    NCGroup.mk K (FractionalIdeal.mk0 K (integr_repre_nonze C)) = C := by
  have hunit :
      FractionalIdeal.mk0 K (integr_repre_nonze C) =
        toPrincipalIdeal (𝓞 K) K (denominatorSquareUnit C) *
          fractionalRepresentative C := by
    apply Units.ext
    simpa using repres_denom_squar C
  rw [hunit, map_mul, mk_fraction]
  have hprincipal :
      NCGroup.mk K
          (toPrincipalIdeal (𝓞 K) K (denominatorSquareUnit C)) = 1 :=
    (NCGroup.mk_one_iff K _).2
      ⟨denominatorSquareUnit C, denomi_total_posit C, rfl⟩
  rw [hprincipal, one_mul]

end NCGroup

namespace QNRepres

open Submission.NumberTheory
open INForm

variable {d : ℤ}
variable (hd : Squarefree d) (hd1 : d ≠ 1)

/-- The denominator-square integral representative of a narrow class in `Q(sqrt d)`. -/
def ideal :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    NCGroup (QFModel d) →
      Ideal (𝓞 (QFModel d)) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  exact NCGroup.integralRepresentative

/-- The chosen integral ideal represents the original narrow class. -/
theorem ideal_represents :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    ∀ C : NCGroup (QFModel d),
      NCGroup.mk (QFModel d)
          (FractionalIdeal.mk0 (QFModel d)
            (NCGroup.integr_repre_nonze C)) = C := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  exact NCGroup.mk_integralRepresentative

/-- A positively oriented ordered basis of the chosen integral representative. -/
def basis :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    ∀ C : NCGroup (QFModel d),
      PositivelyOrientedBasis (quadraticIntegersBasis hd hd1)
        (NCGroup.integralRepresentative C) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  intro C
  exact positivelyOrientedBasis (quadraticIntegersBasis hd hd1)
    (NCGroup.integralRepresentative C)
    (NCGroup.integr_repre_bot C)

end QNRepres

end

end Submission.NumberTheory.Milne
