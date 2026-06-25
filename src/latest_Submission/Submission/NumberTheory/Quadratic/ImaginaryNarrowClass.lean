import Submission.NumberTheory.Quadratic.FieldFormSetup
import Submission.NumberTheory.ClassGroup.NarrowClassGroup

/-!
# Narrow classes in an imaginary quadratic field

A negative quadratic radicand admits no embedding into the real numbers.  Consequently every
nonzero element is totally positive vacuously and the narrow class group is the ordinary class
group.  The statements use the canonical coordinate-field instances constructed from a
squarefree radicand.
-/

namespace Submission.NumberTheory.Milne

open Submission.NumberTheory
open scoped NumberField QuadraticAlgebra

noncomputable section

/-- A quadratic field with negative radicand has no real embedding. -/
theorem imaginary_no_embedding {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) (hdneg : d < 0) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    IsEmpty (QFModel d →+* ℝ) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  constructor
  intro phi
  let w : QFModel d := QuadraticAlgebra.omega
  have hw : w * w = (d : QFModel d) := by
    apply QuadraticAlgebra.ext <;>
      simp [w, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  have hphi : phi w * phi w = (d : ℝ) := by
    calc
      phi w * phi w = phi (w * w) := (map_mul phi w w).symm
      _ = phi (d : QFModel d) := congrArg phi hw
      _ = (d : ℝ) := by simp
  have hdnegR : (d : ℝ) < 0 := by exact_mod_cast hdneg
  nlinarith [sq_nonneg (phi w)]

/-- In the imaginary quadratic case the genuine narrow class group is the ordinary class
group of the ring of integers. -/
noncomputable def imaginaryQuadraticNarrow {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) (hdneg : d < 0) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
      quadraticNonsquareFact hd hd1
    letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
    letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
    NCGroup (QFModel d) ≃*
      ClassGroup (𝓞 (QFModel d)) := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) :=
    quadraticNonsquareFact hd hd1
  letI : Module.Finite ℚ (QFModel d) := quadraticModuleFinite hd hd1
  letI : NumberField (QFModel d) := quadraticFieldNumber hd hd1
  letI : IsEmpty (QFModel d →+* ℝ) :=
    imaginary_no_embedding hd hd1 hdneg
  exact narrowClassEquiv (QFModel d)

end

end Submission.NumberTheory.Milne
