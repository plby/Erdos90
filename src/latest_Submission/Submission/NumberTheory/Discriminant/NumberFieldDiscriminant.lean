import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.40(a) and Remark 2.42

The sign of a number-field discriminant is determined by the number of complex places.
We also record the isomorphism invariance and the lower bound used in Remark 2.42.
-/

namespace Submission.NumberTheory.Milne

/-- Proposition 2.40(a): the sign of the discriminant is `(-1)^s`, where `s` is the
number of complex places. -/
theorem number_discr_sign
    (K : Type*) [Field K] [NumberField K] :
    (NumberField.discr K).sign =
      (-1) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
  exact NumberField.sign_discr (K := K)

/-- Isomorphic number fields have the same degree and discriminant, as stated in Remark 2.42. -/
theorem number_same_discr
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (f : K ≃+* L) :
    Module.finrank ℚ K = Module.finrank ℚ L ∧
      NumberField.discr K = NumberField.discr L := by
  let fQ : K ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := f) fun _ => by simp
  exact ⟨fQ.toLinearEquiv.finrank_eq, NumberField.discr_eq_discr_of_ringEquiv K f⟩

/-- A number field of degree greater than one cannot have discriminant `0`, `±1`, or `±2`.
This is the Hermite-Minkowski consequence invoked in Remark 2.42. -/
theorem nontrivial_discr_two
    (K : Type*) [Field K] [NumberField K]
    (h : 1 < Module.finrank ℚ K) :
    2 < |NumberField.discr K| := by
  exact NumberField.abs_discr_gt_two (K := K) h

end Submission.NumberTheory.Milne
