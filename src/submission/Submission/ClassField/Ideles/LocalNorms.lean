import Submission.ClassField.LocalFields.ArchimedeanPlaces
import Submission.ClassField.LocalFields.NormSubgroups
import Submission.ClassField.UnramifiedCohom.FiniteFieldNorms

/-!
# Chapter V, Section 4, Proposition 4.12: local norm groups

For the archimedean extension `ℝ ⊆ ℂ`, the norm image is exactly the positive
real numbers.  The two nonarchimedean clauses of Proposition 4.12 are not yet
available in the imported development:

* Part (b) needs the openness of the norm subgroup for a finite extension of
  characteristic-zero nonarchimedean local fields.  Chapter I currently has
  norm transitivity, but not the local compactness, closed norm image, and
  valuation-unit intersection results used in Lemma I.1.3.  Consequently there
  is no theorem from which to extract a principal-unit subgroup
  `1 + 𝖭_K ^ m` contained in the norm image.
* Part (c) needs surjectivity of the norm on the unit groups of an unramified
  local extension.  Chapter III proves norm surjectivity for the finite residue
  fields and trace surjectivity on their additive groups, and identifies the
  successive principal-unit quotients.  What remains missing is compatibility
  of the local-field norm with those quotient maps and the completeness
  argument lifting the successive approximations to a unit of the extension.

Thus this file records the exact available archimedean clause and introduces no
axioms for the missing nonarchimedean statements.
-/

namespace Submission.CField.Ideles

open Set

/-- **Proposition V.4.12(a).** The values of the norm on nonzero complex
numbers are exactly the positive real numbers. -/
theorem complex_norm_range :
    Set.range (fun z : ℂˣ ↦ Algebra.norm ℝ (z : ℂ)) = Set.Ioi 0 :=
  LFTheory.range_complex_units

/-- **Proposition V.4.12(a), norm-subgroup form.** The norm subgroup of
`ℂ / ℝ` is the subgroup of positive real units. -/
theorem complex_normSubgroup :
    LFTheory.normSubgroup ℝ ℂ = Units.posSubgroup ℝ := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    rw [Units.mem_posSubgroup]
    have hz' : Algebra.norm ℝ (z : ℂ) = (x : ℝ) := by
      simpa [LFTheory.normOnUnits] using congrArg Units.val hz
    rw [← hz']
    exact (Set.ext_iff.mp complex_norm_range
      (Algebra.norm ℝ (z : ℂ))).mp ⟨z, rfl⟩
  · intro hx
    have hx' : (x : ℝ) ∈ Set.Ioi 0 := (Units.mem_posSubgroup x).mp hx
    rw [← complex_norm_range] at hx'
    rcases hx' with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Units.ext
    simpa [LFTheory.normOnUnits] using hz

end Submission.CField.Ideles
