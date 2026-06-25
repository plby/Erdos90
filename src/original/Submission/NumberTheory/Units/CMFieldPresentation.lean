import Mathlib.NumberTheory.NumberField.CMField

/-!
# Milne, Algebraic Number Theory, CM fields as square-root extensions

Every CM field is generated over its maximal real subfield by the square root of an element whose
conjugates are negative.  We express negativity through the complex embeddings of the CM field:
the square has real part strictly less than zero under every embedding.
-/

namespace Submission.NumberTheory.Milne

open NumberField ComplexEmbedding
open scoped ComplexConjugate

noncomputable section

variable (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Milne's square-root description of a CM field: there is a generator `η` over `K⁺` whose
square belongs to `K⁺` and is negative under every complex embedding of `K`. -/
theorem cm_totally_negative :
    ∃ (η : K) (a : K⁺),
      (a : K) = η ^ 2 ∧
      (∀ φ : K →+* ℂ, (φ (a : K)).re < 0) ∧
      IntermediateField.adjoin K⁺ {η} = ⊤ := by
  have hconj : NumberField.IsCMField.complexConj K ≠ (1 : K ≃ₐ[K⁺] K) :=
    NumberField.IsCMField.complexConj_ne_one K
  obtain ⟨x, hx⟩ : ∃ x : K, NumberField.IsCMField.complexConj K x ≠ x := by
    by_contra h
    push Not at h
    apply hconj
    ext x
    simpa using h x
  let η : K := x - NumberField.IsCMField.complexConj K x
  have hη0 : η ≠ 0 := sub_ne_zero.mpr hx.symm
  have hconjη : NumberField.IsCMField.complexConj K η = -η := by
    simp [η, NumberField.IsCMField.complexConj_apply_apply]
  have hconjsq : NumberField.IsCMField.complexConj K (η ^ 2) = η ^ 2 := by
    rw [map_pow, hconjη, neg_sq]
  let a : K⁺ := ⟨η ^ 2,
    (NumberField.IsCMField.complexConj_eq_self_iff K (η ^ 2)).mp hconjsq⟩
  refine ⟨η, a, rfl, ?_, ?_⟩
  · intro φ
    have hmapη : φ η ≠ 0 := (map_ne_zero φ).mpr hη0
    have him : (φ x).im ≠ 0 := by
      intro him
      apply hmapη
      rw [show φ η = φ x - conj (φ x) by
        simp [η, NumberField.IsCMField.complexEmbedding_complexConj]]
      rw [Complex.sub_conj, him]
      simp
    have hφη : φ η = ((2 * (φ x).im : ℝ) : ℂ) * Complex.I := by
      rw [show φ η = φ x - conj (φ x) by
        simp [η, NumberField.IsCMField.complexEmbedding_complexConj]]
      exact Complex.sub_conj (φ x)
    calc
      (φ (η ^ 2)).re = ((((2 * (φ x).im : ℝ) : ℂ) * Complex.I) ^ 2).re := by
        rw [map_pow, hφη]
      _ = -(2 * (φ x).im) ^ 2 := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
      _ < 0 := neg_lt_zero.mpr (sq_pos_of_ne_zero (mul_ne_zero (by norm_num) him))
  · have hηnotmem : η ∉ (⊥ : IntermediateField K⁺ K) := by
      intro hη
      have hηplus : η ∈ K⁺ := by
        rw [IntermediateField.mem_bot] at hη
        obtain ⟨y, hy⟩ := hη
        rw [← hy]
        exact y.property
      have hfixed : NumberField.IsCMField.complexConj K η = η :=
        (NumberField.IsCMField.complexConj_eq_self_iff K η).mpr hηplus
      rw [hconjη] at hfixed
      exact hη0 (neg_eq_self.mp hfixed)
    letI : IsSimpleOrder (IntermediateField K⁺ K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime K⁺ K (by
        rw [Algebra.IsQuadraticExtension.finrank_eq_two]
        exact Nat.prime_two)
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin K⁺ {η}) with h | h
    · exact False.elim (hηnotmem (h ▸ IntermediateField.subset_adjoin K⁺ {η} (by simp)))
    · exact h

end

end Submission.NumberTheory.Milne
