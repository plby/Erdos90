import Mathlib.FieldTheory.Finite.Basic

/-!
# Class Field Theory, Chapter I, paragraph 1.8: residue-field Frobenius

The maximal unramified extension of a local field and its infinite Galois
group are not currently available in Mathlib.  This file proves the finite
residue-field statement underlying Milne's description
`Gal(K^un/K) equiv Zhat`: on every finite residue extension, the cardinality
power map is the unique Frobenius, its order is the residue degree, and every
automorphism is a unique power of it modulo that degree.
-/

namespace Submission.CField.NCorr

open Module

noncomputable section

variable (k l : Type*) [Field k] [Field l] [Fintype k] [Finite l]
  [Algebra k l] [Algebra.IsAlgebraic k l]

/-- The finite-level arithmetic Frobenius occurring in paragraph 1.8. -/
abbrev residueFrobenius : l ≃ₐ[k] l :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k l

omit [Finite l] in
/-- Arithmetic Frobenius acts by raising to the cardinality of the base
residue field. -/
@[simp]
theorem residueFrobenius_apply (x : l) :
    residueFrobenius k l x = x ^ Fintype.card k :=
  rfl

omit [Finite l] in
/-- The cardinality-power action uniquely characterizes arithmetic
Frobenius on a finite residue extension. -/
theorem residueFrobenius_unique (sigma : l ≃ₐ[k] l)
    (hsigma : ∀ x : l, sigma x = x ^ Fintype.card k) :
    sigma = residueFrobenius k l := by
  ext x
  rw [hsigma]
  rfl

/-- The order of finite-level Frobenius is the residue degree. -/
theorem order_residue_frobenius :
    orderOf (residueFrobenius k l) = finrank k l :=
  FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k l

/-- Every automorphism of a finite residue extension is a unique power of
Frobenius with exponent in `Fin [l : k]`.  This is the finite quotient of the
procyclic description in paragraph 1.8. -/
theorem unique_residue_frobenius (sigma : l ≃ₐ[k] l) :
    ∃! n : Fin (finrank k l), residueFrobenius k l ^ n.1 = sigma := by
  have h := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l
  obtain ⟨n, hn⟩ := h.surjective sigma
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact h.injective (hm.trans hn.symm)

omit [Fintype k] [Algebra.IsAlgebraic k l] in
/-- In particular, every finite residue Galois group is cyclic. -/
theorem residue_galois_cyclic : IsCyclic (l ≃ₐ[k] l) :=
  inferInstance

end

end Submission.CField.NCorr
