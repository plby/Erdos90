import Mathlib

namespace Submission.NumberTheory

namespace TNDisc

open Module

/-- Corollary 18: a family of `finrank K L` elements in a finite separable extension is a
basis exactly when its discriminant is nonzero. The basis condition is expressed as linear
independence because the cardinality is already fixed to `finrank K L`. -/
theorem linear_independent_discr
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (b : Fin (Module.finrank K L) → L) :
    LinearIndependent K b ↔ Algebra.discr K b ≠ 0 := by
  constructor
  · intro hb
    let B : Basis (Fin (Module.finrank K L)) K L :=
      Basis.mk hb <| (hb.span_eq_top_of_card_eq_finrank' (by simp)).ge
    simpa [B] using Algebra.discr_not_zero_of_basis K B
  · intro hdisc
    by_contra hb
    exact hdisc (Algebra.discr_zero_of_not_linearIndependent K hb)

end TNDisc

end Submission.NumberTheory
