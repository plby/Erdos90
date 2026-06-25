import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Chapter IV, Section 5.2: endomorphisms of a finite direct power

Milne first identifies linear maps between finite direct sums with matrices
of linear maps. The special case he labels (42) is already the equivalence
`endVecAlgEquivMatrixEnd` in Mathlib.
-/

namespace Submission.CField.BDim

universe u v w

variable (k : Type u) [CommSemiring k]
  (A : Type v) [Semiring A] [Algebra k A]
  (M : Type w) [AddCommMonoid M] [Module k M] [Module A M]
  [IsScalarTower k A M]

/-- Milne's equation (42): endomorphisms of `m` copies of `M` are
`m`-by-`m` matrices with entries in `End_A(M)`. -/
def endAlgMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.End A (ι → M) ≃ₐ[k] Matrix ι ι (Module.End A M) :=
  endVecAlgEquivMatrixEnd ι k A M

end Submission.CField.BDim
