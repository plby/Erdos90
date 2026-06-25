import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.NumberTheory.Padics.Complex

/-!
# The completed algebraic closure of a p-adic field

This records the algebraic-closedness assertion in Milne's Remark 7.41.
The general theorem says that the completion of an algebraically closed
nonarchimedean normed field of characteristic zero remains algebraically
closed.  Mathlib writes `PadicAlgCl p` for a chosen algebraic closure of
`Q_p` and `PadicComplex p` for its completion.
-/

namespace Submission.NumberTheory.Milne

/-- Milne, Remark 7.41: the completion of an algebraically closed
nonarchimedean normed field of characteristic zero is algebraically closed. -/
theorem completion_alg_closed
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CharZero K] [IsAlgClosed K] :
    IsAlgClosed (UniformSpace.Completion K) := by
  letI : NontriviallyNormedField (UniformSpace.Completion K) := {
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
      refine ⟨(x : UniformSpace.Completion K), ?_⟩
      simpa using hx }
  letI : CharZero (UniformSpace.Completion K) :=
    (RingHom.charZero_iff
      (algebraMap K (UniformSpace.Completion K)).injective).mp inferInstance
  letI : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.of_normedAlgebra K
  apply IsAlgClosed.of_denseRange (K := K)
  simpa only [show
      (algebraMap K (UniformSpace.Completion K) :
        K → UniformSpace.Completion K) = UniformSpace.Completion.coe' by
      funext x
      rfl] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange (UniformSpace.Completion.coe' :
        K → UniformSpace.Completion K))

variable (p : ℕ) [Fact p.Prime]

/-- Milne, Remark 7.41: the completion of the algebraic closure of `Q_p`
is algebraically closed. -/
theorem padic_cl_closed :
    IsAlgClosed (UniformSpace.Completion (PadicAlgCl p)) := by
  exact completion_alg_closed (PadicAlgCl p)

end Submission.NumberTheory.Milne
