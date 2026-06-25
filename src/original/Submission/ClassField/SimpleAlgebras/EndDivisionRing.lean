import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Milne, Class Field Theory, Lemma IV.1.16 (Schur's lemma)

The endomorphism ring of a simple module is a division ring.  Milne works
with finite-dimensional modules over a finite-dimensional algebra over a
field; the ring-theoretic statement needs none of those finiteness hypotheses.
-/

namespace Submission.CField.SAlgebr

universe u v

variable (A : Type u) (S : Type v)
  [Ring A] [AddCommGroup S] [Module A S] [IsSimpleModule A S]

/-- **Lemma IV.1.16 (Schur's lemma), literal algebraic content.**  The
endomorphism ring of a simple module admits its canonical division-ring
structure. -/
theorem simple_end_division :
    Nonempty (DivisionRing (Module.End A S)) := by
  letI : DecidableEq (Module.End A S) := Classical.decEq _
  exact ⟨inferInstance⟩

/-- Equivalently, every nonzero endomorphism of a simple module is an
automorphism.  This is the formulation used in Milne's proof. -/
theorem simple_end_bijective
    {f : Module.End A S} (hf : f ≠ 0) :
    Function.Bijective f :=
  LinearMap.bijective_of_ne_zero hf

end Submission.CField.SAlgebr
