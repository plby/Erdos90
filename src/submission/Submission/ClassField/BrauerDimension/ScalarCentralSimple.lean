import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Submission.ClassField.BrauerGroups.ScalarExtensionCentral

/-!
# Chapter IV, Section 5, Proposition 5.6

Milne proves that separable scalar extension preserves finite-dimensional
semisimple algebras.  The central-simple factor case follows directly from
Proposition IV.2.15 and is the part currently supported by the local tensor
product API.
-/

namespace Submission.CField.BDim

open scoped TensorProduct

universe u v

variable (k : Type v) (K A : Type u) [Field k] [Field K] [Algebra k K]
  [Module.Finite k K]
  [Ring A] [Algebra k A]

/-- Proposition IV.5.6 for a central simple factor: after extending scalars,
the algebra is still simple and hence semisimple.  No separability hypothesis
is needed in this central case. -/
theorem extension_semisimple_simple
    [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A] :
    IsSemisimpleRing (A ⊗[k] K) := by
  letI : IsSimpleRing (A ⊗[k] K) :=
    BGroups.tensor_simple_ring k A K
  letI : Module.Finite k (A ⊗[k] K) :=
    Module.Finite.tensorProduct k A K
  letI : IsArtinianRing (A ⊗[k] K) :=
    IsArtinianRing.of_finite k (A ⊗[k] K)
  exact IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance

end Submission.CField.BDim
