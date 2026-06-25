import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.ClassField.BrauerGroups.CentralizerInfCentralizers

/-!
# Milne, Proposition IV.2.3: literal statement and dimension formula

The tracked file proves the centralizer equality without finite-dimensional
hypotheses.  This file records its numerical finite-dimensional consequence,
using the standing convention in Milne's chapter that `k`-algebras are
finite-dimensional.
-/

namespace Submission.CField.BGroups

open Algebra.TensorProduct

noncomputable section

universe u

variable (k A A' : Type u) [Field k]
variable [Ring A] [Ring A'] [Algebra k A] [Algebra k A']

/-- The dimension formula attached to Proposition IV.2.3: the dimension of
the tensor-product centralizer is the product of the two centralizer
dimensions. -/
theorem finrank_centralizer_tensor
    (B : Subalgebra k A) (B' : Subalgebra k A') :
    Module.finrank k
        (Subalgebra.centralizer k
          ((Algebra.TensorProduct.map B.val B'.val).range :
            Set (TensorProduct k A A'))) =
      Module.finrank k (Subalgebra.centralizer k (B : Set A)) *
        Module.finrank k (Subalgebra.centralizer k (B' : Set A')) := by
  let C := Subalgebra.centralizer k (B : Set A)
  let C' := Subalgebra.centralizer k (B' : Set A')
  let f : TensorProduct k C C' →ₐ[k] TensorProduct k A A' :=
    Algebra.TensorProduct.map C.val C'.val
  letI : Module.Free k C := Module.Free.of_divisionRing k C
  letI : Module.Free k C' := Module.Free.of_divisionRing k C'
  letI : Module.Flat k C := Module.Flat.of_free
  letI : Module.Flat k C' := Module.Flat.of_free
  have hf : Function.Injective f := by
    simpa [f] using
      (TensorProduct.map_injective_of_flat_flat'
        C.val.toLinearMap C'.val.toLinearMap
        Subtype.val_injective Subtype.val_injective)
  rw [centralizer_tensorProduct k A A' B B']
  change Module.finrank k f.range =
    Module.finrank k C * Module.finrank k C'
  calc
    Module.finrank k f.range = Module.finrank k (TensorProduct k C C') :=
      (AlgEquiv.ofInjective f hf).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank k C * Module.finrank k C' :=
      Module.finrank_tensorProduct

/-- The literal source package follows from the tracked centralizer theorem
and the dimension calculation above. -/
theorem literalFormulaStatement
    (B : Subalgebra k A) (B' : Subalgebra k A') :
    Subalgebra.centralizer k
      (Algebra.TensorProduct.map B.val B'.val).range =
        (Algebra.TensorProduct.map
          (Subalgebra.centralizer k (B : Set A)).val
          (Subalgebra.centralizer k (B' : Set A')).val).range ∧
    Module.finrank k
      (Subalgebra.centralizer k
        ((Algebra.TensorProduct.map B.val B'.val).range :
          Set (TensorProduct k A A'))) =
      Module.finrank k (Subalgebra.centralizer k (B : Set A)) *
        Module.finrank k (Subalgebra.centralizer k (B' : Set A'))
  :=
  ⟨centralizer_tensorProduct k A A' B B',
    finrank_centralizer_tensor k A A' B B'⟩

end

end Submission.CField.BGroups
