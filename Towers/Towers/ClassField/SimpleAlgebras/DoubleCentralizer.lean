import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Chapter IV, Theorem 1.14: the double centralizer theorem

Mathlib's Jacobson density theorem proves that the canonical action map from a semisimple
ring to the endomorphisms commuting with all module endomorphisms is surjective when the
module is finite over its endomorphism ring.  Finite-dimensionality over the ground field
supplies that finiteness hypothesis.  A faithful action makes the map injective as well.
-/

namespace Towers.CField.SAlgebr

variable (k A V : Type*) [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
variable [IsSemisimpleModule A V] [Module.Finite k V]

include k

/-- Theorem IV.1.14, surjective form: every endomorphism of `V` commuting with all
`A`-linear endomorphisms is multiplication by an element of `A`. -/
theorem doubleCentralizer_surjective :
    Function.Surjective
      (Module.toModuleEnd (Module.End A V) (S := A) V) := by
  letI : Module.Finite (Module.End A V) V :=
    Module.Finite.of_restrictScalars_finite k (Module.End A V) V
  exact Module.Finite.toModuleEnd_moduleEnd_surjective

/-- For a faithful semisimple module, the action map onto the double centralizer is
bijective. -/
theorem doubleCentralizer_bijective [FaithfulSMul A V] :
    Function.Bijective
      (Module.toModuleEnd (Module.End A V) (S := A) V) := by
  refine ⟨?_, doubleCentralizer_surjective k A V⟩
  intro a b hab
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
  intro v
  exact DFunLike.congr_fun hab v

/-- The ring-theoretic form of the double centralizer theorem. -/
noncomputable def doubleCentralizerEquiv [FaithfulSMul A V] :
    A ≃+* Module.End (Module.End A V) V :=
  RingEquiv.ofBijective
    (Module.toModuleEnd (Module.End A V) (S := A) V)
    (doubleCentralizer_bijective k A V)

end Towers.CField.SAlgebr
