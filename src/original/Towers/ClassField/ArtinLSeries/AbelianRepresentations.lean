import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Chapter VIII, Section 10: representations of abelian groups

The source diagonalizes a finite-dimensional complex representation of an
abelian finite group into characters.  Mathlib supplies the key irreducible
statement below.  Maschke semisimplicity is also available, but a packaged
finite direct-sum decomposition into irreducibles, and the Artin/Brauer
induction theorems used later in the source, are not currently available.
-/

namespace Towers.CField.ALSeries

noncomputable section

variable {G V : Type*} [Group G] [IsMulCommutative G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Every irreducible finite-dimensional complex representation of an
abelian group is one-dimensional. -/
theorem irreducible_abelian_representation
    (rho : Representation ℂ G V) [rho.IsIrreducible] :
    Module.finrank ℂ V = 1 :=
  Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative rho

end

end Towers.CField.ALSeries
