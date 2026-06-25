import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Milne, Class Field Theory, Example IV.1.10

A division algebra is simple, and its finitely generated modules have finite
bases. These facts do not require commutativity of the division algebra.
-/

namespace Towers.CField.SAlgebr

universe u v

variable (D : Type u) [DivisionRing D]

/-- **Example IV.1.10.** A division algebra has no nonzero proper two-sided
ideals. -/
theorem division_algebra_simple : IsSimpleRing D :=
  inferInstance

variable (V : Type v) [AddCommGroup V] [Module D V]

/-- Every module over a division algebra is free. -/
theorem division_module_free : Module.Free D V :=
  inferInstance

/-- A finitely generated module over a division algebra has a basis indexed by
its finite dimension. -/
noncomputable def divisionModuleBasis [Module.Finite D V] :
    Module.Basis (Fin (Module.finrank D V)) D V :=
  Module.finBasis D V

end Towers.CField.SAlgebr
