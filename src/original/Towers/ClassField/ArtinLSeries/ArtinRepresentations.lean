import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Towers.ClassField.DirichletSeries.Characters

/-!
# Chapter VIII, Section 10: the algebraic input to Artin L-series

The Dirichlet functional equation is handled separately using Mathlib's
analytic API.  The representation-theoretic facts needed to make the
unramified local polynomial independent of a chosen Frobenius lift were
already proved in Chapter VI; they are given source-local names below.

Mathlib does not yet package arithmetic Artin Euler products or their
induction formula, so this file stops at the exact finite-dimensional linear
algebra used to define an unramified local polynomial.
-/

namespace Towers.CField.ALSeries

open Module Towers.CField.DSeries

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- The trace character of a complex representation is constant on conjugacy
classes. -/
theorem artinTrace_conj (rho : Representation ℂ G V) (g h : G) :
    rho.character (h * g * h⁻¹) = rho.character g :=
  character_conj rho g h

omit [FiniteDimensional ℂ V] in
/-- In any chosen basis, the trace character is the ordinary matrix trace. -/
theorem artin_trace_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (rho : Representation ℂ G V) (g : G) :
    rho.character g = Matrix.trace (LinearMap.toMatrix b b (rho g)) := by
  rw [trace_eq_character, LinearMap.trace_eq_matrix_trace ℂ b]

/-- In a chosen basis, Milne's local polynomial is the reverse
characteristic polynomial of the representing matrix. -/
theorem matrix_charpoly_rev {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V)
    (rho : Representation ℂ G V) (g : G) :
    artinPolynomial rho g = (LinearMap.toMatrix b b (rho g)).charpolyRev := by
  rw [artinPolynomial, ← LinearMap.charpoly_toMatrix (rho g) b,
    Matrix.reverse_charpoly]

/-- Equivalently, the local polynomial is `det(1 - T rho(g))`. -/
theorem det_x_smul {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V)
    (rho : Representation ℂ G V) (g : G) :
    artinPolynomial rho g =
      Matrix.det (1 - (Polynomial.X : Polynomial ℂ) •
        (LinearMap.toMatrix b b (rho g)).map Polynomial.C) := by
  rw [matrix_charpoly_rev b rho g, Matrix.charpolyRev]

/-- The polynomial defining an unramified Artin Euler factor depends only on
the Frobenius conjugacy class. -/
theorem artinPolynomial_conj (rho : Representation ℂ G V) (g h : G) :
    artinPolynomial rho (h * g * h⁻¹) = artinPolynomial rho g :=
  Towers.CField.DSeries.artinPolynomial_conj rho g h

end

end Towers.CField.ALSeries
