import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Towers.ClassField.Characters.DirichletCharacters

/-!
# Chapter VI, Section 2: Euler products

Lemma 2.6 is used in the direction from absolute convergence of a series to
convergence of the corresponding product.  Mathlib packages this direction
for complete normed commutative rings, together with nonvanishing of the
limit when no factor vanishes.  The converse equivalence in the elementary
real-positive formulation of the text is not a single packaged theorem.

Proposition 2.7 is available for ordinary Dirichlet characters over
`ℚ`.  The book states it for ray-class characters of arbitrary number fields;
that more general character type and Euler product are not currently present
as a unified Mathlib API.
-/

namespace Towers.CField.EProduc

open Filter Nat Topology
open scoped LSeries.notation

/-- Lemma 2.6, forward direction: an absolutely summable sequence gives a
convergent infinite product of `1 + b i`. -/
theorem multipliable_one_add {I R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {b : I → R} (hb : Summable fun i ↦ ‖b i‖) :
    Multipliable fun i ↦ 1 + b i :=
  multipliable_one_add_of_summable hb

/-- Lemma 2.6 also gives the book's convention that the limiting product is
nonzero, provided none of its factors is zero. -/
theorem tprod_ne_zero {I R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [NormMulClass R]
    {b : I → R} (hfactor : ∀ i, 1 + b i ≠ 0)
    (hb : Summable fun i ↦ ‖b i‖) :
    ∏' i, (1 + b i) ≠ 0 :=
  tprod_one_add_ne_zero_of_summable hfactor hb

/-- Proposition 2.7 for rational Dirichlet characters, stated directly for
the analytically continued `LFunction`. -/
theorem dirichlet_eulerProduct {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Primes ↦ (1 - chi p * (p : ℂ) ^ (-s))⁻¹)
      (DirichletCharacter.LFunction chi s) := by
  rw [chi.LFunction_eq_LSeries hs]
  exact chi.LSeries_eulerProduct_hasProd hs

end Towers.CField.EProduc
