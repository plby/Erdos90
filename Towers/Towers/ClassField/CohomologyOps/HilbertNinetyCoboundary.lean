import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Chapter II, Proposition 1.22: Hilbert 90

Noether's form of Hilbert 90 says that the first cohomology of the
multiplicative Galois module is trivial.  Mathlib proves this by Milne's
argument, using Dedekind's linear independence of field automorphisms to
choose a nonzero twisted trace.
-/

namespace Towers.CField.COps

open groupCohomology

/-- **Proposition II.1.22 (Hilbert 90).** For a finite Galois extension
`L/K`, `H¹(Gal(L/K), Lˣ)` is trivial. -/
theorem ninetyCoboundary90
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∀ x : H1 (Rep.ofAlgebraAutOnUnits K L), x = 0 := by
  intro x
  exact Subsingleton.elim x 0

/-- The cocycle formulation used in Milne's proof: every multiplicative
crossed homomorphism `Gal(L/K) → Lˣ` is principal. -/
theorem isMulCoboundary
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (f : Gal(L/K) → Lˣ) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f :=
  isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf

end Towers.CField.COps
