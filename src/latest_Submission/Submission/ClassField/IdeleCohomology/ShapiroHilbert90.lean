import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Chapter VII, Section 2: Shapiro's lemma and Hilbert 90

Proposition 2.3 identifies the cohomology of the product of completions above
a fixed prime with the cohomology of one decomposition group.  Its
cohomological step is exactly Shapiro's lemma, recorded below for an arbitrary
coinduced representation.  Corollary 2.6(a) then uses Hilbert 90 on each
local multiplicative group.

`CompletionInducedModule` supplies the arithmetic additive and multiplicative
completion-product identifications and combines the latter with this Shapiro
isomorphism.  The remaining Section 2 work is the corresponding local-unit
subrepresentation, its assembly into the idele restricted product, and the
direct-sum decomposition of idele cohomology.
-/

namespace Submission.CField.ICohomo

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- **Proposition VII.2.3, Shapiro step.** The cohomology of a coinduced
`G`-module is the cohomology of its coefficient module over the subgroup. -/
noncomputable def shapiro
    (H : Subgroup G) (A : Rep k H) (r : ℕ) :
    groupCohomology (Rep.coind H.subtype A) r ≅ groupCohomology A r :=
  groupCohomology.coindIso A r

/-- **Corollary VII.2.6(a), local input.** The first cohomology of the
multiplicative Galois module of a finite field extension is trivial. -/
theorem hilbert_90_trivial
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    ∀ x : groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L), x = 0 := by
  intro x
  exact Subsingleton.elim x 0

end

end Submission.CField.ICohomo
