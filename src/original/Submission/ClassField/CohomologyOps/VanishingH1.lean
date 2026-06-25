import Submission.ClassField.CohomologyOps.ShortComplexMap

/-!
# Milne, Class Field Theory, Example II.1.36

For a normal subgroup `H`, Hilbert--90 vanishing in degree one turns
Proposition 1.34 into the degree-two exact sequence used for towers of Galois
extensions.  This file proves that cohomological step with the actual
inflation and restriction maps.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

variable (A : Rep k G) (H : Subgroup G) [H.Normal]

omit [H.Normal] in
private theorem vanishing_below_1
    (hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1))
    (j : ℕ) (hj : 0 < j) (hj2 : j < 2) :
    IsZero (groupCohomology (Rep.res H.subtype A) j) := by
  have : j = 1 := by omega
  subst j
  exact hH1

/-- The degree-two complex

`H²(G/H, Aᴴ) → H²(G, A) → H²(H, A)`

from Example II.1.36. -/
noncomputable abbrev vanishingBelowComplex
    (hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1)) :
    ShortComplex (ModuleCat k) :=
  restrictionCochainsComplex A H 2 (by omega)
    (vanishing_below_1 A H hH1)

/-- **Example II.1.36, cohomological step.** If `H¹(H,A)=0`, inflation is
injective and the degree-two inflation--restriction sequence is exact. -/
theorem vanishing_below_mono
    (hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1)) :
    (vanishingBelowComplex A H hH1).Exact ∧
      Mono (vanishingBelowComplex A H hH1).f :=
  cochains_short_mono A H 2 (by omega)
    (vanishing_below_1 A H hH1)

/-- Proposition-valued form of the degree-two exact sequence in Example
II.1.36. -/
def InflationRestriction : Prop :=
  ∀ hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1),
    (vanishingBelowComplex A H hH1).Exact ∧
      Mono (vanishingBelowComplex A H hH1).f

theorem inflationRestriction :
    InflationRestriction A H :=
  vanishing_below_mono A H

end

end Submission.CField.COps
