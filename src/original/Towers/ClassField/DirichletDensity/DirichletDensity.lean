import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Towers.NumberTheory.Density.PrimeIdealNatural

/-!
# Chapter VI, Section 4: Dirichlet density

This file records Milne's definitions at the start of Section 4.  His
notation `f(s) ~ g(s)` means that their difference stays bounded as the real
variable `s` decreases to `1` from the right.  Dirichlet density is then this
bounded-difference relation for the prime-ideal reciprocal-power sum.

The comparison with polar and natural density in Proposition 4.1, and the
analytic estimates used later in the section, require Tauberian and Euler
product results not presently packaged in Mathlib.  They are therefore not
asserted here.
-/

namespace Towers.CField.DDensit

open IsDedekindDomain NumberField Set
open scoped BigOperators

noncomputable section

/-- A real-valued function is bounded on some punctured right neighborhood
of `1`. -/
def BoundedNearRight (f : ℝ → ℝ) : Prop :=
  ∃ ε > 0, ∃ B : ℝ, ∀ s ∈ Ioo (1 : ℝ) (1 + ε), |f s| ≤ B

/-- Milne's relation `f(s) ~ g(s)` as `s` decreases to `1`: the difference
is bounded on a right neighborhood of `1`. -/
def BoundedDifferenceNear (f g : ℝ → ℝ) : Prop :=
  BoundedNearRight fun s ↦ f s - g s

/-- The reciprocal-power sum over a set of prime ideals. -/
def primeReciprocalSum
    (K : Type*) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' p : T, Real.rpow (p.1.asIdeal.absNorm : ℝ) (-s)

/-- A set of prime ideals has Dirichlet density `δ` when its reciprocal-power
sum differs by a bounded function from `δ * log (1 / (s - 1))` near `1` from
the right. -/
def PrimeDirichletDensity
    (K : Type*) [Field K] [NumberField K]
    (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  BoundedDifferenceNear
    (primeReciprocalSum K T)
    (fun s ↦ δ * Real.log (1 / (s - 1)))

end

end Towers.CField.DDensit
