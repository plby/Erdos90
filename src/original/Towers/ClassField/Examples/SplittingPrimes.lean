import Towers.NumberTheory.Ramification.FactorizationInExtensions
import Towers.NumberTheory.Density.PrimeIdealNatural

/-!
# Class Field Theory, Introduction: primes that split completely

This file defines Milne's set `Spl(L/K)` of finite primes of a number field
that split completely in a finite extension.  The definition records both the
number of primes above `p` and the conditions `e = f = 1`, matching equation
(4) and the discussion immediately preceding Theorem 0.1.
-/

namespace Towers.CField.Examples

open IsDedekindDomain NumberField
open scoped NumberField

noncomputable section

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- A finite prime `p` of `K` splits completely in `L` when it has `[L : K]`
distinct primes above it, each with ramification index and inertia degree one. -/
def SplitsCompletelyAt
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  (Ideal.primesOver p.asIdeal (NumberField.RingOfIntegers L)).ncard =
      Module.finrank K L ∧
    ∀ P ∈ Ideal.primesOver p.asIdeal (NumberField.RingOfIntegers L),
      Ideal.ramificationIdx p.asIdeal P = 1 ∧
        Ideal.inertiaDeg p.asIdeal P = 1

/-- Milne's `Spl(L/K)`, the set of finite primes of `K` splitting completely
in `L`. -/
def splittingPrimes :
    Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {p | SplitsCompletelyAt K L p}

omit [NumberField K] [NumberField L] in
@[simp]
theorem splitting_primes
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    p ∈ splittingPrimes K L ↔ SplitsCompletelyAt K L p :=
  Iff.rfl

end

end Towers.CField.Examples
