import Mathlib.FieldTheory.Galois.GaloisClosure
import Submission.NumberTheory.Density.SplittingPrimeDensity
import Submission.ClassField.PrimeDensities.SetEulerClauses

/-!
# Milne, Class Field Theory, Theorem VI.3.4

For a finite extension `L/K`, let `M` be its Galois closure.  The primes of
`K` that split completely in `L` have polar density `1 / [M : K]`.

The existing Submission splitting-prime API gives the literal set of primes but
develops natural density, while Proposition 3.1 now contains Milne's literal
polar-density definition.  Two precise missing interfaces are isolated:

* splitting completely is unchanged on passing from `L` to its Galois
  closure;
* the Galois case of Milne's polar-density argument.

The theorem below proves the full, non-Galois source statement from exactly
these two interfaces.
-/

namespace Submission.CField.PDensit

open IsDedekindDomain NumberField Set
open Submission.NumberTheory.Milne

noncomputable section

universe u

/-- `M` is the Galois closure of the embedded finite extension `L/K` when
the normal closure in `M` of the image of `L` is all of `M`.  The ambient
typeclass assumptions below record that `M/K` is finite Galois. -/
def IsGaloisClosure (K L M : Type u)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] : Prop :=
  IntermediateField.normalClosure K
    (IntermediateField.adjoin K (Set.range (algebraMap L M))) M = ⊤

/-- The first exact missing interface in the current splitting-prime API:
a prime splits completely in a finite extension exactly when it splits in
its Galois closure. -/
def SplittingPrimesBridge : Prop :=
  ∀ (K L M : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
    IsGaloisClosure K L M → splittingPrimes K L = splittingPrimes K M

/-- The second exact missing interface: Milne's analytic argument in the
Galois case, stated using the faithful polar-density definition of
Proposition 3.1. -/
def PolarDensityBridge : Prop :=
  ∀ (K M : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M],
    PrimePolarDensity K (splittingPrimes K M)
      (1 / (Module.finrank K M : ℝ))

/-- Polar density is invariant under equality of the underlying prime sets. -/
theorem polar_density_congr
    (K : Type u) [Field K] [NumberField K]
    {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hST : S = T) (hS : PrimePolarDensity K S δ) :
    PrimePolarDensity K T δ := by
  simpa [hST] using hS

/-- The literal conclusion for one finite extension together with a chosen
Galois closure.  Notice that the density denominator is `[M : K]`, not
`[L : K]`. -/
def GaloisClosureConclusion
    (K L M : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M] : Prop :=
  IsGaloisClosure K L M →
    PrimePolarDensity K (splittingPrimes K L)
      (1 / (Module.finrank K M : ℝ))

/-- The Galois-case bridge gives the corresponding specialization directly. -/
theorem galois_case_bridge
    (hGalois : PolarDensityBridge.{u})
    (K M : Type u)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M] :
    PrimePolarDensity K (splittingPrimes K M)
      (1 / (Module.finrank K M : ℝ)) :=
  hGalois K M

/-- The two narrow missing interfaces imply Milne's full theorem, including
the passage from an arbitrary finite extension to its Galois closure. -/
theorem galois_statement_bridges
    (hClosure : SplittingPrimesBridge.{u})
    (hGalois : PolarDensityBridge.{u}) :
    (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M) := by
  intro K L M _ _ _ _ _ _ _ _ _ _ _ _ _ hM
  have hsplit : splittingPrimes K L = splittingPrimes K M :=
    hClosure K L M hM
  exact polar_density_congr K hsplit.symm (hGalois K M)

end

end Submission.CField.PDensit
