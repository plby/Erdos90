import Submission.ClassField.PrimeDensities.ContainsNoNorm
import Submission.ClassField.DirichletDensity.PolarLogBridge

/-!
# Chapter VI, Section 4, Proposition 4.5
-/

namespace Submission.CField.DDensit

open IsDedekindDomain NumberField Set
open Submission.CField.PDensit

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The finite primes of residue degree one over `ℚ`.  Equivalently, their
absolute ideal norm is a rational prime. -/
def degreePrimeIdeals : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {p | Nat.Prime p.asIdeal.absNorm}

/-- The exact clause Proposition 4.4(a) used below. -/
def Input : Prop :=
  PrimeDirichletDensity K
    (Set.univ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) 1

/-- The exact "union and second piece imply first piece" case of
Proposition 4.4(d). -/
def RightSubtractionInput : Prop :=
  ∀ (T T₁ T₂ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (δ δ₂ : ℝ),
    T = T₁ ∪ T₂ → Disjoint T₁ T₂ →
      PrimeDirichletDensity K T δ →
      PrimeDirichletDensity K T₂ δ₂ →
      PrimeDirichletDensity K T₁ (δ - δ₂)

/-- The complement of the degree-one primes satisfies the exact hypothesis
of Proposition 3.2. -/
theorem ideals_compl_contains :
    ContainsNoAbsolute K (degreePrimeIdeals K)ᶜ := by
  intro p hp hprime
  exact hp hprime

/-- Proposition 3.2 gives density zero to the complementary primes;
Proposition 4.1 transfers that to Dirichlet density, and Proposition 4.4(d)
subtracts it from the density one of all primes. -/
theorem ideals_41_44
    (h32 : (∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ContainsNoAbsolute K T → PrimePolarDensity K T 0))
    (h41 : PolarDirichletBridge.{u})
    (h44a : Input K)
    (h44d : RightSubtractionInput K) :
    PrimeDirichletDensity K (degreePrimeIdeals K) 1
  := by
  let T := degreePrimeIdeals K
  have hcomplPolar : PrimePolarDensity K Tᶜ 0 :=
    h32 Tᶜ (ideals_compl_contains K)
  have hcomplDirichlet : PrimeDirichletDensity K Tᶜ 0 :=
    h41.1 K Tᶜ 0 hcomplPolar
  have hunion : (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = T ∪ Tᶜ :=
    (Set.union_compl_self T).symm
  have hdis : Disjoint T Tᶜ := by
    exact Set.disjoint_left.2 fun p hpT hpCompl ↦ hpCompl hpT
  have hsubtract := h44d Set.univ T Tᶜ 1 0 hunion hdis
    h44a hcomplDirichlet
  simpa [T] using hsubtract

end

end Submission.CField.DDensit
