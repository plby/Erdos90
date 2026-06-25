import Submission.ClassField.DirichletDensity.CongruenceClassQuotient

/-! # Chapter VIII, Section 7, Theorems 7.1 and 7.2 -/

namespace Submission.CField.CDensit

open IsDedekindDomain NumberField
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.DDensit

noncomputable section
universe u

/-- **Theorem VIII.7.1.** Every nontrivial complex character of a ray class
group has nonzero ordered ideal `L`-value at `1`. -/
def RayLNonvanishing : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) (chi : RayClassGroup K m →* ℂˣ),
    chi ≠ 1 → congruenceLValue K chi ≠ 0

/-- The prime ideals in one prescribed class of `I^m/H`. -/
def idealsCongruenceClass
    (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport))
    (k : CongruenceClassQuotient K m H) :
    Set (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  {p | ∃ hp : p ∉ m.finiteSupport,
    congruencePrimeClass K H ⟨p, hp⟩ = k}

/-- **Theorem VIII.7.2.** Every class of a congruence quotient contains prime
ideals with Dirichlet density the reciprocal of the subgroup index. -/
def CongruenceClassDensity : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)),
    rayPrincipalSubgroup K m ≤ H →
    ∀ k : CongruenceClassQuotient K m H,
      PrimeDirichletDensity K
        (idealsCongruenceClass K m H k)
        ((1 : ℝ) / H.index)

/-- Algebraic passage from ray-class characters to characters of every
coarser congruence quotient, including compatibility of their ordered ideal
`L`-values. -/
def NonvanishingDescendsBridge : Prop :=
  RayLNonvanishing.{u} →
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)),
    rayPrincipalSubgroup K m ≤ H →
    LValuesNonzero K m H

/-- The remaining analytic character-orthogonality/Tauberian step: nonzero
`L(1,chi)` for all nontrivial quotient characters gives the density of each
individual congruence class. -/
def CongruenceNonvanishingBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport)),
    rayPrincipalSubgroup K m ≤ H →
    LValuesNonzero K m H →
    ∀ k : CongruenceClassQuotient K m H,
      PrimeDirichletDensity K
        (idealsCongruenceClass K m H k)
        ((1 : ℝ) / H.index)

/-- Theorem 7.2 follows from Theorem 7.1 through the two precisely separated
algebraic and analytic steps above. -/
theorem density_statement_chebotarev
    (h71 : RayLNonvanishing.{u})
    (hDescend : NonvanishingDescendsBridge.{u})
    (hDensity : CongruenceNonvanishingBridge.{u}) :
    CongruenceClassDensity.{u} := by
  intro K _ _ m H hH k
  exact hDensity K m H hH (hDescend h71 K m H hH) k

end
end Submission.CField.CDensit
