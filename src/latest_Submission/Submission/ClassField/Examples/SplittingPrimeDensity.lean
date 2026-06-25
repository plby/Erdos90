import Submission.ClassField.Examples.SplittingPrimes
import Submission.NumberTheory.Galois.CompositumDegreeCriterion
import Submission.NumberTheory.Density.SplittingPrimeDensity

/-!
# Class Field Theory, Introduction, Theorem 0.1

Frobenius's theorem says that the finite primes splitting completely in a
finite Galois extension `L / K` have natural density `1 / [L : K]`.  The
analytic theorem is recorded below as a proposition because its proof is not
yet available in the pinned Mathlib.  We prove the consequence used in the
next paragraph of the text: this density determines the degree of the
extension.
-/

namespace Submission.CField.Examples

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open scoped NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Theorem 0.1 (Frobenius), exact statement.** The finite primes of `K`
that split completely in `L` have natural density `1 / [L : K]`.

The manuscript states this theorem without proof.  Its analytic proof is the
identity-conjugacy-class case of the Chebotarev density theorem.
-/
abbrev SplittingPrimeDensity : Prop :=
  PNDensit K (splittingPrimes K L)
    (1 / Module.finrank K L : Real)

/-- The completely-split case of Chebotarev is exactly Frobenius's
Theorem 0.1.  All arithmetic identifications—including removal of ramified
primes and the equivalence between identity Frobenius and complete
splitting—are discharged by the splitting-prime density theorem. -/
theorem splitting_prime_chebotarev
    (hcheb : ChebotarevDensityTheorem K L) :
    SplittingPrimeDensity K L := by
  exact splitting_density_chebotarev K L hcheb

/-- Theorem 0.1 for the trivial extension, without any analytic hypothesis. -/
theorem splitting_density_self : SplittingPrimeDensity K K :=
  splitting_prime_chebotarev K K (chebotarev_theorem_self K)

variable (M : Type*) [Field M] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  [NumberField M] [FiniteDimensional K M] [IsGalois K M] in
/-- The observation immediately following Theorem 0.1: the density of the
set of completely split primes determines the degree of the extension. -/
theorem finrank_splitting_primes
    (hL : SplittingPrimeDensity K L) (hM : SplittingPrimeDensity K M)
    (hsplit : splittingPrimes K L = splittingPrimes K M) :
    Module.finrank K L = Module.finrank K M := by
  have hdensity :
      (1 / Module.finrank K L : Real) =
        (1 / Module.finrank K M : Real) := by
    unfold SplittingPrimeDensity PNDensit at hL hM
    rw [hsplit] at hL
    exact tendsto_nhds_unique hL hM
  have hcast :
      (Module.finrank K L : Real) = Module.finrank K M := by
    apply inv_injective
    simpa only [one_div] using hdensity
  exact_mod_cast hcast

section IntermediateFields

variable {Omega : Type*} [Field Omega] [Algebra K Omega]
  [FiniteDimensional K Omega]

/-- The full consequence stated after Theorem 0.1: two Galois intermediate
fields with the same completely split primes are equal.

The hypotheses display the two inputs used in the manuscript: Frobenius's
density theorem for both fields and their compositum, and the standard fact
that a prime splits in the compositum exactly when it splits in both factors.
-/
theorem intermediate_splitting_primes
    (L M : IntermediateField K Omega)
    (hcompositum :
      splittingPrimes K (L ⊔ M : IntermediateField K Omega) =
        splittingPrimes K L ∩ splittingPrimes K M)
    (hsplitting : splittingPrimes K L = splittingPrimes K M)
    (hcompositumDensity :
      PNDensit K
        (splittingPrimes K (L ⊔ M : IntermediateField K Omega))
        (1 / Module.finrank K (L ⊔ M : IntermediateField K Omega) : Real))
    (hLDensity :
      PNDensit K (splittingPrimes K L)
        (1 / Module.finrank K L : Real))
    (hMDensity :
      PNDensit K (splittingPrimes K M)
        (1 / Module.finrank K M : Real)) :
    L = M := by
  exact
    intermediate_splitting_density
      L M (splittingPrimes K L) (splittingPrimes K M)
        (splittingPrimes K (L ⊔ M : IntermediateField K Omega))
        hcompositum hsplitting
        hcompositumDensity hLDensity hMDensity

/-- The consequence following Theorem 0.1 with all splitting and density
compatibilities supplied by Chebotarev: two finite Galois intermediate
fields having the same completely split primes are equal. -/
theorem splitting_primes_chebotarev
    (L M : IntermediateField K Omega)
    [NumberField Omega]
    [IsGalois K L] [IsGalois K M]
    (hchebCompositum : ChebotarevDensityTheorem K (L ⊔ M : IntermediateField K Omega))
    (hchebL : ChebotarevDensityTheorem K L)
    (hchebM : ChebotarevDensityTheorem K M)
    (hsplitting : splittingPrimes K L = splittingPrimes K M) :
    L = M := by
  apply intermediate_splitting_primes K L M
  · exact splitting_sup_inter L M
  · exact hsplitting
  · exact splitting_density_chebotarev K
      (L ⊔ M : IntermediateField K Omega) hchebCompositum
  · exact splitting_density_chebotarev K L hchebL
  · exact splitting_density_chebotarev K M hchebM

end IntermediateFields

end

end Submission.CField.Examples
