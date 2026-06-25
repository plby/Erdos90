import Submission.ClassField.NormIndex.CanonicalTateFormula
import Submission.ClassField.CyclicIdeles.FixedIndexBridges
import Submission.ClassField.CyclicIdeles.FixedHerbrandAssembly
import Submission.ClassField.KummerNormIndex.SecondInequalityTower
import Submission.ClassField.HasseNorm.ClassH1
import Submission.ClassField.BrauerLocalization.IdeleIdealSupport

/-!
# The algebraic proof of Theorem VII.5.1

Section VII.6 supplies the second inequality for cyclic extensions of prime
degree without using the analytic ideal theorem VI.4.9.  This file feeds
that result into the already formalized cyclic cohomology argument and the
Sylow/inflation--restriction reductions of Lemmas VII.5.3--VII.5.4.
-/

namespace Submission.CField.CIdeles

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.KNIndex
open Submission.CField.HNorm

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

private abbrev normPrincipalSubgroup
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (IK K) :=
  principalIdeles (NumberField.RingOfIntegers K) K ⊔
    ideleNormSubgroup (K := K) (L := L)

/-- The algebraic second inequality of §VII.6 gives all three clauses of
Theorem VII.5.1 in the prime-cyclic case. -/
theorem primeCyclicCases : PrimeCyclicCases.{u} := by
  intro K L _ _ _ _ _ _ _ _ hprime
  have hsecond : SecondInequalityAt K L :=
    second_inequality_cyclic
      (Module.finrank K L) hprime K L rfl
  have hcard :=
    nat_principal_index K L
  have hindexDvd : (normPrincipalSubgroup K L).index ∣
      Module.finrank K L := by
    rw [← hcard]
    exact hsecond.2
  have hindexLe : (normPrincipalSubgroup K L).index ≤
      Module.finrank K L :=
    Nat.le_of_dvd Module.finrank_pos hindexDvd
  exact claims_second_inequality
    Submission.CField.BLoc.ideleHerbrandQuotient
    tateIndexBridge scalarResizingBridge
    K L hindexLe

/-- **Lemma VII.5.3.**  The checked fixed-field, finiteness, and primary
index comparisons assemble to the Sylow reduction used below. -/
theorem algebraicStatement : SylowReductionBridge.{u} :=
  sylow_bridge_index
    sylowFixedBridge
    hFinitenessBridge
    ideleFinitenessBridge
    idelePrimaryBridge

/-- **Theorem VII.5.1.**  The second inequality and the two low-degree
idèle-class cohomology assertions for every finite Galois extension. -/
theorem ideleCohomologyClaims :
    IdeleCohomologyClaims.{u} :=
  algebraicStatement
    (pCyclicCases primeCyclicCases)

end

end Submission.CField.CIdeles
