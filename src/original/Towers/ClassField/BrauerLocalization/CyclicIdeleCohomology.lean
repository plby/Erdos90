import Towers.ClassField.CyclicIdeles.NormPrincipalSubgroup
import Towers.ClassField.CyclicIdeles.FixedIndexBridges
import Towers.ClassField.CyclicIdeles.FixedField
import Towers.ClassField.CyclicIdeles.NormIndexTower
import Towers.ClassField.CyclicIdeles.NormalSubgroup
import Towers.ClassField.CyclicIdeles.TrivialExtension
import Towers.ClassField.NormIndex.CanonicalTateFormula
import Towers.ClassField.HasseNorm.ClassH1
import Towers.ClassField.HasseNorm.IdeleIdealCompatibility
import Towers.ClassField.BrauerLocalization.IdeleIdealSupport
import Towers.ClassField.DirichletDensity.Prerequisites

/-!
# Assembly for Chapter VII, Section 5
-/

namespace Towers.CField.BLoc

open Towers.CField.NIndex
open Towers.CField.CIdeles
open Towers.CField.HNorm
open Towers.CField.ARecip
open Towers.CField.RCGroups
open Towers.CField.PDensit

universe u

/-- **Lemma VII.5.2.**  In the cyclic case, the second inequality,
vanishing of `H¹`, degree-two divisibility, and the displayed degree
equality are equivalent. -/
theorem normPrincipalCriteria :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic Gal(L/K)],
      (ClaimA K L ↔ ClaimB K L) ∧
        (ClaimB K L ↔ ClaimC K L) ∧
        (ClaimA K L ↔ DegreeEquality K L) :=
  normPrincipalStatement
    ideleHerbrandQuotient tateIndexBridge
      scalarResizingBridge

/-- The idealic second inequality of VI.4.9 proves all prime-cyclic cases
of Theorem VII.5.1.  The ideal/idèle index comparison, the cyclic Herbrand
quotient calculation, and the scalar-resizing comparison have all been
discharged. -/
theorem cases_second_inequality
    (h49 : (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier)) :
    PrimeCyclicCases.{u} := by
  intro K L _ _ _ _ _ _ _ _ _hprime
  exact claims_second_inequality
    ideleHerbrandQuotient tateIndexBridge
      scalarResizingBridge K L
        (idele_index_finrank h49
          Towers.CField.HNorm.idealInequalityBridge K L)

/-- **Theorem VII.5.1**, reduced only to the analytic second inequality
VI.4.9.  Lemmas VII.5.3 and VII.5.4, as well as the ideal/idèle index
comparison needed in the prime-cyclic case, are unconditional. -/
theorem assembly_second_inequality
    (h49 : (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier)) :
    IdeleCohomologyClaims.{u} :=
  (sylow_bridge_index
      sylowFixedBridge hFinitenessBridge
      ideleFinitenessBridge idelePrimaryBridge)
    ((p_reduction_bridge
        normalSubgroupBridge trivialExtensionBridge
        fixedFieldBridge indexTowerBridge)
      (cases_second_inequality h49))

/-- Theorem VII.5.1 from the named analytic results preceding VI.4.9.
Ray-class and congruence-quotient finiteness, split-prime norm membership,
both reduction lemmas, and the ideal/idèle comparison are all internal. -/
theorem previous_analytic_results
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (h41a : DDensit.PolarImpliesDirichlet.{u})
    (h48 : DDensit.CongruenceDensityFormula.{u}) :
    IdeleCohomologyClaims.{u} :=
  assembly_second_inequality
    (DDensit.prerequisites_statement_previous
      h34 h41a h48)

end Towers.CField.BLoc
