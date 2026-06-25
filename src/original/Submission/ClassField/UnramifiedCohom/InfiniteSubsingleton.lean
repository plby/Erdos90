import Submission.ClassField.Shifting.TransportAlongEquivalences
import Submission.ClassField.UnramifiedCohom.FiniteQuotient
import Submission.ClassField.UnramifiedCohom.FixedFieldUnits
import Submission.ClassField.UnramifiedCohom.SpectralUnits
import Submission.ClassField.UnramifiedCohom.UnramifiedLayers

/-!
# Milne, Class Field Theory, Corollary III.1.6

For an infinite unramified Galois extension, the continuous cohomology of
the discrete unit module vanishes in every positive degree.  The proof uses
the actual finite-quotient colimit from Proposition II.4.2.  At an open
normal subgroup, invariant ambient integral units are identified first with
the integral units of the fixed field and then with its spectral units, so
Proposition III.1.1 applies without an auxiliary coefficient hypothesis.
-/

namespace Submission.CField.UCohom

open CategoryTheory CategoryTheory.Limits
open Submission.CField.Shifting
open Submission.CField.PCohom
open Submission.CField.LBrauer
open ValuativeRel

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

private abbrev A (K : Type) [NontriviallyNormedField K]
    [ValuativeRel K] := Valuation.integer (ValuativeRel.valuation K)

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance infiniteUnramifiedUnitsContinuousCohomologySubsingletonValuativeRel :
    ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance infiniteUnramifiedUnitsContinuousCohomologySubsingletonValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [IsGalois K L]

set_option maxHeartbeats 2000000 in
-- Each finite level installs two canonical integral models and three representation isomorphisms.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Corollary III.1.6.** Positive continuous cohomology of the unit group
of an infinite unramified Galois extension vanishes.  Units are modeled as
the units of the integral closure of the base valuation ring in `L`, with
the discrete topology and its continuous Krull action. -/
theorem infinite_cohomology_subsingleton
    (hUnramified : IUExt.IsUnramified K L) :
    letI : Algebra (A K) L :=
      ((algebraMap K L).comp (algebraMap (A K) K)).toAlgebra
    letI : IsScalarTower (A K) K L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let M := integralDiscreteAction (A K) K L
    ∀ r : ℕ, 0 < r →
      Subsingleton ((continuousInhomogeneousComplex M).homology r) := by
  letI : Algebra (A K) L :=
    ((algebraMap K L).comp (algebraMap (A K) K)).toAlgebra
  letI : IsScalarTower (A K) K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  dsimp only
  intro r hr
  let M := integralDiscreteAction (A K) K L
  apply continuous_subsingleton_quotients (M := M) (r := r)
  intro Nd
  let Nopen : OpenNormalSubgroup Gal(L/K) := OrderDual.ofDual Nd
  let N : ClosedSubgroup Gal(L/K) :=
    ⟨(Nopen : Subgroup Gal(L/K)), Nopen.toOpenSubgroup.isClosed⟩
  let F := IntermediateField.fixedField (Nopen : Subgroup Gal(L/K))
  have hopen : IsOpen F.fixingSubgroup.carrier := by
    rw [InfiniteGalois.fixingSubgroup_fixedField N]
    exact Nopen.toOpenSubgroup.isOpen'
  letI : FiniteDimensional K F :=
    (InfiniteGalois.isOpen_iff_finite F).mp hopen
  letI : IsGalois K F :=
    IsGalois.of_fixedField_normal_subgroup
      (Nopen : Subgroup Gal(L/K))
  let E : FiniteGaloisIntermediateField K L :=
    { toIntermediateField := F }
  have hUF : FUExt.IsUnramified K F :=
    hUnramified E
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  letI : MulSemiringAction Gal(F/K) 𝒪[F] :=
    FLExt.integerGaloisAction K F
  let CF := Rep.ofMulDistribMulAction Gal(F/K) 𝒪[F]ˣ
  have hfiniteVanishing : Subsingleton (groupCohomology CF r) := by
    exact
      (FUExt.unramified_units_acyclic
        K F hUF).1 r hr
  let eG : Gal(L/K) ⧸ N.1 ≃* Gal(F/K) :=
    InfiniteGalois.normalAutEquivQuotient N
  let eFixed := integralRepIso (A K) K L N
  let eSpectral := spectralRepIso K F
  let eCoeff :
      (underlyingRep M).quotientToInvariants N.1 ≅
        Rep.res eG.toMonoidHom CF :=
    eFixed ≪≫ (Rep.resFunctor eG.toMonoidHom).mapIso eSpectral
  let eCoeffH :
      groupCohomology ((underlyingRep M).quotientToInvariants N.1) r ≅
        groupCohomology (Rep.res eG.toMonoidHom CF) r :=
    (groupCohomology.functor ℤ (Gal(L/K) ⧸ N.1) r).mapIso eCoeff
  let eGroupH : groupCohomology CF r ≅
      groupCohomology (Rep.res eG.toMonoidHom CF) r :=
    cohomologyMulIso eG CF r
  let eH :
      groupCohomology ((underlyingRep M).quotientToInvariants N.1) r ≅
        groupCohomology CF r :=
    eCoeffH ≪≫ eGroupH.symm
  have hzeroTarget : IsZero (groupCohomology CF r) := by
    letI : Subsingleton (groupCohomology CF r) := hfiniteVanishing
    exact ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.subsingleton_of_isZero (hzeroTarget.of_iso eH)

end

end Submission.CField.UCohom
