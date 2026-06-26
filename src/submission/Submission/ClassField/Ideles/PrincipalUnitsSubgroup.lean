import Submission.ClassField.Ideles.LocalNorms
import Submission.ClassField.NormCorrespondence.StandardOpenSubgroups
import Submission.ClassField.UnramifiedCohom.FormallyMaximalIdeal
import Submission.ClassField.LocalReciprocity.MaximalIntermediate

/-!
# Chapter V, Section 4, Proposition 4.12

Part (a) is already proved in `LocalNorms`.  Here the newer local-field APIs
are used to supply the exact principal-unit conclusion of part (b) in the
finite Galois case, and the full unit-surjectivity conclusion of part (c)
from the source-facing unramified integral model.
-/

namespace Submission.CField.Ideles

open IsLocalRing ValuativeRel
open Submission.CField.LFTheory
open Submission.CField.NCorr
open Submission.CField.UCohom
open Submission.CField.LRecip
open Submission.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance principalUnitsLeNormSubgroupValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance principalUnitsLeNormSubgroupValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [Module.Finite K L]

/-- **Proposition V.4.12(b), finite Galois case.**  Openness of the norm
subgroup and the principal-unit neighborhood basis produce an `m` for which
`1 + p_K^m` is contained in the norm group. -/
theorem principal_units_subgroup
    [IsGalois K L] :
    ∃ m : ℕ,
      principalUnitField K m ≤ normSubgroup K L := by
  letI : Finite (Kˣ ⧸ normSubgroup K L) :=
    Finite.of_injective (localArtinEquiv K L)
      (localArtinEquiv K L).injective
  letI : (normSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  apply principal_unit_field K (normSubgroup K L)
  exact norm_subgroup K L

/-- The exact remaining non-Galois input in Proposition V.4.12(b): the norm
subgroup of every finite characteristic-zero local extension is open. -/
def NormSubgroupOpen : Prop :=
  IsOpen (normSubgroup K L : Set Kˣ)

omit [Module.Finite K L] in
/-- Once the openness assertion is available, the literal principal-unit
conclusion of Proposition V.4.12(b) has no further hypotheses. -/
theorem norm_open
    (hopen : NormSubgroupOpen K L) :
    ∃ m : ℕ,
      principalUnitField K m ≤ normSubgroup K L :=
  principal_unit_field K (normSubgroup K L) hopen

private abbrev A := Valuation.integer (valuation K)

/-- **Proposition V.4.12(c).**  For a finite unramified extension, every
unit of `K` is a norm from `L`.  The integral model is a presentation of the
unramified extension, not an additional norm or approximation hypothesis. -/
theorem local_units_subgroup
    (U : Type) [CommRing U] [Algebra (A K) U] [Algebra U L]
    [IsScalarTower (A K) U L] [IsIntegralClosure U (A K) L]
    [Module.Finite (A K) U] [IsLocalRing U]
    [Algebra.IsUnramifiedAt (A K) (maximalIdeal U)] :
    localUnitSubgroup K ≤ normSubgroup K L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  intro x hx
  let u : 𝒪[K]ˣ := localInteger K ⟨x, hx⟩
  obtain ⟨v, hv⟩ :=
    unramified_units_model K L U u
  let y : Lˣ := Units.map (𝒪[L]).subtype.toMonoidHom v
  refine ⟨y, ?_⟩
  apply Units.ext
  change Algebra.norm K ((((v : 𝒪[L]) : L))) = (x : Kˣ)
  calc
    Algebra.norm K ((((v : 𝒪[L]) : L))) = ((u : 𝒪[K]) : K) := hv
    _ = (x : Kˣ) := rfl

end

end Submission.CField.Ideles
