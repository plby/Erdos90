import Submission.ClassField.NormCorrespondence.InverseLimit
import Submission.ClassField.Reciprocity.RestrictedFactorFamily

/-!
# The finite-restriction topology in Proposition V.5.2

The absolute abelian Galois group is the Galois group of the maximal
abelian subextension, hence the inverse limit of its finite Galois layers.
This file proves that a map into it is continuous exactly when all finite
restrictions are continuous, discharging the topological interface isolated
in `Proposition52SourceStatement`.
-/

namespace Submission.CField.Recip

open CategoryTheory Opposite
open CategoryTheory.Limits
open FiniteGaloisIntermediateField ProfiniteGrp
open Submission.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The quotient model of the absolute abelian Galois group is
homeomorphic, as a topological group, to the Galois group of the maximal
abelian fixed field. -/
noncomputable def abelianContinuousMaximal :
    AbsoluteAbelianGalois K ≃ₜ*
      Gal(maximalAbelianIntermediate K/K) := by
  let e := abelianGaloisMaximal K
  have he : Continuous e := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact InfiniteGalois.restrictNormalHom_continuous
      (maximalAbelianIntermediate K)
  let h := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
  exact
    { toMulEquiv := e
      continuous_toFun := he
      continuous_invFun := h.continuous_invFun }

/-- Continuity of a map to the absolute abelian Galois group can be tested
after restriction to every finite abelian subextension. -/
theorem restrictionTopologyInterface :
    RestrictionTopologyInterface (K := K) := by
  intro phi hphi
  let A := maximalAbelianIntermediate K
  let eAb := abelianContinuousMaximal K
  let eLim := InfiniteGalois.continuousMulEquivToLimit K A
  have hLim : Continuous (fun a => eLim (eAb (phi a))) := by
    rw [continuous_induced_rng]
    apply continuous_pi
    intro Eop
    let E := Eop.unop
    let L := maximalAbelianSubextension K E
    let eFinite := (maximalAbelianLevel K E).autCongr
    have hFiniteInv : Continuous eFinite.symm :=
      continuous_of_discreteTopology
    have hRestricted : Continuous
        (fun a => localAbelianRestriction L (phi a)) := by
      simpa only [MonoidHom.coe_comp, Function.comp_apply] using hphi L
    have hCoordinate : Continuous (fun a =>
        maximalAbelianRestriction K E
          (abelianGaloisMaximal K (phi a))) := by
      convert hFiniteInv.comp hRestricted using 1
      funext a
      change _ = eFinite.symm
        (localAbelianRestriction (maximalAbelianSubextension K E) (phi a))
      rw [abelian_restriction_subextension]
      exact (eFinite.symm_apply_apply _).symm
    convert hCoordinate
    exact (DiscreteTopology.eq_bot (α := Gal(E/K))).symm
  have hBack : Continuous (fun a => eAb.symm (eLim.symm (eLim (eAb (phi a))))) :=
    eAb.continuous_invFun.comp (eLim.continuous_invFun.comp hLim)
  simpa only [ContinuousMulEquiv.symm_apply_apply] using hBack

/-- Proposition V.5.2 with its purely topological inverse-limit hypothesis
discharged. Its sole remaining input is the compatible arithmetic system of
finite-layer local Artin products. -/
theorem restriction_topology_system
    (D : LASystem (K := K)) :
    GlobalArtinProposition (K := K) :=
  restrictedFamilyStatement D (restrictionTopologyInterface K)

end

end Submission.CField.Recip
