import Submission.ClassField.LocalReciprocity.ArtinMap
import Submission.ClassField.NormCorrespondence.InverseLimit

/-!
# Finite local Artin homomorphisms and descent

`FiniteLocalArtinMap` constructs the finite norm-residue equivalence from
local invariant base change.  This file exposes the corresponding
homomorphism on field units, proves its kernel and surjectivity, and gives a
general descent theorem along a surjective restriction homomorphism.

The descent result isolates the remaining content of finite-level
functoriality: once the kernel of the restricted upper Artin map is the lower
norm subgroup, the lower norm-residue equivalence and the commuting square
are canonical consequences rather than additional choices.
-/

namespace Submission.CField.LRecip

noncomputable section

open scoped IsMulCommutative
open CategoryTheory.Limits Rep
open Submission.CField.LFTheory
open Submission.CField.BGroups
open Submission.CField.LBrauer

variable (K L : Type)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The invariant and fixed-field base-change data consumed by the finite
local Artin construction. -/
structure LAData where
  invK : BrauerGroup K ≃* Multiplicative LocalInvariant
  invL : BrauerGroup L ≃* Multiplicative LocalInvariant
  baseChange : ∀ x : BrauerGroup K,
    invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L
  invFixed : ∀ H : Subgroup Gal(L/K),
    BrauerGroup (IntermediateField.fixedField H) ≃*
      Multiplicative LocalInvariant
  fixedBaseChange : ∀ (H : Subgroup Gal(L/K))
      (x : BrauerGroup (IntermediateField.fixedField H)),
    invL (brauerBaseChange (IntermediateField.fixedField H) L x) =
      invFixed H x ^ Module.finrank (IntermediateField.fixedField H) L

namespace LAData

variable [IsMulCommutative Gal(L/K)]

/-- The finite norm-residue equivalence attached to local invariant data. -/
noncomputable def normResidueEquiv (D : LAData K L) :
    (Kˣ ⧸ normSubgroup K L) ≃* Gal(L/K) :=
  abelianLocalResidue K L
    D.invK D.invL D.baseChange D.invFixed D.fixedBaseChange

/-- The finite local Artin homomorphism before quotienting by the norm
subgroup. -/
noncomputable def artinHom (D : LAData K L) :
    Kˣ →* Gal(L/K) :=
  D.normResidueEquiv K L |>.toMonoidHom.comp
    (QuotientGroup.mk' (normSubgroup K L))

@[simp]
theorem artinHom_apply (D : LAData K L) (x : Kˣ) :
    D.artinHom K L x =
      D.normResidueEquiv K L
        (QuotientGroup.mk' (normSubgroup K L) x) :=
  rfl

/-- The kernel of the finite local Artin homomorphism is exactly the field
norm subgroup. -/
theorem artinHom_ker (D : LAData K L) :
    (D.artinHom K L).ker = normSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker, artinHom_apply]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply (D.normResidueEquiv K L).injective
    simpa using hx
  · intro hx
    have hq : QuotientGroup.mk' (normSubgroup K L) x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    rw [hq, map_one]

/-- The finite local Artin homomorphism is surjective. -/
theorem artinHom_surjective (D : LAData K L) :
    Function.Surjective (D.artinHom K L) := by
  intro sigma
  let q := (D.normResidueEquiv K L).symm sigma
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (normSubgroup K L) q
  refine ⟨x, ?_⟩
  rw [artinHom_apply, hx]
  exact (D.normResidueEquiv K L).apply_symm_apply sigma

/-- The quotient equivalence recovered from the finite Artin homomorphism's
kernel and surjectivity is the original norm-residue equivalence. -/
theorem surjective_artin_hom
    (D : LAData K L) :
    (QuotientGroup.quotientMulEquivOfEq (D.artinHom_ker K L).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (D.artinHom K L) (D.artinHom_surjective K L)) =
      D.normResidueEquiv K L := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (normSubgroup K L) q
  rfl

end LAData

section Descent

variable {A G Q : Type*} [CommGroup A] [CommGroup G] [CommGroup Q]

/-- A surjective homomorphism whose kernel is a prescribed subgroup induces
the canonical quotient equivalence. -/
noncomputable def normResidueSurjective
    (N : Subgroup A) (f : A →* G) (hf : Function.Surjective f)
    (hker : f.ker = N) : A ⧸ N ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

@[simp]
theorem residue_surjective_mk
    (N : Subgroup A) (f : A →* G) (hf : Function.Surjective f)
    (hker : f.ker = N) (x : A) :
    normResidueSurjective N f hf hker
        (QuotientGroup.mk' N x) = f x :=
  rfl

/-- Restricting a surjective upper Artin homomorphism along a surjective
finite restriction map remains surjective. -/
theorem restrictedArtin_surjective
    (upperArtin : A →* G) (hupper : Function.Surjective upperArtin)
    (restriction : G →* Q) (hrestriction : Function.Surjective restriction) :
    Function.Surjective (restriction.comp upperArtin) :=
  hrestriction.comp hupper

/-- Descend an upper finite Artin map along restriction.  The sole arithmetic
input is the kernel identification with the lower norm subgroup. -/
noncomputable def descendedResidueEquiv
    (N : Subgroup A)
    (upperArtin : A →* G) (hupper : Function.Surjective upperArtin)
    (restriction : G →* Q) (hrestriction : Function.Surjective restriction)
    (hker : (restriction.comp upperArtin).ker = N) :
    A ⧸ N ≃* Q :=
  normResidueSurjective N (restriction.comp upperArtin)
    (restrictedArtin_surjective upperArtin hupper restriction hrestriction)
    hker

/-- The descended norm-residue equivalence makes the finite restriction
square commute on every field unit. -/
@[simp]
theorem descended_residue_mk
    (N : Subgroup A)
    (upperArtin : A →* G) (hupper : Function.Surjective upperArtin)
    (restriction : G →* Q) (hrestriction : Function.Surjective restriction)
    (hker : (restriction.comp upperArtin).ker = N) (x : A) :
    descendedResidueEquiv N upperArtin hupper restriction hrestriction
        hker (QuotientGroup.mk' N x) =
      restriction (upperArtin x) :=
  rfl

end Descent

namespace LAData

variable [IsMulCommutative Gal(L/K)]
variable {Q : Type*} [CommGroup Q]

/-- Descend the finite local Artin map constructed from invariant data along
a surjective finite restriction map.  Proving the displayed kernel equality
is exactly the norm-compatibility input still required in a field tower. -/
noncomputable def descendedResidueEquiv
    (D : LAData K L)
    (restriction : Gal(L/K) →* Q)
    (hrestriction : Function.Surjective restriction)
    (N : Subgroup Kˣ)
    (hker : (restriction.comp (D.artinHom K L)).ker = N) :
    Kˣ ⧸ N ≃* Q :=
  LRecip.descendedResidueEquiv N
    (A := Kˣ) (G := Gal(L/K)) (Q := Q)
    (D.artinHom K L) (D.artinHom_surjective K L)
    restriction hrestriction hker

set_option maxHeartbeats 1000000 in
-- The quotient equivalence and finite Artin map require deeper reduction here.
/-- The descended equivalence attached to an existing finite local Artin map
makes restriction commute on representatives. -/
@[simp]
theorem descended_residue_mk
    (D : LAData K L)
    (restriction : Gal(L/K) →* Q)
    (hrestriction : Function.Surjective restriction)
    (N : Subgroup Kˣ)
    (hker : (restriction.comp (D.artinHom K L)).ker = N)
    (x : Kˣ) :
    D.descendedResidueEquiv K L restriction hrestriction N hker
        (QuotientGroup.mk' N x) =
      restriction (D.artinHom K L x) := by
  exact LRecip.descended_residue_mk
    (A := Kˣ) (G := Gal(L/K)) (Q := Q)
    N (D.artinHom K L) (D.artinHom_surjective K L)
    restriction hrestriction hker x

end LAData

end

end Submission.CField.LRecip

namespace Submission.CField.LFTheory

noncomputable section

open CategoryTheory Opposite
open Submission.CField.LRecip

variable (K : Type) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- Local-invariant data at every finite level of the maximal abelian
extension, together with functoriality of the resulting finite Artin maps.

Unlike a family of arbitrary quotient equivalences, the homomorphisms in the
compatibility field are the concrete maps constructed by Tate's theorem in
`FiniteLocalArtinMap`. -/
structure CASystem where
  data (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    LAData K E
  compatible : ∀ {E F :
      (FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K))ᵒᵖ}
      (f : E ⟶ F) (x : Kˣ),
    (finGaloisGroupFunctor K (maximalAbelianIntermediate K)).map f
        ((data E.unop).artinHom K E.unop x) =
      (data F.unop).artinHom K F.unop x

namespace CASystem

variable (D : CASystem K)

/-- A compatible system of concrete finite local Artin data supplies the
exact finite norm-residue family consumed by the inverse-limit assembly. -/
noncomputable def compat_abeli_recip :
    CARecip K where
  hom E := (D.data E).artinHom K E
  compatible f x := D.compatible f x
  equiv E := (D.data E).normResidueEquiv K E
  equiv_mk _ _ := rfl

/-- Assemble a compatible system of the concrete finite local Artin maps
into the abelianized absolute Galois group. -/
noncomputable def assemble :
    Kˣ →* AbsoluteAbelianGalois K :=
  CAArtin.assemble K
    (D.compat_abeli_recip K).toCAArtin

omit [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
/-- The assembled concrete finite Artin system induces its norm-residue
equivalence on every lifted finite level. -/
theorem induce_recip_assem
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    InducesLocalReciprocity K (D.assemble K)
      (maximalAbelianSubextension K E) :=
  CARecip.induce_recip_assem
    K (D.compat_abeli_recip K) E

end CASystem

end

end Submission.CField.LFTheory
