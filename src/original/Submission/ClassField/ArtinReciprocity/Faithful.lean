import Submission.ClassField.ArtinReciprocity.Statements
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.FieldTheory.Galois.Basic

/-!
# Chapter V, Section 3: Corollary 3.7 (source-faithful statement)

For a fixed modulus `m`, Corollary V.3.7 identifies the intermediate fields
of the ray class field with the subgroups of the ray class group.  It also
records how inclusion, compositum, and intersection translate under this
order-reversing correspondence.

The present `GlobalExistenceTheorem` produces, for the ray-principal
subgroup at `m`, a finite abelian extension whose ray norm subgroup is that
subgroup.  The present `IdealReciprocityLaw`, however, only produces an
Artin isomorphism at an existentially chosen modulus.  It does not say that
the isomorphism is available at an already fixed `m`.  Accordingly,
`FixedModulusBridge` below isolates exactly that missing compatibility;
it is not added as a hypothesis to any of the three correspondence formulas.
Once the fixed-modulus ray class field and its Artin isomorphism are supplied,
the formulas are formal consequences of the Galois correspondence.
-/

namespace Submission.CField.ARecip

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open RCGroups
open scoped nonZeroDivisors Pointwise

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The ray class group `C_m = I^m / i(K_{m,1})`. -/
abbrev FaithfulRayGroup (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) :=
  IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸ rayPrincipalSubgroup K m

/-- A realization of the ray class field at the *specified* modulus `m`.

The `artinEquiv` field is the fixed-modulus conclusion needed in Corollary
V.3.7.  It is deliberately kept separate from `IdealReciprocityLaw`,
whose current interface chooses its modulus existentially. -/
structure FMRay (K : Type u) [Field K] [NumberField K]
    (m : Modulus K) where
  extension : ANExt K
  artinEquiv :
    FaithfulRayGroup K m ≃* Gal(extension.carrier/K)

namespace FMRay

variable {m : Modulus K} (M : FMRay K m)

/-- The norm class subgroup associated with an intermediate field, expressed
through the Artin isomorphism as the inverse image of its fixing subgroup. -/
def normClassSubgroup (L : IntermediateField K M.extension.carrier) :
    Subgroup (FaithfulRayGroup K m) :=
  M.artinEquiv.comapSubgroup L.fixingSubgroup

/-- The exact ray-class-field/subgroup correspondence of Corollary V.3.7. -/
def subgroupCorrespondence :
    IntermediateField K M.extension.carrier ≃o
      (Subgroup (FaithfulRayGroup K m))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup.trans
    M.artinEquiv.comapSubgroup.dual

@[simp]
theorem subgroupCorrespondence_apply
    (L : IntermediateField K M.extension.carrier) :
    (M.subgroupCorrespondence L).ofDual = M.normClassSubgroup L :=
  rfl

/-- The assignment `L ↦ Nm(C_{L,m})` is a bijection. -/
theorem subgroupCorrespondence_bijective :
    Function.Bijective M.subgroupCorrespondence :=
  M.subgroupCorrespondence.bijective

/-- First formula in Corollary V.3.7:
`L₁ ⊆ L₂ ↔ Nm(C_{L₁,m}) ⊇ Nm(C_{L₂,m})`. -/
theorem norm_class_reverse
    (L₁ L₂ : IntermediateField K M.extension.carrier) :
    L₁ ≤ L₂ ↔ M.normClassSubgroup L₂ ≤ M.normClassSubgroup L₁ := by
  change L₁ ≤ L₂ ↔ M.subgroupCorrespondence L₁ ≤ M.subgroupCorrespondence L₂
  exact M.subgroupCorrespondence.le_iff_le.symm

/-- Second formula in Corollary V.3.7: the norm class subgroup of a
compositum is the intersection of the two norm class subgroups. -/
theorem norm_class_sup
    (L₁ L₂ : IntermediateField K M.extension.carrier) :
    M.normClassSubgroup (L₁ ⊔ L₂) =
      M.normClassSubgroup L₁ ⊓ M.normClassSubgroup L₂ := by
  change (M.subgroupCorrespondence (L₁ ⊔ L₂)).ofDual =
    (M.subgroupCorrespondence L₁).ofDual ⊓
      (M.subgroupCorrespondence L₂).ofDual
  exact M.subgroupCorrespondence.map_sup L₁ L₂

/-- The product of subgroups occurring in the third formula.  Since the ray
class group is commutative, this supremum has carrier the pointwise product. -/
def subgroupProduct
    (H₁ H₂ : Subgroup (FaithfulRayGroup K m)) :
    Subgroup (FaithfulRayGroup K m) :=
  H₁ ⊔ H₂

/-- In the abelian ray class group, `H₁ ⊔ H₂` really is the subgroup product
`H₁ H₂` appearing in the source. -/
theorem coe_subgroupProduct
    (H₁ H₂ : Subgroup (FaithfulRayGroup K m)) :
    (subgroupProduct H₁ H₂ : Set (FaithfulRayGroup K m)) =
      (H₁ : Set (FaithfulRayGroup K m)) * H₂ := by
  simpa [subgroupProduct] using Subgroup.mul_normal H₁ H₂

/-- Third formula in Corollary V.3.7: the norm class subgroup of an
intersection is the product of the two norm class subgroups. -/
theorem norm_class_inf
    (L₁ L₂ : IntermediateField K M.extension.carrier) :
    M.normClassSubgroup (L₁ ⊓ L₂) =
      subgroupProduct (M.normClassSubgroup L₁) (M.normClassSubgroup L₂) := by
  change (M.subgroupCorrespondence (L₁ ⊓ L₂)).ofDual =
    (M.subgroupCorrespondence L₁).ofDual ⊔
      (M.subgroupCorrespondence L₂).ofDual
  exact M.subgroupCorrespondence.map_inf L₁ L₂

/-- Carrier-level version of the third formula, literally using pointwise
subgroup multiplication as in the source. -/
theorem coe_subgroup_inf
    (L₁ L₂ : IntermediateField K M.extension.carrier) :
    (M.normClassSubgroup (L₁ ⊓ L₂) :
        Set (FaithfulRayGroup K m)) =
      (M.normClassSubgroup L₁ : Set (FaithfulRayGroup K m)) *
        M.normClassSubgroup L₂ := by
  rw [M.norm_class_inf L₁ L₂]
  exact coe_subgroupProduct _ _

end FMRay

/-- What the current existence theorem supplies when applied to the
ray-principal subgroup at a fixed modulus.  No additional hypothesis is used. -/
theorem ray_candidate_existence
    (hExistence : GlobalExistenceTheorem K) (m : Modulus K) :
    ∃ L : ANExt K,
      L.IsUnramifiedOutside m ∧
        rayNormSubgroup L m = rayPrincipalSubgroup K m := by
  obtain ⟨L, hunramified, hnorm⟩ :=
    hExistence m (rayPrincipalSubgroup K m) le_rfl
  exact ⟨L, hunramified, hnorm.symm⟩

/-- What the current reciprocity theorem supplies: an Artin quotient
isomorphism at *some* modulus, chosen together with the isomorphism. -/
theorem some_modulus_reciprocity
    (hReciprocity : IdealReciprocityLaw K)
    (L : ANExt K) :
    ∃ m : Modulus K,
      L.ExactRamificationSupport m ∧
        Nonempty
          ((IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸ rayNormSubgroup L m) ≃*
            Gal(L.carrier/K)) := by
  obtain ⟨m, ψ, hramified, hArtin, e, he⟩ := hReciprocity L
  exact ⟨m, hramified, ⟨e⟩⟩

/-- The precise fixed-modulus compatibility absent from the present
interfaces of Theorems V.3.5--3.6.  It asks only for the Artin equivalence for
an existence-theorem candidate whose norm subgroup is ray-principal. -/
def FixedModulusBridge
    (K : Type u) [Field K] [NumberField K] (m : Modulus K) : Prop :=
  ∀ L : ANExt K,
    L.IsUnramifiedOutside m →
    rayNormSubgroup L m = rayPrincipalSubgroup K m →
      Nonempty (FaithfulRayGroup K m ≃* Gal(L.carrier/K))

/-- The existence theorem plus exactly the missing fixed-modulus Artin bridge
constructs the ray class field datum used above. -/
theorem modulus_existence_bridge
    (hExistence : GlobalExistenceTheorem K) (m : Modulus K)
    (hBridge : FixedModulusBridge K m) :
    Nonempty (FMRay K m) := by
  obtain ⟨L, hunramified, hnorm⟩ :=
    ray_candidate_existence hExistence m
  exact ⟨{
    extension := L
    artinEquiv := Classical.choice (hBridge L hunramified hnorm) }⟩

end

end Submission.CField.ARecip
