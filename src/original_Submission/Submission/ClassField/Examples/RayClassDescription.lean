import Submission.ClassField.Examples.ClassFieldExistence

/-!
# Class Field Theory, Introduction, Theorem 0.8

Artin's theorem is the global ideal reciprocity law: at a modulus with
exactly the ramified support, the Frobenius map factors through the ray class
group and induces the norm-quotient isomorphism with the Galois group.
-/

namespace Submission.CField.Examples

open IsDedekindDomain NumberField
open Submission.CField.RCGroups
open Submission.CField.ARecip
open scoped nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **Theorem 0.8 (Artin), exact statement.** This is the Chapter V global
ideal reciprocity law, whose fields record the Artin map, exact ramification
support, norm-quotient isomorphism, and Frobenius compatibility. -/
abbrev RayDescriptionStatement : Prop :=
  IdealReciprocityLaw K

/-- The source-shaped ray-class description supplied by Theorem 0.8 for
each finite abelian extension. -/
theorem rayClassDescription
    (h08 : RayDescriptionStatement K)
    (L : ANExt K) :
    Nonempty (RCDescri K L) :=
  ray_description_reciprocity K h08 L

namespace RCDescri

variable {K}

/-- The kernel of the Artin map is exactly the product of ray-principal
ideals and ideal norms displayed in Theorem 0.8. -/
theorem ker_artin_ray
    {L : ANExt K}
    (D : RCDescri K L) :
    D.artinMap.ker = rayNormSubgroup L D.modulus := by
  ext I
  change D.artinMap I = 1 ↔ I ∈ rayNormSubgroup L D.modulus
  rw [← D.artinEquiv_apply I, D.artinEquiv.map_eq_one_iff]
  constructor
  · intro h
    have hmem :
        QuotientGroup.mk' (rayPrincipalSubgroup K D.modulus) I ∈
          rayClassExtension K L D.modulus :=
      (QuotientGroup.eq_one_iff
        (QuotientGroup.mk' (rayPrincipalSubgroup K D.modulus) I)).1 h
    change I ∈ rayClassPreimage K D.modulus
      (rayClassExtension K L D.modulus) at hmem
    rwa [ray_preimage_extension] at hmem
  · intro h
    apply (QuotientGroup.eq_one_iff
      (QuotientGroup.mk' (rayPrincipalSubgroup K D.modulus) I)).2
    change I ∈ rayClassPreimage K D.modulus
      (rayClassExtension K L D.modulus)
    rwa [ray_preimage_extension]

/-- In particular, the Artin map kills every ray-principal ideal, so it
factors through the ray class group as asserted in Theorem 0.8. -/
theorem ray_principal_artin
    {L : ANExt K}
    (D : RCDescri K L) :
    rayPrincipalSubgroup K D.modulus ≤ D.artinMap.ker := by
  rw [D.ker_artin_ray]
  exact ray_principal_norm K L D.modulus

/-- The Artin homomorphism on the ray class group. -/
noncomputable def rayClassArtin
    {L : ANExt K}
    (D : RCDescri K L) :
    RayClassGroup K D.modulus →* Gal(L.carrier/K) :=
  QuotientGroup.lift
    (rayPrincipalSubgroup K D.modulus)
    D.artinMap D.ray_principal_artin

@[simp]
theorem ray_artin_mk
    {L : ANExt K}
    (D : RCDescri K L)
    (I : IdealsPrimeTo (𝓞 K) K D.modulus.finiteSupport) :
    D.rayClassArtin
        (QuotientGroup.mk' (rayPrincipalSubgroup K D.modulus) I) =
      D.artinMap I :=
  rfl

end RCDescri

end

end Submission.CField.Examples
