import Towers.ClassField.ArtinReciprocity.FrobeniusExamples
import Towers.ClassField.Ideles.FiniteRaySubgroup
import Towers.ClassField.Reciprocity.Reciprocity

/-!
# Remark VII.8.3: reciprocity from the ray-class construction

This file carries out the construction invoked in Remark VII.8.3 instead of
assuming an idèle-extension bridge which already knows principal reciprocity.
For a modulus `m`, Proposition V.4.6 gives

`I_m / K_{m,1} ≃ C_K`.

The ideal map gives a homomorphism from the left-hand quotient to the ray
class group.  Transporting it across this equivalence produces a map from the
idèle class group.  The idèle Artin map is its composite with
`I_K → C_K`; hence its value on every principal idèle is `1` by the
quotient relation itself.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open NumberField
open Towers.CField.RCGroups
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u v

variable {K : Type u} [Field K] [NumberField K]

private abbrev OK := NumberField.RingOfIntegers K

/-- The map from `I_m / K_{m,1}` to the ray class group induced by the
idèle-to-ideal map.  Its well-definedness is the kernel calculation in
Proposition V.4.6(a), not a principal-reciprocity assumption. -/
noncomputable def modulusPrincipalRay
    (m : Modulus K) (B : IdealMapBridge m) :
    (modulusIdeles m ⧸ modulusPrincipalIdeles m) →* RayClassGroup K m :=
  QuotientGroup.lift (modulusPrincipalIdeles m)
    (modulusIdeleRay m B) (by
      rw [modulus_ray_ker m B]
      exact le_sup_left)

@[simp]
theorem modulus_ray_mk
    (m : Modulus K) (B : IdealMapBridge m)
    (a : modulusIdeles m) :
    modulusPrincipalRay m B
        (QuotientGroup.mk' (modulusPrincipalIdeles m) a) =
      modulusIdeleRay m B a :=
  QuotientGroup.lift_mk' _ _ _

/-- The ray-class map on the full idèle class group, obtained by transporting
the preceding quotient map across Proposition V.4.6(b). -/
noncomputable def ideleRayHom
    (m : Modulus K) (B : IdealMapBridge m)
    (hWA : WeakApproximation m) :
    IdeleClassGroup (OK (K := K)) K →* RayClassGroup K m :=
  (modulusPrincipalRay m B).comp
    (modulusIdeleEquiv m hWA).symm.toMonoidHom

/-- On an idèle satisfying the modulus conditions, the transported map is
literally the ray class of its associated ideal.  This is the compatibility
used in Example V.4.10 to identify the local components. -/
@[simp]
theorem ray_mk_modulus
    (m : Modulus K) (B : IdealMapBridge m)
    (hWA : WeakApproximation m) (a : modulusIdeles m) :
    ideleRayHom m B hWA
        (QuotientGroup.mk' (principalIdeles (OK (K := K)) K) a.1) =
      modulusIdeleRay m B a := by
  change modulusPrincipalRay m B
      ((modulusIdeleEquiv m hWA).symm
        (QuotientGroup.mk' (principalIdeles (OK (K := K)) K) a.1)) = _
  have he : modulusIdeleEquiv m hWA
      (QuotientGroup.mk' (modulusPrincipalIdeles m) a) =
        QuotientGroup.mk' (principalIdeles (OK (K := K)) K) a.1 := by
    rfl
  have he' := congrArg (modulusIdeleEquiv m hWA).symm he
  rw [(modulusIdeleEquiv m hWA).symm_apply_apply] at he'
  rw [← he']
  exact modulus_ray_mk m B a

/-- The idèle homomorphism attached to a ray-class character.  Unlike
`RayExtensionBridge`, this definition factors through the idèle class
group visibly, so no kernel clause is supplied as data. -/
noncomputable def rayCharacterHom
    {G : Type v} [CommGroup G]
    (m : Modulus K) (B : IdealMapBridge m)
    (hWA : WeakApproximation m)
    (chi : RayClassGroup K m →* G) :
    IdeleGroup (OK (K := K)) K →* G :=
  (chi.comp (ideleRayHom m B hWA)).comp
    (QuotientGroup.mk' (principalIdeles (OK (K := K)) K))

/-- The constructed idèle character agrees with the original ray-class
character on `I_m`, after applying the idèle-to-ideal map. -/
@[simp]
theorem ray_character_modulus
    {G : Type v} [CommGroup G]
    (m : Modulus K) (B : IdealMapBridge m)
    (hWA : WeakApproximation m)
    (chi : RayClassGroup K m →* G) (a : modulusIdeles m) :
    rayCharacterHom m B hWA chi a.1 =
      chi (modulusIdeleRay m B a) := by
  change chi (ideleRayHom m B hWA
      (QuotientGroup.mk' (principalIdeles (OK (K := K)) K) a.1)) = _
  rw [ray_mk_modulus]

/-- The quotient map to the idèle class group kills every diagonal idèle. -/
theorem principal_idele_class (x : Kˣ) :
    QuotientGroup.mk' (principalIdeles (OK (K := K)) K)
        (principalIdele (OK (K := K)) K x) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [QuotientGroup.ker_mk']
  exact ⟨x, rfl⟩

/-- Pull a character of the idèle class group back to the idèles.  This is
the formal content of the phrase in Remark VII.8.3 that the Artin map is
defined on `C_K`. -/
noncomputable def ideleCharacterHom
    {G : Type v} [CommGroup G]
    (psi : IdeleClassGroup (OK (K := K)) K →* G) :
    IdeleGroup (OK (K := K)) K →* G :=
  psi.comp (QuotientGroup.mk' (principalIdeles (OK (K := K)) K))

/-- **Remark VII.8.3.** Every homomorphism defined on the idèle class group
is trivial on the diagonal copy of `K×` after pulling it back to the idèles.

This is the assumption-free logical core of the remark: the conclusion is
proved directly from the quotient relation and is not stored in a bridge
record. -/
theorem principalReciprocity
    {G : Type v} [CommGroup G]
    (psi : IdeleClassGroup (OK (K := K)) K →* G) :
    TrivialPrincipalIdeles (OK (K := K)) K G
      (ideleCharacterHom psi) := by
  intro x
  change psi
      (QuotientGroup.mk' (principalIdeles (OK (K := K)) K)
        (principalIdele (OK (K := K)) K x)) = 1
  rw [principal_idele_class, map_one]

/-- The ray-class construction above is an instance of the assumption-free
class-group statement.  Proposition V.4.6 is used only to construct the map
on `C_K`; it is not asked to provide principal reciprocity. -/
theorem ray_principal_reciprocity
    {G : Type v} [CommGroup G]
    (m : Modulus K) (B : IdealMapBridge m)
    (hWA : WeakApproximation m)
    (chi : RayClassGroup K m →* G) :
    TrivialPrincipalIdeles (OK (K := K)) K G
      (rayCharacterHom m B hWA chi) :=
  principalReciprocity (chi.comp (ideleRayHom m B hWA))

/-- The cyclotomic specialization stated in Remark VII.8.3.  Here `chi` is
the ray-class Artin character of Example V.4.10. -/
theorem reciprocity_construction_principal
    (n : ℕ) [NeZero n]
    (L : Type v) [Field L] [NumberField L] [Algebra ℚ L]
    [IsCyclotomicExtension {n} ℚ L]
    [IsMulCommutative Gal(L/ℚ)]
    (psi : IdeleClassGroup (NumberField.RingOfIntegers ℚ) ℚ →*
      Gal(L/ℚ)) :
    TrivialPrincipalIdeles (NumberField.RingOfIntegers ℚ) ℚ
      Gal(L/ℚ) (ideleCharacterHom (K := ℚ) (G := Gal(L/ℚ)) psi) :=
  principalReciprocity (K := ℚ) (G := Gal(L/ℚ)) psi

/-- The literal ray-class specialization of the preceding cyclotomic
statement. -/
theorem cyclotomic_ray_reciprocity
    (n : ℕ) [NeZero n]
    (L : Type v) [Field L] [NumberField L] [Algebra ℚ L]
    [IsCyclotomicExtension {n} ℚ L]
    [IsMulCommutative Gal(L/ℚ)]
    (m : Modulus ℚ) (B : IdealMapBridge m)
    (hWA : WeakApproximation m)
    (chi : RayClassGroup ℚ m →* Gal(L/ℚ)) :
    TrivialPrincipalIdeles (NumberField.RingOfIntegers ℚ) ℚ
      Gal(L/ℚ) (rayCharacterHom (K := ℚ) (G := Gal(L/ℚ)) m B hWA chi) :=
  ray_principal_reciprocity (K := ℚ) (G := Gal(L/ℚ)) m B hWA chi

end

end Towers.CField.RExist
