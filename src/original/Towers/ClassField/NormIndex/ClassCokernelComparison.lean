import Towers.ClassField.NormIndex.PrincipalIdelesSmul
import Towers.ClassField.NormIndex.UnitsPlacesIdeles

/-!
# The categorical idèle-class cokernel is the concrete quotient

The idèle-class representation used in Theorem VII.4.3 is defined as the
categorical cokernel of `Lˣ → I_L`.  This file identifies it, equivariantly,
with the representation on the literal quotient `C_L = I_L/Lˣ`.  In
particular, later Tate-cohomology calculations can use the concrete quotient
and its concrete Galois action without postulating a comparison.
-/

namespace Towers.CField.NIndex

open CategoryTheory CategoryTheory.Limits
open IsDedekindDomain NumberField Representation
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The representation carried by the literal quotient idèle class group. -/
@[reducible]
noncomputable def explicitIdeleRepresentation : Rep ℤ Gal(L/K) := by
  letI := ideleDistribAction (K := K) (L := L)
  exact Rep.ofMulDistribMulAction Gal(L/K)
    (IdeleClassGroup (NumberField.RingOfIntegers L) L)

/-- The literal quotient map `I_L → C_L`, as an equivariant morphism. -/
noncomputable def ideleExplicitHom :
    (concreteActionData (K := K) (L := L)).representation ⟶
      explicitIdeleRepresentation (K := K) (L := L) := by
  letI := idelesGaloisAction (K := K) (L := L)
  letI := ideleDistribAction (K := K) (L := L)
  exact Rep.ofHom
    { toLinearMap :=
        (MonoidHom.toAdditive
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L))).toIntLinearMap
      isIntertwining' := fun sigma ↦ by
        ext x
        rfl }

omit [FiniteDimensional K L] in
@[simp]
theorem idele_explicit_hom
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    ideleExplicitHom (K := K) (L := L) (Additive.ofMul x) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x) :=
  rfl

omit [FiniteDimensional K L] in
private theorem principal_comp_explicit :
    (concreteActionData (K := K) (L := L)).principalIdeleHom ≫
        ideleExplicitHom (K := K) (L := L) = 0 := by
  ext x
  apply Additive.toMul.injective
  exact (QuotientGroup.eq_one_iff _).2 ⟨x.toMul, rfl⟩

/-- The map from the categorical cokernel to the literal quotient. -/
noncomputable def classCokernelExplicit :
    classCokernelRepresentation (K := K) (L := L) ⟶
      explicitIdeleRepresentation (K := K) (L := L) :=
  cokernel.desc
    (concreteActionData (K := K) (L := L)).principalIdeleHom
    (ideleExplicitHom (K := K) (L := L))
    (principal_comp_explicit (K := K) (L := L))

omit [FiniteDimensional K L] in
@[simp]
theorem cokernel_quotient_apply
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    classCokernelExplicit (K := K) (L := L)
        (cokernel.π
          (concreteActionData (K := K) (L := L)).principalIdeleHom
          (Additive.ofMul x)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x) := by
  change
    ((cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom ≫
      classCokernelExplicit (K := K) (L := L)) (Additive.ofMul x)) = _
  rw [classCokernelExplicit, cokernel.π_desc]
  rfl

omit [FiniteDimensional K L] in
private theorem cokernel_explicit_surjective :
    Function.Surjective
      (classCokernelExplicit (K := K) (L := L)) := by
  intro c
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (NumberField.RingOfIntegers L) L) c.toMul
  refine ⟨cokernel.π
      (concreteActionData (K := K) (L := L)).principalIdeleHom
      (Additive.ofMul x), ?_⟩
  rw [cokernel_quotient_apply]
  exact congrArg Additive.ofMul hx

omit [FiniteDimensional K L] in
private theorem cokernel_explicit_injective :
    Function.Injective
      (classCokernelExplicit (K := K) (L := L)) := by
  intro z z' hzz'
  obtain ⟨x, rfl⟩ :=
    (Rep.epi_iff_surjective
      (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)).1
      (inferInstance : Epi
        (cokernel.π
          (concreteActionData (K := K) (L := L)).principalIdeleHom)) z
  obtain ⟨y, rfl⟩ :=
    (Rep.epi_iff_surjective
      (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)).1
      (inferInstance : Epi
        (cokernel.π
          (concreteActionData (K := K) (L := L)).principalIdeleHom)) z'
  have hxq := cokernel_quotient_apply (K := K) (L := L) x.toMul
  have hyq := cokernel_quotient_apply (K := K) (L := L) y.toMul
  change classCokernelExplicit (K := K) (L := L)
      ((Rep.Hom.hom (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)) x) =
    classCokernelExplicit (K := K) (L := L)
      ((Rep.Hom.hom (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)) y) at hzz'
  change classCokernelExplicit (K := K) (L := L)
      ((Rep.Hom.hom (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)) x) = _ at hxq
  change classCokernelExplicit (K := K) (L := L)
      ((Rep.Hom.hom (cokernel.π
        (concreteActionData (K := K) (L := L)).principalIdeleHom)) y) = _ at hyq
  rw [hxq, hyq] at hzz'
  have hxy :
      (Additive.toMul x : IdeleGroup (NumberField.RingOfIntegers L) L) /
          (Additive.toMul y : IdeleGroup (NumberField.RingOfIntegers L) L) ∈
      principalIdeles (NumberField.RingOfIntegers L) L :=
    QuotientGroup.eq_iff_div_mem.mp
      (Additive.ofMul.injective hzz')
  obtain ⟨a, ha⟩ := hxy
  have hsub : x - y =
      (concreteActionData (K := K) (L := L)).principalIdeleHom
        (Additive.ofMul a) := by
    apply Additive.toMul.injective
    exact ha.symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  change (Rep.Hom.hom (cokernel.π
    (concreteActionData (K := K) (L := L)).principalIdeleHom))
      (x - y) = 0
  rw [hsub]
  exact congrArg
    (fun f ↦ f (Additive.ofMul a))
    (cokernel.condition
      (concreteActionData (K := K) (L := L)).principalIdeleHom)

/-- The categorical cokernel representation in Theorem VII.4.3 is
equivariantly isomorphic to the representation on the literal idèle-class
quotient. -/
noncomputable def cokernelIsoExplicit :
    classCokernelRepresentation (K := K) (L := L) ≅
      explicitIdeleRepresentation (K := K) (L := L) := by
  let f := classCokernelExplicit (K := K) (L := L)
  letI : Mono f := (Rep.mono_iff_injective f).2
    (cokernel_explicit_injective (K := K) (L := L))
  letI : Epi f := (Rep.epi_iff_surjective f).2
    (cokernel_explicit_surjective (K := K) (L := L))
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

end

end Towers.CField.NIndex
