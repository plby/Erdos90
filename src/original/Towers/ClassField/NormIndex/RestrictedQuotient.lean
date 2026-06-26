import Towers.ClassField.NormIndex.ClassCokernelComparison

/-!
# The restricted quotient in Theorem VII.4.3

If principal ideles together with `I_{L,T}` generate all ideles, inclusion of
`I_{L,T}` induces an equivariant isomorphism

`I_{L,T} / U(T) ≅ I_L / Lˣ`.

Both sides are the literal categorical cokernels used in the statement of
Theorem VII.4.3.
-/

namespace Towers.CField.NIndex

open CategoryTheory CategoryTheory.Limits
open IsDedekindDomain NumberField Representation
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HQuotie

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Inclusion of the restricted ideles, followed by the literal idèle-class
quotient map. -/
noncomputable def restrictedExplicitHom
    (S : Finset (NumberFieldPlace K)) :
    idelesRepresentation (K := K) (L := L) S ⟶
      explicitIdeleRepresentation (K := K) (L := L) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  letI := idelesDistribAction (K := K) (L := L) S
  letI := ideleDistribAction (K := K) (L := L)
  exact Rep.ofHom
    { toLinearMap :=
        (MonoidHom.toAdditive
          ((QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L)).comp
              (ICohomo.idelesAtPlaces
                (K := K) (L := L) S).subtype)).toIntLinearMap
      isIntertwining' := fun sigma ↦ by
        ext x
        rfl }

omit [FiniteDimensional K L] in
@[simp]
theorem restricted_explicit_hom
    (S : Finset (NumberFieldPlace K))
    (x : ICohomo.idelesAtPlaces (K := K) (L := L) S) :
    restrictedExplicitHom (K := K) (L := L) S
        (Additive.ofMul x) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L)
          (x : IdeleGroup (NumberField.RingOfIntegers L) L)) :=
  rfl

omit [FiniteDimensional K L] in
/-- The restricted diagonal is injective. -/
theorem restricted_principal_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (restrictedPrincipalHom (K := K) (L := L) S) := by
  intro x y hxy
  change Additive (unitsAtPlaces (K := K) (L := L) S) at x y
  apply Additive.toMul.injective
  apply Subtype.ext
  apply principalIdele_injective (NumberField.RingOfIntegers L) L
  exact congrArg
    (fun z : Additive
        (ICohomo.idelesAtPlaces (K := K) (L := L) S) ↦
      (z.toMul : IdeleGroup (NumberField.RingOfIntegers L) L)) hxy

omit [FiniteDimensional K L] in
private theorem restricted_principal_explicit
    (S : Finset (NumberFieldPlace K)) :
    restrictedPrincipalHom (K := K) (L := L) S ≫
        restrictedExplicitHom (K := K) (L := L) S = 0 := by
  ext x
  change Additive (unitsAtPlaces (K := K) (L := L) S) at x
  apply Additive.toMul.injective
  apply (QuotientGroup.eq_one_iff _).2
  exact ⟨(x.toMul : Lˣ), rfl⟩

/-- The map from the restricted categorical cokernel to the literal full
idèle-class quotient. -/
noncomputable def ideleCokernelExplicit
    (S : Finset (NumberFieldPlace K)) :
    restrictedIdeleRepresentation (K := K) (L := L) S ⟶
      explicitIdeleRepresentation (K := K) (L := L) :=
  cokernel.desc
    (restrictedPrincipalHom (K := K) (L := L) S)
    (restrictedExplicitHom (K := K) (L := L) S)
    (restricted_principal_explicit (K := K) (L := L) S)

omit [FiniteDimensional K L] in
@[simp]
theorem restricted_cokernel_quotient
    (S : Finset (NumberFieldPlace K))
    (x : ICohomo.idelesAtPlaces (K := K) (L := L) S) :
    ideleCokernelExplicit (K := K) (L := L) S
        (cokernel.π
          (restrictedPrincipalHom (K := K) (L := L) S)
          (Additive.ofMul x)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L)
          (x : IdeleGroup (NumberField.RingOfIntegers L) L)) := by
  change
    ((cokernel.π (restrictedPrincipalHom (K := K) (L := L) S) ≫
      ideleCokernelExplicit (K := K) (L := L) S)
        (Additive.ofMul x)) = _
  rw [ideleCokernelExplicit, cokernel.π_desc]
  rfl

omit [FiniteDimensional K L] in
private theorem restricted_cokernel_explicit
    (S : Finset (NumberFieldPlace K))
    (hgenerate : GeneratesIdelesPrincipal (K := K) (L := L) S) :
    Function.Surjective
      (ideleCokernelExplicit (K := K) (L := L) S) := by
  intro c
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (NumberField.RingOfIntegers L) L) c.toMul
  have hxgenerate : x ∈
      principalIdeles (NumberField.RingOfIntegers L) L ⊔
        ICohomo.idelesAtPlaces (K := K) (L := L) S := by
    rw [hgenerate]
    trivial
  obtain ⟨p, hp, y, hy, hpy⟩ := Subgroup.mem_sup.mp hxgenerate
  let y' : ICohomo.idelesAtPlaces (K := K) (L := L) S := ⟨y, hy⟩
  refine ⟨cokernel.π
      (restrictedPrincipalHom (K := K) (L := L) S)
      (Additive.ofMul y'), ?_⟩
  rw [restricted_cokernel_quotient]
  apply Additive.toMul.injective
  change QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers L) L) y = c.toMul
  rw [← hx]
  calc
    QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers L) L) y =
        1 * QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) y :=
      (one_mul _).symm
    _ = QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) p *
        QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) y := by
      exact congrArg
        (fun z ↦ z * QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) y)
        ((QuotientGroup.eq_one_iff p).2 hp).symm
    _ = QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) (p * y) :=
      (map_mul _ _ _).symm
    _ = QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x := by
      rw [hpy]

omit [FiniteDimensional K L] in
private theorem restricted_cokernel_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (ideleCokernelExplicit (K := K) (L := L) S) := by
  intro z z' hzz'
  obtain ⟨x, rfl⟩ :=
    (Rep.epi_iff_surjective
      (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))).1
      (inferInstance : Epi
        (cokernel.π
          (restrictedPrincipalHom (K := K) (L := L) S))) z
  obtain ⟨y, rfl⟩ :=
    (Rep.epi_iff_surjective
      (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))).1
      (inferInstance : Epi
        (cokernel.π
          (restrictedPrincipalHom (K := K) (L := L) S))) z'
  change Additive
    (ICohomo.idelesAtPlaces (K := K) (L := L) S) at x y
  have hxq := restricted_cokernel_quotient
    (K := K) (L := L) S x.toMul
  have hyq := restricted_cokernel_quotient
    (K := K) (L := L) S y.toMul
  change ideleCokernelExplicit (K := K) (L := L) S
      ((Rep.Hom.hom (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))) x) =
    ideleCokernelExplicit (K := K) (L := L) S
      ((Rep.Hom.hom (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))) y) at hzz'
  change ideleCokernelExplicit (K := K) (L := L) S
      ((Rep.Hom.hom (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))) x) = _ at hxq
  change ideleCokernelExplicit (K := K) (L := L) S
      ((Rep.Hom.hom (cokernel.π
        (restrictedPrincipalHom (K := K) (L := L) S))) y) = _ at hyq
  rw [hxq, hyq] at hzz'
  have hxy :
      ((x.toMul : ICohomo.idelesAtPlaces (K := K) (L := L) S) :
          IdeleGroup (NumberField.RingOfIntegers L) L) /
        ((y.toMul : ICohomo.idelesAtPlaces (K := K) (L := L) S) :
          IdeleGroup (NumberField.RingOfIntegers L) L) ∈
      principalIdeles (NumberField.RingOfIntegers L) L :=
    QuotientGroup.eq_iff_div_mem.mp
      (Additive.ofMul.injective hzz')
  obtain ⟨a, ha⟩ := hxy
  have haRestricted :
      principalIdele (NumberField.RingOfIntegers L) L a ∈
        ICohomo.idelesAtPlaces (K := K) (L := L) S := by
    rw [ha]
    exact (ICohomo.idelesAtPlaces (K := K) (L := L) S).div_mem
      x.toMul.property y.toMul.property
  let a' : unitsAtPlaces (K := K) (L := L) S :=
    ⟨a, (principal_ideles_places
      (K := K) (L := L) S a).1 haRestricted⟩
  have hsub : x - y =
      restrictedPrincipalHom (K := K) (L := L) S
        (Additive.ofMul a') := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact ha.symm
  apply sub_eq_zero.mp
  rw [← map_sub]
  change (Rep.Hom.hom (cokernel.π
    (restrictedPrincipalHom (K := K) (L := L) S))) (x - y) = 0
  rw [hsub]
  exact congrArg
    (fun f ↦ f (Additive.ofMul a'))
    (cokernel.condition
      (restrictedPrincipalHom (K := K) (L := L) S))

/-- Under the generation hypothesis, the restricted cokernel is the literal
full idèle-class representation. -/
noncomputable def restrictedCokernelExplicit
    (S : Finset (NumberFieldPlace K))
    (hgenerate : GeneratesIdelesPrincipal (K := K) (L := L) S) :
    restrictedIdeleRepresentation (K := K) (L := L) S ≅
      explicitIdeleRepresentation (K := K) (L := L) := by
  let f := ideleCokernelExplicit (K := K) (L := L) S
  letI : Mono f := (Rep.mono_iff_injective f).2
    (restricted_cokernel_injective
      (K := K) (L := L) S)
  letI : Epi f := (Rep.epi_iff_surjective f).2
    (restricted_cokernel_explicit
      (K := K) (L := L) S hgenerate)
  letI : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

/-- The quotient-comparison bridge in Theorem VII.4.3 is unconditional. -/
theorem restrictedQuotientBridge :
    RestrictedQuotientBridge.{u} := by
  intro K L _ _ _ _ _ _ _ S hgenerate
  exact ⟨(restrictedCokernelExplicit
      (K := K) (L := L) S hgenerate) ≪≫
    (cokernelIsoExplicit (K := K) (L := L)).symm⟩

end

end Towers.CField.NIndex
