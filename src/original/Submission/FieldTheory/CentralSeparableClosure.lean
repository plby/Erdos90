import Submission.FieldTheory.CentralEmbeddingKummer

/-!
# Transporting central embedding solutions to a fixed separable closure

Finite Galois realizations constructed by Kummer theory are initially
abstract field extensions.  This file embeds them into the fixed separable
closure, preserving a chosen embedding of an intermediate coefficient field.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Submission.CField.LBrauer

universe u v w x

variable {K : Type u} {L : Type v} {N : Type w}
  [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra K N] [Algebra L N]
  [IsScalarTower K L N]

/-- A separable extension of `L` embeds into the fixed separable closure of
`K` through any prescribed `K`-embedding of `L`. -/
theorem separable_embedding_extends
    [Algebra.IsSeparable L N]
    (j : L →ₐ[K] SeparableClosure K) :
    ∃ i : N →ₐ[K] SeparableClosure K, i.restrictDomain L = j :=
  IsSepClosed.surjective_restrictDomain_of_isSeparable
    (M := SeparableClosure K) L j

/-- The range restriction of a field embedding, regarded as an equivalence
onto its intermediate-field range. -/
noncomputable def algFieldRange
    (i : N →ₐ[K] SeparableClosure K) :
    N ≃ₐ[K] i.fieldRange := by
  let f : N →ₐ[K] i.fieldRange :=
    { toFun := fun x =>
        ⟨i x, (AlgHom.mem_fieldRange (f := i)).2 ⟨x, rfl⟩⟩
      map_one' := by apply Subtype.ext; exact map_one i
      map_mul' := by intro x y; apply Subtype.ext; exact map_mul i x y
      map_zero' := by apply Subtype.ext; exact map_zero i
      map_add' := by intro x y; apply Subtype.ext; exact map_add i x y
      commutes' := by intro x; apply Subtype.ext; exact i.commutes x }
  apply AlgEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply i.injective
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := i)).1 y.property
    exact ⟨x, Subtype.ext hx⟩

@[simp]
theorem alg_field_range
    (i : N →ₐ[K] SeparableClosure K) (x : N) :
    ((algFieldRange i x : i.fieldRange) : SeparableClosure K) = i x :=
  by simp [algFieldRange]

/-- The image of a finite Galois extension in the fixed separable closure is
a finite Galois intermediate field. -/
noncomputable def galoisFieldRange
    [FiniteDimensional K N] [IsGalois K N]
    (i : N →ₐ[K] SeparableClosure K) :
    FiniteGaloisIntermediateField K (SeparableClosure K) := by
  let e := algFieldRange i
  letI : FiniteDimensional K i.fieldRange := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K i.fieldRange := IsGalois.of_algEquiv e
  exact ⟨i.fieldRange⟩

@[simp]
theorem galois_range_intermediate
    [FiniteDimensional K N] [IsGalois K N]
    (i : N →ₐ[K] SeparableClosure K) :
    (galoisFieldRange i).toIntermediateField = i.fieldRange :=
  rfl

/-- An abstract finite Galois extension can be placed in the fixed separable
closure while preserving a chosen embedding of an intermediate field. -/
theorem galois_range_extends
    [FiniteDimensional K N] [IsGalois K N]
    (j : L →ₐ[K] SeparableClosure K) :
    ∃ (i : N →ₐ[K] SeparableClosure K)
        (E : FiniteGaloisIntermediateField K (SeparableClosure K)),
      i.restrictDomain L = j ∧
        E.toIntermediateField = i.fieldRange := by
  letI : Algebra.IsSeparable L N :=
    Algebra.isSeparable_tower_top_of_isSeparable (L := L) K N
  obtain ⟨i, hi⟩ :=
    separable_embedding_extends (N := N) j
  exact ⟨i, galoisFieldRange i, hi, rfl⟩

/-- The image of the prescribed coefficient-field embedding lies in the image
of any extending top-field embedding. -/
theorem range_restrict_domain
    (i : N →ₐ[K] SeparableClosure K)
    (j : L →ₐ[K] SeparableClosure K)
    (hi : i.restrictDomain L = j) :
    j.fieldRange ≤ i.fieldRange := by
  intro x hx
  obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange (f := j)).1 hx
  apply (AlgHom.mem_fieldRange (f := i)).2
  refine ⟨algebraMap L N y, ?_⟩
  have hiy := DFunLike.congr_fun hi y
  exact hiy.trans hy

/-- The inclusion between the two image fields agrees with the original
scalar-tower inclusion under the field-range equivalences. -/
theorem range_inclusion_alg
    (i : N →ₐ[K] SeparableClosure K)
    (j : L →ₐ[K] SeparableClosure K)
    (hi : i.restrictDomain L = j) (y : L) :
    IntermediateField.inclusion
        (range_restrict_domain i j hi)
        (algFieldRange j y) =
      algFieldRange i (algebraMap L N y) := by
  apply Subtype.ext
  change j y = i (algebraMap L N y)
  exact (DFunLike.congr_fun hi y).symm

set_option synthInstance.maxHeartbeats 200000 in
-- Restriction through two nested field ranges unfolds several scalar towers.
/-- Transport by field-range equivalences commutes with Galois restriction. -/
theorem restriction_aut_congr
    [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K N] [IsGalois K N]
    (i : N →ₐ[K] SeparableClosure K)
    (j : L →ₐ[K] SeparableClosure K)
    (hi : i.restrictDomain L = j)
    (sigma : Gal(N/K)) (tau : Gal(L/K))
    (hbase : ∀ y : L,
      sigma (algebraMap L N y) = algebraMap L N (tau y)) :
    galoisRestrictionHom K
        (F := galoisFieldRange j)
        (E := galoisFieldRange i)
        (range_restrict_domain i j hi)
        ((algFieldRange i).autCongr sigma) =
      (algFieldRange j).autCongr tau := by
  let hFE : galoisFieldRange j ≤ galoisFieldRange i :=
    range_restrict_domain i j hi
  apply AlgEquiv.ext
  intro x
  change (galoisRestrictionHom K hFE
      ((algFieldRange i).autCongr sigma)) x =
    ((algFieldRange j).autCongr tau) x
  apply (IntermediateField.inclusion hFE).injective
  refine (galois_restriction_hom K hFE
    ((algFieldRange i).autCongr sigma) x).trans ?_
  obtain ⟨y, rfl⟩ := (algFieldRange j).surjective x
  have hinclusion (z : L) :
      IntermediateField.inclusion hFE (algFieldRange j z) =
        algFieldRange i (algebraMap L N z) :=
    range_inclusion_alg i j hi z
  have hbottom :
      (algFieldRange j).autCongr tau (algFieldRange j y) =
        algFieldRange j (tau y) := by
    simp [AlgEquiv.autCongr_apply]
  calc
    (algFieldRange i).autCongr sigma
          (IntermediateField.inclusion hFE (algFieldRange j y)) =
        (algFieldRange i).autCongr sigma
          (algFieldRange i (algebraMap L N y)) := by rw [hinclusion]
    _ = algFieldRange i (sigma (algebraMap L N y)) := by
      simp [AlgEquiv.autCongr_apply]
    _ = algFieldRange i (algebraMap L N (tau y)) := by rw [hbase]
    _ = IntermediateField.inclusion hFE
          (algFieldRange j (tau y)) := (hinclusion (tau y)).symm
    _ = IntermediateField.inclusion hFE
          ((algFieldRange j).autCongr tau
            (algFieldRange j y)) := by rw [hbottom]

set_option synthInstance.maxHeartbeats 200000 in
-- The nested subtype fields require explicit restriction and inclusion towers.
/-- Restriction from the absolute Galois group to a bundled finite Galois
intermediate field. -/
noncomputable def absoluteRestrictionHom
    (F : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Gal(SeparableClosure K/K) →* Gal(F/K) := by
  letI : Algebra F (SeparableClosure K) := F.toIntermediateField.toAlgebra
  letI : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal K F := IsGalois.to_normal
  exact AlgEquiv.restrictNormalHom F

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- Finite-level restriction followed by absolute restriction is absolute
restriction directly to the smaller finite Galois field. -/
theorem galois_restriction_absolute
    {F E : FiniteGaloisIntermediateField K (SeparableClosure K)}
    (hFE : F ≤ E) (sigma : Gal(SeparableClosure K/K)) :
    galoisRestrictionHom K hFE
        (absoluteRestrictionHom (K := K) E sigma) =
      absoluteRestrictionHom (K := K) F sigma := by
  letI : Algebra E (SeparableClosure K) := E.toIntermediateField.toAlgebra
  letI : Algebra F (SeparableClosure K) := F.toIntermediateField.toAlgebra
  letI : IsScalarTower K E (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal K E := IsGalois.to_normal
  letI : Normal K F := IsGalois.to_normal
  change galoisRestrictionHom K hFE
      (AlgEquiv.restrictNormalHom E sigma) =
    AlgEquiv.restrictNormalHom F sigma
  apply AlgEquiv.ext
  intro x
  apply (IntermediateField.inclusion hFE).injective
  refine (galois_restriction_hom K hFE
    (AlgEquiv.restrictNormalHom E sigma) x).trans ?_
  apply Subtype.ext
  calc
    ((AlgEquiv.restrictNormalHom E sigma
        (IntermediateField.inclusion hFE x) : E) : SeparableClosure K) =
        sigma ((IntermediateField.inclusion hFE x : E) : SeparableClosure K) :=
      AlgEquiv.restrictNormalHom_apply E sigma
        (IntermediateField.inclusion hFE x)
    _ = sigma (x : SeparableClosure K) := rfl
    _ = ((AlgEquiv.restrictNormalHom F sigma x : F) : SeparableClosure K) :=
      (AlgEquiv.restrictNormalHom_apply F sigma x).symm
    _ = ((IntermediateField.inclusion hFE
        (AlgEquiv.restrictNormalHom F sigma x) : E) : SeparableClosure K) := rfl

set_option synthInstance.maxHeartbeats 300000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- An abstract finite Galois weak solution can be transported to a finite
Galois intermediate field of the fixed separable closure. -/
theorem weak_solution_separable
    {Q G : Type*} [Group Q] [Group G]
    [FiniteDimensional K L] [IsGalois K L]
    [FiniteDimensional K N] [IsGalois K N]
    (j : L →ₐ[K] SeparableClosure K)
    (q : Q →* G)
    (galoisEquiv : Gal(L/K) ≃* G)
    (lift : Gal(N/K) →* Q)
    (baseHom : Gal(N/K) →* Gal(L/K))
    (hlift : q.comp lift = galoisEquiv.toMonoidHom.comp baseHom)
    (hbase : ∀ sigma : Gal(N/K), ∀ y : L,
      sigma (algebraMap L N y) = algebraMap L N (baseHom sigma y)) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (hFE : galoisFieldRange j ≤ E)
        (liftE : Gal(E/K) →* Q),
      q.comp liftE =
        galoisEquiv.toMonoidHom.comp
          ((algFieldRange j).autCongr.symm.toMonoidHom.comp
            (galoisRestrictionHom K hFE)) := by
  letI : Algebra.IsSeparable L N :=
    Algebra.isSeparable_tower_top_of_isSeparable (L := L) K N
  obtain ⟨i, hi⟩ :=
    separable_embedding_extends (N := N) j
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    galoisFieldRange i
  let hFE : galoisFieldRange j ≤ E :=
    range_restrict_domain i j hi
  let liftE : Gal(E/K) →* Q :=
    lift.comp (algFieldRange i).autCongr.symm.toMonoidHom
  refine ⟨E, hFE, liftE, ?_⟩
  ext rho
  let sigma : Gal(N/K) := (algFieldRange i).autCongr.symm rho
  have hrestriction :=
    restriction_aut_congr i j hi sigma
      (baseHom sigma) (hbase sigma)
  have hsigma : (algFieldRange i).autCongr sigma = rho :=
    (algFieldRange i).autCongr.apply_symm_apply rho
  rw [hsigma] at hrestriction
  have hrestriction' :
      galoisRestrictionHom K hFE rho =
        (algFieldRange j).autCongr (baseHom sigma) := by
    simpa [E, hFE, sigma] using hrestriction
  have hbaseEq :
      (algFieldRange j).autCongr.symm
          (galoisRestrictionHom K hFE rho) =
        baseHom sigma := by
    rw [hrestriction']
    exact (algFieldRange j).autCongr.symm_apply_apply (baseHom sigma)
  have hliftAt := DFunLike.congr_fun hlift sigma
  change q (lift sigma) =
    galoisEquiv
      ((algFieldRange j).autCongr.symm
        (galoisRestrictionHom K hFE rho))
  rw [hbaseEq]
  exact hliftAt

set_option synthInstance.maxHeartbeats 500000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- Vanishing of a central cubic obstruction produces a weak solution over a
finite Galois subfield of the fixed separable closure. -/
theorem cubic_weak_solution
    {K₀ L₀ : Type u} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    {Q : Type v} {G : Type x} [Group Q] [Finite Q] [Group G] [Finite G]
    [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
    (j : L₀ →ₐ[K₀] SeparableClosure K₀)
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (hkernelCard : Nat.card q.ker = 3)
    (galoisEquiv : Gal(L₀/K₀) ≃* G)
    (kernelToUnits : q.ker →* L₀ˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L₀/K₀), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (zeta : L₀) (hzeta : IsPrimitiveRoot zeta 3)
    (hzero : centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1) :
    ∃ (E : FiniteGaloisIntermediateField K₀ (SeparableClosure K₀))
        (hFE : galoisFieldRange j ≤ E)
        (liftE : Gal(E/K₀) →* Q),
      q.comp liftE =
        galoisEquiv.toMonoidHom.comp
          ((algFieldRange j).autCongr.symm.toMonoidHom.comp
            (galoisRestrictionHom K₀ hFE)) := by
  rcases central_kummer_solution
      q hq hcentral hkernelCard galoisEquiv kernelToUnits
      hkernelToUnits hfixed hkernel zeta hzeta hzero with
    ⟨lift, hlift⟩ | ⟨b, a, hb, hradical, hirr, hGal, hbij⟩
  · apply weak_solution_separable
      (N := L₀) j q galoisEquiv lift (MonoidHom.id Gal(L₀/K₀))
    · simpa using hlift
    · intro sigma y
      simp
  · letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
    letI : IsGalois K₀ (CubicKummerAdjoin a) := hGal
    obtain ⟨lift, baseHom, hlift, hbase⟩ :=
      bijective_weak_solution
        q hq hcentral galoisEquiv kernelToUnits hfixed hkernel
        b hb a hradical hirr hbij
    exact weak_solution_separable
      j q galoisEquiv lift baseHom hlift hbase

set_option synthInstance.maxHeartbeats 500000 in
-- Restriction through the two nested finite subfields unfolds several towers.
/-- Vanishing of a central cubic obstruction produces a weak solution on the
absolute Galois group, with the prescribed finite quotient as its base map. -/
theorem absolute_weak_solution
    {K₀ L₀ : Type u} [Field K₀] [Field L₀] [Algebra K₀ L₀]
    {Q : Type v} {G : Type x} [Group Q] [Finite Q] [Group G] [Finite G]
    [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀]
    (j : L₀ →ₐ[K₀] SeparableClosure K₀)
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (hkernelCard : Nat.card q.ker = 3)
    (galoisEquiv : Gal(L₀/K₀) ≃* G)
    (kernelToUnits : q.ker →* L₀ˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L₀/K₀), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (zeta : L₀) (hzeta : IsPrimitiveRoot zeta 3)
    (hzero : centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1) :
    ∃ liftAbs : Gal(SeparableClosure K₀/K₀) →* Q,
      q.comp liftAbs =
        galoisEquiv.toMonoidHom.comp
          ((algFieldRange j).autCongr.symm.toMonoidHom.comp
            (absoluteRestrictionHom (K := K₀)
              (galoisFieldRange j))) := by
  obtain ⟨E, hFE, liftE, hliftE⟩ :=
    cubic_weak_solution j q hq hcentral hkernelCard
      galoisEquiv kernelToUnits hkernelToUnits hfixed hkernel
      zeta hzeta hzero
  let liftAbs : Gal(SeparableClosure K₀/K₀) →* Q :=
    liftE.comp (absoluteRestrictionHom (K := K₀) E)
  refine ⟨liftAbs, ?_⟩
  ext sigma
  have hliftAt := DFunLike.congr_fun hliftE
    (absoluteRestrictionHom (K := K₀) E sigma)
  change q (liftE (absoluteRestrictionHom (K := K₀) E sigma)) =
    galoisEquiv
      ((algFieldRange j).autCongr.symm
        (galoisRestrictionHom K₀ hFE
          (absoluteRestrictionHom (K := K₀) E sigma))) at hliftAt
  change q (liftE (absoluteRestrictionHom (K := K₀) E sigma)) =
    galoisEquiv
      ((algFieldRange j).autCongr.symm
        (absoluteRestrictionHom (K := K₀)
          (galoisFieldRange j) sigma))
  rw [galois_restriction_absolute (K := K₀) hFE] at hliftAt
  exact hliftAt

end TBluepr
end Submission
