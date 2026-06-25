import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Milne, Class Field Theory, Remark II.3.12: Tor examples

This file supplies kernel-checked proofs of the two torsion-free examples in
Remark II.3.12.  In either tensor variable, torsion-freeness over `ℤ` implies
the vanishing of the first integral Tor group.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

/-- The first integral Tor group of two underlying module objects vanishes. -/
private def CatTorVanishes (M C : ModuleCat.{0} ℤ) : Prop :=
  IsZero ((((CategoryTheory.Tor (ModuleCat.{0} ℤ) 1).obj M).obj C))

/-- Flatness of the left factor kills the first categorical Tor. -/
private theorem cat_tor_flat
    (M C : ModuleCat.{0} ℤ) [Module.Flat ℤ M] :
    CatTorVanishes M C := by
  let F := (tensoringLeft (ModuleCat.{0} ℤ)).obj M
  let P := projectiveResolution C
  change IsZero ((F.leftDerived 1).obj C)
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F 1)
  change IsZero
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology 1)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.exactAt_iff'
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
      2 1 0 (by simp) (by simp)).2
  exact (P.exact_succ 0).map F

universe u

variable {R : Type u} [CommRing R]

/-- Flatness of the right factor also kills the first categorical Tor. -/
private theorem cat_tor_vanishes
    (M C : ModuleCat.{u} R) [Module.Flat R C] :
    IsZero ((((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj M).obj C)) := by
  let F := (tensoringLeft (ModuleCat.{u} R)).obj M
  let P := projectiveResolution C
  change IsZero ((F.leftDerived 1).obj C)
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F 1)
  change IsZero
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology 1)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply (HomologicalComplex.exactAt_iff'
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
      2 1 0 (by simp) (by simp)).2
  let d₂ : P.complex.X 2 →ₗ[R] P.complex.X 1 := (P.complex.d 2 1).hom
  let d₁ : P.complex.X 1 →ₗ[R] P.complex.X 0 := (P.complex.d 1 0).hom
  let π : P.complex.X 0 →ₗ[R] C := (P.π.f 0).hom
  let q := d₁.rangeRestrict
  let i := (LinearMap.range d₁).subtype
  have hqsurj : Function.Surjective q := by
    rw [← LinearMap.range_eq_top, LinearMap.range_rangeRestrict]
  have hexact₂q : Function.Exact d₂ q := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact (P.exact_succ 0).moduleCat_range_eq_ker.symm
  have hexactiq : Function.Exact i π := by
    rw [LinearMap.exact_iff]
    simpa [i] using (P.exact₀.moduleCat_range_eq_ker).symm
  have hπsurj : Function.Surjective π := by
    letI : Epi (P.π.f 0) := Cofork.IsColimit.epi P.isColimitCokernelCofork
    exact (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hiT : Function.Injective (LinearMap.lTensor M i) :=
    LinearMap.lTensor_injective_of_exact_of_flat π hπsurj i
      (Submodule.injective_subtype _) hexactiq M
  have hexactTq : Function.Exact
      (LinearMap.lTensor M d₂) (LinearMap.lTensor M q) :=
    lTensor_exact M hexact₂q hqsurj
  have hfactor : d₁ = i.comp q := rfl
  have hcomp : LinearMap.lTensor M d₁ =
      (LinearMap.lTensor M i).comp (LinearMap.lTensor M q) :=
    (congrArg (LinearMap.lTensor M) hfactor).trans
      (LinearMap.lTensor_comp M i q)
  have hexactT : Function.Exact
      (LinearMap.lTensor M d₂) (LinearMap.lTensor M d₁) := by
    rw [LinearMap.exact_iff] at hexactTq ⊢
    rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot]
    · exact hexactTq
    · exact LinearMap.ker_eq_bot.mpr hiT
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  change LinearMap.range (LinearMap.lTensor M d₂) =
    LinearMap.ker (LinearMap.lTensor M d₁)
  exact (LinearMap.exact_iff.mp hexactT).symm

/-- First torsion-free example in Remark II.3.12: if the left underlying
abelian group is torsion-free, then `Tor₁ᴢ(M,C)=0`. -/
theorem tor_torsion_proved
    {G : Type} [Group G] (M C : Rep ℤ G)
    [Module.IsTorsionFree ℤ M] :
    IsZero ((((CategoryTheory.Tor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ C))) := by
  letI : Module.Flat ℤ (ModuleCat.of ℤ M) := inferInstance
  exact cat_tor_flat
    (ModuleCat.of ℤ M) (ModuleCat.of ℤ C)

/-- Second torsion-free example in Remark II.3.12: if the right underlying
abelian group is torsion-free, then `Tor₁ᴢ(M,C)=0`. -/
theorem tor_vanishes_proved
    {G : Type} [Group G] (M C : Rep ℤ G)
    [Module.IsTorsionFree ℤ C] :
    IsZero ((((CategoryTheory.Tor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ C))) := by
  letI : Module.Flat ℤ (ModuleCat.of ℤ C) := inferInstance
  exact cat_tor_vanishes
    (ModuleCat.of ℤ M) (ModuleCat.of ℤ C)

end

end Towers.CField.Shifting
