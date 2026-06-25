import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Class Field Theory, Proposition II.1.25: arbitrary products

Group cohomology commutes with arbitrary products of modules.  The proof uses
the inhomogeneous cochain complex together with exactness of products of
modules.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits

universe u

variable (k G : Type u) [CommRing k] [Group G]

noncomputable instance rep_products_shape (ι : Type u) :
    HasProductsOfShape ι (Rep.{u} k G) := by
  letI : HasLimitsOfShape (Discrete ι) (Action (ModuleCat.{u} k) G) := inferInstance
  exact Adjunction.hasLimitsOfShape_of_equivalence
    ((Rep.repIsoAction k G).functor :
      Rep.{u} k G ⥤ Action (ModuleCat.{u} k) G)

set_option backward.isDefEq.respectTransparency false in
/-- Inhomogeneous cochains commute with arbitrary products of representations. -/
noncomputable instance cochains_functor_preserves
    {ι : Type u} (A : ι → Rep k G) :
    PreservesLimit (Discrete.functor A) (groupCohomology.cochainsFunctor k G) := by
  letI : PreservesLimit (Discrete.functor A) (forget (Rep k G)) := by
    change PreservesLimit (Discrete.functor A)
      (forget₂ (Rep k G) (ModuleCat k) ⋙ forget (ModuleCat k))
    infer_instance
  haveI : IsIso (piComparison (groupCohomology.cochainsFunctor k G) A) := by
    have component_isIso (n : ℕ) :
        IsIso ((piComparison (groupCohomology.cochainsFunctor k G) A).f n) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      let K : ι → CochainComplex (ModuleCat k) ℕ := fun i ↦
        (groupCohomology.cochainsFunctor k G).obj (A i)
      let B : ι → ModuleCat k := fun i ↦ (K i).X n
      let eB : (∏ᶜ K).X n ≅ ∏ᶜ B :=
        PreservesProduct.iso
          (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n)
          K
      let targetEquiv :
          (∏ᶜ K).X n ≃ ((i : ι) → B i) :=
        eB.toLinearEquiv.toEquiv.trans (Concrete.productEquiv B)
      have targetEquiv_apply
          (z : (∏ᶜ K).X n)
          (i : ι) :
          targetEquiv z i = ((Pi.π K i).f n) z := by
        change (Concrete.productEquiv B (eB.hom z)) i = _
        rw [Concrete.productEquiv_apply_apply]
        change (Pi.π B i) (eB.hom z) = _
        simpa [eB, PreservesProduct.iso_hom] using
          (elementwise_of% piComparison_comp_π
            (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n)
            K i) z
      have comparison_apply
          (z : (groupCohomology.inhomogeneousCochains (∏ᶜ A)).X n)
          (i : ι) (g : Fin n → G) :
          (targetEquiv
            (((piComparison (groupCohomology.cochainsFunctor k G) A).f n) z) i) g =
              Concrete.productEquiv A (z g) i := by
        rw [targetEquiv_apply]
        change ((((piComparison (groupCohomology.cochainsFunctor k G) A) ≫
          Pi.π K i).f n) z) g = _
        rw [piComparison_comp_π]
        rw [Concrete.productEquiv_apply_apply]
        rfl
      constructor
      · intro x y hxy
        apply funext
        intro g
        apply (Concrete.productEquiv A).injective
        apply funext
        intro i
        have hi := congrArg (fun z ↦ (targetEquiv z i) g) hxy
        simpa only [comparison_apply] using hi
      · intro y
        let x : (groupCohomology.inhomogeneousCochains (∏ᶜ A)).X n :=
          fun g ↦ (Concrete.productEquiv A).symm (fun i ↦ (targetEquiv y i) g)
        refine ⟨x, ?_⟩
        apply targetEquiv.injective
        apply funext
        intro i
        apply funext
        intro g
        rw [comparison_apply, Equiv.apply_symm_apply]
    letI (n : ℕ) : IsIso ((piComparison
        (groupCohomology.cochainsFunctor k G) A).f n) := component_isIso n
    exact HomologicalComplex.Hom.isIso_of_components _
  exact PreservesProduct.of_iso_comparison (groupCohomology.cochainsFunctor k G) A

set_option backward.isDefEq.respectTransparency false in
/-- Homology of complexes of modules commutes with arbitrary products. -/
noncomputable def homologyProductIso
    {ι : Type u} (K : ι → CochainComplex (ModuleCat k) ℕ) (n : ℕ) :
    (∏ᶜ K).homology n ≅ ∏ᶜ fun i ↦ (K i).homology n := by
  let X₁ : Discrete ι ⥤ ModuleCat k :=
    Discrete.functor fun i ↦ ((K i).sc n).X₁
  let X₂ : Discrete ι ⥤ ModuleCat k :=
    Discrete.functor fun i ↦ ((K i).sc n).X₂
  let X₃ : Discrete ι ⥤ ModuleCat k :=
    Discrete.functor fun i ↦ ((K i).sc n).X₃
  let f : X₁ ⟶ X₂ := Discrete.natTrans fun i ↦ ((K i.as).sc n).f
  let g : X₂ ⟶ X₃ := Discrete.natTrans fun i ↦ ((K i.as).sc n).g
  let S : ShortComplex (Discrete ι ⥤ ModuleCat k) :=
    ShortComplex.mk f g (by
      apply NatTrans.ext
      funext i
      change ((K i.as).sc n).f ≫ ((K i.as).sc n).g = 0
      exact ((K i.as).sc n).zero)
  let F : (Discrete ι ⥤ ModuleCat k) ⥤ ModuleCat k := lim
  let eExact : (S.map F).homology ≅ F.obj S.homology := S.mapHomologyIso F
  let ePoint : Discrete.functor (fun i ↦ (K i).homology n) ≅ S.homology :=
    Discrete.natIso fun i ↦ S.mapHomologyIso ((evaluation (Discrete ι) (ModuleCat k)).obj i)
  let e₁ : ((∏ᶜ K).sc n).X₁ ≅ (S.map F).X₁ :=
    PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ)
        ((ComplexShape.up ℕ).prev n)) K
  let e₂ : ((∏ᶜ K).sc n).X₂ ≅ (S.map F).X₂ :=
    PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n) K
  let e₃ : ((∏ᶜ K).sc n).X₃ ≅ (S.map F).X₃ :=
    PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ)
        ((ComplexShape.up ℕ).next n)) K
  let eS : (∏ᶜ K).sc n ≅ S.map F := ShortComplex.isoMk e₁ e₂ e₃
    (by
      apply Pi.hom_ext
      intro i
      simp only [e₁, e₂, S, F, f, X₁, X₂, ShortComplex.map_f,
        PreservesProduct.iso_hom, lim_map, HomologicalComplex.shortComplexFunctor_obj_X₁,
        HomologicalComplex.shortComplexFunctor_obj_X₂,
        HomologicalComplex.shortComplexFunctor_obj_f]
      rw [Category.assoc, limMap_π]
      change
        (piComparison
            (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ)
              ((ComplexShape.up ℕ).prev n)) K ≫
          Pi.π (fun b ↦ (HomologicalComplex.eval
            (ModuleCat k) (ComplexShape.up ℕ) ((ComplexShape.up ℕ).prev n)).obj (K b)) i) ≫
            (K i).d ((ComplexShape.up ℕ).prev n) n =
          (∏ᶜ K).d ((ComplexShape.up ℕ).prev n) n ≫
            piComparison
              (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n) K ≫
                Pi.π (fun b ↦ (HomologicalComplex.eval
                  (ModuleCat k) (ComplexShape.up ℕ) n).obj (K b)) i
      simpa only [piComparison_comp_π, Category.assoc] using (Pi.π K i).comm _ _)
    (by
      apply Pi.hom_ext
      intro i
      simp only [e₂, e₃, S, F, g, X₂, X₃, ShortComplex.map_g,
        PreservesProduct.iso_hom, lim_map, HomologicalComplex.shortComplexFunctor_obj_X₂,
        HomologicalComplex.shortComplexFunctor_obj_X₃,
        HomologicalComplex.shortComplexFunctor_obj_g]
      rw [Category.assoc, limMap_π]
      change
        (piComparison
            (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) n) K ≫
          Pi.π (fun b ↦ (HomologicalComplex.eval
            (ModuleCat k) (ComplexShape.up ℕ) n).obj (K b)) i) ≫
            (K i).d n ((ComplexShape.up ℕ).next n) =
          (∏ᶜ K).d n ((ComplexShape.up ℕ).next n) ≫
            piComparison
              (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ)
                ((ComplexShape.up ℕ).next n)) K ≫
                  Pi.π (fun b ↦ (HomologicalComplex.eval
                    (ModuleCat k) (ComplexShape.up ℕ) ((ComplexShape.up ℕ).next n)).obj (K b)) i
      simpa only [piComparison_comp_π, Category.assoc] using (Pi.π K i).comm _ _)
  exact (ShortComplex.homologyFunctor (ModuleCat k)).mapIso eS ≪≫ eExact ≪≫
    (HasLimit.isoOfNatIso ePoint).symm

/-- **Proposition II.1.25.** Group cohomology commutes with arbitrary products
of representations. -/
noncomputable def groupProductIso
    {ι : Type u} (A : ι → Rep k G) (n : ℕ) :
    groupCohomology (∏ᶜ A) n ≅ ∏ᶜ fun i ↦ groupCohomology (A i) n :=
  (HomologicalComplex.homologyFunctor
      (ModuleCat k) (ComplexShape.up ℕ) n).mapIso
        (PreservesProduct.iso (groupCohomology.cochainsFunctor k G) A) ≪≫
    homologyProductIso k
      (fun i ↦ groupCohomology.inhomogeneousCochains (A i)) n

end Submission.CField.COps
