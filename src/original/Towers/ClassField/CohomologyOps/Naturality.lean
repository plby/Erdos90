import Towers.ClassField.CohomologyOps.CastCompSymm
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open scoped MonoidalCategory

variable {G : Type} [Group G]

theorem i_cocycles_id {A B : Rep ℤ G} (f : A ⟶ B) (n : ℕ)
    (x : groupCohomology.cocycles A n) :
    groupCohomology.iCocycles B n
        (groupCohomology.cocyclesMap (MonoidHom.id G) f n x) =
      fun g => f (groupCohomology.iCocycles A n x g) := by
  have h := congrArg (fun q => q x)
    (HomologicalComplex.cyclesMap_i
      (groupCohomology.cochainsMap (MonoidHom.id G) f) n)
  simpa only [ConcreteCategory.comp_apply,
    groupCohomology.cochainsMap_id_f_hom_eq_compLeft,
    LinearMap.compLeft_apply] using h

set_option backward.isDefEq.respectTransparency false in
theorem cocycles_cocycle_natural
    {M N M' N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N')
    (r s : ℕ) (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.cocyclesMap (MonoidHom.id G) (f ⊗ₘ g) (r + s)
        (cupCocycle M N r s x y) =
      cupCocycle M' N' r s
        (groupCohomology.cocyclesMap (MonoidHom.id G) f r x)
        (groupCohomology.cocyclesMap (MonoidHom.id G) g s y) := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (M' ⊗ N' : Rep ℤ G) (r + s))).1 inferInstance
  have hmap := i_cocycles_id (f ⊗ₘ g) (r + s)
    (cupCocycle M N r s x y)
  have hmap' :
      groupCohomology.iCocycles (M' ⊗ N' : Rep ℤ G) (r + s)
          (groupCohomology.cocyclesMap (MonoidHom.id G) (f ⊗ₘ g) (r + s)
            (cupCocycle M N r s x y)) =
        fun z => (f ⊗ₘ g)
          (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
            (cupCocycle M N r s x y) z) := by
    convert hmap using 1
  have hsource := i_cup_cocycle M N r s x y
  have htarget := i_cup_cocycle M' N' r s
    (groupCohomology.cocyclesMap (MonoidHom.id G) f r x)
    (groupCohomology.cocyclesMap (MonoidHom.id G) g s y)
  have hf := i_cocycles_id f r x
  have hg := i_cocycles_id g s y
  rw [hmap', hsource, htarget, hf, hg]
  exact cochainCup_natural f g r s
    (groupCohomology.iCocycles M r x)
    (groupCohomology.iCocycles N s y)

/-- Proposition II.1.38(a): cup product is natural in both coefficient
modules. -/
theorem cupCohomology_natural
    {M N M' N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N')
    (r s : ℕ) (a : groupCohomology M r) (b : groupCohomology N s) :
    groupCohomology.map (MonoidHom.id G) (f ⊗ₘ g) (r + s)
        (cupCohomology M N r s a b) =
      cupCohomology M' N' r s
        (groupCohomology.map (MonoidHom.id G) f r a)
        (groupCohomology.map (MonoidHom.id G) g s b) := by
  induction a using groupCohomology_induction_on with
  | h x =>
      induction b using groupCohomology_induction_on with
      | h y =>
          rw [cupCohomology_π]
          have ht := congrArg (fun q => q (cupCocycle M N r s x y))
            (groupCohomology.π_map (MonoidHom.id G) (f ⊗ₘ g) (r + s))
          have hf := congrArg (fun q => q x)
            (groupCohomology.π_map (MonoidHom.id G) f r)
          have hg := congrArg (fun q => q y)
            (groupCohomology.π_map (MonoidHom.id G) g s)
          simp only [ConcreteCategory.comp_apply] at ht hf hg
          calc
            groupCohomology.map (MonoidHom.id G) (f ⊗ₘ g) (r + s)
                (groupCohomology.π (M ⊗ N : Rep ℤ G) (r + s)
                  (cupCocycle M N r s x y)) =
              groupCohomology.π (M' ⊗ N' : Rep ℤ G) (r + s)
                (groupCohomology.cocyclesMap (MonoidHom.id G) (f ⊗ₘ g)
                  (r + s) (cupCocycle M N r s x y)) := by
                    convert ht using 1
            _ = groupCohomology.π (M' ⊗ N' : Rep ℤ G) (r + s)
                (cupCocycle M' N' r s
                  (groupCohomology.cocyclesMap (MonoidHom.id G) f r x)
                  (groupCohomology.cocyclesMap (MonoidHom.id G) g s y)) := by
                    rw [cocycles_cocycle_natural]
            _ = cupCohomology M' N' r s
                (groupCohomology.π M' r
                  (groupCohomology.cocyclesMap (MonoidHom.id G) f r x))
                (groupCohomology.π N' s
                  (groupCohomology.cocyclesMap (MonoidHom.id G) g s y)) := by
                    rw [cupCohomology_π]
            _ = _ := by rw [← hf, ← hg]

end Towers.CField.COps.CPBuild
