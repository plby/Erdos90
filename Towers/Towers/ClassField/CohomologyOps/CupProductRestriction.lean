import Towers.ClassField.CohomologyOps.GradedCommutativity

namespace Towers.CField.COps.CPFuncto

open CategoryTheory
open Towers.CField.COps.CPBuild
open scoped MonoidalCategory TensorProduct

variable {G K : Type} [Group G] [Group K]

theorem initialProduct_map (f : K →* G) (r s : ℕ)
    (q : Fin (r + s) → K) :
    f (initialProduct r s q) = initialProduct r s (f ∘ q) := by
  unfold initialProduct Fin.partialProd
  rw [map_list_prod, List.map_take, List.map_ofFn]

theorem cochainCup_restrict (f : K →* G)
    (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    cochainCup (Rep.res f M) (Rep.res f N) r s
        (fun q => φ (f ∘ q)) (fun q => ψ (f ∘ q)) =
      fun q => cochainCup M N r s φ ψ (f ∘ q) := by
  funext q
  simp only [cochainCup]
  rw [← initialProduct_map f r s q]
  rfl

noncomputable section

theorem i_cocycles_restrict (f : K →* G)
    (A : Rep ℤ G) (n : ℕ) (x : groupCohomology.cocycles A n) :
    groupCohomology.iCocycles (Rep.res f A) n
        (groupCohomology.cocyclesMap f (𝟙 (Rep.res f A)) n x) =
      fun q => groupCohomology.iCocycles A n x (f ∘ q) := by
  have h := congrArg (fun q => q x)
    (HomologicalComplex.cyclesMap_i
      (groupCohomology.cochainsMap f (𝟙 (Rep.res f A))) n)
  simpa only [ConcreteCategory.comp_apply, groupCohomology.cochainsMap_f,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compLeft_apply, LinearMap.funLeft_apply] using h

theorem cocycles_cocycle_restrict (f : K →* G)
    (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.cocyclesMap f
        (𝟙 (Rep.res f (M ⊗ N : Rep ℤ G))) (r + s)
        (cupCocycle M N r s x y) =
      cupCocycle (Rep.res f M) (Rep.res f N) r s
        (groupCohomology.cocyclesMap f (𝟙 (Rep.res f M)) r x)
        (groupCohomology.cocyclesMap f (𝟙 (Rep.res f N)) s y) := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles
      (Rep.res f (M ⊗ N : Rep ℤ G)) (r + s))).1 inferInstance
  rw [i_cocycles_restrict, i_cup_cocycle]
  have hcup := i_cup_cocycle
    (Rep.res f M) (Rep.res f N) r s
    (groupCohomology.cocyclesMap f (𝟙 (Rep.res f M)) r x)
    (groupCohomology.cocyclesMap f (𝟙 (Rep.res f N)) s y)
  have hcup' :
      groupCohomology.iCocycles (Rep.res f (M ⊗ N : Rep ℤ G)) (r + s)
          (cupCocycle (Rep.res f M) (Rep.res f N) r s
            (groupCohomology.cocyclesMap f (𝟙 (Rep.res f M)) r x)
            (groupCohomology.cocyclesMap f (𝟙 (Rep.res f N)) s y)) =
        cochainCup (Rep.res f M) (Rep.res f N) r s
          (groupCohomology.iCocycles (Rep.res f M) r
            (groupCohomology.cocyclesMap f (𝟙 (Rep.res f M)) r x))
          (groupCohomology.iCocycles (Rep.res f N) s
            (groupCohomology.cocyclesMap f (𝟙 (Rep.res f N)) s y)) := by
    exact hcup
  rw [hcup', i_cocycles_restrict,
    i_cocycles_restrict]
  exact (cochainCup_restrict f M N r s
    (groupCohomology.iCocycles M r x)
    (groupCohomology.iCocycles N s y)).symm

/-- Cup products commute with restriction along an arbitrary group
homomorphism. -/
theorem cupCohomology_restrict (f : K →* G)
    (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) (b : groupCohomology N s) :
    groupCohomology.map f
        (𝟙 (Rep.res f (M ⊗ N : Rep ℤ G))) (r + s)
        (cupCohomology M N r s a b) =
      cupCohomology (Rep.res f M) (Rep.res f N) r s
        (groupCohomology.map f (𝟙 (Rep.res f M)) r a)
        (groupCohomology.map f (𝟙 (Rep.res f N)) s b) := by
  induction a using groupCohomology_induction_on with
  | h x =>
      induction b using groupCohomology_induction_on with
      | h y =>
          rw [cupCohomology_π]
          have ht := congrArg (fun q => q (cupCocycle M N r s x y))
            (groupCohomology.π_map f
              (𝟙 (Rep.res f (M ⊗ N : Rep ℤ G))) (r + s))
          have hx := congrArg (fun q => q x)
            (groupCohomology.π_map f (𝟙 (Rep.res f M)) r)
          have hy := congrArg (fun q => q y)
            (groupCohomology.π_map f (𝟙 (Rep.res f N)) s)
          simp only [ConcreteCategory.comp_apply] at ht hx hy
          calc
            groupCohomology.map f
                (𝟙 (Rep.res f (M ⊗ N : Rep ℤ G))) (r + s)
                (groupCohomology.π (M ⊗ N : Rep ℤ G) (r + s)
                  (cupCocycle M N r s x y)) =
              groupCohomology.π
                  (Rep.res f (M ⊗ N : Rep ℤ G)) (r + s)
                (groupCohomology.cocyclesMap f
                  (𝟙 (Rep.res f (M ⊗ N : Rep ℤ G))) (r + s)
                  (cupCocycle M N r s x y)) := by
                    convert ht using 1
            _ = groupCohomology.π
                  (Rep.res f (M ⊗ N : Rep ℤ G)) (r + s)
                (cupCocycle (Rep.res f M) (Rep.res f N) r s
                  (groupCohomology.cocyclesMap f
                    (𝟙 (Rep.res f M)) r x)
                  (groupCohomology.cocyclesMap f
                    (𝟙 (Rep.res f N)) s y)) := by
                    rw [cocycles_cocycle_restrict]
            _ = cupCohomology (Rep.res f M) (Rep.res f N) r s
                (groupCohomology.π (Rep.res f M) r
                  (groupCohomology.cocyclesMap f
                    (𝟙 (Rep.res f M)) r x))
                (groupCohomology.π (Rep.res f N) s
                    (groupCohomology.cocyclesMap f
                      (𝟙 (Rep.res f N)) s y)) := by
                    rw [cupCohomology_π]
                    rfl
            _ = _ := by rw [← hx, ← hy]

/-- Proposition II.1.39(c): the restriction of a cup product to a subgroup
is the cup product of the restrictions. -/
theorem cup_cohomology_restriction
    (H : Subgroup G) (M N : Rep ℤ G) (r s : ℕ)
    (a : groupCohomology M r) (b : groupCohomology N s) :
    groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (M ⊗ N : Rep ℤ G))) (r + s)
        (cupCohomology M N r s a b) =
      cupCohomology (Rep.res H.subtype M) (Rep.res H.subtype N) r s
        (groupCohomology.map H.subtype
          (𝟙 (Rep.res H.subtype M)) r a)
        (groupCohomology.map H.subtype
          (𝟙 (Rep.res H.subtype N)) s b) :=
  cupCohomology_restrict H.subtype M N r s a b

end

end Towers.CField.COps.CPFuncto
