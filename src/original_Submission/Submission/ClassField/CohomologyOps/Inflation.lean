import Submission.ClassField.CohomologyOps.CupProductRestriction

namespace Submission.CField.COps.CPFuncto

open CategoryTheory
open Submission.CField.COps.CPBuild
open scoped MonoidalCategory TensorProduct

variable {G K : Type} [Group G] [Group K]

noncomputable section

theorem i_cocycles (f : K →* G)
    {A : Rep ℤ G} {A' : Rep ℤ K} (p : Rep.res f A ⟶ A')
    (n : ℕ) (x : groupCohomology.cocycles A n) :
    groupCohomology.iCocycles A' n
        (groupCohomology.cocyclesMap f p n x) =
      fun z => p (groupCohomology.iCocycles A n x (f ∘ z)) := by
  have h := congrArg (fun q => q x)
    (HomologicalComplex.cyclesMap_i
      (groupCohomology.cochainsMap f p) n)
  simpa only [ConcreteCategory.comp_apply, groupCohomology.cochainsMap_f,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compLeft_apply, LinearMap.funLeft_apply] using h

theorem cocycles_cup_cocycle (f : K →* G)
    {M N : Rep ℤ G} {M' N' : Rep ℤ K}
    (p : Rep.res f M ⟶ M') (q : Rep.res f N ⟶ N')
    (r s : ℕ) (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.cocyclesMap f (p ⊗ₘ q) (r + s)
        (cupCocycle M N r s x y) =
      cupCocycle M' N' r s
        (groupCohomology.cocyclesMap f p r x)
        (groupCohomology.cocyclesMap f q s y) := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (M' ⊗ N' : Rep ℤ K) (r + s))).1 inferInstance
  rw [i_cocycles, i_cup_cocycle]
  have hcup := i_cup_cocycle M' N' r s
    (groupCohomology.cocyclesMap f p r x)
    (groupCohomology.cocyclesMap f q s y)
  rw [hcup, i_cocycles, i_cocycles]
  have hnat := cochainCup_natural p q r s
    (fun z => groupCohomology.iCocycles M r x (f ∘ z))
    (fun z => groupCohomology.iCocycles N s y (f ∘ z))
  rw [cochainCup_restrict f M N r s
    (groupCohomology.iCocycles M r x)
    (groupCohomology.iCocycles N s y)] at hnat
  exact hnat

/-- Cup products commute with the simultaneous contravariant change of
group and covariant change of both coefficient modules. -/
theorem cupCohomology_map (f : K →* G)
    {M N : Rep ℤ G} {M' N' : Rep ℤ K}
    (p : Rep.res f M ⟶ M') (q : Rep.res f N ⟶ N')
    (r s : ℕ) (a : groupCohomology M r) (b : groupCohomology N s) :
    groupCohomology.map f (p ⊗ₘ q) (r + s)
        (cupCohomology M N r s a b) =
      cupCohomology M' N' r s
        (groupCohomology.map f p r a)
        (groupCohomology.map f q s b) := by
  induction a using groupCohomology_induction_on with
  | h x =>
      induction b using groupCohomology_induction_on with
      | h y =>
          rw [cupCohomology_π]
          have ht := congrArg (fun z => z (cupCocycle M N r s x y))
            (groupCohomology.π_map f (p ⊗ₘ q) (r + s))
          have hp := congrArg (fun z => z x)
            (groupCohomology.π_map f p r)
          have hq := congrArg (fun z => z y)
            (groupCohomology.π_map f q s)
          simp only [ConcreteCategory.comp_apply] at ht hp hq
          calc
            groupCohomology.map f (p ⊗ₘ q) (r + s)
                (groupCohomology.π (M ⊗ N : Rep ℤ G) (r + s)
                  (cupCocycle M N r s x y)) =
              groupCohomology.π (M' ⊗ N' : Rep ℤ K) (r + s)
                (groupCohomology.cocyclesMap f (p ⊗ₘ q) (r + s)
                  (cupCocycle M N r s x y)) := by
                    convert ht using 1
            _ = groupCohomology.π (M' ⊗ N' : Rep ℤ K) (r + s)
                (cupCocycle M' N' r s
                  (groupCohomology.cocyclesMap f p r x)
                  (groupCohomology.cocyclesMap f q s y)) := by
                    rw [cocycles_cup_cocycle]
            _ = cupCohomology M' N' r s
                (groupCohomology.π M' r
                  (groupCohomology.cocyclesMap f p r x))
                (groupCohomology.π N' s
                  (groupCohomology.cocyclesMap f q s y)) := by
                    rw [cupCohomology_π]
            _ = _ := by rw [← hp, ← hq]

variable (H : Subgroup G) [H.Normal]

/-- The canonical inclusion of the `H`-invariants, regarded as a
`G / H`-module, into the original `G`-module. -/
noncomputable def inflationInvariantsInclusion (A : Rep ℤ G) :
    Rep.res (QuotientGroup.mk' H) (A.quotientToInvariants H) ⟶ A := by
  letI := A.hV2
  letI := (A.quotientToInvariants H).hV2
  exact Rep.ofHom (A.ρ.quotientToInvariants_lift H)

/-- Proposition II.1.39(e): inflation from `G / H` commutes with cup
products.  The coefficient map on the product is the tensor of the two
canonical inclusions `M^H → M` and `N^H → N`; no identification of
`M^H ⊗ N^H` with `(M ⊗ N)^H` is assumed. -/
theorem cupCohomology_inflation
    (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology (M.quotientToInvariants H) r)
    (y : groupCohomology (N.quotientToInvariants H) s) :
    groupCohomology.map (QuotientGroup.mk' H)
        (inflationInvariantsInclusion H M ⊗ₘ
          inflationInvariantsInclusion H N) (r + s)
        (cupCohomology (M.quotientToInvariants H)
          (N.quotientToInvariants H) r s x y) =
      cupCohomology M N r s
        ((groupCohomology.infNatTrans (k := ℤ) H r).app M x)
        ((groupCohomology.infNatTrans (k := ℤ) H s).app N y) := by
  simpa only [groupCohomology.infNatTrans_app,
    inflationInvariantsInclusion] using
      (cupCohomology_map (QuotientGroup.mk' H)
        (inflationInvariantsInclusion H M)
        (inflationInvariantsInclusion H N) r s x y)

end

end Submission.CField.COps.CPFuncto
