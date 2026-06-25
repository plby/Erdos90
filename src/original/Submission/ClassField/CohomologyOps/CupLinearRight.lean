import Submission.ClassField.CohomologyOps.ICocyclesCocycle

namespace Submission.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidalCategory

variable {G : Type} [Group G]

/-- The additive cup map, regarded as an integer-linear map using the stored
module structures on the cycle objects. -/
noncomputable def cocycleCupRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) :
    groupCohomology.cocycles N s →ₗ[ℤ]
      groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s) where
  toFun := cocycleAddRight M N r s x
  map_add' := (cocycleAddRight M N r s x).map_add
  map_smul' a y := by
    change (cocycleAddRight M N r s x)
        ((groupCohomology.cocycles N s).isModule.smul a y) =
      (groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s)).isModule.smul a
        ((cocycleAddRight M N r s x) y)
    rw [int_smul_eq_zsmul (groupCohomology.cocycles N s).isModule,
      int_smul_eq_zsmul
        (groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s)).isModule]
    exact (cocycleAddRight M N r s x).map_zsmul a y

@[simp]
theorem cocycle_cup_right (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (y : groupCohomology.cocycles N s) :
    cocycleCupRight M N r s x y = cupCocycle M N r s x y := rfl

noncomputable def boundaryCocycle (M : Rep ℤ G) (r : ℕ)
    (f : (Fin r → G) → M) : groupCohomology.cocycles M (r + 1) :=
  groupCohomology.toCocycles M r (r + 1) f

theorem cocycles_boundary_cocycle (M : Rep ℤ G) (r : ℕ)
    (f : (Fin r → G) → M) :
    groupCohomology.iCocycles M (r + 1) (boundaryCocycle M r f) =
      cochainDifferential M r f := by
  unfold boundaryCocycle
  have h := congrArg (fun q => q f)
    ((groupCohomology.inhomogeneousCochains M).toCycles_i r (r + 1))
  change groupCohomology.iCocycles M (r + 1)
      (groupCohomology.toCocycles M r (r + 1) f) =
    (groupCohomology.inhomogeneousCochains M).d r (r + 1) f at h
  rw [groupCohomology.inhomogeneousCochains.d_def] at h
  simpa only [ConcreteCategory.comp_apply,
    groupCohomology.inhomogeneousCochains.d_def, cochainDifferential] using h

theorem cochain_cup_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N s) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s f (groupCohomology.iCocycles N s y)) =
      cochainCast (by omega : (r + s) + 1 = (r + 1) + s)
        (cochainCup M N (r + 1) s (cochainDifferential M r f)
          (groupCohomology.iCocycles N s y)) := by
  rw [cochainCup_d, cocycles_cocycle, cochain_cup_right]
  ext g
  simp only [Pi.add_apply, Pi.smul_apply, cochainCast, Pi.zero_apply]
  change _ + (M ⊗ N : Rep ℤ G).hV2.smul ((-1 : ℤ) ^ r) 0 = _
  rw [int_smul_eq_zsmul (M ⊗ N : Rep ℤ G).hV2, smul_zero, add_zero]

noncomputable def boundaryCupLeft (M N : Rep ℤ G) (r s : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N s) :
    groupCohomology.cocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1) :=
  groupCohomology.toCocycles (M ⊗ N : Rep ℤ G) (r + s) ((r + s) + 1)
    (cochainCup M N r s f (groupCohomology.iCocycles N s y))

theorem i_cocycles_cup (M N : Rep ℤ G) (r s : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N s) :
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
        (boundaryCupLeft M N r s f y) =
      cochainCast (by omega : (r + s) + 1 = (r + 1) + s)
        (cochainCup M N (r + 1) s (cochainDifferential M r f)
          (groupCohomology.iCocycles N s y)) := by
  unfold boundaryCupLeft
  have h := congrArg
    (fun q => q (cochainCup M N r s f (groupCohomology.iCocycles N s y)))
    ((groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).toCycles_i
      (r + s) ((r + s) + 1))
  change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      (groupCohomology.toCocycles (M ⊗ N : Rep ℤ G)
        (r + s) ((r + s) + 1)
        (cochainCup M N r s f (groupCohomology.iCocycles N s y))) =
    (groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).d
      (r + s) ((r + s) + 1)
      (cochainCup M N r s f (groupCohomology.iCocycles N s y)) at h
  rw [groupCohomology.inhomogeneousCochains.d_def] at h
  have h' :
      groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
          (groupCohomology.toCocycles (M ⊗ N : Rep ℤ G)
            (r + s) ((r + s) + 1)
            (cochainCup M N r s f (groupCohomology.iCocycles N s y))) =
        cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
          (cochainCup M N r s f (groupCohomology.iCocycles N s y)) := by
    simpa only [ConcreteCategory.comp_apply,
      groupCohomology.inhomogeneousCochains.d_def, cochainDifferential] using h
  rw [h']
  exact cochain_cup_cocycle M N r s f y

theorem boundary_cup_left (M N : Rep ℤ G) (r s : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N s) :
    groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      (boundaryCupLeft M N r s f y) = 0 := by
  unfold boundaryCupLeft
  have h := congrArg
    (fun q => q (cochainCup M N r s f (groupCohomology.iCocycles N s y)))
    ((groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).toCycles_comp_homologyπ
      (r + s) ((r + s) + 1))
  simpa only [ConcreteCategory.comp_apply, LinearMap.zero_apply] using h

theorem cup_d_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (f : (Fin s → G) → N) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s (groupCohomology.iCocycles M r x) f) =
      (-1 : ℤ) ^ r •
        cochainCast (by omega : (r + s) + 1 = r + (s + 1))
          (cochainCup M N r (s + 1) (groupCohomology.iCocycles M r x)
            (cochainDifferential N s f)) := by
  rw [cochainCup_d, cocycles_cocycle, cochain_cup_left]
  ext g
  simp only [Pi.add_apply, Pi.smul_apply, cochainCast, Pi.zero_apply, zero_add]

noncomputable def boundaryCupRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (f : (Fin s → G) → N) :
    groupCohomology.cocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1) :=
  groupCohomology.toCocycles (M ⊗ N : Rep ℤ G) (r + s) ((r + s) + 1)
    (cochainCup M N r s (groupCohomology.iCocycles M r x) f)

theorem i_cocycles_boundary (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (f : (Fin s → G) → N) :
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
        (boundaryCupRight M N r s x f) =
      (-1 : ℤ) ^ r •
        cochainCast (by omega : (r + s) + 1 = r + (s + 1))
          (cochainCup M N r (s + 1) (groupCohomology.iCocycles M r x)
            (cochainDifferential N s f)) := by
  unfold boundaryCupRight
  have h := congrArg
    (fun q => q (cochainCup M N r s (groupCohomology.iCocycles M r x) f))
    ((groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).toCycles_i
      (r + s) ((r + s) + 1))
  change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      (groupCohomology.toCocycles (M ⊗ N : Rep ℤ G)
        (r + s) ((r + s) + 1)
        (cochainCup M N r s (groupCohomology.iCocycles M r x) f)) =
    (groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).d
      (r + s) ((r + s) + 1)
      (cochainCup M N r s (groupCohomology.iCocycles M r x) f) at h
  rw [groupCohomology.inhomogeneousCochains.d_def] at h
  have h' :
      groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
          (groupCohomology.toCocycles (M ⊗ N : Rep ℤ G)
            (r + s) ((r + s) + 1)
            (cochainCup M N r s (groupCohomology.iCocycles M r x) f)) =
        cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
          (cochainCup M N r s (groupCohomology.iCocycles M r x) f) := by
    simpa only [ConcreteCategory.comp_apply,
      groupCohomology.inhomogeneousCochains.d_def, cochainDifferential] using h
  rw [h']
  exact cup_d_cocycle M N r s x f

theorem boundary_cup_zero (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (f : (Fin s → G) → N) :
    groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      (boundaryCupRight M N r s x f) = 0 := by
  unfold boundaryCupRight
  have h := congrArg
    (fun q => q (cochainCup M N r s (groupCohomology.iCocycles M r x) f))
    ((groupCohomology.inhomogeneousCochains (M ⊗ N : Rep ℤ G)).toCycles_comp_homologyπ
      (r + s) ((r + s) + 1))
  simpa only [ConcreteCategory.comp_apply, LinearMap.zero_apply] using h

theorem cup_boundary_zero (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) (f : (Fin s → G) → N) :
    groupCohomology.π (M ⊗ N : Rep ℤ G) (r + (s + 1))
      (cupCocycle M N r (s + 1) x (boundaryCocycle N s f)) = 0 := by
  have hsigned :
      boundaryCupRight M N r s x f =
        (-1 : ℤ) ^ r • cupCocycle M N r (s + 1) x (boundaryCocycle N s f) := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1))).1 inferInstance
    rw [i_cocycles_boundary]
    have hm := map_zsmul (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G)
      ((r + s) + 1)).hom ((-1 : ℤ) ^ r)
        (cupCocycle M N r (s + 1) x (boundaryCocycle N s f))
    rw [hm]
    change _ = (-1 : ℤ) ^ r •
      groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
        (cupCocycle M N r (s + 1) x (boundaryCocycle N s f))
    have hi :
        groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1)
            (cupCocycle M N r (s + 1) x (boundaryCocycle N s f)) =
          cochainCup M N r (s + 1) (groupCohomology.iCocycles M r x)
            (groupCohomology.iCocycles N (s + 1) (boundaryCocycle N s f)) :=
      i_cup_cocycle M N r (s + 1) x (boundaryCocycle N s f)
    rw [hi, cocycles_boundary_cocycle]
    rfl
  have hz := congrArg
    (fun z => groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + s) + 1) z)
    hsigned
  change groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      (boundaryCupRight M N r s x f) =
    groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + s) + 1)
      ((-1 : ℤ) ^ r • cupCocycle M N r (s + 1) x (boundaryCocycle N s f)) at hz
  rw [boundary_cup_zero] at hz
  have hm := map_zsmul (groupCohomology.π (M ⊗ N : Rep ℤ G)
    ((r + s) + 1)).hom ((-1 : ℤ) ^ r)
      (cupCocycle M N r (s + 1) x (boundaryCocycle N s f))
  rw [hm] at hz
  rcases neg_one_pow_eq_or ℤ r with hr | hr <;> rw [hr] at hz
  · simpa using hz.symm
  · simpa using hz.symm

noncomputable def cupCocyclesLinear (M N : Rep ℤ G)
    (r s : ℕ) (x : groupCohomology.cocycles M r) :
    groupCohomology.cocycles N (s + 1) →ₗ[ℤ]
      groupCohomology (M ⊗ N : Rep ℤ G) (r + (s + 1)) :=
  (groupCohomology.π (M ⊗ N : Rep ℤ G) (r + (s + 1))).hom.comp
    (cocycleCupRight M N r (s + 1) x)

noncomputable def cupCocyclesCohomology (M N : Rep ℤ G)
    (r s : ℕ) (x : groupCohomology.cocycles M r) :
    groupCohomology.cocycles N (s + 1) ⟶
      groupCohomology (M ⊗ N : Rep ℤ G) (r + (s + 1)) :=
  ModuleCat.ofHom (cupCocyclesLinear M N r s x)

theorem cocycles_comp_cup (M N : Rep ℤ G)
    (r s : ℕ) (x : groupCohomology.cocycles M r) :
    groupCohomology.toCocycles N s (s + 1) ≫
      cupCocyclesCohomology M N r s x = 0 := by
  apply ModuleCat.hom_ext
  apply DFunLike.ext _ _
  intro f
  change groupCohomology.π (M ⊗ N : Rep ℤ G) (r + (s + 1))
    (cupCocycle M N r (s + 1) x (boundaryCocycle N s f)) = 0
  exact cup_boundary_zero M N r s x f

noncomputable def cupCohomologyRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) :
    groupCohomology N (s + 1) ⟶
      groupCohomology (M ⊗ N : Rep ℤ G) (r + (s + 1)) :=
  ((groupCohomology.inhomogeneousCochains N).homologyIsCokernel
      (i := s) (j := s + 1) (by simp)).desc
    (CokernelCofork.ofπ (cupCocyclesCohomology M N r s x)
      (cocycles_comp_cup M N r s x))

theorem π_comp_cupCohomologyRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) :
    groupCohomology.π N (s + 1) ≫ cupCohomologyRight M N r s x =
      cupCocyclesCohomology M N r s x := by
  unfold cupCohomologyRight
  exact Cofork.IsColimit.π_desc
    ((groupCohomology.inhomogeneousCochains N).homologyIsCokernel
      (i := s) (j := s + 1) (by simp))

end Submission.CField.COps.CPBuild
