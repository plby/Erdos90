import Submission.ClassField.CohomologyOps.CochainCastZero

namespace Submission.CField.COps.CPBuild

open CategoryTheory
open scoped MonoidalCategory

variable {G : Type} [Group G]

theorem cocycles_cocycle (A : Rep ℤ G) (n : ℕ)
    (x : groupCohomology.cocycles A n) :
    cochainDifferential A n (groupCohomology.iCocycles A n x) = 0 := by
  change (inhomogeneousCochains.d A n).hom
      (groupCohomology.iCocycles A n x) = 0
  have h := congrArg (fun f => f x)
    ((groupCohomology.inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [groupCohomology.inhomogeneousCochains.d_def] using h

/-- The cocycle represented by the explicit cup of two cocycles. -/
noncomputable def cupCocycle (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s) :=
  groupCohomology.cocyclesMk
    (cochainCup M N r s
      (groupCohomology.iCocycles M r x)
      (groupCohomology.iCocycles N s y))
    (by
      change cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s
          (groupCohomology.iCocycles M r x)
          (groupCohomology.iCocycles N s y)) = 0
      exact cochain_cocycle M N r s _ _
        (cocycles_cocycle M r x) (cocycles_cocycle N s y))

@[simp]
theorem i_cup_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
        (cupCocycle M N r s x y) =
      cochainCup M N r s
        (groupCohomology.iCocycles M r x)
        (groupCohomology.iCocycles N s y) := by
  apply groupCohomology.iCocycles_mk
  change cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
    (cochainCup M N r s
      (groupCohomology.iCocycles M r x)
      (groupCohomology.iCocycles N s y)) = 0
  exact cochain_cocycle M N r s _ _
    (cocycles_cocycle M r x) (cocycles_cocycle N s y)

/-- For a fixed left cocycle, cup product is additive in the right cocycle. -/
noncomputable def cocycleAddRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r) :
    groupCohomology.cocycles N s →+
      groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s) where
  toFun := cupCocycle M N r s x
  map_zero' := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s))).1 inferInstance
    simp only [map_zero]
    change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
      (cupCocycle M N r s x 0) = 0
    rw [i_cup_cocycle]
    simp only [map_zero]
    exact cochain_cup_right M N r s _
  map_add' := by
    intro y₁ y₂
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s))).1 inferInstance
    simp only [map_add]
    change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
      (cupCocycle M N r s x (y₁ + y₂)) =
        groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
          (cupCocycle M N r s x y₁) +
        groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
          (cupCocycle M N r s x y₂)
    rw [i_cup_cocycle, i_cup_cocycle, i_cup_cocycle]
    simp only [map_add]
    exact cochain_cup_add M N r s _ _ _

@[simp]
theorem cocycle_cup_add (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    cocycleAddRight M N r s x y = cupCocycle M N r s x y := rfl

/-- The right-additive cup map is additive in the left cocycle. -/
noncomputable def cocycleCupAdd (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.cocycles M r →+
      (groupCohomology.cocycles N s →+
        groupCohomology.cocycles (M ⊗ N : Rep ℤ G) (r + s)) where
  toFun := cocycleAddRight M N r s
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s))).1 inferInstance
    simp only [cocycle_cup_add, AddMonoidHom.zero_apply, map_zero]
    change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
      (cupCocycle M N r s 0 y) = 0
    rw [i_cup_cocycle]
    simp only [map_zero]
    exact cochain_cup_left M N r s _
  map_add' := by
    intro x₁ x₂
    apply AddMonoidHom.ext
    intro y
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s))).1 inferInstance
    simp only [cocycle_cup_add, AddMonoidHom.add_apply, map_add]
    change groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
      (cupCocycle M N r s (x₁ + x₂) y) =
        groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
          (cupCocycle M N r s x₁ y) +
        groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
          (cupCocycle M N r s x₂ y)
    rw [i_cup_cocycle, i_cup_cocycle, i_cup_cocycle]
    simp only [map_add]
    exact cochain_add_left M N r s _ _ _

@[simp]
theorem i_cocycles_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) (r + s)
        (cocycleCupAdd M N r s x y) =
      cochainCup M N r s
        (groupCohomology.iCocycles M r x)
        (groupCohomology.iCocycles N s y) := by
  exact i_cup_cocycle M N r s x y

end Submission.CField.COps.CPBuild
