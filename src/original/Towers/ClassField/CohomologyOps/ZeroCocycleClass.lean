import Towers.ClassField.CohomologyOps.BiDescent

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidalCategory

variable {G : Type} [Group G]

instance cohomology_pi_iso (A : Rep ℤ G) :
    IsIso (groupCohomology.π A 0) := by
  exact CochainComplex.isIso_homologyπ₀ (groupCohomology.inhomogeneousCochains A)

/-- The inverse of the degree-zero class map, as a linear map to cocycles. -/
noncomputable def zeroCocycleClass (A : Rep ℤ G) :
    groupCohomology A 0 →ₗ[ℤ] groupCohomology.cocycles A 0 :=
  (inv (groupCohomology.π A 0)).hom

@[simp]
theorem zero_cocycle_classπ (A : Rep ℤ G)
    (x : groupCohomology.cocycles A 0) :
    zeroCocycleClass A (groupCohomology.π A 0 x) = x := by
  change inv (groupCohomology.π A 0) (groupCohomology.π A 0 x) = x
  exact IsIso.hom_inv_id_apply (groupCohomology.π A 0) x

/-- Cup product in bidegree `(0,0)`, with both representatives recovered by
the inverse of the degree-zero class map. -/
noncomputable def cupZeroRight (M N : Rep ℤ G)
    (x : groupCohomology M 0) :
    groupCohomology N 0 →ₗ[ℤ] groupCohomology (M ⊗ N : Rep ℤ G) 0 :=
  (groupCohomology.π (M ⊗ N : Rep ℤ G) 0).hom.comp
    ((cocycleCupRight M N 0 0 (zeroCocycleClass M x)).comp
      (zeroCocycleClass N))

noncomputable def cupZeroAdd (M N : Rep ℤ G) :
    groupCohomology M 0 →+
      (groupCohomology N 0 →ₗ[ℤ] groupCohomology (M ⊗ N : Rep ℤ G) 0) where
  toFun := cupZeroRight M N
  map_zero' := by
    ext y
    change groupCohomology.π (M ⊗ N : Rep ℤ G) 0
      (cupCocycle M N 0 0 (zeroCocycleClass M 0) (zeroCocycleClass N y)) = 0
    rw [map_zero]
    have hc := congrArg (fun q => q (zeroCocycleClass N y))
      ((cocycleCupAdd M N 0 0).map_zero)
    have hc' : cupCocycle M N 0 0 0 (zeroCocycleClass N y) = 0 := hc
    rw [hc', map_zero]
  map_add' x₁ x₂ := by
    ext y
    change groupCohomology.π (M ⊗ N : Rep ℤ G) 0
      (cupCocycle M N 0 0 (zeroCocycleClass M (x₁ + x₂))
        (zeroCocycleClass N y)) = _
    rw [map_add]
    change groupCohomology.π (M ⊗ N : Rep ℤ G) 0
      ((cocycleCupAdd M N 0 0)
        (zeroCocycleClass M x₁ + zeroCocycleClass M x₂)
        (zeroCocycleClass N y)) = _
    rw [map_add, AddMonoidHom.add_apply, map_add]
    change _ = cupZeroRight M N x₁ y +
      cupZeroRight M N x₂ y
    rfl

noncomputable def cupZero (M N : Rep ℤ G) :
    groupCohomology M 0 →ₗ[ℤ]
      groupCohomology N 0 →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) 0 where
  toFun := cupZeroAdd M N
  map_add' := (cupZeroAdd M N).map_add
  map_smul' a x := by
    change (cupZeroAdd M N)
        ((groupCohomology M 0).isModule.smul a x) =
      a • (cupZeroAdd M N) x
    rw [int_smul_eq_zsmul (groupCohomology M 0).isModule]
    exact (cupZeroAdd M N).map_zsmul a x

@[simp]
theorem cup_cohomologyπ (M N : Rep ℤ G)
    (x : groupCohomology.cocycles M 0)
    (y : groupCohomology.cocycles N 0) :
    cupZero M N (groupCohomology.π M 0 x)
        (groupCohomology.π N 0 y) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) 0 (cupCocycle M N 0 0 x y) := by
  simp [cupZero, cupZeroAdd, cupZeroRight]
  rfl

theorem i_cocycles_representative (M N : Rep ℤ G)
    (x : groupCohomology.cocycles M 0)
    (y : groupCohomology.cocycles N 0) (g : Fin (0 + 0) → G) :
    groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) 0
        (cupCocycle M N 0 0 x y) g =
      tensorElement M N
        (groupCohomology.iCocycles M 0 x (fun i => i.elim0))
        (groupCohomology.iCocycles N 0 y (fun i => i.elim0)) := by
  have hi := i_cup_cocycle M N 0 0 x y
  rw [hi]
  exact cochain_cup_zero M N _ _ g

/-- Mixed bidegree `(0,s+1)`: only the positive-degree right variable needs
quotient descent; the left class has a unique degree-zero cocycle lift. -/
noncomputable def cupPositiveRight (M N : Rep ℤ G) (s : ℕ)
    (x : groupCohomology M 0) :
    groupCohomology N (s + 1) →ₗ[ℤ]
      groupCohomology (M ⊗ N : Rep ℤ G) (0 + (s + 1)) :=
  (cupCohomologyRight M N 0 s (zeroCocycleClass M x)).hom

theorem π_comp_cupCohomologyZeroPositiveRight (M N : Rep ℤ G) (s : ℕ)
    (x : groupCohomology M 0) :
    groupCohomology.π N (s + 1) ≫
      ModuleCat.ofHom (cupPositiveRight M N s x) =
        cupCocyclesCohomology M N 0 s (zeroCocycleClass M x) := by
  exact π_comp_cupCohomologyRight M N 0 s (zeroCocycleClass M x)

theorem cup_cohomology_add (M N : Rep ℤ G) (s : ℕ)
    (x₁ x₂ : groupCohomology M 0) :
    cupPositiveRight M N s (x₁ + x₂) =
      cupPositiveRight M N s x₁ +
        cupPositiveRight M N s x₂ := by
  ext z
  induction z using groupCohomology_induction_on with
  | h y =>
  have hsum := congrArg (fun q => q y)
    (π_comp_cupCohomologyZeroPositiveRight M N s (x₁ + x₂))
  have h₁ := congrArg (fun q => q y)
    (π_comp_cupCohomologyZeroPositiveRight M N s x₁)
  have h₂ := congrArg (fun q => q y)
    (π_comp_cupCohomologyZeroPositiveRight M N s x₂)
  simp only [ConcreteCategory.comp_apply] at hsum h₁ h₂
  have hsum' : cupPositiveRight M N s (x₁ + x₂)
      (groupCohomology.π N (s + 1) y) =
    cupCocyclesCohomology M N 0 s
      (zeroCocycleClass M (x₁ + x₂)) y := hsum
  have h₁' : cupPositiveRight M N s x₁
      (groupCohomology.π N (s + 1) y) =
    cupCocyclesCohomology M N 0 s (zeroCocycleClass M x₁) y := h₁
  have h₂' : cupPositiveRight M N s x₂
      (groupCohomology.π N (s + 1) y) =
    cupCocyclesCohomology M N 0 s (zeroCocycleClass M x₂) y := h₂
  rw [hsum']
  change _ = cupPositiveRight M N s x₁
      (groupCohomology.π N (s + 1) y) +
    cupPositiveRight M N s x₂
      (groupCohomology.π N (s + 1) y)
  rw [h₁', h₂']
  have hc := congrArg (fun q => q y)
    ((cocycleCupAdd M N 0 (s + 1)).map_add
      (zeroCocycleClass M x₁) (zeroCocycleClass M x₂))
  have hc' :
      cupCocycle M N 0 (s + 1)
          (zeroCocycleClass M x₁ + zeroCocycleClass M x₂) y =
        cupCocycle M N 0 (s + 1) (zeroCocycleClass M x₁) y +
          cupCocycle M N 0 (s + 1) (zeroCocycleClass M x₂) y := hc
  change groupCohomology.π (M ⊗ N : Rep ℤ G) (0 + (s + 1))
      (cupCocycle M N 0 (s + 1)
        (zeroCocycleClass M (x₁ + x₂)) y) = _
  rw [map_add, hc', map_add]
  rfl

theorem cup_cohomology_positive (M N : Rep ℤ G) (s : ℕ) :
    cupPositiveRight M N s 0 = 0 := by
  ext z
  induction z using groupCohomology_induction_on with
  | h y =>
  have hz := congrArg (fun q => q y)
    (π_comp_cupCohomologyZeroPositiveRight M N s 0)
  simp only [ConcreteCategory.comp_apply] at hz
  have hz' : cupPositiveRight M N s 0
      (groupCohomology.π N (s + 1) y) =
    cupCocyclesCohomology M N 0 s (zeroCocycleClass M 0) y := hz
  rw [hz']
  change groupCohomology.π (M ⊗ N : Rep ℤ G) (0 + (s + 1))
    (cupCocycle M N 0 (s + 1) (zeroCocycleClass M 0) y) = 0
  rw [map_zero]
  have hc := congrArg (fun q => q y) ((cocycleCupAdd M N 0 (s + 1)).map_zero)
  have hc' : cupCocycle M N 0 (s + 1) 0 y = 0 := hc
  rw [hc', map_zero]

noncomputable def cupPositiveAdd (M N : Rep ℤ G) (s : ℕ) :
    groupCohomology M 0 →+
      (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) (0 + (s + 1))) where
  toFun := cupPositiveRight M N s
  map_zero' := cup_cohomology_positive M N s
  map_add' := cup_cohomology_add M N s

noncomputable def cupZeroPositive (M N : Rep ℤ G) (s : ℕ) :
    groupCohomology M 0 →ₗ[ℤ]
      groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) (0 + (s + 1)) where
  toFun := cupPositiveAdd M N s
  map_add' := (cupPositiveAdd M N s).map_add
  map_smul' a x := by
    change (cupPositiveAdd M N s)
        ((groupCohomology M 0).isModule.smul a x) =
      a • (cupPositiveAdd M N s) x
    rw [int_smul_eq_zsmul (groupCohomology M 0).isModule]
    exact (cupPositiveAdd M N s).map_zsmul a x

@[simp]
theorem cup_zero_positiveπ (M N : Rep ℤ G) (s : ℕ)
    (x : groupCohomology.cocycles M 0)
    (y : groupCohomology.cocycles N (s + 1)) :
    cupZeroPositive M N s (groupCohomology.π M 0 x)
        (groupCohomology.π N (s + 1) y) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) (0 + (s + 1))
        (cupCocycle M N 0 (s + 1) x y) := by
  change cupCohomologyRight M N 0 s
      (zeroCocycleClass M (groupCohomology.π M 0 x))
      (groupCohomology.π N (s + 1) y) = _
  rw [zero_cocycle_classπ]
  have h := congrArg (fun q => q y) (π_comp_cupCohomologyRight M N 0 s x)
  simpa only [ConcreteCategory.comp_apply] using h

theorem cup_boundary_right (M N : Rep ℤ G) (r : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N 0) :
    groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
      (cupCocycle M N (r + 1) 0 (boundaryCocycle M r f) y) = 0 := by
  let h : (r + 1) + 0 = (r + 0) + 1 := by omega
  letI : IsIso (cohomologyCast (M ⊗ N : Rep ℤ G) h) := by
    unfold cohomologyCast
    infer_instance
  apply (ModuleCat.mono_iff_injective
    (cohomologyCast (M ⊗ N : Rep ℤ G) h)).1 inferInstance
  rw [map_zero]
  exact cup_boundary_cast M N r 0 f y

/-- Mixed bidegree `(r+1,0)`, before descending the positive left variable. -/
noncomputable def cupCohomologyCycles
    (M N : Rep ℤ G) (r : ℕ) (x : groupCohomology.cocycles M (r + 1)) :
    groupCohomology N 0 →ₗ[ℤ]
      groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + 0) :=
  (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)).hom.comp
    ((cocycleCupRight M N (r + 1) 0 x).comp (zeroCocycleClass N))

noncomputable def cupCyclesAdd
    (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology.cocycles M (r + 1) →+
      (groupCohomology N 0 →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + 0)) where
  toFun := cupCohomologyCycles M N r
  map_zero' := by
    ext y
    change groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
      (cupCocycle M N (r + 1) 0 0 (zeroCocycleClass N y)) = 0
    have hc := congrArg (fun q => q (zeroCocycleClass N y))
      ((cocycleCupAdd M N (r + 1) 0).map_zero)
    have hc' : cupCocycle M N (r + 1) 0 0 (zeroCocycleClass N y) = 0 := hc
    rw [hc', map_zero]
  map_add' x₁ x₂ := by
    ext y
    change groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
      (cupCocycle M N (r + 1) 0 (x₁ + x₂) (zeroCocycleClass N y)) = _
    have hc := congrArg (fun q => q (zeroCocycleClass N y))
      ((cocycleCupAdd M N (r + 1) 0).map_add x₁ x₂)
    have hc' :
        cupCocycle M N (r + 1) 0 (x₁ + x₂) (zeroCocycleClass N y) =
          cupCocycle M N (r + 1) 0 x₁ (zeroCocycleClass N y) +
            cupCocycle M N (r + 1) 0 x₂ (zeroCocycleClass N y) := hc
    rw [hc', map_add]
    rfl

noncomputable def cupCyclesLinear
    (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology.cocycles M (r + 1) →ₗ[ℤ]
      (groupCohomology N 0 →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + 0)) where
  toFun := cupCyclesAdd M N r
  map_add' := (cupCyclesAdd M N r).map_add
  map_smul' a x := by
    change (cupCyclesAdd M N r)
        ((groupCohomology.cocycles M (r + 1)).isModule.smul a x) =
      a • (cupCyclesAdd M N r) x
    rw [int_smul_eq_zsmul (groupCohomology.cocycles M (r + 1)).isModule]
    exact (cupCyclesAdd M N r).map_zsmul a x

noncomputable def cupPositiveCycles
    (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology.cocycles M (r + 1) ⟶
      ModuleCat.of ℤ (groupCohomology N 0 →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + 0)) :=
  ModuleCat.ofHom (cupCyclesLinear M N r)

theorem cocycles_cup_cycles
    (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology.toCocycles M r (r + 1) ≫
      cupPositiveCycles M N r = 0 := by
  apply ModuleCat.hom_ext
  apply DFunLike.ext _ _
  intro f
  apply DFunLike.ext _ _
  intro y
  change groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
    (cupCocycle M N (r + 1) 0 (boundaryCocycle M r f)
      (zeroCocycleClass N y)) = 0
  exact cup_boundary_right M N r f (zeroCocycleClass N y)

/-- Mixed bidegree `(r+1,0)`, descended in the positive left variable. -/
noncomputable def cupCohomologyZero (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology M (r + 1) ⟶
      ModuleCat.of ℤ (groupCohomology N 0 →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + 0)) :=
  ((groupCohomology.inhomogeneousCochains M).homologyIsCokernel
      (i := r) (j := r + 1) (by simp)).desc
    (CokernelCofork.ofπ (cupPositiveCycles M N r)
      (cocycles_cup_cycles M N r))

theorem π_comp_cupCohomologyPositiveZero (M N : Rep ℤ G) (r : ℕ) :
    groupCohomology.π M (r + 1) ≫ cupCohomologyZero M N r =
      cupPositiveCycles M N r := by
  unfold cupCohomologyZero
  exact Cofork.IsColimit.π_desc
    ((groupCohomology.inhomogeneousCochains M).homologyIsCokernel
      (i := r) (j := r + 1) (by simp))

@[simp]
theorem cup_cohomology_zeroπ (M N : Rep ℤ G) (r : ℕ)
    (x : groupCohomology.cocycles M (r + 1))
    (y : groupCohomology.cocycles N 0) :
    (cupCohomologyZero M N r (groupCohomology.π M (r + 1) x))
        (groupCohomology.π N 0 y) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
        (cupCocycle M N (r + 1) 0 x y) := by
  have h := congrArg (fun q => q x) (π_comp_cupCohomologyPositiveZero M N r)
  have h' := h
  simp only [ConcreteCategory.comp_apply] at h'
  rw [h']
  change groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + 0)
      (cupCocycle M N (r + 1) 0 x
        (zeroCocycleClass N (groupCohomology.π N 0 y))) = _
  rw [zero_cocycle_classπ]

end Towers.CField.COps.CPBuild
