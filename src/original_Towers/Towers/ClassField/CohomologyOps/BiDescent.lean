import Towers.ClassField.CohomologyOps.CupLinearRight

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidalCategory

variable {G : Type} [Group G]

/-- Transport cocycles along an equality of degrees. -/
noncomputable def cocyclesCast (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    groupCohomology.cocycles A m ⟶ groupCohomology.cocycles A n :=
  eqToHom (congrArg (groupCohomology.cocycles A) h)

/-- Transport cohomology classes along an equality of degrees. -/
noncomputable def cohomologyCast (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    groupCohomology A m ⟶ groupCohomology A n :=
  eqToHom (congrArg (groupCohomology A) h)

theorem cocycles_cast_i (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    cocyclesCast A h ≫ groupCohomology.iCocycles A n =
      groupCohomology.iCocycles A m ≫
        eqToHom (congrArg (fun j => (groupCohomology.inhomogeneousCochains A).X j) h) := by
  subst h
  simp [cocyclesCast]

theorem π_comp_cohomologyCast (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    groupCohomology.π A m ≫ cohomologyCast A h =
      cocyclesCast A h ≫ groupCohomology.π A n := by
  subst h
  simp [cocyclesCast, cohomologyCast]

theorem cochain_hom (A : Rep ℤ G) {m n : ℕ} (h : m = n)
    (f : (Fin m → G) → A) :
    (eqToHom (congrArg (fun j => (groupCohomology.inhomogeneousCochains A).X j) h)) f =
      cochainCast h.symm f := by
  subst h
  rfl

theorem cup_boundary_cast (M N : Rep ℤ G) (r s : ℕ)
    (f : (Fin r → G) → M) (y : groupCohomology.cocycles N s) :
    cohomologyCast (M ⊗ N : Rep ℤ G)
        (by omega : (r + 1) + s = (r + s) + 1)
        (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + s)
          (cupCocycle M N (r + 1) s (boundaryCocycle M r f) y)) = 0 := by
  let h : (r + 1) + s = (r + s) + 1 := by omega
  have hc :
      cocyclesCast (M ⊗ N : Rep ℤ G) h
          (cupCocycle M N (r + 1) s (boundaryCocycle M r f) y) =
        boundaryCupLeft M N r s f y := by
    apply (ModuleCat.mono_iff_injective
      (groupCohomology.iCocycles (M ⊗ N : Rep ℤ G) ((r + s) + 1))).1 inferInstance
    have hi := congrArg
      (fun q => q (cupCocycle M N (r + 1) s (boundaryCocycle M r f) y))
      (cocycles_cast_i (M ⊗ N : Rep ℤ G) h)
    have hi' := hi
    simp only [ConcreteCategory.comp_apply] at hi'
    rw [cochain_hom, i_cup_cocycle,
      cocycles_boundary_cocycle] at hi'
    · rw [hi']
      rw [i_cocycles_cup]
    · exact h
  have hp := congrArg
    (fun q => q (cupCocycle M N (r + 1) s (boundaryCocycle M r f) y))
    (π_comp_cohomologyCast (M ⊗ N : Rep ℤ G) h)
  have hp' := hp
  simp only [ConcreteCategory.comp_apply] at hp'
  rw [hc, boundary_cup_left] at hp'
  exact hp'

/-- For positive degrees in both variables, normalize the output degree so a
left coboundary lands in the literal successor degree used by the complex. -/
noncomputable def normalizedCupCohomology (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M (r + 1)) :
    groupCohomology N (s + 1) ⟶
      groupCohomology (M ⊗ N : Rep ℤ G) ((r + (s + 1)) + 1) :=
  cupCohomologyRight M N (r + 1) s x ≫
    cohomologyCast (M ⊗ N : Rep ℤ G)
      (by omega : (r + 1) + (s + 1) = (r + (s + 1)) + 1)

theorem π_comp_normalizedCupCohomologyRight (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M (r + 1)) :
    groupCohomology.π N (s + 1) ≫ normalizedCupCohomology M N r s x =
      cupCocyclesCohomology M N (r + 1) s x ≫
        cohomologyCast (M ⊗ N : Rep ℤ G)
          (by omega : (r + 1) + (s + 1) = (r + (s + 1)) + 1) := by
  unfold normalizedCupCohomology
  rw [← Category.assoc, π_comp_cupCohomologyRight]

theorem normalized_cup_add (M N : Rep ℤ G) (r s : ℕ)
    (x₁ x₂ : groupCohomology.cocycles M (r + 1)) :
    normalizedCupCohomology M N r s (x₁ + x₂) =
      normalizedCupCohomology M N r s x₁ +
        normalizedCupCohomology M N r s x₂ := by
  ext z
  induction z using groupCohomology_induction_on with
  | h y =>
  have hsum := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s (x₁ + x₂))
  have h₁ := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s x₁)
  have h₂ := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s x₂)
  simp only [ConcreteCategory.comp_apply] at hsum h₁ h₂
  rw [hsum]
  change _ = normalizedCupCohomology M N r s x₁
      (groupCohomology.π N (s + 1) y) +
    normalizedCupCohomology M N r s x₂
      (groupCohomology.π N (s + 1) y)
  rw [h₁, h₂]
  have hc := congrArg (fun q => q y)
    ((cocycleCupAdd M N (r + 1) (s + 1)).map_add x₁ x₂)
  have hc' :
      cupCocycle M N (r + 1) (s + 1) (x₁ + x₂) y =
        cupCocycle M N (r + 1) (s + 1) x₁ y +
          cupCocycle M N (r + 1) (s + 1) x₂ y := hc
  change cohomologyCast (M ⊗ N : Rep ℤ G) _
      (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))
        (cupCocycle M N (r + 1) (s + 1) (x₁ + x₂) y)) = _
  rw [hc']
  simp only [map_add]
  rfl

theorem normalized_cup_cohomology (M N : Rep ℤ G) (r s : ℕ) :
    normalizedCupCohomology M N r s 0 = 0 := by
  ext z
  induction z using groupCohomology_induction_on with
  | h y =>
  have hzero := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s 0)
  simp only [ConcreteCategory.comp_apply] at hzero
  rw [hzero]
  have hc := congrArg (fun q => q y)
    ((cocycleCupAdd M N (r + 1) (s + 1)).map_zero)
  have hc' : cupCocycle M N (r + 1) (s + 1) 0 y = 0 := hc
  change cohomologyCast (M ⊗ N : Rep ℤ G) _
      (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))
        (cupCocycle M N (r + 1) (s + 1) 0 y)) = 0
  rw [hc']
  simp only [map_zero]

noncomputable def normalizedCupAdd (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.cocycles M (r + 1) →+
      (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + (s + 1)) + 1)) where
  toFun x := (normalizedCupCohomology M N r s x).hom
  map_zero' := by
    exact congrArg ModuleCat.Hom.hom
      (normalized_cup_cohomology M N r s)
  map_add' x₁ x₂ := by
    exact congrArg ModuleCat.Hom.hom
      (normalized_cup_add M N r s x₁ x₂)

theorem normalized_cup_boundary (M N : Rep ℤ G)
    (r s : ℕ) (f : (Fin r → G) → M) :
    normalizedCupCohomology M N r s (boundaryCocycle M r f) = 0 := by
  ext z
  induction z using groupCohomology_induction_on with
  | h y =>
  have hv := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s (boundaryCocycle M r f))
  simp only [ConcreteCategory.comp_apply] at hv
  rw [hv]
  change cohomologyCast (M ⊗ N : Rep ℤ G)
      (by omega : (r + 1) + (s + 1) = (r + (s + 1)) + 1)
      (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))
        (cupCocycle M N (r + 1) (s + 1) (boundaryCocycle M r f) y)) = 0
  exact cup_boundary_cast M N r (s + 1) f y

noncomputable def normalizedCupLinear (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.cocycles M (r + 1) →ₗ[ℤ]
      (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + (s + 1)) + 1)) where
  toFun := normalizedCupAdd M N r s
  map_add' := (normalizedCupAdd M N r s).map_add
  map_smul' a x := by
    change (normalizedCupAdd M N r s)
        ((groupCohomology.cocycles M (r + 1)).isModule.smul a x) =
      a • (normalizedCupAdd M N r s) x
    rw [int_smul_eq_zsmul (groupCohomology.cocycles M (r + 1)).isModule]
    exact (normalizedCupAdd M N r s).map_zsmul a x

noncomputable def normalizedCupCycles (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.cocycles M (r + 1) ⟶
      ModuleCat.of ℤ (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + (s + 1)) + 1)) :=
  ModuleCat.ofHom (normalizedCupLinear M N r s)

theorem cocycles_normalized_cycles
    (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.toCocycles M r (r + 1) ≫
      normalizedCupCycles M N r s = 0 := by
  apply ModuleCat.hom_ext
  apply DFunLike.ext _ _
  intro f
  apply DFunLike.ext _ _
  intro y
  change normalizedCupCohomology M N r s (boundaryCocycle M r f) y = 0
  rw [normalized_cup_boundary]
  rfl

/-- The cup product descended in both variables, in positive degrees.  The
output degree is normalized to the literal successor `(r + (s+1)) + 1`. -/
noncomputable def cupBilinearPositive (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology M (r + 1) ⟶
      ModuleCat.of ℤ (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + (s + 1)) + 1)) :=
  ((groupCohomology.inhomogeneousCochains M).homologyIsCokernel
      (i := r) (j := r + 1) (by simp)).desc
    (CokernelCofork.ofπ (normalizedCupCycles M N r s)
      (cocycles_normalized_cycles M N r s))

theorem π_comp_cupCohomologyBilinearPositive (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology.π M (r + 1) ≫ cupBilinearPositive M N r s =
      normalizedCupCycles M N r s := by
  unfold cupBilinearPositive
  exact Cofork.IsColimit.π_desc
    ((groupCohomology.inhomogeneousCochains M).homologyIsCokernel
      (i := r) (j := r + 1) (by simp))

end Towers.CField.COps.CPBuild
