import Towers.ClassField.CohomologyOps.ZeroCocycleClass

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidalCategory

variable {G : Type} [Group G]

theorem cohomology_cast_symm (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    cohomologyCast A h ≫ cohomologyCast A h.symm = 𝟙 _ := by
  subst h
  simp [cohomologyCast]

/-- Positive-positive cup product with its output transported from the
successor-normalized degree to the literal sum of the two degrees. -/
noncomputable def cupCohomologyPositive
    (M N : Rep ℤ G) (r s : ℕ) (x : groupCohomology M (r + 1)) :
    groupCohomology N (s + 1) →ₗ[ℤ]
      groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1)) :=
  (cohomologyCast (M ⊗ N : Rep ℤ G)
      (by omega : (r + (s + 1)) + 1 = (r + 1) + (s + 1))).hom.comp
    ((cupBilinearPositive M N r s).hom x)

noncomputable def cupCohomologyAdd
    (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology M (r + 1) →+
      (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))) where
  toFun := cupCohomologyPositive M N r s
  map_zero' := by
    apply LinearMap.ext
    intro y
    simp [cupCohomologyPositive]
  map_add' x₁ x₂ := by
    apply LinearMap.ext
    intro y
    simp [cupCohomologyPositive]

noncomputable def cupPositive
    (M N : Rep ℤ G) (r s : ℕ) :
    groupCohomology M (r + 1) →ₗ[ℤ]
      (groupCohomology N (s + 1) →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))) where
  toFun := cupCohomologyAdd M N r s
  map_add' := (cupCohomologyAdd M N r s).map_add
  map_smul' a x := by
    change (cupCohomologyAdd M N r s)
        ((groupCohomology M (r + 1)).isModule.smul a x) =
      a • (cupCohomologyAdd M N r s) x
    rw [int_smul_eq_zsmul (groupCohomology M (r + 1)).isModule]
    exact (cupCohomologyAdd M N r s).map_zsmul a x

@[simp]
theorem cup_positiveπ (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M (r + 1))
    (y : groupCohomology.cocycles N (s + 1)) :
    cupPositive M N r s
        (groupCohomology.π M (r + 1) x)
        (groupCohomology.π N (s + 1) y) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))
        (cupCocycle M N (r + 1) (s + 1) x y) := by
  change cohomologyCast (M ⊗ N : Rep ℤ G)
      (by omega : (r + (s + 1)) + 1 = (r + 1) + (s + 1))
      (cupBilinearPositive M N r s
        (groupCohomology.π M (r + 1) x)
        (groupCohomology.π N (s + 1) y)) = _
  have hx := congrArg (fun q => q x)
    (π_comp_cupCohomologyBilinearPositive M N r s)
  simp only [ConcreteCategory.comp_apply] at hx
  rw [hx]
  have hy := congrArg (fun q => q y)
    (π_comp_normalizedCupCohomologyRight M N r s x)
  simp only [ConcreteCategory.comp_apply] at hy
  change cohomologyCast (M ⊗ N : Rep ℤ G) _
      (normalizedCupCohomology M N r s x
        (groupCohomology.π N (s + 1) y)) = _
  rw [hy]
  let h : (r + 1) + (s + 1) = (r + (s + 1)) + 1 := by omega
  change cohomologyCast (M ⊗ N : Rep ℤ G) h.symm
      (cohomologyCast (M ⊗ N : Rep ℤ G) h
        (groupCohomology.π (M ⊗ N : Rep ℤ G) ((r + 1) + (s + 1))
          (cupCocycle M N (r + 1) (s + 1) x y))) = _
  have hc := congrArg
    (fun q => q (groupCohomology.π (M ⊗ N : Rep ℤ G)
      ((r + 1) + (s + 1)) (cupCocycle M N (r + 1) (s + 1) x y)))
    (cohomology_cast_symm (M ⊗ N : Rep ℤ G) h)
  simpa only [ConcreteCategory.comp_apply] using hc

/-- The cup-product pairing of Proposition II.1.38, assembled for every pair
of nonnegative degrees. -/
noncomputable def cupCohomology (M N : Rep ℤ G) :
    (r s : ℕ) → groupCohomology M r →ₗ[ℤ]
      (groupCohomology N s →ₗ[ℤ]
        groupCohomology (M ⊗ N : Rep ℤ G) (r + s))
  | 0, 0 => cupZero M N
  | 0, s + 1 => cupZeroPositive M N s
  | r + 1, 0 => (cupCohomologyZero M N r).hom
  | r + 1, s + 1 => cupPositive M N r s

/-- The assembled pairing is represented by Milne's explicit inhomogeneous
cup formula in every pair of nonnegative degrees. -/
@[simp]
theorem cupCohomology_π (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s) :
    cupCohomology M N r s (groupCohomology.π M r x)
        (groupCohomology.π N s y) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) (r + s)
        (cupCocycle M N r s x y) := by
  cases r with
  | zero =>
      cases s with
      | zero =>
          simp [cupCohomology]
      | succ s =>
          simp [cupCohomology]
  | succ r =>
      cases s with
      | zero =>
          simpa [cupCohomology] using cup_cohomology_zeroπ M N r x y
      | succ s =>
          simp [cupCohomology]

end Towers.CField.COps.CPBuild
