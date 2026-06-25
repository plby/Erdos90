import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Towers.ClassField.CohomologyOps.NatCardNsmul

/-!
# Milne, Class Field Theory, Corollary II.1.32

Positive-degree cohomology of a finite group with finitely generated abelian coefficients is
finite.  The proof follows Milne: the inhomogeneous cochain groups, hence cocycles and their
cohomology quotients, are finitely generated; Corollary II.1.31 makes the cohomology torsion.
-/

namespace Towers.CField.COps

open CategoryTheory Rep

variable {G : Type} [Group G] [Finite G]

noncomputable section

/-- The inhomogeneous `r`-cochains of a finite group are finitely generated whenever the
coefficient abelian group is finitely generated. -/
instance cohomology_module_cochains
    (A : Rep ℤ G) [Module.Finite ℤ A] (r : ℕ) :
    Module.Finite ℤ ((groupCohomology.inhomogeneousCochains A).X r) := by
  let f : ((Fin r → G) → A) →ₗ[ℤ]
      ((groupCohomology.inhomogeneousCochains A).X r) :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro m x
        rw [RingHom.id_apply] }
  exact Module.Finite.of_surjective f fun x ↦ ⟨x, rfl⟩

/-- The group of inhomogeneous `r`-cocycles is finitely generated over `ℤ`. -/
instance cohomology_module_cocycles
    (A : Rep ℤ G) [Module.Finite ℤ A] (r : ℕ) :
    Module.Finite ℤ (groupCohomology.cocycles A r) := by
  letI : IsNoetherian ℤ ((groupCohomology.inhomogeneousCochains A).X r) := inferInstance
  let f : groupCohomology.cocycles A r →ₗ[ℤ]
      (groupCohomology.inhomogeneousCochains A).X r :=
    { toFun := fun x ↦ groupCohomology.iCocycles A r x
      map_add' := map_add (groupCohomology.iCocycles A r).hom
      map_smul' := by
        intro m x
        convert! AddMonoidHom.map_zsmul
          (groupCohomology.iCocycles A r).hom.toAddMonoidHom m x
        all_goals
          ext
          apply int_smul_eq_zsmul }
  apply Module.Finite.of_injective f
  intro x y hxy
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles A r)).mp (by infer_instance)
  change groupCohomology.iCocycles A r x =
    groupCohomology.iCocycles A r y at hxy
  exact hxy

/-- Group cohomology of a finite group with finitely generated abelian coefficients remains
finitely generated as an abelian group. -/
instance cohomology_module_finite
    (A : Rep ℤ G) [Module.Finite ℤ A] (r : ℕ) :
    Module.Finite ℤ (groupCohomology A r) := by
  apply Module.Finite.of_surjective (groupCohomology.π A r).hom
  exact fun x ↦ groupCohomology_induction_on x fun y ↦ ⟨y, rfl⟩

/-- **Corollary II.1.32.** For a finite group `G` and a `G`-module finitely generated as an
abelian group, `H^r(G,A)` is finite in every positive degree. -/
theorem finite_cohomology_module
    (A : Rep ℤ G) [Module.Finite ℤ A] (r : ℕ) (hr : 0 < r) :
    Finite (groupCohomology A r) := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(Nat.card G : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
  · exact Int.ofNat_ne_zero.mpr Nat.card_pos.ne'
  · change (groupCohomology A r).isModule.smul (Nat.card G : ℤ) x = 0
    rw [int_smul_eq_zsmul (groupCohomology A r).isModule, natCast_zsmul]
    exact nat_nsmul_cohomology A r hr x

end

end Towers.CField.COps
