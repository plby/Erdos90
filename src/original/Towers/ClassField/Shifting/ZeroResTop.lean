import Towers.ClassField.Shifting.AssemblingShifts
import Towers.ClassField.Shifting.BoundaryIso

/-!
# Milne, Class Field Theory, Theorem II.3.11

This file packages Tate's two-degree shift in every Tate range represented by
the project.  The isomorphisms are attached to the chosen generator
`gamma : H²(G,C)`.
-/

namespace Towers.CField.Shifting

open AddSubgroup CategoryTheory CategoryTheory.Limits Rep

noncomputable section

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
/-- Vanishing after restriction to the top subgroup implies vanishing over
the original group.  Shapiro restriction has a left inverse because the top
subgroup has index one. -/
theorem cohomology_res_top
    (C : Rep ℤ G) (n : ℕ)
    (h : IsZero (groupCohomology (Rep.res (⊤ : Subgroup G).subtype C) n)) :
    IsZero (groupCohomology C n) := by
  letI : Subsingleton
      (groupCohomology (Rep.res (⊤ : Subgroup G).subtype C) n) :=
    ModuleCat.subsingleton_of_isZero h
  letI : Subsingleton (groupCohomology C n) := by
    constructor
    intro x y
    suffices ∀ z : groupCohomology C n, z = 0 by
      rw [this x, this y]
    intro z
    let r := COps.shapiroRestriction C (⊤ : Subgroup G) n
    let c := COps.corestriction C (⊤ : Subgroup G) n
    have hrel : (r ≫ c) z = (⊤ : Subgroup G).index • z := by
      exact congrArg (fun q ↦ q z)
        (COps.shapiro_restriction_corestriction
          C (⊤ : Subgroup G) n)
    have hrz : r z = 0 := Subsingleton.elim _ _
    calc
      z = (⊤ : Subgroup G).index • z := by simp
      _ = (r ≫ c) z := hrel.symm
      _ = c (r z) := rfl
      _ = 0 := by rw [hrz, map_zero]
  exact ModuleCat.isZero_of_subsingleton _

/-- **Theorem II.3.11.** Let `C` satisfy `H¹(H,C)=0`, and let every
`H²(H,C)` have order `|H|`.  A chosen generator of `H²(G,C)` determines
isomorphisms `H_T^r(G,ℤ) ≅ H_T^(r+2)(G,C)` in every Tate range represented
by the project. -/
noncomputable def cohomologyResTop
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) :
    TateTwoShift C := by
  apply restricted_boundary_iso C gamma hgamma
    (by simpa [Nat.card_eq_fintype_card] using hcardG)
    (cohomology_res_top C 1 (hC1 ⊤)) hC1
  intro H
  exact splitting_boundary_iso C gamma hgamma hcardG hcardH H

end

end Towers.CField.Shifting
