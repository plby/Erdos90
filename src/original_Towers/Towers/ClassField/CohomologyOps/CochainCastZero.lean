import Towers.ClassField.CohomologyOps.InitialTupleCast

namespace Towers.CField.COps.CPBuild

open CategoryTheory
open scoped MonoidalCategory

variable {G : Type} [Group G]

omit [Group G] in
@[simp]
theorem cochainCast_zero {A : Type*} [Zero A] {m n : ℕ} (h : m = n) :
    cochainCast (G := G) h (0 : (Fin n → G) → A) = 0 := by
  rfl

/-- The explicit cup of two inhomogeneous cocycles is again a cocycle. -/
theorem cochain_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (hφ : cochainDifferential M r φ = 0)
    (hψ : cochainDifferential N s ψ = 0) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s φ ψ) = 0 := by
  rw [cochainCup_d, hφ, hψ]
  simp only [cochain_cup_left, cochain_cup_right]
  rfl

/-- Cup product with a cocycle sends a coboundary in the left variable to the
coboundary of the lower-degree cup. -/
theorem cochain_cup_d (M N : Rep ℤ G) (r s : ℕ)
    (α : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (hψ : cochainDifferential N s ψ = 0) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s α ψ) =
      cochainCast (by omega : (r + s) + 1 = (r + 1) + s)
        (cochainCup M N (r + 1) s
          (cochainDifferential M r α) ψ) := by
  rw [cochainCup_d, hψ]
  simp only [cochain_cup_right, cochainCast_zero, smul_zero, add_zero]

/-- Cup product with a cocycle sends a coboundary in the right variable to a
signed coboundary, with the sign dictated by the left degree. -/
theorem cochain_d_cocycle (M N : Rep ℤ G) (r s : ℕ)
    (φ : (Fin r → G) → M) (β : (Fin s → G) → N)
    (hφ : cochainDifferential M r φ = 0) :
    cochainDifferential (M ⊗ N : Rep ℤ G) (r + s)
        (cochainCup M N r s φ β) =
      (-1 : ℤ) ^ r •
        cochainCast (by omega : (r + s) + 1 = r + (s + 1))
          (cochainCup M N r (s + 1) φ
            (cochainDifferential N s β)) := by
  rw [cochainCup_d, hφ]
  simp only [cochain_cup_left, cochainCast_zero, zero_add]

end Towers.CField.COps.CPBuild
