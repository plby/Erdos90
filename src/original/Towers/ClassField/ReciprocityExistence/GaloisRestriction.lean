import Mathlib.FieldTheory.Galois.Basic

/-!
# Restriction from a literal compositum

This lightweight file isolates the Galois-theoretic vertical map used in
VII.8.4(b), independently of the finite idèle norm implementation.
-/

namespace Towers.CField.RExist

open Set

noncomputable section

universe u

variable {K K' M : Type u}
    [Field K] [Field K'] [Field M]
    [Algebra K K'] [Algebra K' M] [Algebra K M]
    [IsScalarTower K K' M]

/-- A `K'`-automorphism of the compositum is in particular a
`K`-automorphism. -/
def compositumRestrictScalars : Gal(M/K') →* Gal(M/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

variable (E : IntermediateField K M) [Normal K E]

/-- The literal right vertical arrow in VII.8.4(b): restrict an automorphism
of the compositum over `K'` to the normal lower field `E/K`. -/
def compositumGaloisRestriction : Gal(M/K') →* Gal(E/K) :=
  (AlgEquiv.restrictNormalHom E).comp compositumRestrictScalars

/-- Restriction from `Gal(EK'/K')` to `Gal(E/K)` is injective because an
automorphism fixing `K'` and `E` fixes their compositum. -/
theorem compositum_restriction_injective
    (hcompositum : E ⊔ IntermediateField.adjoin K
      (Set.range (algebraMap K' M)) = ⊤) :
    Function.Injective (compositumGaloisRestriction
      (K := K) (K' := K') (M := M) E) := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  let equalizer : IntermediateField K M :=
    { carrier := {x | σ x = τ x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change σ (x + y) = τ (x + y)
        rw [map_add, hx, hy, map_add]
      mul_mem' := by
        intro x y hx hy
        change σ (x * y) = τ (x * y)
        rw [map_mul, hx, hy, map_mul]
      inv_mem' := by
        intro x hx
        change σ x⁻¹ = τ x⁻¹
        rw [map_inv₀, hx, map_inv₀]
      algebraMap_mem' := by
        intro x
        change σ (algebraMap K M x) = τ (algebraMap K M x)
        rw [IsScalarTower.algebraMap_apply K K' M,
          σ.commutes, τ.commutes] }
  have hE : E ≤ equalizer := by
    intro y hy
    change σ y = τ y
    have hy' := DFunLike.congr_fun hστ ⟨y, hy⟩
    change (AlgEquiv.restrictNormalHom E (σ.restrictScalars K)) ⟨y, hy⟩ =
      (AlgEquiv.restrictNormalHom E (τ.restrictScalars K)) ⟨y, hy⟩ at hy'
    have hyval := congrArg Subtype.val hy'
    calc
      σ y = ((AlgEquiv.restrictNormalHom E (σ.restrictScalars K)
          ⟨y, hy⟩ : E) : M) :=
        (AlgEquiv.restrictNormalHom_apply E (σ.restrictScalars K)
          ⟨y, hy⟩).symm
      _ = ((AlgEquiv.restrictNormalHom E (τ.restrictScalars K)
          ⟨y, hy⟩ : E) : M) := hyval
      _ = τ y := AlgEquiv.restrictNormalHom_apply E (τ.restrictScalars K)
        ⟨y, hy⟩
  have hK' : IntermediateField.adjoin K
      (Set.range (algebraMap K' M)) ≤ equalizer := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, rfl⟩
    change σ (algebraMap K' M z) = τ (algebraMap K' M z)
    rw [σ.commutes, τ.commutes]
  have htop : (⊤ : IntermediateField K M) ≤ equalizer := by
    rw [← hcompositum]
    exact sup_le hE hK'
  exact htop (by simp)

end

end Towers.CField.RExist
