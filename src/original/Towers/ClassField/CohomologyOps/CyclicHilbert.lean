import Towers.ClassField.CohomologyOps.HilbertNinetyCoboundary

/-!
# Chapter II, Corollary 1.23: cyclic Hilbert 90
-/

namespace Towers.CField.COps

open groupCohomology

/-- **Corollary II.1.23.** If `L/K` is cyclic, `sigma` generates its Galois
group, and `a` has norm one, then `a = sigma(b) / b` for some `b ∈ Lˣ`. -/
theorem gal_div_one
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {sigma : Gal(L/K)} (hsigma : ∀ τ, τ ∈ Subgroup.zpowers sigma)
    {a : L} (ha : Algebra.norm K a = 1) :
    ∃ b : Lˣ, sigma b / b = a := by
  have ha_inv : Algebra.norm K a⁻¹ = 1 := by
    rw [Algebra.norm_inv, ha, inv_one]
  obtain ⟨b, hb⟩ := exists_div_of_norm_eq_one (K := K) (L := L) hsigma ha_inv
  refine ⟨b, ?_⟩
  calc
    sigma b / b = (b / sigma b)⁻¹ := by simp
    _ = (a⁻¹)⁻¹ := congrArg Inv.inv hb
    _ = a := inv_inv a

end Towers.CField.COps
