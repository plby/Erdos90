import Towers.NumberTheory.Dedekind.InvariantFactorsUniqueness
import Mathlib.Data.Fin.SuccPred

/-!
# Helpers for rank-sized invariant-factor recursion
-/

namespace Towers.NumberTheory.Milne

/-- Appending a common lower bound to an antitone finite tuple preserves antitonicity. -/
theorem antitone_fin_snoc
    {L : Type*} [Preorder L]
    {n : ℕ} (c : Fin n → L) (hc : Antitone c) (z : L)
    (hz : ∀ i, z ≤ c i) :
    Antitone (Fin.snoc c z) := by
  intro i j hij
  by_cases hj : j = Fin.last n
  · subst j
    by_cases hi : i = Fin.last n
    · subst i
      exact le_rfl
    · rw [← Fin.castSucc_castPred i hi]
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hz (i.castPred hi)
  · have hi : i ≠ Fin.last n := by
      intro hi
      subst i
      apply hj
      exact Fin.le_antisymm (Fin.le_last j) hij
    rw [← Fin.castSucc_castPred i hi, ← Fin.castSucc_castPred j hj]
    simpa only [Fin.snoc_castSucc] using
      hc ((Fin.castPred_le_castPred_iff).mpr hij)

/-- If multiplication by every element of `I` carries the ambient module into `P`, then `I`
annihilates the quotient by `P`. -/
theorem annihilator_smul_top
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (P : Submodule A M)
    (h : I • (⊤ : Submodule A M) ≤ P) :
    I ≤ Module.annihilator A (M ⧸ P) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact h (Submodule.smul_mem_smul hr Submodule.mem_top)

end Towers.NumberTheory.Milne
