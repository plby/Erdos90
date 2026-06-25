import Submission.NumberTheory.Dedekind.InvariantFactorsQuotient
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Rank-sized local invariant factors

Over a PID, the quotient decomposition attached to a same-rank inclusion has exactly the rank of
the ambient torsion-free module many cyclic slots.
-/

namespace Submission.NumberTheory.Milne

open Module
open scoped DirectSum

universe u v

/-- The PID quotient decomposition indexed by exactly `Module.finrank R M` cyclic factors. -/
theorem pid_same_direct
    (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ I : Fin (Module.finrank R M) → Ideal R,
      (∀ i, I i ≠ ⊥) ∧
        Nonempty ((M ⧸ N) ≃ₗ[R]
          ⨁ i : Fin (Module.finrank R M), R ⧸ I i) := by
  classical
  let ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  let a : Fin n → R := N.smithNormalFormCoeffs b h
  have ha : ∀ i, a i ≠ 0 := fun i =>
    N.smithNormalFormCoeffs_ne_zero b h i
  have hn : n = Module.finrank R M := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let reindex : Fin n ≃ Fin (Module.finrank R M) := finCongr hn
  let I : Fin (Module.finrank R M) → Ideal R := fun i =>
    Ideal.span ({a (reindex.symm i)} : Set R)
  have hI : ∀ i, I i ≠ ⊥ := by
    intro i
    change Ideal.span ({a (reindex.symm i)} : Set R) ≠ ⊥
    exact Ideal.span_singleton_eq_bot.not.mpr (ha (reindex.symm i))
  let quotientPi :
      (M ⧸ N) ≃ₗ[R]
        ∀ i : Fin n, R ⧸ Ideal.span ({a i} : Set R) :=
    N.quotientEquivPiSpan b h
  let piDirectSum :
      (∀ i : Fin n, R ⧸ Ideal.span ({a i} : Set R)) ≃ₗ[R]
        ⨁ i : Fin n, R ⧸ Ideal.span ({a i} : Set R) :=
    (DirectSum.linearEquivFunOnFintype R (Fin n)
      (fun i => R ⧸ Ideal.span ({a i} : Set R))).symm
  let reindexDirectSum :
      (⨁ i : Fin n, R ⧸ Ideal.span ({a i} : Set R)) ≃ₗ[R]
        ⨁ i : Fin (Module.finrank R M), R ⧸ I i := by
    simpa [I, reindex] using
      (DirectSum.lequivCongrLeft R reindex :
        (⨁ i : Fin n, R ⧸ Ideal.span ({a i} : Set R)) ≃ₗ[R]
          ⨁ i : Fin (Module.finrank R M),
            R ⧸ Ideal.span ({a (reindex.symm i)} : Set R))
  exact ⟨I, hI, ⟨quotientPi ≪≫ₗ piDirectSum ≪≫ₗ reindexDirectSum⟩⟩

end Submission.NumberTheory.Milne
