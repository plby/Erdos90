import Submission.ClassField.SimpleAlgebras.PairwiseModulesIsomorphic

/-!
# Milne, Class Field Theory, Corollary IV.1.20

Minimal left ideals in a finite-dimensional simple algebra are mutually
isomorphic, and the regular module is their finite direct sum.
-/

namespace Submission.CField.SAlgebr

universe u v

variable (k : Type u) (A : Type v)
variable [Field k] [Ring A] [Algebra k A]
variable [Module.Finite k A] [IsSimpleRing A]

include k

/-- **Corollary IV.1.20, first part.** Any two minimal left ideals are
isomorphic as left modules. -/
theorem minimal_ideals_isomorphic
    (I J : Ideal A) [IsSimpleModule A I] [IsSimpleModule A J] :
    Nonempty (I ≃ₗ[A] J) := by
  letI : IsSemisimpleRing A := simple_semisimple_ring k A
  exact simple_modules_isotypic A
    (IsSimpleRing.isIsotypic A A) I J

/-- **Corollary IV.1.20, second part.** The left regular module is a finite
direct sum of minimal left ideals. -/
theorem direct_minimal_ideals :
    ∃ (n : ℕ) (I : Fin n → Ideal A),
      (∀ i, IsSimpleModule A (I i)) ∧
      Nonempty (A ≃ₗ[A] Π₀ i, I i) := by
  letI : IsSemisimpleRing A := simple_semisimple_ring k A
  obtain ⟨n, I, e, hI⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A A
  exact ⟨n, I, hI, ⟨e⟩⟩

end Submission.CField.SAlgebr
