import Submission.NumberTheory.Dedekind.FactorPseudobasisExistence
import Submission.NumberTheory.Dedekind.FactorPresentationUniqueness
import Submission.NumberTheory.Dedekind.InvariantFactorTheorem

/-!
# Milne's invariant-factor theorem in simultaneous pseudobasis form
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u

/-- **Theorem 3.32 (Invariant Factor Theorem).** A same-rank inclusion of finite torsion-free
modules over a Dedekind domain admits simultaneous ideal pseudobases with a descending chain of
integral invariant factors. The chain is uniquely determined by the quotient, hence by the pair
`M ⊇ N`. -/
theorem dedekind_rank_pseudobasis
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (hrank : Module.finrank A N = Module.finrank A M) :
    ∃ b : Fin (Module.finrank A M) → Ideal A,
      Antitone b ∧
        Nonempty
          (IFPseudo A M N (Module.finrank A M) b) ∧
        Nonempty ((M ⧸ N) ≃ₗ[A]
          DirectSum (Fin (Module.finrank A M))
            (fun i ↦ idealQuotientModule A (b i))) ∧
        ∀ c : Fin (Module.finrank A M) → Ideal A,
          Antitone c →
          Nonempty ((M ⧸ N) ≃ₗ[A]
            DirectSum (Fin (Module.finrank A M))
              (fun i ↦ idealQuotientModule A (c i))) →
          c = b := by
  obtain ⟨n, b₀, hb₀, ⟨e₀⟩⟩ :=
    dedekind_same_decomposition
      A M N hrank
  obtain ⟨b, hb, hpb, ⟨eb⟩⟩ :=
    rank_invariant_pseudobasis
      A M N n b₀ hb₀ e₀
  refine ⟨b, hb, hpb, ⟨eb⟩, ?_⟩
  intro c hc ⟨ec⟩
  exact invariant_factors_common
    A (M ⧸ N) (Module.finrank A M) c b hc hb ec eb

end Submission.NumberTheory.Milne
