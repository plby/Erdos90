import Submission.NumberTheory.Dedekind.InvariantFactorsCRT

/-!
# Milne, Algebraic Number Theory, assembly of invariant factors

The elementary-divisor description of a finite torsion module records one column of cyclic
prime-power quotients for each prime.  Once these columns have a common finite length, sorting
each column and applying the Chinese remainder theorem row by row produces the descending chain
of invariant factors.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

/-- A rectangular prime-primary cyclic decomposition assembles into a decomposition by a
descending chain of invariant-factor ideals. -/
theorem invariant_primary_columns
    (A T : Type*) [CommRing A]
    [AddCommGroup T] [Module A T]
    (ι : Type*) [Finite ι]
    (P : ι → Ideal A) (hP : ∀ i, (P i).IsMaximal)
    (hP_inj : Function.Injective P)
    (n : ℕ) (e : ι → Fin n → ℕ)
    (hT : Nonempty
      (T ≃ₗ[A] ⨁ i, ⨁ j, A ⧸ P i ^ e i j)) :
    ∃ b : Fin n → Ideal A,
      Antitone b ∧ Nonempty (T ≃ₗ[A] ⨁ j, A ⧸ b j) := by
  classical
  letI := Fintype.ofFinite ι
  let b : Fin n → Ideal A := invariantFactorIdeal A ι P n e
  let sortColumns :
      (⨁ i, ⨁ j, A ⧸ P i ^ e i j) ≃ₗ[A]
        ⨁ i, ⨁ j, A ⧸ P i ^ sortedExponents (e i) j :=
    DFinsupp.mapRange.linearEquiv fun i ↦
      sortDirectLinear A (P i) n (e i)
  refine ⟨b, invariant_factor_antitone A ι P n e, ?_⟩
  obtain ⟨equiv⟩ := hT
  exact ⟨equiv.trans sortColumns |>.trans
    (quotientsPrimaryColumns A ι P hP hP_inj n e).symm⟩

end Submission.NumberTheory.Milne
