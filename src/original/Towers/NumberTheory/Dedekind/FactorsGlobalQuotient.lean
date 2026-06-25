import Towers.NumberTheory.Dedekind.InvariantFactorsPadding

/-!
# Milne, Algebraic Number Theory, global invariant factors for primary cyclic columns

This is the global CRT assembly step in Theorem 3.32.  A finite family of prime-primary cyclic
columns is padded, sorted within each column, and transposed into a descending sequence of global
ideal quotients.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- Prime-power cyclic columns at distinct maximal ideals assemble into quotients by a descending
chain of integral ideals. -/
theorem invariant_quotients_columns
    (A : Type*) [CommRing A]
    (ι : Type*) [Finite ι]
    (P : ι → Ideal A) (hP : ∀ i, (P i).IsMaximal)
    (hP_inj : Function.Injective P)
    (d : ι → ℕ) (e : ∀ i, Fin (d i) → ℕ) :
    ∃ (n : ℕ) (b : Fin n → Ideal A),
      Antitone b ∧
        Nonempty
          ((⨁ i, ⨁ j, A ⧸ P i ^ e i j) ≃ₗ[A]
            ⨁ j, A ⧸ b j) := by
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨n, e', ⟨hrect⟩⟩ :=
    rectangular_prime_columns A ι P d e
  let b : Fin n → Ideal A := invariantFactorIdeal A ι P n e'
  refine ⟨n, b, invariant_factor_antitone A ι P n e', ⟨hrect ≪≫ₗ ?_⟩⟩
  exact (primaryColumnsUnsorted
    A ι P hP hP_inj n e').symm

end Towers.NumberTheory.Milne
