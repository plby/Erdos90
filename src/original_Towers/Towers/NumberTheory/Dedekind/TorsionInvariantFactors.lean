import Towers.NumberTheory.Dedekind.DedekindModules
import Towers.NumberTheory.Dedekind.PrimePowerDecomposition
import Towers.NumberTheory.Dedekind.FactorsGlobalQuotient

/-!
# Milne, Algebraic Number Theory, invariant factors of finite torsion modules

The primary decomposition gives one finite cyclic column for each prime.  Reindexing those
columns by finite ordinals and applying the global CRT assembly yields Milne's invariant-factor
description of every finite torsion module over a Dedekind domain.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

universe u v

/- **Invariant-factor theorem for finite torsion modules over a Dedekind domain.** -/
set_option maxHeartbeats 2000000 in
-- Choosing and padding all primary cyclic columns creates a large dependent elaboration problem.
theorem torsion_invariant_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    ∃ (n : ℕ) (b : Fin n → Ideal A),
      Antitone b ∧ Nonempty (M ≃ₗ[A] ⨁ j, A ⧸ b j) := by
  classical
  obtain ⟨ℙ, _, hℙ, d, hInternal⟩ :=
    torsion_prime_decomposition A M hM
  let T : ℙ → Submodule A M := fun p ↦
    Submodule.torsionBySet A M (p.1 ^ d p : Ideal A)
  have hcomponent (p : ℙ) :
      ∃ (ι : Type u) (_ : Fintype ι) (e : ι → ℕ),
        Nonempty (T p ≃ₗ[A] ⨁ i : ι, A ⧸ p.1 ^ e i) := by
    letI : p.1.IsPrime := Ideal.isPrime_of_prime (hℙ p.1 p.2)
    letI : Module.Finite A (T p) :=
      Module.Finite.of_fg (IsNoetherian.noetherian (T p))
    exact dedekind_torsion_decomposition
      A (T p) p.1 (hℙ p.1 p.2).ne_zero (d p)
        (Submodule.torsionBySet_isTorsionBySet
          (R := A) (M := M) ((p.1 ^ d p : Ideal A) : Set A))
  choose ι hι e he using hcomponent
  letI (p : ℙ) : Fintype (ι p) := hι p
  let card : ℙ → ℕ := fun p => Fintype.card (ι p)
  let idx : ∀ p : ℙ, ι p ≃ Fin (card p) := fun p => Fintype.equivFin (ι p)
  let eFin : ∀ p : ℙ, Fin (card p) → ℕ := fun p j => e p ((idx p).symm j)
  let primaryEquiv : M ≃ₗ[A] ⨁ p : ℙ, T p :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap T) hInternal).symm
  let componentEquiv :
      (⨁ p : ℙ, T p) ≃ₗ[A]
        ⨁ p : ℙ, ⨁ j : Fin (card p), A ⧸ p.1 ^ eFin p j :=
    DFinsupp.mapRange.linearEquiv fun p =>
      (he p).some ≪≫ₗ DirectSum.lequivCongrLeft A (idx p)
  have hPmax : ∀ p : ℙ, (p.1 : Ideal A).IsMaximal := by
    intro p
    exact Ideal.IsPrime.isMaximal
      (Ideal.isPrime_of_prime (hℙ p.1 p.2)) (hℙ p.1 p.2).ne_zero
  have hPinj : Function.Injective (fun p : ℙ => (p.1 : Ideal A)) := by
    intro p q hpq
    exact Subtype.ext hpq
  obtain ⟨n, b, hb, ⟨hpack⟩⟩ :=
    invariant_quotients_columns
      A ℙ (fun p => p.1) hPmax hPinj card eFin
  exact ⟨n, b, hb, ⟨primaryEquiv ≪≫ₗ componentEquiv ≪≫ₗ hpack⟩⟩

/-- The quotient of a same-rank inclusion of finite modules has a presentation by a descending
chain of invariant-factor ideals. -/
theorem same_rank_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M)
    (h : Module.finrank A N = Module.finrank A M) :
    ∃ (n : ℕ) (b : Fin n → Ideal A),
      Antitone b ∧ Nonempty ((M ⧸ N) ≃ₗ[A] ⨁ j, A ⧸ b j) := by
  letI : Module.Finite A (M ⧸ N) :=
    Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  apply torsion_invariant_decomposition A (M ⧸ N)
  rw [← Module.finrank_eq_zero_iff_isTorsion, N.finrank_quotient, h, Nat.sub_self]

end Towers.NumberTheory.Milne
