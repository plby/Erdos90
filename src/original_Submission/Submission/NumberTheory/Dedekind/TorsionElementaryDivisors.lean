import Submission.NumberTheory.Dedekind.DedekindModules
import Submission.NumberTheory.Dedekind.PrimePowerDecomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Milne, Algebraic Number Theory, elementary divisors over a Dedekind domain

Combining the primary decomposition of a finite torsion module with the structure theorem for
each prime-primary component gives a global decomposition into quotients by prime powers.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u v

/- **Elementary-divisor theorem over a Dedekind domain.** Every finite torsion module is a
finite direct sum of quotients by powers of nonzero prime ideals. -/
set_option maxHeartbeats 2000000 in
-- The dependent choice of a cyclic decomposition for every primary component is elaboration-heavy.
theorem torsion_module_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    ∃ (ι : Type u) (_ : Fintype ι) (P : ι → Ideal A)
      (_ : ∀ i, (P i).IsPrime) (_ : ∀ i, P i ≠ ⊥) (e : ι → ℕ),
      Nonempty (M ≃ₗ[A] DirectSum ι (fun i ↦ A ⧸ P i ^ e i)) := by
  classical
  obtain ⟨ℙ, _, hℙ, d, hInternal⟩ :=
    torsion_prime_decomposition A M hM
  let T : ℙ → Submodule A M := fun p ↦
    Submodule.torsionBySet A M (p.1 ^ d p : Ideal A)
  have hcomponent (p : ℙ) :
      ∃ (ι : Type u) (_ : Fintype ι) (e : ι → ℕ),
        Nonempty
          (T p ≃ₗ[A] DirectSum ι (fun i ↦ A ⧸ p.1 ^ e i)) := by
    letI : p.1.IsPrime := Ideal.isPrime_of_prime (hℙ p.1 p.2)
    letI : Module.Finite A (T p) :=
      Module.Finite.of_fg (IsNoetherian.noetherian (T p))
    exact dedekind_torsion_decomposition
      A (T p) p.1 (hℙ p.1 p.2).ne_zero (d p)
        (Submodule.torsionBySet_isTorsionBySet
          (R := A) (M := M) ((p.1 ^ d p : Ideal A) : Set A))
  choose ι hι e he using hcomponent
  letI (p : ℙ) : Fintype (ι p) := hι p
  let primaryEquiv : M ≃ₗ[A] DirectSum ℙ (fun p ↦ T p) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap T) hInternal).symm
  let componentEquiv :
      DirectSum ℙ (fun p ↦ T p) ≃ₗ[A]
        DirectSum ℙ
          (fun p ↦ DirectSum (ι p) (fun i ↦ A ⧸ p.1 ^ e p i)) :=
    DFinsupp.mapRange.linearEquiv fun p ↦ Classical.choice (he p)
  let flatten :
      DirectSum (Σ p, ι p)
          (fun x ↦ A ⧸ x.1.1 ^ e x.1 x.2) ≃ₗ[A]
        DirectSum ℙ
          (fun p ↦ DirectSum (ι p) (fun i ↦ A ⧸ p.1 ^ e p i)) :=
    DirectSum.sigmaLcurryEquiv
      (δ := fun p i ↦ A ⧸ p.1 ^ e p i) A
  refine ⟨Σ p, ι p, inferInstance, fun x ↦ x.1.1, ?_, ?_, fun x ↦ e x.1 x.2, ⟨?_⟩⟩
  · intro x
    exact Ideal.isPrime_of_prime (hℙ x.1.1 x.1.2)
  · intro x
    exact (hℙ x.1.1 x.1.2).ne_zero
  · exact primaryEquiv.trans (componentEquiv.trans flatten.symm)

end Submission.NumberTheory.Milne
