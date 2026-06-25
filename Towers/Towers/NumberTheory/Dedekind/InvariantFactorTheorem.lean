import Towers.NumberTheory.Dedekind.PseudobasisGlobal
import Towers.NumberTheory.Dedekind.TorsionInvariantFactors

/-!
# Milne, Algebraic Number Theory, the invariant-factor theorem

For a same-rank inclusion of finite torsion-free modules over a Dedekind domain, the quotient is
finite torsion.  Applying the torsion-module structure theorem produces a descending sequence of
integral ideals.  We also retain the square ideal pseudobases of the inclusion, so the quotient
description is attached to the global coordinate map.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

universe u

/-- **Theorem 3.32, quotient form.**  The quotient of a same-rank inclusion of finite
torsion-free modules over a Dedekind domain is a direct sum of quotients by a descending chain of
integral ideals. -/
theorem dedekind_same_decomposition
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (hrank : Module.finrank A N = Module.finrank A M) :
    ∃ (n : ℕ) (b : Fin n → Ideal A),
      Antitone b ∧ Nonempty ((M ⧸ N) ≃ₗ[A] ⨁ j, A ⧸ b j) := by
  apply torsion_invariant_decomposition
  rw [← Module.finrank_eq_zero_iff_isTorsion, N.finrank_quotient, hrank,
    Nat.sub_self]

/-- The global coordinate-and-quotient form of Theorem 3.32.  A same-rank inclusion has square
nonzero ideal pseudobases, and the cokernel of the resulting injective coordinate map has a
descending invariant-factor decomposition. -/
theorem dedekind_same_pseudobasis
    (A M : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (hrank : Module.finrank A N = Module.finrank A M) :
    ∃ (n : ℕ) (I J : Fin n → Ideal A),
      (∀ i, I i ≠ ⊥) ∧ (∀ j, J j ≠ ⊥) ∧
      ∃ (eM : M ≃ₗ[A] ⨁ i, I i) (eN : N ≃ₗ[A] ⨁ j, J j)
        (f : (⨁ j, J j) →ₗ[A] (⨁ i, I i)),
        Function.Injective f ∧
          (∀ x : N, f (eN x) = eM x.1) ∧
          ∃ (r : ℕ) (b : Fin r → Ideal A),
            Antitone b ∧ Nonempty
              (((⨁ i, I i) ⧸ LinearMap.range f) ≃ₗ[A]
                ⨁ j, A ⧸ b j) := by
  obtain ⟨n, I, J, hI, hJ, eM, eN, f, hf, hcomm, hquot⟩ :=
    dedekind_submodule_pseudobasis A M N hrank
  letI : Module.Finite A (⨁ i, I i) := Module.Finite.equiv eM
  obtain ⟨r, b, hb, hequiv⟩ :=
    torsion_invariant_decomposition A
      ((⨁ i, I i) ⧸ LinearMap.range f) hquot
  exact ⟨n, I, J, hI, hJ, eM, eN, f, hf, hcomm, r, b, hb, hequiv⟩

end Towers.NumberTheory.Milne
