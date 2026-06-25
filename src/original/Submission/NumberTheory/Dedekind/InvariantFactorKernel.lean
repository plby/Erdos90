import Submission.NumberTheory.Dedekind.InvariantFactorsUniqueness
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The final invariant factor acts into the kernel

For an antitone invariant-factor presentation, the final ideal is the annihilator of the whole
presented module.  Consequently, after identifying a lattice quotient with that presentation,
the final ideal times the ambient lattice is contained in the sublattice.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

/-- A name for an ideal quotient that can be used safely inside dependent type families. -/
abbrev idealQuotientModule (A : Type*) [CommRing A] (I : Ideal A) := A ⧸ I

/-- The final ideal in an antitone invariant-factor presentation kills every value of a linear
map into that presentation. -/
theorem invariant_last_smul
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (n : ℕ) (b : Fin (n + 1) → Ideal A) (hb : Antitone b)
    (q : M →ₗ[A] DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i))) :
    b (Fin.last n) • (⊤ : Submodule A M) ≤ LinearMap.ker q := by
  rw [← annihilator_quotients_last A n b hb]
  refine Submodule.smul_le.mpr fun r hr x _ ↦ ?_
  rw [LinearMap.mem_ker, q.map_smul]
  exact Module.mem_annihilator.mp hr (q x)

/-- If a lattice quotient has an antitone invariant-factor presentation, multiplication by its
final ideal carries the ambient lattice into the sublattice. -/
theorem invariant_smul_submodule
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin (n + 1) → Ideal A) (hb : Antitone b)
    (e : (M ⧸ N) ≃ₗ[A]
      (DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i)))) :
    b (Fin.last n) • (⊤ : Submodule A M) ≤ N := by
  let q : M →ₗ[A]
      DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i)) :=
    e.toLinearMap.comp N.mkQ
  intro x hx
  have hqx : q x = 0 := LinearMap.mem_ker.mp
    (invariant_last_smul A M n b hb q hx)
  have hmk : N.mkQ x = 0 := by
    apply e.injective
    simpa [q] using hqx
  exact (Submodule.Quotient.mk_eq_zero N).mp hmk

/-- If the final ideal in an antitone invariant-factor presentation is the unit ideal, then the
presented quotient is zero and the original submodule is the whole ambient module. -/
theorem submodule_top_last
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin (n + 1) → Ideal A) (hb : Antitone b)
    (e : (M ⧸ N) ≃ₗ[A]
      DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i)))
    (hlast : b (Fin.last n) = ⊤) :
    N = ⊤ := by
  apply top_unique
  have h := invariant_smul_submodule A M N n b hb e
  simpa [hlast] using h

end Submission.NumberTheory.Milne
