import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Milne, Algebraic Number Theory, local invariant factors

We record the diagonal-basis theorem underlying Theorem 3.32 over a PID, and apply it after
localizing a Dedekind domain at a nonzero prime.  The global pseudobasis patching and divisibility
chain of invariant factors are not currently available in Mathlib.
-/

namespace Towers.NumberTheory.Milne

open Module

/-- The same-rank diagonal-basis statement underlying the invariant-factor theorem over a PID. -/
theorem pid_same_bases
    (R M : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (n : ℕ) (bM : Basis (Fin n) R M) (bN : Basis (Fin n) R N)
      (a : Fin n → R), (∀ i, a i ≠ 0) ∧ ∀ i, (bN i : M) = a i • bM i := by
  let ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  obtain ⟨bM, a, bN, ha⟩ := N.exists_smith_normal_form_of_rank_eq b h
  refine ⟨n, bM, bN, a, ?_, ha⟩
  intro i hai
  apply bN.ne_zero i
  apply Subtype.ext
  simp [ha i, hai]

/-- At every nonzero prime of a Dedekind domain, a same-rank inclusion of finite torsion-free
modules has a square diagonal matrix in suitable bases after localization. -/
theorem dedekind_diagonal_bases
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M]
    (N : Submodule A M)
    (h : Module.finrank A N = Module.finrank A M)
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (n : ℕ)
      (bM : Basis (Fin n) (Localization.AtPrime P)
        (LocalizedModule P.primeCompl M))
      (bN : Basis (Fin n) (Localization.AtPrime P)
        (N.localized P.primeCompl))
      (a : Fin n → Localization.AtPrime P),
      (∀ i, a i ≠ 0) ∧ ∀ i, (bN i : LocalizedModule P.primeCompl M) = a i • bM i := by
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  letI : Module.Finite A N := Module.Finite.of_fg (IsNoetherian.noetherian _)
  have hMloc :
      Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
        Module.finrank A M := by
    have h₁ := congrArg Cardinal.toNat <|
      IsLocalization.rank_eq (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
        (N := LocalizedModule P.primeCompl M)
    have h₂ := congrArg Cardinal.toNat <|
      IsLocalizedModule.lift_rank_eq P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)
        P.primeCompl_le_nonZeroDivisors
    have h₁' : Module.finrank (Localization.AtPrime P)
        (LocalizedModule P.primeCompl M) =
        Module.finrank A (LocalizedModule P.primeCompl M) := by simpa using h₁
    have h₂' : Module.finrank A (LocalizedModule P.primeCompl M) =
        Module.finrank A M := by simpa using h₂
    exact h₁'.trans h₂'
  have hNloc :
      Module.finrank (Localization.AtPrime P) (N.localized P.primeCompl) =
        Module.finrank A N := by
    have h₁ := congrArg Cardinal.toNat <|
      IsLocalization.rank_eq (Localization.AtPrime P) P.primeCompl
        P.primeCompl_le_nonZeroDivisors
        (N := N.localized P.primeCompl)
    have h₂ := congrArg Cardinal.toNat <|
      IsLocalizedModule.lift_rank_eq P.primeCompl (N.toLocalized P.primeCompl)
        P.primeCompl_le_nonZeroDivisors
    have h₁' : Module.finrank (Localization.AtPrime P) (N.localized P.primeCompl) =
        Module.finrank A (N.localized P.primeCompl) := by simpa using h₁
    have h₂' : Module.finrank A (N.localized P.primeCompl) =
        Module.finrank A N := by simpa using h₂
    exact h₁'.trans h₂'
  exact pid_same_bases
    (Localization.AtPrime P) (LocalizedModule P.primeCompl M)
    (N.localized P.primeCompl) (hNloc.trans (h.trans hMloc.symm))

end Towers.NumberTheory.Milne
