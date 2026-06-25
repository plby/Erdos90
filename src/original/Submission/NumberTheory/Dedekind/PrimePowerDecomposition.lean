import Submission.NumberTheory.Dedekind.TorsionLocalization
import Submission.NumberTheory.Dedekind.PowerLinearEquiv

/-!
# Prime-power torsion modules over Dedekind domains

The canonical localization equivalence lets us state the local PID structure theorem directly
for the original module.  Thus a finite module killed by a power of a nonzero prime is, as a
module over the Dedekind domain, a finite direct sum of cyclic modules over the corresponding
local DVR.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u v

/-- A finite module killed by a power of a nonzero prime ideal is, already as an `A`-module,
isomorphic to the finite direct sum of cyclic modules supplied by the PID structure theorem over
the localization at that prime. -/
theorem dedekind_torsion_cyclic
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    ∃ (ι : Type u) (_ : Fintype ι)
      (p : ι → Localization.AtPrime P)
      (_ : ∀ i, Irreducible (p i)) (k : ι → ℕ),
      Nonempty
        (M ≃ₗ[A]
          ⨁ i : ι, Localization.AtPrime P ⧸
            Localization.AtPrime P ∙ p i ^ k i) := by
  letI : P.IsMaximal :=
    Ideal.IsPrime.isMaximal (show P.IsPrime from inferInstance) hP
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  obtain ⟨ι, hι, p, hp, k, ⟨localEquiv⟩⟩ :=
    dedekind_cyclic_decomposition A M P hP e hM
  refine ⟨ι, hι, p, hp, k, ⟨?_⟩⟩
  exact
    (torsionSetLocalization A M P e hM).trans
      (localEquiv.restrictScalars A)

/-- **Prime-primary structure theorem over a Dedekind domain.** A finite module annihilated by a
power of a nonzero prime ideal is a finite direct sum of quotients by powers of that prime. -/
theorem dedekind_torsion_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    ∃ (ι : Type u) (_ : Fintype ι) (k : ι → ℕ),
      Nonempty (M ≃ₗ[A] ⨁ i : ι, A ⧸ P ^ k i) := by
  classical
  letI : P.IsMaximal :=
    Ideal.IsPrime.isMaximal (show P.IsPrime from inferInstance) hP
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  obtain ⟨ι, hι, p, hp, k, ⟨localEquiv⟩⟩ :=
    dedekind_cyclic_decomposition A M P hP e hM
  let S := Localization.AtPrime P
  have hIdeal (i : ι) :
      S ∙ p i ^ k i =
        (P.map (algebraMap A S)) ^ k i := by
    change Ideal.span {p i ^ k i} = _
    rw [← Ideal.span_singleton_pow, ← (hp i).maximalIdeal_eq,
      ← Localization.AtPrime.map_eq_maximalIdeal]
  let normalize :
      (⨁ i : ι, S ⧸ S ∙ p i ^ k i) ≃ₗ[S]
        ⨁ i : ι, S ⧸ (P.map (algebraMap A S)) ^ k i :=
    DFinsupp.mapRange.linearEquiv fun i ↦
      Submodule.quotEquivOfEq _ _ (hIdeal i)
  let descend :
      (⨁ i : ι, S ⧸ (P.map (algebraMap A S)) ^ k i) ≃ₗ[A]
        ⨁ i : ι, A ⧸ P ^ k i :=
    DFinsupp.mapRange.linearEquiv fun i ↦
      (linearLocalizationPrime A P (k i)).symm
  refine ⟨ι, hι, k, ⟨?_⟩⟩
  exact
    ((torsionSetLocalization A M P e hM).trans
      ((localEquiv.trans normalize).restrictScalars A)).trans descend

end Submission.NumberTheory.Milne
