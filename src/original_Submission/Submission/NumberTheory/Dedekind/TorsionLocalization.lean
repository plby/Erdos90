import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Localization of prime-power torsion modules

A module killed by a power of a maximal ideal is unchanged by localization at that ideal.  This
is the bridge from the primary components of a torsion module over a Dedekind domain to modules
over the corresponding local PID.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

universe u v

/-- If `M` is annihilated by `P ^ e`, every denominator outside the maximal ideal `P` already
acts invertibly on `M`; consequently the canonical localization map is bijective. -/
theorem localized_bijective_torsion
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (P : Ideal A) [P.IsMaximal] (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    Function.Bijective (LocalizedModule.mkLinearMap P.primeCompl M) := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    have hk : x - y ∈
        LinearMap.ker (LocalizedModule.mkLinearMap P.primeCompl M) := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [LocalizedModule.mem_ker_mkLinearMap_iff] at hk
    obtain ⟨s, hs, hsxy⟩ := hk
    obtain ⟨c, i, hi, hci⟩ := Ideal.IsMaximal.exists_inv_pow P hs e
    have hi0 : i • (x - y) = 0 := @hM (x - y) ⟨i, hi⟩
    calc
      x - y = 1 • (x - y) := (one_smul A (x - y)).symm
      _ = (c * s + i) • (x - y) := by rw [hci]
      _ = c • (s • (x - y)) + i • (x - y) := by
        rw [add_smul, mul_smul]
      _ = 0 := by
        rw [hsxy, hi0, smul_zero, add_zero]
  · intro z
    induction z using LocalizedModule.induction_on with
    | _ x s =>
        obtain ⟨c, i, hi, hci⟩ := Ideal.IsMaximal.exists_inv_pow P s.2 e
        refine ⟨c • x, ?_⟩
        rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def]
        have hi0 : i • x = 0 := @hM x ⟨i, hi⟩
        symm
        calc
          x = 1 • x := (one_smul A x).symm
          _ = (c * s.1 + i) • x := by rw [hci]
          _ = s.1 • c • x + i • x := by
            rw [add_smul, mul_comm c s.1, mul_smul]
          _ = s.1 • c • x := by rw [hi0, add_zero]

/-- The canonical `A`-linear equivalence from a prime-power torsion module to its localization. -/
noncomputable def torsionSetLocalization
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (P : Ideal A) [P.IsMaximal] (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    M ≃ₗ[A] LocalizedModule P.primeCompl M :=
  LinearEquiv.ofBijective (LocalizedModule.mkLinearMap P.primeCompl M)
    (localized_bijective_torsion A M P e hM)

@[simp]
theorem torsion_set_localization
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (P : Ideal A) [P.IsMaximal] (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) (x : M) :
    torsionSetLocalization A M P e hM x =
      LocalizedModule.mkLinearMap P.primeCompl M x :=
  rfl

/-- Localizing a module killed by a power of a nonzero maximal ideal produces a torsion module
over the local ring. -/
theorem localized_module_torsion
    (A M : Type*) [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M]
    (P : Ideal A) [P.IsMaximal] (hP : P ≠ ⊥) (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    Module.IsTorsion (Localization.AtPrime P)
      (LocalizedModule P.primeCompl M) := by
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hpow0 : p ^ e ≠ 0 := pow_ne_zero e hp0
  have hpowmem : p ^ e ∈ P ^ e := Ideal.pow_mem_pow hp e
  have hmap0 :
      algebraMap A (Localization.AtPrime P) (p ^ e) ≠ 0 :=
    by simpa using
      (IsLocalization.injective (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors).ne hpow0
  intro z
  refine ⟨⟨algebraMap A (Localization.AtPrime P) (p ^ e),
    mem_nonZeroDivisors_of_ne_zero hmap0⟩, ?_⟩
  induction z using LocalizedModule.induction_on with
  | _ x s =>
      have hx0 : (p ^ e : A) • LocalizedModule.mk x s = 0 := by
        rw [LocalizedModule.smul'_mk, @hM x ⟨p ^ e, hpowmem⟩,
          LocalizedModule.zero_mk]
      change algebraMap A (Localization.AtPrime P) (p ^ e) •
        LocalizedModule.mk x s = 0
      simpa only [IsScalarTower.algebraMap_smul] using hx0

/-- Each prime-power primary component of a finite torsion module over a Dedekind domain becomes,
after localization at its prime, a finite direct sum of cyclic prime-power modules over the local
PID. -/
theorem dedekind_cyclic_decomposition
    (A : Type u) (M : Type v) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) (e : ℕ)
    (hM : Module.IsTorsionBySet A M (P ^ e : Ideal A)) :
    ∃ (ι : Type u) (_ : Fintype ι)
      (p : ι → Localization.AtPrime P)
      (_ : ∀ i, Irreducible (p i)) (k : ι → ℕ),
      Nonempty <| LocalizedModule P.primeCompl M ≃ₗ[Localization.AtPrime P]
        ⨁ i : ι, Localization.AtPrime P ⧸
          Localization.AtPrime P ∙ p i ^ k i := by
  letI : P.IsMaximal :=
    Ideal.IsPrime.isMaximal (show P.IsPrime from inferInstance) hP
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  exact Module.equiv_directSum_of_isTorsion
    (localized_module_torsion A M P hP e hM)

end Submission.NumberTheory.Milne
