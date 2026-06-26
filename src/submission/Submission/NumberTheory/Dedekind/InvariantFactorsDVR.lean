import Submission.NumberTheory.Dedekind.InvariantFactorsLocal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Milne, Algebraic Number Theory, invariant factors over a DVR

Over a discrete valuation ring, the diagonal entries in a full-rank Smith basis can be
normalized to powers of one uniformizer.  Sorting their exponents gives the divisibility chain
which is part of the invariant-factor theorem.
-/

namespace Submission.NumberTheory.Milne

open Module

/-- Over a DVR, unit factors can be removed from any nonzero square diagonalization and the
remaining uniformizer exponents can be sorted. -/
theorem dvr_diagonal_bases
    (R M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M]
    (N : Submodule R M) (n : ℕ)
    (bM : Basis (Fin n) R M) (bN : Basis (Fin n) R N)
    (a : Fin n → R) (ha : ∀ i, a i ≠ 0)
    (hdiag : ∀ i, (bN i : M) = a i • bM i) :
    ∃ (bM' : Basis (Fin n) R M) (bN' : Basis (Fin n) R N)
      (ϖ : R) (_ : Irreducible ϖ) (e : Fin n → ℕ),
      Monotone e ∧ ∀ i, (bN' i : M) = ϖ ^ e i • bM' i := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  choose e u heu using fun i ↦
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha i) hϖ
  let bN' : Basis (Fin n) R N := bN.unitsSMul fun i ↦ (u i)⁻¹
  have hdiag' : ∀ i, (bN' i : M) = ϖ ^ e i • bM i := by
    intro i
    simp only [bN', Basis.unitsSMul_apply, Submodule.coe_smul_of_tower]
    change (↑((u i)⁻¹) : R) • (bN i : M) = _
    rw [hdiag i, heu i]
    rw [← mul_smul]
    simp
  let σ : Equiv.Perm (Fin n) := Tuple.sort e
  let e' : Fin n → ℕ := e ∘ σ
  let bM' : Basis (Fin n) R M := bM.reindex σ.symm
  let bN'' : Basis (Fin n) R N := bN'.reindex σ.symm
  refine ⟨bM', bN'', ϖ, hϖ, e', ?_, ?_⟩
  · exact Tuple.monotone_sort e
  · intro i
    simpa [bM', bN'', e', σ, Basis.reindex_apply] using hdiag' (σ i)

/-- A same-rank inclusion of finite torsion-free modules over a DVR has diagonal bases whose
diagonal entries are monotonically ordered powers of one uniformizer. -/
theorem dvr_same_bases
    (R M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (n : ℕ) (bM : Basis (Fin n) R M) (bN : Basis (Fin n) R N)
      (ϖ : R) (_ : Irreducible ϖ) (e : Fin n → ℕ),
      Monotone e ∧ ∀ i, (bN i : M) = ϖ ^ e i • bM i := by
  obtain ⟨n, bM, bN, a, ha, hdiag⟩ :=
    pid_same_bases R M N h
  obtain ⟨bM', bN', ϖ, hϖ, e, he, hdiag'⟩ :=
    dvr_diagonal_bases R M N n bM bN a ha hdiag
  exact ⟨n, bM', bN', ϖ, hϖ, e, he, hdiag'⟩

/-- At a nonzero prime of a Dedekind domain, the local diagonal entries can be chosen as an
ordered sequence of powers of one uniformizer. -/
theorem dedekind_same_bases
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
      (ϖ : Localization.AtPrime P) (_ : Irreducible ϖ) (e : Fin n → ℕ),
      Monotone e ∧
        ∀ i, (bN i : LocalizedModule P.primeCompl M) = ϖ ^ e i • bM i := by
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
  obtain ⟨n, bM, bN, a, ha, hdiag⟩ :=
    dedekind_diagonal_bases A M N h P hP
  obtain ⟨bM', bN', ϖ, hϖ, e, he, hdiag'⟩ :=
    dvr_diagonal_bases (Localization.AtPrime P)
      (LocalizedModule P.primeCompl M) (N.localized P.primeCompl)
      n bM bN a ha hdiag
  exact ⟨n, bM', bN', ϖ, hϖ, e, he, hdiag'⟩

/-- The principal ideals attached to the ordered DVR diagonalization form the descending chain
appearing in Milne's invariant-factor theorem. -/
theorem dvr_same_ideals
    (R M : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (n : ℕ) (bM : Basis (Fin n) R M) (bN : Basis (Fin n) R N)
      (b : Fin n → Ideal R),
      Antitone b ∧
        ∃ (ϖ : R) (_ : Irreducible ϖ) (e : Fin n → ℕ),
          Monotone e ∧
            b = (fun i ↦ Ideal.span {ϖ ^ e i}) ∧
            ∀ i, (bN i : M) = ϖ ^ e i • bM i := by
  obtain ⟨n, bM, bN, ϖ, hϖ, e, he, hdiag⟩ :=
    dvr_same_bases R M N h
  let b : Fin n → Ideal R := fun i ↦ Ideal.span {ϖ ^ e i}
  have hb : Antitone b := by
    intro i j hij
    change Ideal.span {ϖ ^ e j} ≤ Ideal.span {ϖ ^ e i}
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow ϖ (he hij)
  exact ⟨n, bM, bN, b, hb, ϖ, hϖ, e, he, rfl, hdiag⟩

end Submission.NumberTheory.Milne
