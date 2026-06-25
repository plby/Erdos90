import Submission.FieldTheory.TameThreeKoch.AbsoluteRestriction

/-!
# Compatibility of cyclotomic and absolute restrictions

This file collects the finite-level restriction lemmas used when a weak
solution over the cyclotomic quadratic extension is compared with an
absolute weak solution over `ℚ`.
-/

noncomputable section

namespace Submission
namespace TBluepr

open scoped Pointwise Topology commutatorElement
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

universe uK uM uQ uE uH uk uOmega uL

/-- Restricting a finite-level weak solution along an absolute Galois
homomorphism preserves its projection to the prescribed finite quotient. -/
theorem restricted_lift_projection
    {K : Type uK} {M : Type uM} {Q : Type uQ} {E : Type uE}
    {H : Type uH}
    [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    [Group Q] [Group E] [Group H]
    (j : M →ₐ[K] SeparableClosure K)
    (F : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hMF : galoisFieldRange j ≤ F)
    (q : E →* Q)
    (galoisEquiv : Gal(M/K) ≃* Q)
    (liftF : Gal(F/K) →* E)
    (hliftF : q.comp liftF =
      galoisEquiv.toMonoidHom.comp
        ((algFieldRange j).autCongr.symm.toMonoidHom.comp
          (galoisRestrictionHom K hMF)))
    (toAbsolute : H →* Gal(SeparableClosure K/K)) :
    q.comp
        (liftF.comp
          ((absoluteRestrictionHom (K := K) F).comp
            toAbsolute)) =
      galoisEquiv.toMonoidHom.comp
        ((algFieldRange j).autCongr.symm.toMonoidHom.comp
          ((absoluteRestrictionHom
            (K := K) (galoisFieldRange j)).comp toAbsolute)) := by
  apply MonoidHom.ext
  intro sigma
  simp only [MonoidHom.comp_apply]
  have hsigma := DFunLike.congr_fun hliftF
    (absoluteRestrictionHom (K := K) F (toAbsolute sigma))
  simp only [MonoidHom.comp_apply] at hsigma
  calc
    q (liftF (absoluteRestrictionHom (K := K) F
        (toAbsolute sigma))) =
        galoisEquiv ((algFieldRange j).autCongr.symm
          (galoisRestrictionHom K hMF
            (absoluteRestrictionHom (K := K) F
              (toAbsolute sigma)))) := hsigma
    _ = galoisEquiv ((algFieldRange j).autCongr.symm
          (absoluteRestrictionHom (K := K)
            (galoisFieldRange j) (toAbsolute sigma))) :=
      congrArg
        (fun tau => galoisEquiv ((algFieldRange j).autCongr.symm tau))
        (galois_restriction_absolute (K := K) hMF
          (toAbsolute sigma))

/-- A finite-level lift restricted from an absolute subgroup is trivial on
every element which fixes the finite field pointwise. -/
theorem restricted_lift_fixes
    {k : Type uk} {K : Type uK} {E : Type uE}
    [Field k] [Field K] [Algebra k K]
    [Algebra k (SeparableClosure K)]
    [Group E]
    (F : FiniteGaloisIntermediateField K (SeparableClosure K))
    (H : Subgroup Gal(SeparableClosure K/k))
    (N : Subgroup Gal(SeparableClosure K/k))
    (hNH : N ≤ H)
    (toRelative : H →* Gal(SeparableClosure K/K))
    (htoRelative_apply : ∀ (sigma : H) (z : SeparableClosure K),
      toRelative sigma z =
        (sigma : Gal(SeparableClosure K/k)) z)
    (liftF : Gal(F/K) →* E)
    (hfixF : ∀ (x : N) (y : F),
      (x : Gal(SeparableClosure K/k)) (y : SeparableClosure K) = y) :
    ∀ x : N,
      (liftF.comp
        ((absoluteRestrictionHom (K := K) F).comp
          toRelative)) ⟨x, hNH x.2⟩ = 1 := by
  intro x
  have hrestrict :
      absoluteRestrictionHom (K := K) F
          (toRelative ⟨x, hNH x.2⟩) = 1 := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    calc
      ↑((absoluteRestrictionHom (K := K) F
          (toRelative ⟨x, hNH x.2⟩)) y) =
          toRelative ⟨x, hNH x.2⟩
            (y : SeparableClosure K) := by
        simp [absoluteRestrictionHom,
          AlgEquiv.restrictNormalHom_apply]
      _ = (x : Gal(SeparableClosure K/k))
          (y : SeparableClosure K) :=
        htoRelative_apply ⟨x, hNH x.2⟩ y
      _ = y := hfixF x y
      _ = ↑((1 : Gal(F/K)) y) := by simp
  change liftF (absoluteRestrictionHom (K := K) F
    (toRelative ⟨x, hNH x.2⟩)) = 1
  rw [hrestrict, map_one]

/-- A subgroup fixing an intermediate field lies in the kernel of every
finite quotient obtained by restricting to that field. -/
theorem comp_restrict_fixes
    {k : Type uk} {Omega : Type uOmega} {Q : Type uQ}
    [Field k] [Field Omega] [Algebra k Omega] [Group Q]
    (L : IntermediateField k Omega)
    (hNormal : Normal k L)
    (rangeEquiv : Gal(L/k) ≃* Q)
    (N : Subgroup Gal(Omega/k))
    (hfix : N ≤ L.fixingSubgroup) :
    N ≤
      (rangeEquiv.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom L)).ker := by
  letI : Normal k L := hNormal
  intro x hx
  have hrestrict : AlgEquiv.restrictNormalHom L x = 1 := by
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    calc
      ↑((AlgEquiv.restrictNormalHom L x) y) =
          x (y : Omega) :=
        AlgEquiv.restrictNormalHom_apply L x y
      _ = y := hfix hx y
      _ = ↑((1 : Gal(L/k)) y) := by simp
  change rangeEquiv (AlgEquiv.restrictNormalHom L x) = 1
  rw [hrestrict, map_one]

/-- Absolute restriction to the field range of an embedding acts, after
transporting back across the range equivalence, by the original absolute
automorphism on embedded elements. -/
theorem range_absolute_restriction
    {K : Type uK} {M : Type uM}
    [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (j : M →ₐ[K] SeparableClosure K)
    (rho : Gal(SeparableClosure K/K)) (y : M) :
    j ((algFieldRange j).autCongr.symm
        (absoluteRestrictionHom
          (K := K) (galoisFieldRange j) rho) y) =
      rho (j y) := by
  letI : FiniteDimensional K j.fieldRange :=
    Module.Finite.equiv (algFieldRange j).toLinearEquiv
  letI : IsGalois K j.fieldRange :=
    IsGalois.of_algEquiv (algFieldRange j)
  letI : Normal K j.fieldRange := IsGalois.to_normal
  rw [← alg_field_range j]
  simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.symm_symm]
  calc
    ↑((AlgEquiv.restrictNormalHom j.fieldRange rho)
        ((algFieldRange j) y)) =
        rho ((algFieldRange j) y : SeparableClosure K) :=
      AlgEquiv.restrictNormalHom_apply j.fieldRange rho
        ((algFieldRange j) y)
    _ = rho (j y) := by rw [alg_field_range]

/-- Restriction to the range of an arbitrary field embedding is compatible
with transport back across the equivalence onto that range. -/
theorem alg_restrict_normal
    {k : Type uk} {L : Type uL} {Omega : Type uOmega}
    [Field k] [Field L] [Field Omega]
    [Algebra k L] [Algebra k Omega]
    (i : L →ₐ[k] Omega)
    (hNormal : Normal k i.fieldRange)
    (rho : Gal(Omega/k)) (x : L) :
    i ((AlgEquiv.autCongr (algHomRange i)).symm
        (AlgEquiv.restrictNormalHom i.fieldRange rho) x) =
      rho (i x) := by
  letI : Normal k i.fieldRange := hNormal
  change (((algHomRange i)
    ((AlgEquiv.autCongr (algHomRange i)).symm
      (AlgEquiv.restrictNormalHom i.fieldRange rho) x) : i.fieldRange) :
        Omega) = rho (i x)
  simp only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.symm_symm]
  calc
    ↑((AlgEquiv.restrictNormalHom i.fieldRange rho)
        ((algHomRange i) x)) =
        rho ((algHomRange i) x : Omega) :=
      AlgEquiv.restrictNormalHom_apply i.fieldRange rho
        ((algHomRange i) x)
    _ = rho (i x) := by rfl

/-- If two finite restrictions induce the same action after embedding into a
common overfield, their transported Galois automorphisms agree. -/
theorem galois_restriction_compatible
    {k : Type uk} {K : Type uK} {M : Type uM} {L : Type uL}
    {Omega : Type uOmega} {H : Type uH}
    [Field k] [Field K] [Field M] [Field L] [Field Omega]
    [Algebra K M] [Algebra k L] [Algebra L M]
    [Algebra K Omega] [Algebra k Omega]
    [Group H]
    (cyclotomicEquiv : Gal(M/K) ≃* Gal(L/k))
    (j : M →ₐ[K] Omega)
    (iL : L →ₐ[k] Omega)
    (eL : L ≃ₐ[k] iL.fieldRange)
    (toAbsolute : H →* Gal(Omega/k))
    (restrictToM : H →* Gal(M/K))
    (restrictToL : Gal(Omega/k) →* Gal(iL.fieldRange/k))
    (hcyclotomic_apply : ∀ (tau : Gal(M/K)) (x : L),
      iL (cyclotomicEquiv tau x) = j (tau (algebraMap L M x)))
    (hrestrictToM_apply : ∀ (sigma : H) (y : M),
      j (restrictToM sigma y) = toAbsolute sigma (j y))
    (hrestrictToL_apply : ∀ (rho : Gal(Omega/k)) (x : L),
      iL ((AlgEquiv.autCongr eL).symm (restrictToL rho) x) =
        rho (iL x))
    (sigma : H) :
    cyclotomicEquiv (restrictToM sigma) =
      (AlgEquiv.autCongr eL).symm
        (restrictToL (toAbsolute sigma)) := by
  apply AlgEquiv.ext
  intro x
  apply iL.injective
  calc
    iL (cyclotomicEquiv (restrictToM sigma) x) =
        j (restrictToM sigma (algebraMap L M x)) :=
      hcyclotomic_apply (restrictToM sigma) x
    _ = toAbsolute sigma (j (algebraMap L M x)) :=
      hrestrictToM_apply sigma (algebraMap L M x)
    _ = toAbsolute sigma (iL x) := by
      have hbase : j (algebraMap L M x) = iL x := by
        simpa using (hcyclotomic_apply (1 : Gal(M/K)) x).symm
      rw [hbase]
    _ = iL ((AlgEquiv.autCongr eL).symm
        (restrictToL (toAbsolute sigma)) x) :=
      (hrestrictToL_apply (toAbsolute sigma) x).symm

end TBluepr
end Submission
