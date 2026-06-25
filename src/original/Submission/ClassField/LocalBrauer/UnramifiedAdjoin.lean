import Submission.NumberTheory.Locals.UnramifiedResidueLift

/-!
# Chapter IV, Section 4: unramified adjoining algebras

The adjoining-root lemmas used here are purely algebraic.  Their Chapter 7
versions were declared in a section carrying an unused Henselian hypothesis;
these variants record the assumptions actually used by the proofs.  This is
important when two equivalent presentations of a local-field valuation ring
coexist and only one has the topological Henselian instance installed.
-/

namespace Submission.CField.LBrauer

noncomputable section

open Algebra Polynomial IsLocalRing

attribute [local instance] Ideal.Quotient.field

universe u v

variable (A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]

/-- A monic polynomial with irreducible reduction defines a local
adjoining-root algebra; no Henselian hypothesis is needed. -/
theorem adjoin_ring_irreducible
    (f : A[X]) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A))) :
    IsLocalRing (AdjoinRoot f) := by
  let S := AdjoinRoot f
  let p := maximalIdeal A
  let I := p.map (algebraMap A S)
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (residue A) f hfred
  letI : IsDomain S := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : Module.Finite A S := hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A S := Algebra.IsIntegral.of_finite A S
  have htarget : IsField
      ((A ⧸ p)[X] ⧸ Ideal.span ({f.map (Ideal.Quotient.mk p)} :
        Set (A ⧸ p)[X])) := by
    letI : (Ideal.span ({f.map (Ideal.Quotient.mk p)} :
        Set (A ⧸ p)[X])).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hfred
    exact Field.toIsField _
  have hsource : IsField (S ⧸ I) :=
    (AdjoinRoot.quotEquivQuotMap f p).toRingEquiv.toMulEquiv.isField htarget
  have hImax : I.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr hsource
  refine IsLocalRing.of_unique_max_ideal ⟨I, hImax, ?_⟩
  intro M hM
  letI : M.IsMaximal := hM
  have hMunder : (M.comap (algebraMap A S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hunder : M.under A = p := IsLocalRing.eq_maximalIdeal hMunder
  have hle : I ≤ M := by
    change p.map (algebraMap A S) ≤ M
    rw [Ideal.map_le_iff_le_comap]
    simpa [Ideal.under_def] using hunder.symm.le
  exact (hImax.eq_of_le hM.ne_top hle).symm

/-- The maximal ideal of the preceding local algebra is the extended base
maximal ideal. -/
theorem adjoin_irreducible_residue
    (f : A[X]) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A))) :
    letI := adjoin_ring_irreducible A f hfmonic hfred
    maximalIdeal (AdjoinRoot f) =
      (maximalIdeal A).map (AdjoinRoot.of f) := by
  letI := adjoin_ring_irreducible A f hfmonic hfred
  symm
  exact IsLocalRing.eq_maximalIdeal <| by
    let p := maximalIdeal A
    have htarget : IsField
        ((A ⧸ p)[X] ⧸ Ideal.span ({f.map (Ideal.Quotient.mk p)} :
          Set (A ⧸ p)[X])) := by
      letI : (Ideal.span ({f.map (Ideal.Quotient.mk p)} :
          Set (A ⧸ p)[X])).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible hfred
      exact Field.toIsField _
    have hsource : IsField
        (AdjoinRoot f ⧸ p.map (AdjoinRoot.of f)) :=
      (AdjoinRoot.quotEquivQuotMap f p).toRingEquiv.toMulEquiv.isField htarget
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hsource

/-- Irreducible separable reduction makes the adjoining-root algebra
formally unramified, without a Henselian hypothesis. -/
theorem formally_irreducible_separable
    (f : A[X]) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A)))
    (hfsep : (f.map (residue A)).Separable) :
    Algebra.FormallyUnramified A (AdjoinRoot f) := by
  let p := maximalIdeal A
  let g := f.map (residue A)
  letI : Module.Finite A (AdjoinRoot f) := hfmonic.finite_adjoinRoot
  letI : IsLocalRing (AdjoinRoot f) :=
    adjoin_ring_irreducible A f hfmonic hfred
  have hmax : maximalIdeal (AdjoinRoot f) =
      p.map (AdjoinRoot.of f) :=
    adjoin_irreducible_residue
      A f hfmonic hfred
  letI : Fact (Irreducible g) := ⟨hfred⟩
  letI : Algebra.IsSeparable (ResidueField A) (AdjoinRoot g) :=
    Submission.NumberTheory.Milne.separable_monic_irreducible
      g (hfmonic.map (residue A)) hfred hfsep
  letI : IsLocalHom (algebraMap A (AdjoinRoot f)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A (AdjoinRoot f))).out 2 0).mp <| by
      simpa [AdjoinRoot.algebraMap_eq] using hmax.symm.le
  let eRing : AdjoinRoot g ≃+* ResidueField (AdjoinRoot f) :=
    (AdjoinRoot.quotEquivQuotMap f p).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq hmax.symm)
  letI : Algebra.IsSeparable (ResidueField A)
      (ResidueField (AdjoinRoot f)) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (RingEquiv.refl (ResidueField A)) eRing ?_
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom,
      RingEquiv.refl_apply]
    change algebraMap (ResidueField A) (ResidueField (AdjoinRoot f))
      (residue A x) = _
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    have h := AdjoinRoot.quotEquivQuotMap_symm_apply_mk f (C x) p
    have h' := congrArg (Ideal.quotEquivOfEq hmax.symm) h
    simpa [eRing] using h'.symm
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  simpa [AdjoinRoot.algebraMap_eq] using hmax.symm

variable (B : Type v) [CommRing B] [IsDomain B]
  [Algebra A B] [Module.IsTorsionFree A B]

/-- The algebra generated by an integral root with irreducible reduced
minimal polynomial is local, without a Henselian hypothesis. -/
theorem adjoin_irreducible_minpoly
    (f : A[X]) (a : B) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A)))
    (haintegral : IsIntegral A a) (hminpoly : minpoly A a = f) :
    IsLocalRing (Algebra.adjoin A ({a} : Set B)) := by
  let e : AdjoinRoot (minpoly A a) ≃ₐ[A] Algebra.adjoin A ({a} : Set B) :=
    minpoly.equivAdjoin haintegral
  have hfred' : Irreducible ((minpoly A a).map (residue A)) := by
    rw [hminpoly]
    exact hfred
  letI : IsLocalRing (AdjoinRoot (minpoly A a)) :=
    adjoin_ring_irreducible A (minpoly A a)
      (hminpoly.symm ▸ hfmonic) hfred'
  exact e.toRingEquiv.isLocalRing

/-- The preceding generated local algebra is formally unramified when the
reduced minimal polynomial is separable. -/
theorem formally_separable_minpoly
    (f : A[X]) (a : B) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A)))
    (hfsep : (f.map (residue A)).Separable)
    (haintegral : IsIntegral A a) (hminpoly : minpoly A a = f) :
    Algebra.FormallyUnramified A (Algebra.adjoin A ({a} : Set B)) := by
  let e : AdjoinRoot (minpoly A a) ≃ₐ[A] Algebra.adjoin A ({a} : Set B) :=
    minpoly.equivAdjoin haintegral
  have hfred' : Irreducible ((minpoly A a).map (residue A)) := by
    rw [hminpoly]
    exact hfred
  have hfsep' : ((minpoly A a).map (residue A)).Separable := by
    rw [hminpoly]
    exact hfsep
  letI : Algebra.FormallyUnramified A (AdjoinRoot (minpoly A a)) :=
    formally_irreducible_separable
      A (minpoly A a) (hminpoly.symm ▸ hfmonic) hfred' hfsep'
  exact Algebra.FormallyUnramified.of_equiv e

end

end Submission.CField.LBrauer
