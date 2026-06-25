import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.AdjoinRoot
import Submission.NumberTheory.Locals.AdicCompleteFree
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Unramified.LocalRing


/-!
# Lifting finite residue-field extensions

This file formalizes the Hensel-lifting construction in Milne, Proposition
7.50.  A simple element of the upper residue field is lifted to a root of a
monic lift of its minimal polynomial.  Applied to a primitive residue-field
element, the lifted root still generates the full residue extension.
-/

namespace Submission.NumberTheory.Milne

open Algebra Polynomial IsLocalRing

noncomputable section

attribute [local instance] Ideal.Quotient.field

variable (A B : Type*) [CommRing A] [CommRing B]
  [HenselianLocalRing A] [HenselianLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

omit [HenselianLocalRing A] in
/-- A monic polynomial whose reduction modulo the maximal ideal is
irreducible defines a local finite algebra.  Its unique maximal ideal is the
extension of the maximal ideal downstairs. -/
theorem adjoin_root_irreducible
    [IsDomain A] [IsDiscreteValuationRing A]
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
  have hunder : M.under A = p :=
    IsLocalRing.eq_maximalIdeal hMunder
  have hle : I ≤ M := by
    change p.map (algebraMap A S) ≤ M
    rw [Ideal.map_le_iff_le_comap]
    simpa [Ideal.under_def] using hunder.symm.le
  exact (hImax.eq_of_le hM.ne_top hle).symm

omit [HenselianLocalRing A] in
/-- In the local adjoining-root algebra, the maximal ideal is exactly the
extension of the maximal ideal downstairs. -/
theorem adjoin_maximal_irreducible
    [IsDomain A] [IsDiscreteValuationRing A]
    (f : A[X]) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A))) :
    letI := adjoin_root_irreducible A f hfmonic hfred
    maximalIdeal (AdjoinRoot f) =
      (maximalIdeal A).map (AdjoinRoot.of f) := by
  letI := adjoin_root_irreducible A f hfmonic hfred
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

/-- An irreducible separable polynomial over a field defines a separable
adjoining-root extension. -/
theorem separable_monic_irreducible
    {k : Type*} [Field k] (g : k[X]) (hgmonic : g.Monic)
    (hirr : Irreducible g) (hsep : g.Separable) :
    Algebra.IsSeparable k (AdjoinRoot g) := by
  letI : Fact (Irreducible g) := ⟨hirr⟩
  have hrootsep : IsSeparable k (AdjoinRoot.root g) := by
    rw [IsSeparable, ← AdjoinRoot.powerBasis_gen (f := g) hirr.ne_zero]
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hgmonic]
    exact hsep
  have hadjoinSep : Algebra.IsSeparable k
      (IntermediateField.adjoin k ({AdjoinRoot.root g} : Set (AdjoinRoot g))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k
      (AdjoinRoot g)).2 hrootsep
  have hadjoin :
      IntermediateField.adjoin k ({AdjoinRoot.root g} : Set (AdjoinRoot g)) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic]
    · exact AdjoinRoot.adjoinRoot_eq_top
    · exact (AdjoinRoot.isIntegral_root hirr.ne_zero).isAlgebraic
  rw [hadjoin] at hadjoinSep
  letI := hadjoinSep
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
    (⊤ : IntermediateField k (AdjoinRoot g)) ≃ₐ[k] AdjoinRoot g)

omit [HenselianLocalRing A] in
/-- A monic polynomial with irreducible separable reduction defines a
formally unramified local extension.  This is the algebraic core of the
unramified extension constructed in Milne, Proposition 7.50. -/
theorem adjoin_formally_separable
    [IsDomain A] [IsDiscreteValuationRing A]
    (f : A[X]) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A)))
    (hfsep : (f.map (residue A)).Separable) :
    Algebra.FormallyUnramified A (AdjoinRoot f) := by
  let p := maximalIdeal A
  let g := f.map (residue A)
  letI : Module.Finite A (AdjoinRoot f) := hfmonic.finite_adjoinRoot
  letI : IsLocalRing (AdjoinRoot f) :=
    adjoin_root_irreducible A f hfmonic hfred
  have hmax : maximalIdeal (AdjoinRoot f) =
      p.map (AdjoinRoot.of f) :=
    adjoin_maximal_irreducible A f hfmonic hfred
  letI : Fact (Irreducible g) := ⟨hfred⟩
  letI : Algebra.IsSeparable (ResidueField A) (AdjoinRoot g) :=
    separable_monic_irreducible g
      (hfmonic.map (residue A)) hfred hfsep
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

/-- A simple root in the ambient residue field lifts to a root of a monic
lift of the given separable residue polynomial.  Keeping the polynomial
explicit is useful for finite intermediate residue extensions of an
infinite ambient extension. -/
theorem monic_separable_reduction
    (f : A[X]) (hfmonic : f.Monic)
    (hfsep : (f.map (residue A)).Separable)
    (a₀ : ResidueField B)
    (ha₀ : ((f.map (residue A)).map
      (algebraMap (ResidueField A) (ResidueField B))).IsRoot a₀) :
    ∃ a : B, (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ := by
  let g : B[X] := f.map (algebraMap A B)
  have hgmonic : g.Monic := hfmonic.map (algebraMap A B)
  have hreduce : g.map (residue B) =
      (f.map (residue A)).map
        (algebraMap (ResidueField A) (ResidueField B)) := by
    change (f.map (algebraMap A B)).map (residue B) = _
    ext n
    simp only [coeff_map]
    exact (IsLocalRing.ResidueField.algebraMap_residue (f.coeff n)).symm
  have hroot : aeval a₀ g = 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, hreduce]
    simpa [Polynomial.IsRoot.def] using ha₀
  have hsimple₀ :
      aeval a₀ (derivative ((f.map (residue A)).map
        (algebraMap (ResidueField A) (ResidueField B)))) ≠ 0 :=
    (hfsep.map).aeval_derivative_ne_zero (by
      simpa [Polynomial.IsRoot.def, aeval_def] using ha₀)
  have hsimple : aeval a₀ (derivative g) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map, hreduce]
    simpa [aeval_def] using hsimple₀
  have hlift :=
    ((HenselianLocalRing.TFAE B).out 0 1).mp
      (inferInstance : HenselianLocalRing B)
  exact hlift g hgmonic a₀ hroot hsimple

theorem monic_lift_separable
    (f₀ : (ResidueField A)[X]) (hf₀monic : f₀.Monic)
    (hf₀sep : f₀.Separable) (a₀ : ResidueField B)
    (ha₀ : (f₀.map (algebraMap (ResidueField A) (ResidueField B))).IsRoot a₀) :
    ∃ f : A[X], f.Monic ∧ f.map (residue A) = f₀ ∧
      ∃ a : B, (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ := by
  have hf₀lift : f₀ ∈ Polynomial.lifts (residue A) :=
    Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective f₀
  obtain ⟨f, hfmap, _hfdegree, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf₀lift hf₀monic
  let g : B[X] := f.map (algebraMap A B)
  have hgmonic : g.Monic := hfmonic.map (algebraMap A B)
  have hreduce : g.map (residue B) =
      f₀.map (algebraMap (ResidueField A) (ResidueField B)) := by
    change (f.map (algebraMap A B)).map (residue B) = _
    rw [← hfmap]
    ext n
    simp only [coeff_map]
    exact (IsLocalRing.ResidueField.algebraMap_residue (f.coeff n)).symm
  have hroot : aeval a₀ g = 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, hreduce]
    simpa [Polynomial.IsRoot.def] using ha₀
  have hsimple₀ :
      aeval a₀ (derivative
        (f₀.map (algebraMap (ResidueField A) (ResidueField B)))) ≠ 0 :=
    (hf₀sep.map).aeval_derivative_ne_zero (by
      simpa [Polynomial.IsRoot.def, aeval_def] using ha₀)
  have hsimple : aeval a₀ (derivative g) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map, hreduce]
    simpa [aeval_def] using hsimple₀
  have hlift :=
    ((HenselianLocalRing.TFAE B).out 0 1).mp
      (inferInstance : HenselianLocalRing B)
  obtain ⟨a, ha, hresidue⟩ := hlift g hgmonic a₀ hroot hsimple
  exact ⟨f, hfmonic, hfmap, a, ha, hresidue⟩

/-- A separable residue-field element lifts to a root of a monic lift of its
minimal polynomial. -/
theorem monic_minpoly_separable
    (a₀ : ResidueField B)
    (hint : IsIntegral (ResidueField A) a₀)
    (hsep : (minpoly (ResidueField A) a₀).Separable) :
    ∃ f : A[X], f.Monic ∧
      f.map (residue A) = minpoly (ResidueField A) a₀ ∧
      ∃ a : B, (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ := by
  let f₀ := minpoly (ResidueField A) a₀
  have hf₀monic : f₀.Monic := minpoly.monic hint
  have hf₀lift : f₀ ∈ Polynomial.lifts (residue A) :=
    Polynomial.map_surjective (residue A) Ideal.Quotient.mk_surjective f₀
  obtain ⟨f, hfmap, _hfdegree, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hf₀lift hf₀monic
  let g : B[X] := f.map (algebraMap A B)
  have hgmonic : g.Monic := hfmonic.map (algebraMap A B)
  have hreduce : g.map (residue B) =
      f₀.map (algebraMap (ResidueField A) (ResidueField B)) := by
    change (f.map (algebraMap A B)).map (residue B) = _
    rw [← hfmap]
    ext n
    simp only [coeff_map]
    exact (IsLocalRing.ResidueField.algebraMap_residue (f.coeff n)).symm
  have hroot : aeval a₀ g = 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, hreduce]
    simpa [f₀, aeval_def] using minpoly.aeval (ResidueField A) a₀
  have hsimple₀ :
      aeval a₀ (derivative f₀) ≠ 0 :=
    hsep.aeval_derivative_ne_zero
      (minpoly.aeval (ResidueField A) a₀)
  have hsimple : aeval a₀ (derivative g) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map,
      ← derivative_map, hreduce]
    simpa [aeval_def] using hsimple₀
  have hlift :=
    ((HenselianLocalRing.TFAE B).out 0 1).mp
      (inferInstance : HenselianLocalRing B)
  obtain ⟨a, ha, hresidue⟩ := hlift g hgmonic a₀ hroot hsimple
  exact ⟨f, hfmonic, hfmap, a, ha, hresidue⟩

/-- A residue-field element in a separable extension lifts to a root of a
monic lift of its minimal polynomial.  This is the Newton--Hensel step in
Milne, Proposition 7.50. -/
theorem monic_minpoly_lift
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (a₀ : ResidueField B) :
    ∃ f : A[X], f.Monic ∧
      f.map (residue A) = minpoly (ResidueField A) a₀ ∧
      ∃ a : B, (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ :=
  monic_minpoly_separable A B a₀
    (Algebra.IsIntegral.isIntegral a₀)
    (Algebra.IsSeparable.isSeparable (ResidueField A) a₀)

/-- A finite separable intermediate field has a primitive element whose
ambient algebra adjoin is exactly the intermediate field's underlying
subalgebra. -/
theorem primitive_separable_intermediate
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (E : IntermediateField F L) [FiniteDimensional F E]
    [Algebra.IsSeparable F E] :
    ∃ x : L, x ∈ E ∧ Algebra.adjoin F {x} = E.toSubalgebra := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F E
  rw [IntermediateField.adjoin_eq_top_iff] at hx
  refine ⟨x, x.property, ?_⟩
  have hmap := congrArg (fun S : Subalgebra F E ↦ S.map E.val) hx
  simpa [IntermediateField.range_val] using hmap

/-- The lifted root can be chosen to reduce to a primitive element of the
finite separable residue-field extension. -/
theorem monic_primitive_lift
    [IsDomain A] [IsIntegrallyClosed A] [IsDomain B]
    [Module.IsTorsionFree A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ (a₀ : ResidueField B) (f : A[X]) (a : B),
      Algebra.adjoin (ResidueField A) {a₀} = ⊤ ∧
        f.Monic ∧
        f.map (residue A) = minpoly (ResidueField A) a₀ ∧
        (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ ∧
        Irreducible f ∧ IsIntegral A a ∧ minpoly A a = f := by
  obtain ⟨a₀, ha₀⟩ :=
    Field.exists_primitive_element (ResidueField A) (ResidueField B)
  rw [IntermediateField.adjoin_eq_top_iff] at ha₀
  obtain ⟨f, hfmonic, hfmap, a, ha, hresidue⟩ :=
    monic_minpoly_lift A B a₀
  have hfred : Irreducible (f.map (residue A)) := by
    rw [hfmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀)
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (residue A) f hfred
  have haeval : aeval a f = 0 := by
    simpa [Polynomial.IsRoot.def, aeval_def] using ha
  have haintegral : IsIntegral A a := ⟨f, hfmonic, haeval⟩
  have hdvd : minpoly A a ∣ f :=
    minpoly.isIntegrallyClosed_dvd haintegral haeval
  have hminpoly : minpoly A a = f :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic haintegral) hfmonic
      ((minpoly.irreducible haintegral).associated_of_dvd hfirr hdvd)
  exact ⟨a₀, f, a, ha₀, hfmonic, hfmap, ha, hresidue,
    hfirr, haintegral, hminpoly⟩

omit [HenselianLocalRing A] [HenselianLocalRing B]
  [IsLocalHom (algebraMap A B)] in
/-- The algebra generated by a lifted root is local.  Via its minimal
polynomial it is equivalent to the local adjoining-root algebra above. -/
theorem irreducible_minpoly_residue
    [IsDomain A] [IsDiscreteValuationRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Module.IsTorsionFree A B]
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
    adjoin_root_irreducible A (minpoly A a)
      (hminpoly.symm ▸ hfmonic) hfred'
  exact e.toRingEquiv.isLocalRing

omit [HenselianLocalRing A] [HenselianLocalRing B]
  [IsLocalHom (algebraMap A B)] in
/-- The algebra generated by a lifted root is formally unramified when its
minimal polynomial has separable irreducible reduction. -/
theorem adjoin_separable_minpoly
    [IsDomain A] [IsDiscreteValuationRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Module.IsTorsionFree A B]
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
    adjoin_formally_separable A
      (minpoly A a) (hminpoly.symm ▸ hfmonic) hfred' hfsep'
  exact Algebra.FormallyUnramified.of_equiv e

omit [HenselianLocalRing A] [HenselianLocalRing B]
  [IsLocalHom (algebraMap A B)] in
/-- The generated unramified local algebra is itself a discrete valuation
ring.  This supplies the valuation ring of the lifted field extension in
Milne's construction. -/
theorem discrete_separable_minpoly
    [IsDomain A] [IsDiscreteValuationRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Module.IsTorsionFree A B]
    (f : A[X]) (a : B) (hfmonic : f.Monic)
    (hfred : Irreducible (f.map (residue A)))
    (hfsep : (f.map (residue A)).Separable)
    (haintegral : IsIntegral A a) (hminpoly : minpoly A a = f) :
    IsDiscreteValuationRing (Algebra.adjoin A ({a} : Set B)) := by
  let U := Algebra.adjoin A ({a} : Set B)
  letI : IsLocalRing U :=
    irreducible_minpoly_residue A B f a
      hfmonic hfred haintegral hminpoly
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral haintegral
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Algebra.FormallyUnramified A U :=
    adjoin_separable_minpoly A B f a
      hfmonic hfred hfsep haintegral hminpoly
  letI : IsDedekindDomain U := isDedekindDomain.of_formallyUnramified A U
  have hnfield : ¬ IsField U := by
    intro hU
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField
        (FaithfulSMul.algebraMap_injective A U) hU)
  have hdedekind : IsDedekindDomain U := inferInstance
  exact ((IsDiscreteValuationRing.TFAE U hnfield).out 2 0).mp hdedekind

/-- If an element upstairs reduces to a primitive residue-field element,
then the residue field of the subalgebra it generates maps onto the full
upper residue field.  This is the residue-degree-one half of the
unramified/totally-ramified decomposition. -/
theorem field_adjoin_surjective
    (a₀ : ResidueField B) (a : B)
    (hprimitive : Algebra.adjoin (ResidueField A) {a₀} = ⊤)
    (hresidue : residue B a = a₀) :
    let U := Algebra.adjoin A ({a} : Set B)
    let P := (maximalIdeal B).under U
    Function.Surjective
      (algebraMap (U ⧸ P) (B ⧸ maximalIdeal B)) := by
  let U := Algebra.adjoin A ({a} : Set B)
  let Q := maximalIdeal B
  let P := Q.under U
  let p := maximalIdeal A
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : P.IsPrime := Ideal.IsPrime.under U Q
  letI : Q.LiesOver P := ⟨rfl⟩
  letI : Q.LiesOver p := by
    change (maximalIdeal B).LiesOver (maximalIdeal A)
    infer_instance
  letI : P.LiesOver p := ⟨by
    change p = (Q.comap (algebraMap U B)).comap (algebraMap A U)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact Ideal.LiesOver.over⟩
  letI : P.LiesOver (maximalIdeal A) := by
    change P.LiesOver p
    infer_instance
  letI : Algebra (ResidueField A) (U ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
  letI : Algebra (U ⧸ P) (ResidueField B) :=
    Ideal.Quotient.algebraOfLiesOver Q P
  letI : IsScalarTower (ResidueField A) (U ⧸ P) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
  letI : IsScalarTower U (U ⧸ P) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  change Function.Surjective (IsScalarTower.toAlgHom (ResidueField A)
    (U ⧸ P) (ResidueField B))
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hprimitive]
  refine Algebra.adjoin_singleton_le ?_
  use algebraMap U (U ⧸ P) ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom,
    ← IsScalarTower.algebraMap_apply]
  simp [hresidue]

/-- The residue image of the algebra generated by a lift `a` is exactly the
residue-field algebra generated by its reduction `a₀`.  Unlike the
surjectivity specialization above, this applies to a generator of any finite
intermediate residue extension in Proposition 7.50. -/
theorem residue_adjoin_range
    (a₀ : ResidueField B) (a : B)
    (hresidue : residue B a = a₀) :
    let U := Algebra.adjoin A ({a} : Set B)
    let Q := maximalIdeal B
    let P := Q.under U
    letI : Algebra (ResidueField A) (U ⧸ P) :=
      Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
    letI : Algebra (U ⧸ P) (ResidueField B) :=
      Ideal.Quotient.algebraOfLiesOver Q P
    letI : IsScalarTower (ResidueField A) (U ⧸ P) (ResidueField B) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl)
    (IsScalarTower.toAlgHom (ResidueField A) (U ⧸ P)
      (ResidueField B)).range =
        Algebra.adjoin (ResidueField A) {a₀} := by
  let U := Algebra.adjoin A ({a} : Set B)
  let Q := maximalIdeal B
  let P := Q.under U
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : P.IsPrime := Ideal.IsPrime.under U Q
  letI : Q.LiesOver P := ⟨rfl⟩
  let p := maximalIdeal A
  letI : Q.LiesOver p := by
    change (maximalIdeal B).LiesOver (maximalIdeal A)
    infer_instance
  letI : P.LiesOver p := ⟨by
    change p = (Q.comap (algebraMap U B)).comap (algebraMap A U)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact Ideal.LiesOver.over⟩
  letI : P.LiesOver (maximalIdeal A) := by
    change P.LiesOver p
    infer_instance
  letI : Algebra (ResidueField A) (U ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
  letI : Algebra (U ⧸ P) (ResidueField B) :=
    Ideal.Quotient.algebraOfLiesOver Q P
  letI : IsScalarTower (ResidueField A) (U ⧸ P) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
  letI : IsScalarTower U (U ⧸ P) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let phi := IsScalarTower.toAlgHom (ResidueField A) (U ⧸ P)
    (ResidueField B)
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    change residue B (u : B) ∈ Algebra.adjoin (ResidueField A) {a₀}
    have hclosed : ∀ x : B, x ∈ Algebra.adjoin A ({a} : Set B) →
        residue B x ∈ Algebra.adjoin (ResidueField A) {a₀} := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff.mp hx, hresidue]
          exact Algebra.subset_adjoin (Set.mem_singleton a₀)
      | algebraMap r =>
          rw [← IsLocalRing.ResidueField.algebraMap_residue]
          exact (Algebra.adjoin (ResidueField A) {a₀}).algebraMap_mem _
      | add x y _ _ hx hy =>
          rw [map_add]
          exact (Algebra.adjoin (ResidueField A) {a₀}).add_mem hx hy
      | mul x y _ _ hx hy =>
          rw [map_mul]
          exact (Algebra.adjoin (ResidueField A) {a₀}).mul_mem hx hy
    exact hclosed u u.property
  · refine Algebra.adjoin_le ?_
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨algebraMap U (U ⧸ P)
      ⟨a, Algebra.self_mem_adjoin_singleton A a⟩, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom,
      ← IsScalarTower.algebraMap_apply]
    simp [hresidue]

/-- The residue map from `A[a]` is onto the ambient residue field exactly
when the reduction of `a` generates that field.  The range equality above
is the stronger form used for proper intermediate residue fields. -/
theorem residue_adjoin_surjective
    (a₀ : ResidueField B) (a : B)
    (hresidue : residue B a = a₀) :
    let U := Algebra.adjoin A ({a} : Set B)
    let Q := maximalIdeal B
    let P := Q.under U
    letI : Algebra (ResidueField A) (U ⧸ P) :=
      Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
    letI : Algebra (U ⧸ P) (ResidueField B) :=
      Ideal.Quotient.algebraOfLiesOver Q P
    letI : IsScalarTower (ResidueField A) (U ⧸ P) (ResidueField B) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl)
    Function.Surjective
        (IsScalarTower.toAlgHom (ResidueField A) (U ⧸ P)
          (ResidueField B)) ↔
      Algebra.adjoin (ResidueField A) {a₀} = ⊤ := by
  let U := Algebra.adjoin A ({a} : Set B)
  let Q := maximalIdeal B
  let P := Q.under U
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : P.IsPrime := Ideal.IsPrime.under U Q
  letI : Q.LiesOver P := ⟨rfl⟩
  let p := maximalIdeal A
  letI : Q.LiesOver p := by
    change (maximalIdeal B).LiesOver (maximalIdeal A)
    infer_instance
  letI : P.LiesOver p := ⟨by
    change p = (Q.comap (algebraMap U B)).comap (algebraMap A U)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact Ideal.LiesOver.over⟩
  letI : P.LiesOver (maximalIdeal A) := by
    change P.LiesOver p
    infer_instance
  letI : Algebra (ResidueField A) (U ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (maximalIdeal A)
  letI : Algebra (U ⧸ P) (ResidueField B) :=
    Ideal.Quotient.algebraOfLiesOver Q P
  letI : IsScalarTower (ResidueField A) (U ⧸ P) (ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
  change Function.Surjective
      (IsScalarTower.toAlgHom (ResidueField A) (U ⧸ P)
        (ResidueField B)) ↔
    Algebra.adjoin (ResidueField A) {a₀} = ⊤
  rw [← AlgHom.range_eq_top,
    residue_adjoin_range A B a₀ a hresidue]

/-- A lift of a primitive lower-residue-field generator makes the residue
map in a local tower surjective. -/
theorem residue_primitive_lift
    (C : Type*) [CommRing C] [IsLocalRing C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsLocalHom (algebraMap A C)] [IsLocalHom (algebraMap C B)]
    (a₀ : ResidueField B) (c : C)
    (hprimitive : Algebra.adjoin (ResidueField A) {a₀} = ⊤)
    (hresidue : residue B (algebraMap C B c) = a₀) :
    Function.Surjective
      (algebraMap (ResidueField C) (ResidueField B)) := by
  change Function.Surjective (IsScalarTower.toAlgHom (ResidueField A)
    (ResidueField C) (ResidueField B))
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hprimitive]
  refine Algebra.adjoin_singleton_le ?_
  use algebraMap C (ResidueField C) c
  rw [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom,
    ← IsScalarTower.algebraMap_apply]
  simpa using hresidue

/-- In the finite integral setting, the algebra generated by the lifted
primitive residue element has exactly the prescribed upper residue field. -/
theorem adjoin_primitive_lift
    [IsDomain A] [IsDiscreteValuationRing A] [IsIntegrallyClosed A]
    [IsDomain B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (a₀ : ResidueField B) (f : A[X]) (a : B)
    (hprimitive : Algebra.adjoin (ResidueField A) {a₀} = ⊤)
    (hfmonic : f.Monic)
    (hfmap : f.map (residue A) = minpoly (ResidueField A) a₀)
    (hresidue : residue B a = a₀)
    (haintegral : IsIntegral A a) (hminpoly : minpoly A a = f) :
    let U := Algebra.adjoin A ({a} : Set B)
    letI := irreducible_minpoly_residue A B f a
      hfmonic (hfmap ▸ minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀))
      haintegral hminpoly
    letI := Algebra.finite_adjoin_simple_of_isIntegral haintegral
    letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
    letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
    letI : FaithfulSMul U B :=
      (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
    letI : IsLocalHom (algebraMap U B) :=
      Algebra.IsIntegral.isLocalHom U B
    Function.Surjective
      (algebraMap (ResidueField U) (ResidueField B)) := by
  let U := Algebra.adjoin A ({a} : Set B)
  have hfred : Irreducible (f.map (residue A)) := by
    rw [hfmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀)
  letI : IsLocalRing U :=
    irreducible_minpoly_residue A B f a
      hfmonic hfred haintegral hminpoly
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral haintegral
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  exact residue_primitive_lift A B U a₀
    ⟨a, Algebra.self_mem_adjoin_singleton A a⟩ hprimitive hresidue

/-- Packaged residue-lifting data for Proposition 7.50.  The generated
subalgebra is finite and integral because `f` is the minimal polynomial of
`a`, and its residue quotient maps onto the full residue field upstairs. -/
theorem primitive_lift_surjective
    [IsDomain A] [IsIntegrallyClosed A] [IsDomain B]
    [Module.IsTorsionFree A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ (a₀ : ResidueField B) (f : A[X]) (a : B),
      Algebra.adjoin (ResidueField A) {a₀} = ⊤ ∧
        f.Monic ∧
        f.map (residue A) = minpoly (ResidueField A) a₀ ∧
        (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ ∧
        Irreducible f ∧ IsIntegral A a ∧ minpoly A a = f ∧
        (let U := Algebra.adjoin A ({a} : Set B)
         let P := (maximalIdeal B).under U
         Function.Surjective
           (algebraMap (U ⧸ P) (B ⧸ maximalIdeal B))) := by
  obtain ⟨a₀, f, a, hprimitive, hfmonic, hfmap, ha, hresidue,
      hfirr, haintegral, hminpoly⟩ :=
    monic_primitive_lift A B
  refine ⟨a₀, f, a, hprimitive, hfmonic, hfmap, ha, hresidue,
    hfirr, haintegral, hminpoly, ?_⟩
  exact field_adjoin_surjective A B a₀ a
    hprimitive hresidue

/-- Constructive half of Milne, Proposition 7.50, for a finite integral
local extension.  A finite separable upper residue field is generated by the
residue of an integral element whose generated algebra is an unramified DVR. -/
theorem unramified_adjoin_prescribed
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ (a₀ : ResidueField B) (f : A[X]) (a : B),
      Algebra.adjoin (ResidueField A) {a₀} = ⊤ ∧
        f.Monic ∧
        f.map (residue A) = minpoly (ResidueField A) a₀ ∧
        (f.map (algebraMap A B)).IsRoot a ∧ residue B a = a₀ ∧
        IsIntegral A a ∧ minpoly A a = f ∧
        (let U := Algebra.adjoin A ({a} : Set B)
         let P := (maximalIdeal B).under U
         IsLocalRing U ∧
           Algebra.FormallyUnramified A U ∧
           IsDiscreteValuationRing U ∧
           P.IsMaximal ∧
           Function.Surjective
             (algebraMap (U ⧸ P) (B ⧸ maximalIdeal B))) := by
  obtain ⟨a₀, f, a, hprimitive, hfmonic, hfmap, ha, hresidue,
      _hfirr, haintegral, hminpoly⟩ :=
    monic_primitive_lift A B
  have hfred : Irreducible (f.map (residue A)) := by
    rw [hfmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀)
  have hfsep : (f.map (residue A)).Separable := by
    rw [hfmap]
    exact Algebra.IsSeparable.isSeparable (ResidueField A) a₀
  let U := Algebra.adjoin A ({a} : Set B)
  let P := (maximalIdeal B).under U
  have hlocal : IsLocalRing U :=
    irreducible_minpoly_residue A B f a
      hfmonic hfred haintegral hminpoly
  have hunramified : Algebra.FormallyUnramified A U :=
    adjoin_separable_minpoly A B f a
      hfmonic hfred hfsep haintegral hminpoly
  have hdvr : IsDiscreteValuationRing U :=
    discrete_separable_minpoly A B f a
      hfmonic hfred hfsep haintegral hminpoly
  have hP : P.IsMaximal := by
    letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)
  refine ⟨a₀, f, a, hprimitive, hfmonic, hfmap, ha, hresidue,
    haintegral, hminpoly, hlocal, hunramified, hdvr, hP, ?_⟩
  exact field_adjoin_surjective A B a₀ a
    hprimitive hresidue

/-- The image of a local subalgebra in the ambient residue field.  This is
the order-preserving map in the residue-field correspondence of Proposition
7.50. -/
noncomputable def residueImage (U : Subalgebra A B) :
    Subalgebra (ResidueField A) (ResidueField B) where
  carrier := residue B '' (U : Set B)
  zero_mem' := ⟨0, U.zero_mem, map_zero _⟩
  one_mem' := ⟨1, U.one_mem, map_one _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, U.add_mem hx hy, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, U.mul_mem hx hy, by simp⟩
  algebraMap_mem' := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨algebraMap A B a, U.algebraMap_mem a,
      (IsLocalRing.ResidueField.algebraMap_residue a).symm⟩

@[simp]
theorem residueImage_top :
    residueImage A B ⊤ = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨b, rfl⟩ := residue_surjective x
  exact ⟨b, trivial, rfl⟩

/-- Taking the residue image is monotone in the local subalgebra. -/
theorem residueImage_mono : Monotone (residueImage A B) := by
  intro U V hUV
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hUV hx, rfl⟩

/-- The residue image preserves binary composita. -/
theorem residueImage_sup (U V : Subalgebra A B) :
    residueImage A B (U ⊔ V) = residueImage A B U ⊔ residueImage A B V := by
  apply le_antisymm
  · rw [Algebra.sup_def]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rcases hx with hx | hx
        · exact (show residueImage A B U ≤ _ from le_sup_left)
            ⟨x, hx, rfl⟩
        · exact (show residueImage A B V ≤ _ from le_sup_right)
            ⟨x, hx, rfl⟩
    | algebraMap a =>
        rw [← IsLocalRing.ResidueField.algebraMap_residue]
        exact (residueImage A B U ⊔ residueImage A B V).algebraMap_mem _
    | add x y _ _ hx hy =>
        rw [map_add]
        exact (residueImage A B U ⊔ residueImage A B V).add_mem hx hy
    | mul x y _ _ hx hy =>
        rw [map_mul]
        exact (residueImage A B U ⊔ residueImage A B V).mul_mem hx hy
  · exact sup_le
      (residueImage_mono A B le_sup_left)
      (residueImage_mono A B le_sup_right)

/-- The residue image of a singly generated subalgebra is generated by the
residue of the same element. -/
theorem residue_adjoin_singleton (a : B) :
    residueImage A B (Algebra.adjoin A ({a} : Set B)) =
      Algebra.adjoin (ResidueField A) {residue B a} := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff.mp hx]
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap r =>
        rw [← IsLocalRing.ResidueField.algebraMap_residue]
        exact (Algebra.adjoin (ResidueField A) {residue B a}).algebraMap_mem _
    | add x y _ _ hx hy => simpa using (Algebra.adjoin (ResidueField A)
        {residue B a}).add_mem hx hy
    | mul x y _ _ hx hy => simpa using (Algebra.adjoin (ResidueField A)
        {residue B a}).mul_mem hx hy
  · apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨a, Algebra.self_mem_adjoin_singleton A a, rfl⟩

/-- The residue image of the algebra generated by `a`. -/
noncomputable def residueImageAdjoin (a : B) :
    Subalgebra (ResidueField A) (ResidueField B) :=
  residueImage A B (Algebra.adjoin A ({a} : Set B))

/-- The residue image of a singly generated local algebra is generated by
the reduction of its generator. -/
theorem residue_adjoin
    (a₀ : ResidueField B) (a : B) (hresidue : residue B a = a₀) :
    residueImageAdjoin A B a = Algebra.adjoin (ResidueField A) {a₀} := by
  rw [residueImageAdjoin, residue_adjoin_singleton, hresidue]

/-- An element of the residue image of `A[a]` is represented by an actual
element of `A[a]` whose ambient residue is the prescribed element. -/
theorem adjoin_element_image
    (a : B) (a₀ : ResidueField B)
    (ha₀ : a₀ ∈ residueImageAdjoin A B a) :
    ∃ u : Algebra.adjoin A ({a} : Set B), residue B (u : B) = a₀ := by
  rcases ha₀ with ⟨u, hu, rfl⟩
  exact ⟨⟨u, hu⟩, rfl⟩

/-- Every element of `A[a]` reduces to an element of its residue image. -/
theorem residue_image_adjoin
    (a : B) (u : Algebra.adjoin A ({a} : Set B)) :
    residue B (u : B) ∈ residueImageAdjoin A B a := by
  exact ⟨u, u.property, rfl⟩

/-- Data realizing a finite intermediate residue extension by an unramified
singly generated local algebra. -/
structure UnramifiedIntermediateLift
    [IsDomain A] [IsDomain B]
    (E : IntermediateField (ResidueField A) (ResidueField B)) where
  residueGenerator : ResidueField B
  residueGenerator_mem : residueGenerator ∈ E
  residue_adjoin_eq :
    Algebra.adjoin (ResidueField A) {residueGenerator} = E.toSubalgebra
  residuePolynomial : (ResidueField A)[X]
  residuePolynomial_monic : residuePolynomial.Monic
  residuePolynomial_irreducible : Irreducible residuePolynomial
  residuePolynomial_separable : residuePolynomial.Separable
  residue_generator_root :
    (residuePolynomial.map
      (algebraMap (ResidueField A) (ResidueField B))).IsRoot residueGenerator
  polynomial : A[X]
  generator : B
  polynomial_monic : polynomial.Monic
  polynomial_reduction : polynomial.map (residue A) = residuePolynomial
  generator_isRoot :
    (polynomial.map (algebraMap A B)).IsRoot generator
  generator_residue : residue B generator = residueGenerator
  generator_integral : IsIntegral A generator
  generator_minpoly : minpoly A generator = polynomial
  adjoin_local_ring : IsLocalRing (Algebra.adjoin A ({generator} : Set B))
  adjoin_formallyUnramified :
    Algebra.FormallyUnramified A (Algebra.adjoin A ({generator} : Set B))
  adjoin_valuation_ring :
    IsDiscreteValuationRing (Algebra.adjoin A ({generator} : Set B))
  adjoin_maximalIdeal :
    ((maximalIdeal B).under
      (Algebra.adjoin A ({generator} : Set B))).IsMaximal
  residueImage_eq : residueImageAdjoin A B generator = E.toSubalgebra

/-- Constructive half of Proposition 7.50 for an arbitrary finite separable
intermediate residue field.  The lifted algebra is an unramified DVR and its
image in the ambient residue field is exactly `E`, rather than necessarily
the whole ambient residue field. -/
theorem adjoin_prescribed_intermediate
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    Nonempty (UnramifiedIntermediateLift A B E) := by
  obtain ⟨a₀, ha₀E, hprimitive⟩ :=
    primitive_separable_intermediate E
  let a₀E : E := ⟨a₀, ha₀E⟩
  let f₀ : (ResidueField A)[X] := minpoly (ResidueField A) a₀E
  have hf₀monic : f₀.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral a₀E)
  have hf₀sep : f₀.Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField A) a₀E
  have ha₀root :
      (f₀.map (algebraMap (ResidueField A) (ResidueField B))).IsRoot a₀ := by
    rw [Polynomial.IsRoot.def, eval_map, ← aeval_def]
    exact minpoly.aeval_algHom (ResidueField A) E.val a₀E
  obtain ⟨f, hfmonic, hfmap, a, ha, hresidue⟩ :=
    monic_lift_separable A B f₀ hf₀monic hf₀sep a₀ ha₀root
  have hfred : Irreducible (f.map (residue A)) := by
    rw [hfmap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀E)
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (residue A) f hfred
  have haeval : aeval a f = 0 := by
    simpa [Polynomial.IsRoot.def, aeval_def] using ha
  have haintegral : IsIntegral A a := ⟨f, hfmonic, haeval⟩
  have hdvd : minpoly A a ∣ f :=
    minpoly.isIntegrallyClosed_dvd haintegral haeval
  have hminpoly : minpoly A a = f :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic haintegral) hfmonic
      ((minpoly.irreducible haintegral).associated_of_dvd hfirr hdvd)
  have hfsep : (f.map (residue A)).Separable := by
    rw [hfmap]
    exact hf₀sep
  let U := Algebra.adjoin A ({a} : Set B)
  let Q := maximalIdeal B
  let P := Q.under U
  have hlocal : IsLocalRing U :=
    irreducible_minpoly_residue A B f a
      hfmonic hfred haintegral hminpoly
  have hunramified : Algebra.FormallyUnramified A U :=
    adjoin_separable_minpoly A B f a
      hfmonic hfred hfsep haintegral hminpoly
  have hdvr : IsDiscreteValuationRing U :=
    discrete_separable_minpoly A B f a
      hfmonic hfred hfsep haintegral hminpoly
  have hP : P.IsMaximal := by
    letI : Algebra.IsIntegral U B := Algebra.IsIntegral.tower_top A
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)
  refine ⟨{
    residueGenerator := a₀
    residueGenerator_mem := ha₀E
    residue_adjoin_eq := hprimitive
    residuePolynomial := f₀
    residuePolynomial_monic := hf₀monic
    residuePolynomial_irreducible :=
      minpoly.irreducible (Algebra.IsIntegral.isIntegral a₀E)
    residuePolynomial_separable := hf₀sep
    residue_generator_root := ha₀root
    polynomial := f
    generator := a
    polynomial_monic := hfmonic
    polynomial_reduction := hfmap
    generator_isRoot := ha
    generator_residue := hresidue
    generator_integral := haintegral
    generator_minpoly := hminpoly
    adjoin_local_ring := hlocal
    adjoin_formallyUnramified := hunramified
    adjoin_valuation_ring := hdvr
    adjoin_maximalIdeal := hP
    residueImage_eq := ?_ }⟩
  rw [residue_adjoin A B a₀ a hresidue, hprimitive]

/-- A chosen realization of a finite separable intermediate residue field by
an unramified local algebra. -/
noncomputable def unramifiedIntermediateLift
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    UnramifiedIntermediateLift A B E :=
  Classical.choice
    (adjoin_prescribed_intermediate A B E)

/-- The unramified local subalgebra chosen for `E`. -/
noncomputable def unramifiedAdjoinIntermediate
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] : Subalgebra A B :=
  Algebra.adjoin A
    ({(unramifiedIntermediateLift A B E).generator} : Set B)

theorem unramified_adjoin_residue
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    Module.Finite A (unramifiedAdjoinIntermediate A B E) := by
  apply Algebra.finite_adjoin_simple_of_isIntegral
  exact (unramifiedIntermediateLift A B E).generator_integral

theorem adjoin_intermediate_ring
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    IsLocalRing (unramifiedAdjoinIntermediate A B E) :=
  (unramifiedIntermediateLift A B E).adjoin_local_ring

theorem adjoin_intermediate_formally
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    Algebra.FormallyUnramified A
      (unramifiedAdjoinIntermediate A B E) :=
  (unramifiedIntermediateLift A B E).adjoin_formallyUnramified

theorem intermediate_discrete_valuation
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    IsDiscreteValuationRing
      (unramifiedAdjoinIntermediate A B E) :=
  (unramifiedIntermediateLift A B E).adjoin_valuation_ring

/-- Over an adically complete base DVR, the chosen finite unramified local
algebra is itself Henselian. -/
theorem adjoin_intermediate_henselian
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [IsAdicComplete (maximalIdeal A) A]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    HenselianLocalRing
      (unramifiedAdjoinIntermediate A B E) := by
  let U := unramifiedAdjoinIntermediate A B E
  letI : Module.Finite A U :=
    unramified_adjoin_residue A B E
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalRing U :=
    adjoin_intermediate_ring A B E
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Algebra.FormallyUnramified A U :=
    adjoin_intermediate_formally A B E
  exact henselian_formally_unramified A U

/-- The residue image of the chosen lift is exactly the prescribed
intermediate residue field. -/
theorem unramified_adjoin_image
    [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [FiniteDimensional (ResidueField A) E]
    [Algebra.IsSeparable (ResidueField A) E] :
    residueImageAdjoin A B
        (unramifiedIntermediateLift A B E).generator =
      E.toSubalgebra :=
  (unramifiedIntermediateLift A B E).residueImage_eq

end

end Submission.NumberTheory.Milne
