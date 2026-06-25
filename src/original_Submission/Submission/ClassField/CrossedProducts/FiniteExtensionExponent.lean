import Mathlib.Algebra.Module.ULift
import Mathlib.FieldTheory.KrullTopology
import Submission.ClassField.CohomologyOps.RestrictionCompatibility
import Submission.ClassField.CrossedProducts.BrauerRestriction
import Submission.ClassField.CrossedProducts.IsMulCoboundary
import Submission.ClassField.CrossedProducts.MultiplicativeHComparison

/-!
# Chapter IV, Section 3, Corollary 3.17: source statement

This file strengthens the finite-Galois exponent statement in the tracked
formalization to the arbitrary finite-extension statement printed in the
source.
-/

namespace Submission.CField.CProduca

open CategoryTheory groupCohomology
open BGroups

noncomputable section

universe u


attribute [local instance] Units.mulDistribMulActionRight

private def sourceRepresentation
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    Representation (ULift.{u} ℤ) G (Additive M) where
  toFun g :=
    { toFun := fun x ↦ Additive.ofMul (g • x.toMul)
      map_add' := fun x y ↦ congrArg Additive.ofMul (smul_mul' g x.toMul y.toMul)
      map_smul' := fun r x ↦
        (Representation.ofMulDistribMulAction G M g).map_smul r.down x }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [mul_smul]

private abbrev sourceRep
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    Rep (ULift.{u} ℤ) G :=
  Rep.of (sourceRepresentation (G := G) (M := M))

private def sourceCocyclesCocycle₂
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {f : G × G → M} (hf : IsMulCocycle₂ f) :
    cocycles₂ (sourceRep (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f,
    (mem_cocycles₂_iff
      (A := sourceRep (G := G) (M := M)) _).2 (by
        intro g h j
        exact congrArg Additive.ofMul (hf g h j))⟩

private def sourceCoboundariesCoboundary₂
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    coboundaries₂ (sourceRep (G := G) (M := M)) :=
  ⟨Additive.ofMul ∘ f, fun g ↦ Additive.ofMul (hf.choose g),
    funext fun p ↦ congrArg Additive.ofMul (hf.choose_spec p.1 p.2)⟩

private theorem sourceMulCoboundary₂_of_mem_coboundaries₂
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (f : G × G → Additive M)
    (hf : f ∈ coboundaries₂ (sourceRep (G := G) (M := M))) :
    IsMulCoboundary₂ (Additive.toMul ∘ f) := by
  rcases hf with ⟨a, rfl⟩
  exact ⟨fun g ↦ (a g).toMul, fun _ _ ↦ rfl⟩

private noncomputable def cocycleAdditive2
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : NMCocycl₂ (G := G) (M := M)) :
    groupCohomology.H2 (sourceRep (G := G) (M := M)) :=
  H2π (sourceRep (G := G) (M := M))
    (sourceCocyclesCocycle₂ c.isMulCocycle₂)

private theorem cocycle_additive_cohomologous
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    {c d : NMCocycl₂ (G := G) (M := M)}
    (h : MHTwo.IsCohomologous c d) :
    cocycleAdditive2 c = cocycleAdditive2 d := by
  rw [cocycleAdditive2, cocycleAdditive2, H2π_eq_iff]
  have hb := (sourceCoboundariesCoboundary₂ h).property
  convert hb using 1

private noncomputable def multiplicativeHAdditive
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (x : MHTwo G M) :
    groupCohomology.H2 (sourceRep (G := G) (M := M)) :=
  Quotient.lift cocycleAdditive2
    (fun _ _ h ↦ cocycle_additive_cohomologous h) x

@[simp] private theorem multiplicative_h_mk
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (c : NMCocycl₂ (G := G) (M := M)) :
    multiplicativeHAdditive (MHTwo.mk c) =
      cocycleAdditive2 c :=
  rfl

private theorem multiplicative_h_additive
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (x y : MHTwo G M) :
    multiplicativeHAdditive (x * y) =
      multiplicativeHAdditive x +
        multiplicativeHAdditive y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      change H2π _ (sourceCocyclesCocycle₂ (c * d).isMulCocycle₂) =
        H2π _ (sourceCocyclesCocycle₂ c.isMulCocycle₂) +
          H2π _ (sourceCocyclesCocycle₂ d.isMulCocycle₂)
      rw [← map_add]
      apply congrArg (H2π (sourceRep (G := G) (M := M)))
      apply Subtype.ext
      rfl

@[simp] private theorem source_multiplicative_additive
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    multiplicativeHAdditive (1 : MHTwo G M) = 0 := by
  have h := multiplicative_h_additive
    (1 : MHTwo G M) (1 : MHTwo G M)
  rw [one_mul] at h
  let a := multiplicativeHAdditive (1 : MHTwo G M)
  have ha : a = a + a := h
  have hz : 0 = a := by
    have hsub := congrArg (fun z ↦ z - a) ha
    simpa [add_assoc] using hsub
  exact hz.symm

private theorem multiplicative_h_injective
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    Function.Injective
      (multiplicativeHAdditive
        (G := G) (M := M)) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  obtain ⟨d, rfl⟩ := MHTwo.exists_mk_eq y
  rw [multiplicative_h_mk,
    multiplicative_h_mk] at hxy
  rw [MHTwo.mk_eq_iff]
  have hb := (H2π_eq_iff
    (sourceCocyclesCocycle₂ c.isMulCocycle₂)
    (sourceCocyclesCocycle₂ d.isMulCocycle₂)).1 hxy
  have hmul := sourceMulCoboundary₂_of_mem_coboundaries₂
    (G := G) (M := M)
    ((Additive.ofMul ∘ c) - (Additive.ofMul ∘ d)) hb
  convert hmul using 1

private def restrictionRepHom
    {G H M : Type u} [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction G M] [MulDistribMulAction H M]
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    Rep.res f (sourceRep (G := G) (M := M)) ⟶
      sourceRep (G := H) (M := M) :=
  Rep.ofHom ⟨LinearMap.id, fun h ↦ LinearMap.ext fun m ↦ by
    exact congrArg Additive.ofMul (hsmul h m.toMul).symm⟩

private noncomputable def additiveHRestriction
    {G H M : Type u} [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction G M] [MulDistribMulAction H M]
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m) :
    groupCohomology.H2 (sourceRep (G := G) (M := M)) →+
      groupCohomology.H2 (sourceRep (G := H) (M := M)) :=
  (groupCohomology.map f
    (restrictionRepHom f hsmul) 2).hom

private theorem multiplicative_additive_restriction
    {G H M : Type u} [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction G M] [MulDistribMulAction H M]
    (f : H →* G) (hsmul : ∀ h : H, ∀ m : M, h • m = f h • m)
    (x : MHTwo G M) :
    multiplicativeHAdditive
        (MHTwo.restrictionHom f hsmul x) =
      additiveHRestriction f hsmul
        (multiplicativeHAdditive x) := by
  induction x using Quotient.inductionOn with
  | _ c =>
      change H2π (sourceRep (G := H) (M := M)) _ =
        groupCohomology.map f
          (restrictionRepHom f hsmul) 2
          (H2π (sourceRep (G := G) (M := M)) _)
      rw [groupCohomology.H2π_comp_map_apply]
      congr 1

private theorem fixing_restriction_one
    (k E : Type u) [Field k] [Field E] [Algebra k E]
    (K : IntermediateField k E)
    (x : MHTwo Gal(E/k) Eˣ)
    (hx : galoisHRestriction k K E x = 1) :
    MHTwo.restrictionHom
        K.fixingSubgroup.subtype
        (by intro sigma m; rfl) x = 1 := by
  let H : Subgroup Gal(E/k) := K.fixingSubgroup
  let e : H ≃* Gal(E/K) := K.fixingSubgroupEquiv
  have he : (galoisTowerInclusion k K E).comp e.toMonoidHom = H.subtype := by
    ext sigma z
    rfl
  have hcomp := MHTwo.restrictionHom_comp
    (galoisTowerInclusion k K E) e.toMonoidHom
    (by intro sigma m; rfl) (by intro sigma m; rfl)
    (by intro sigma m; rfl) x
  change MHTwo.restrictionHom
      (galoisTowerInclusion k K E) (by intro sigma m; rfl) x = 1 at hx
  rw [hx, map_one] at hcomp
  have hresEq :
      MHTwo.restrictionHom
          ((galoisTowerInclusion k K E).comp e.toMonoidHom)
          (by intro sigma m; rfl) x =
        MHTwo.restrictionHom H.subtype
          (by intro sigma m; rfl) x := by
    cases he
    rfl
  rw [hresEq] at hcomp
  exact hcomp.symm

private theorem subgroup_nsmul_restriction
    {G M : Type u} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (H : Subgroup G) [H.FiniteIndex]
    (x : MHTwo G M)
    (hx : MHTwo.restrictionHom H.subtype
      (by intro sigma m; rfl) x = 1) :
    H.index • multiplicativeHAdditive x = 0 := by
  have hres := multiplicative_additive_restriction
    H.subtype (by intro sigma m; rfl) x
  rw [hx, source_multiplicative_additive] at hres
  have hres' :
      COps.restriction
          (sourceRep (G := G) (M := M)) H 2
          (multiplicativeHAdditive x) = 0 := by
    simpa [additiveHRestriction,
      restrictionRepHom] using hres.symm
  have htransfer := congrArg
    (fun f ↦ f (multiplicativeHAdditive x))
    (COps.restriction_corestriction_degrees
      (sourceRep (G := G) (M := M)) H 2)
  simpa [hres'] using htransfer.symm

private theorem relative_brauer_intermediate
    (k E : Type u) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    (K : IntermediateField k E)
    (x : relativeBrauerGroup k E)
    (hx : relativeBrauerChange k K E x = 1) :
    x ^ Module.finrank k K = 1 := by
  let e := CProduc.hRelativeBrauer k E
  let y : MHTwo Gal(E/k) Eˣ := e.symm x
  have hyBrauer : galoisHRestriction k K E y = 1 := by
    rw [GaloisRestrictionCompatibility]
    apply (CProduc.hRelativeBrauer K E).injective
    rw [h_brauer_restriction, map_one]
    simpa [y, e] using hx
  have hyRes := fixing_restriction_one k E K y hyBrauer
  let H : Subgroup Gal(E/k) := K.fixingSubgroup
  letI : H.FiniteIndex := inferInstance
  have hyAdd : H.index • multiplicativeHAdditive y = 0 :=
    subgroup_nsmul_restriction H y hyRes
  have hmapPow :
      multiplicativeHAdditive (y ^ H.index) =
        H.index • multiplicativeHAdditive y := by
    induction H.index with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, multiplicative_h_additive, ih,
          succ_nsmul]
  have hyPowIndex : y ^ H.index = 1 := by
    apply multiplicative_h_injective
    rw [hmapPow, hyAdd, source_multiplicative_additive]
  have hindex : H.index = Module.finrank k K :=
    (IntermediateField.finrank_eq_fixingSubgroup_index K).symm
  calc
    x ^ Module.finrank k K = (e y) ^ Module.finrank k K := by
      exact congrArg (fun z ↦ z ^ Module.finrank k K) (by
        simp [y])
    _ = e (y ^ Module.finrank k K) := (map_pow e y _).symm
    _ = 1 := by rw [← hindex, hyPowIndex, map_one]

set_option maxHeartbeats 1000000 in
-- The normal-closure and relative-Brauer calculation has a large elaboration term.
set_option synthInstance.maxHeartbeats 200000 in
-- Typeclass synthesis traverses several nested intermediate-field algebra structures.
/-- The Brauer class of a finite-dimensional central division algebra is
killed by the degree of the algebra. -/
theorem brauer_division_degree
    (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k D] [Module.Finite k D] :
    (brauerClass k (centralDivisionCSA k D)) ^
        Nat.sqrt (Module.finrank k D) = 1 := by
  classical
  obtain ⟨F, hcomm, hmax, hsep⟩ := maximal_separable_subfield k D
  letI : IsSimpleRing F :=
    commutative_subalgebra_simple k D F hcomm
  letI : Field F :=
    fieldCommutativeSubalgebra k D F hcomm
  letI : Algebra.IsSeparable k F := hsep
  have hdim : Module.finrank k D = (Module.finrank k F) ^ 2 :=
    (maximal_subfield_sq k D F hcomm).1 hmax
  have hsplitF : ISBy k F D :=
    embedding_split_sq k F D F.val hdim
  let i : F →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let F' : IntermediateField k (SeparableClosure k) := i.fieldRange
  let eF : F ≃ₐ[k] F' := AlgEquiv.ofInjectiveField i
  letI : Module.Finite k F' := Module.Finite.equiv eF.toLinearEquiv
  letI : Algebra.IsSeparable k F' := AlgEquiv.Algebra.isSeparable eF
  letI : Algebra F F' := eF.toRingHom.toAlgebra
  letI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    exact (eF.commutes r).symm
  have hsplitF' : ISBy k F' D :=
    ISBy.tower k F F' D hsplitF
  let N : IntermediateField k (SeparableClosure k) :=
    IntermediateField.normalClosure k F' (SeparableClosure k)
  letI : FiniteDimensional k N :=
    normalClosure.is_finiteDimensional k F' (SeparableClosure k)
  letI : IsGalois k N :=
    IsGalois.normalClosure k F' (SeparableClosure k)
  have hsplitN : ISBy k N D :=
    ISBy.tower k F' N D hsplitF'
  have hF'N : F' ≤ N := IntermediateField.le_normalClosure _
  let K : IntermediateField k N := F'.restrict hF'N
  let eK : F' ≃ₐ[k] K := IntermediateField.restrict_algEquiv hF'N
  letI : Algebra F' K := eK.toRingHom.toAlgebra
  letI : IsScalarTower k F' K :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := F') (A := K)
      fun r ↦ (eK.commutes r).symm
  have hsplitK : ISBy k K D :=
    ISBy.tower k F' K D hsplitF'
  have hmemN :
      brauerClass k (centralDivisionCSA k D) ∈ relativeBrauerGroup k N :=
    (brauer_relative_split
      k N (centralDivisionCSA k D)).2 hsplitN
  let xN : relativeBrauerGroup k N :=
    ⟨brauerClass k (centralDivisionCSA k D), hmemN⟩
  have hxK : relativeBrauerChange k K N xN = 1 := by
    apply Subtype.ext
    change brauerBaseChange k K
      (brauerClass k (centralDivisionCSA k D)) = 1
    exact (relative_brauer_group k K
      (brauerClass k (centralDivisionCSA k D))).1
      ((brauer_relative_split
        k K (centralDivisionCSA k D)).2 hsplitK)
  have hx := relative_brauer_intermediate
    k N K xN hxK
  have hdegree : Module.finrank k K = Nat.sqrt (Module.finrank k D) := by
    calc
      Module.finrank k K = Module.finrank k F' :=
        eK.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k F := eF.toLinearEquiv.finrank_eq.symm
      _ = Nat.sqrt (Module.finrank k D) := by rw [hdim]; simp
  exact congrArg Subtype.val (hdegree ▸ hx)

/-- The degree of a finite-dimensional central division algebra divides the
degree of every finite field extension which splits it. -/
theorem division_dvd_split
    (k D L : Type u) [Field k] [DivisionRing D] [Algebra k D]
    [Algebra.IsCentral k D] [Module.Finite k D]
    [Field L] [Algebra k L] [Module.Finite k L]
    (hsplit : ISBy k L D) :
    Nat.sqrt (Module.finrank k D) ∣ Module.finrank k L := by
  obtain ⟨B, i, hi, hBdim, hDB⟩ :=
    (split_similar_containing k L D).1 hsplit
  obtain ⟨q, hq, E, hEdiv, hEalg, hEcentral, hEfinite, ⟨eB⟩⟩ :=
    matrix_division_algebra k B
  letI : NeZero q := hq
  letI : DivisionRing E := hEdiv
  letI : Algebra k E := hEalg
  letI : Algebra.IsCentral k E := hEcentral
  letI : Module.Finite k E := hEfinite
  have hBE : IsBrauerEquivalent B (centralDivisionCSA k E) := by
    refine ⟨1, q, one_ne_zero, NeZero.ne q, ?_⟩
    exact ⟨(matrixFinAlg k B).trans eB⟩
  have hDE : IsBrauerEquivalent
      (centralDivisionCSA k D) (centralDivisionCSA k E) :=
    hDB.trans hBE
  obtain ⟨eDE⟩ :=
    (division_brauer_equivalent k D E).1 hDE
  obtain ⟨d, hd⟩ := finrank_simple_square k D
  have hsquare : (Module.finrank k L) ^ 2 = (q * d) ^ 2 := by
    calc
      (Module.finrank k L) ^ 2 = Module.finrank k B := hBdim.symm
      _ = Module.finrank k (Matrix (Fin q) (Fin q) E) :=
        eB.toLinearEquiv.finrank_eq
      _ = q * q * Module.finrank k E := by
        rw [Module.finrank_matrix, Fintype.card_fin]
      _ = q * q * Module.finrank k D := by
        rw [eDE.toLinearEquiv.finrank_eq]
      _ = (q * d) ^ 2 := by rw [hd]; ring
  have hdegree : Module.finrank k L = q * d :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) hsquare
  rw [hd]
  simp only [Nat.sqrt_eq']
  exact ⟨q, by simpa [mul_comm] using hdegree⟩

private theorem brauer_finrank_relative
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (z : BrauerGroup.{u, u} k) (hz : z ∈ relativeBrauerGroup k L) :
    z ^ Module.finrank k L = 1 := by
  induction z using Quotient.inductionOn with
  | _ A =>
      obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hAD⟩ :=
        division_brauer_representative k A
      letI : DivisionRing D := hDdiv
      letI : Algebra k D := hDalg
      letI : Algebra.IsCentral k D := hDcentral
      letI : Module.Finite k D := hDfinite
      have hsplitA : ISBy k L A :=
        (brauer_relative_split k L A).1 hz
      have hAA : IsBrauerEquivalent (centralSimpleCSA k A) A := by
        refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
        exact ⟨AlgEquiv.refl⟩
      have hAD' : IsBrauerEquivalent
          (centralSimpleCSA k A) (centralDivisionCSA k D) :=
        hAA.trans hAD
      have hsplitD : ISBy k L D :=
        (split_brauer_equivalent k L A D hAD').1 hsplitA
      have hdiv : Nat.sqrt (Module.finrank k D) ∣ Module.finrank k L :=
        division_dvd_split k D L hsplitD
      obtain ⟨q, hq⟩ := hdiv
      have hclass : brauerClass k A = brauerClass k (centralDivisionCSA k D) :=
        (brauer_class k A (centralDivisionCSA k D)).2 hAD
      change (brauerClass k A) ^ Module.finrank k L = 1
      rw [hclass, hq, pow_mul,
        brauer_division_degree, one_pow]

/-- **Corollary IV.3.17, second assertion (literal source statement).**
For every finite extension `L/k`, with no separability or normality
hypothesis, the relative Brauer group is killed by `[L : k]`. -/
theorem relative_brauer_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (x : relativeBrauerGroup k L) :
    x ^ Module.finrank k L = 1 := by
  apply Subtype.ext
  exact brauer_finrank_relative
    k L x.1 x.2

end

end Submission.CField.CProduca
