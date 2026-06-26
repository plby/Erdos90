import Submission.ClassField.Reciprocity.RationalPrimeUnit

/-!
# Chapter V, Section 5, Lemma 5.9: topological conclusion

This file packages the algebraic decomposition proved in
`Lemma59SourceStatement` as a multiplicative equivalence and then verifies
that it is the asserted topological-group equivalence.  The rational factor
has the discrete topology, exactly as in the source.
-/

namespace Submission.CField.Recip

open Filter IsDedekindDomain NumberField Topology
open Submission.CField.Ideles
open scoped RestrictedProduct

noncomputable section

/-- The literal multiplicative equivalence in Lemma V.5.9. -/
noncomputable def rationalIdeleDecomposition :
    RationalDecompositionFactors ≃* IdeleGroup ℤ ℚ :=
  MulEquiv.ofBijective rationalDecompositionHom
    ⟨rational_decomposition_injective,
      rational_decomposition_surjective⟩

@[simp]
theorem rational_idele_decomposition
    (x : RationalDecompositionFactors) :
    rationalIdeleDecomposition x = rationalDecompositionHom x :=
  rfl

/-- For the unique infinite place of `ℚ`, the algebraic equivalence used in
the decomposition is also a homeomorphism. -/
noncomputable def rationalUnitsContinuous :
    (InfiniteAdeleRing ℚ)ˣ ≃ₜ* Rat.infinitePlace.Completionˣ where
  __ := rationalInfiniteEquiv
  continuous_toFun := by
    change Continuous fun x : (InfiniteAdeleRing ℚ)ˣ =>
      ContinuousMulEquiv.piUnits x (default : InfinitePlace ℚ)
    exact (continuous_apply _).comp ContinuousMulEquiv.piUnits.continuous
  continuous_invFun := by
    apply rationalInfiniteEquiv.toEquiv.continuous_symm_iff.mpr
    change IsOpenMap fun x : (InfiniteAdeleRing ℚ)ˣ =>
      ContinuousMulEquiv.piUnits x (default : InfinitePlace ℚ)
    exact (Homeomorph.piUnique
      (fun v : InfinitePlace ℚ => v.Completionˣ)).isOpenMap.comp
        ContinuousMulEquiv.piUnits.isOpenMap

/-- The canonical identification of the unique real completion with `ℝ` is
an isometry and hence a multiplicative homeomorphism. -/
private noncomputable def rationalInfiniteContinuous :
    Rat.infinitePlace.Completion ≃ₜ* ℝ where
  __ := rationalInfiniteCompletion.toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm.continuous

private theorem open_infinite_units :
    IsOpen (RationalPositiveUnits :
      Set Rat.infinitePlace.Completionˣ) := by
  change IsOpen ((Units.map rationalInfiniteCompletion.toMonoidHom) ⁻¹'
    (Units.posSubgroup ℝ : Set ℝˣ))
  apply IsOpen.preimage
  · exact Units.mapContinuousMulEquiv
      rationalInfiniteContinuous |>.continuous
  · rw [show (Units.posSubgroup ℝ : Set ℝˣ) =
        {x : ℝˣ | 0 < (x : ℝ)} by
      ext x
      change (x ∈ Units.posSubgroup ℝ) ↔ 0 < (x : ℝ)
      exact Units.mem_posSubgroup (R := ℝ) x]
    exact isOpen_lt continuous_const Units.continuous_val

private theorem continuous_remaining_factors :
    Continuous (fun x :
      RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ =>
        (show IdeleGroup ℤ ℚ from
          (rationalInfiniteEquiv.symm x.1.1, x.2.1))) := by
  apply Continuous.prodMk
  · exact rationalUnitsContinuous.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)
  · exact continuous_subtype_val.comp continuous_snd

private theorem open_remaining_factors :
    IsOpenMap (fun x :
      RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ =>
        (show IdeleGroup ℤ ℚ from
          (rationalInfiniteEquiv.symm x.1.1, x.2.1))) := by
  have hinf : IsOpenMap (fun x : RationalPositiveUnits =>
      rationalInfiniteEquiv.symm x.1) := by
    exact rationalUnitsContinuous.symm.isOpenMap.comp
      open_infinite_units.isOpenMap_subtype_val
  have hfinset : IsOpen (everywhereUnitIdeles ℤ ℚ :
      Set (FiniteIdeles ℤ ℚ)) := by
    change IsOpen {a : FiniteIdeles ℤ ℚ |
      ∀ v, a.1 v ∈ IdeleUnitSubgroup ℤ ℚ v}
    apply RestrictedProduct.isOpen_forall_mem
    intro v
    apply Submonoid.isOpen_units
    change IsOpen (v.adicCompletionIntegers ℚ :
      Set (v.adicCompletion ℚ))
    exact Valued.isOpen_valuationSubring _
  have hfin : IsOpenMap (fun x : everywhereUnitIdeles ℤ ℚ => x.1) :=
    hfinset.isOpenMap_subtype_val
  exact hinf.prodMap hfin

private theorem continuous_decomposition_hom :
    Continuous rationalDecompositionHom := by
  rw [continuous_prod_of_discrete_left]
  intro q
  change Continuous fun x :
      RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ =>
    principalIdele ℤ ℚ (discreteRationalUnits q) *
      (show IdeleGroup ℤ ℚ from
        (rationalInfiniteEquiv.symm x.1.1, x.2.1))
  exact continuous_const.mul continuous_remaining_factors

private theorem open_decomposition_hom :
    IsOpenMap rationalDecompositionHom := by
  rw [isOpenMap_prod_of_discrete_left]
  intro q
  change IsOpenMap fun x :
      RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ =>
    principalIdele ℤ ℚ (discreteRationalUnits q) *
      (show IdeleGroup ℤ ℚ from
        (rationalInfiniteEquiv.symm x.1.1, x.2.1))
  exact (isOpenMap_mul_left
    (principalIdele ℤ ℚ (discreteRationalUnits q))).comp
      open_remaining_factors

/-- **Lemma V.5.9.** Multiplication induces the asserted topological-group
equivalence
`ℚˣ × (ℝ_{>0} × ∏ₚ ℤₚˣ) ≃ ℐ_ℚ`, with `ℚˣ` discrete. -/
noncomputable def rationalDecompositionContinuous :
    RationalDecompositionFactors ≃ₜ* IdeleGroup ℤ ℚ where
  __ := rationalIdeleDecomposition
  continuous_toFun := continuous_decomposition_hom
  continuous_invFun :=
    rationalIdeleDecomposition.toEquiv.continuous_symm_iff.mpr
      open_decomposition_hom

@[simp]
theorem rational_decomposition_continuous
    (x : RationalDecompositionFactors) :
    rationalDecompositionContinuous x =
      rationalDecompositionHom x :=
  rfl

end

end Submission.CField.Recip
