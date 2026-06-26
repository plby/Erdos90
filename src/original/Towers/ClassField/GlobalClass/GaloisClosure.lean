import Mathlib.FieldTheory.Galois.GaloisClosure
import Towers.ClassField.KummerNormIndex.NormExponent
import Towers.ClassField.GlobalClass.Corestriction
import Towers.ClassField.GlobalClass.Existential

/-!
# Passing norm limitation through a Galois closure

An algebra equivalence can be regarded as a degree-one extension.  Norm
transitivity and the extension--norm power formula then show directly that
it does not change the idèle-class norm subgroup.  This is the transport
needed when an arbitrary finite extension is embedded in its normal closure.
-/

namespace Towers.CField.GClass

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NIndex
open Towers.CField.KNIndex

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- The degree-one tower carries three overlapping algebra structures.
/-- Isomorphic finite extensions have the same idèle-class norm subgroup. -/
theorem canonical_range_alg
    {K E F : Type u} [Field K] [NumberField K]
    [Field E] [NumberField E] [Field F] [NumberField F]
    [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] [FiniteDimensional K F]
    (e : E ≃ₐ[K] F) :
    (canonicalIdeleNorm (K := K) (L := E)).range =
      (canonicalIdeleNorm (K := K) (L := F)).range := by
  letI : Algebra E F := e.toRingEquiv.toRingHom.toAlgebra
  let eEF : E ≃ₐ[E] F :=
    { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  letI : FiniteDimensional E F :=
    Module.Finite.equiv eEF.toLinearEquiv
  letI : IsGalois E F := IsGalois.of_algEquiv eEF
  letI : IsScalarTower K E F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro x
    exact (e.commutes x).symm
  have hfinrank : Module.finrank E F = 1 := by
    simpa using eEF.toLinearEquiv.finrank_eq.symm
  let extension := canonicalExtensionData (K := E) (L := F)
  have hnormSurjective : Function.Surjective
      (canonicalIdeleNorm (K := E) (L := F)) := by
    intro c
    refine ⟨extension.classMap c, ?_⟩
    have hpower := DFunLike.congr_fun
      (canonical_comp_extension E F) c
    simpa [hfinrank] using hpower
  have htrans : canonicalIdeleNorm (K := K) (L := F) =
      (canonicalIdeleNorm (K := K) (L := E)).comp
        (canonicalIdeleNorm (K := E) (L := F)) :=
    canonical_idele_trans
      (norm_trans_arbitrary (K := K) (E := E) (L := F))
  rw [htrans, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr hnormSurjective]
  exact MonoidHom.range_eq_map _

set_option maxHeartbeats 4000000 in
-- The normal closure and its two transported intermediate fields create a
-- large dependent field-instance telescope.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The fixed-field norm-limitation theorem yields exactly the existential
form required by Lemma VII.9.4.  The passage to and from the normal closure
uses only the degree-one transport theorem above. -/
theorem existential_limitation_corestriction
    (hcore : CorestrictionCokernelBridge.{u})
    (hindex : GaloisIndexFormula.{u}) :
    ExistentialNormLimitation.{u} := by
  intro K E _ _ _ _ _ _
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : IsAlgClosure K (AlgebraicClosure E) := inferInstance
  letI : IsGalois K (AlgebraicClosure E) :=
    IsAlgClosure.isGalois K (AlgebraicClosure E)
  let L := IntermediateField.normalClosure K E (AlgebraicClosure E)
  letI : IsGalois K L :=
    IsGalois.normalClosure K E (AlgebraicClosure E)
  letI : FiniteDimensional K L :=
    normalClosure.is_finiteDimensional K E (AlgebraicClosure E)
  letI : NumberField L := NumberField.of_module_finite K L
  let j : E →ₐ[K] L := IsScalarTower.toAlgHom K E L
  let E' : IntermediateField K L := j.fieldRange
  let eE : E ≃ₐ[K] E' := by
    simpa [E', AlgHom.fieldRange_toSubalgebra j] using
      (AlgEquiv.ofInjectiveField j)
  letI : NumberField E' := NumberField.of_module_finite K E'
  let H : Subgroup Gal(L/K) := E'.fixingSubgroup
  let A : IntermediateField K L :=
    maximalSubfieldInside K L H
  have hfixed : IntermediateField.fixedField H = E' := by
    exact IsGalois.fixedField_fixingSubgroup E'
  have hEA' :
      (canonicalIdeleNorm (K := K) (L := E)).range =
        (canonicalIdeleNorm (K := K) (L := E')).range :=
    canonical_range_alg eE
  have hE'A :
      (canonicalIdeleNorm (K := K) (L := E')).range =
        (canonicalIdeleNorm (K := K) (L := A)).range := by
    have h := norm_maximal_abelian
      hcore hindex K L H
    rw [hfixed] at h
    exact h
  let Aext : FAExt K :=
    { carrier := A
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      isAbelian := inferInstance }
  let M : FASubext K :=
    Aext.finiteAbelianSubextension
  letI : NumberField M.1 := NumberField.of_module_finite K M.1
  have hAM :
      (canonicalIdeleNorm (K := K) (L := A)).range =
        (canonicalIdeleNorm (K := K) (L := M.1)).range :=
    canonical_range_alg
      Aext.algSeparableClosure
  refine ⟨M, ?_⟩
  rw [idele_class_range]
  exact hAM.symm.trans (hE'A.symm.trans hEA'.symm)

/-- Source-order form: Theorem VII.5.1, the invariant theorem VIII.4.7,
Tate's degree-minus-two theorem, and the corestriction square imply the
existential norm-limitation statement used in Chapter VII. -/
theorem existential_limitation_results
    (h51 : Towers.CField.CIdeles.IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u})
    (hcore : CorestrictionCokernelBridge.{u}) :
    ExistentialNormLimitation.{u} := by
  apply existential_limitation_corestriction hcore
  apply galois_formula_isomorphism
  exact isomorphism_previous_results h51 h47 hTate

end

end Towers.CField.GClass
