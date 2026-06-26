import Submission.ClassField.HasseNorm.ClassH1
import Submission.ClassField.HasseNorm.IdeleDecomposition

/-!
# The resized idèle-class short exact sequence

This file transports the literal sequence `0 → Lˣ → I_L → C_L → 0`
from integral representations to the common universe used by the Hasse norm
cohomology argument.  Only the coefficient ring changes from `ℤ` to
`ULift ℤ`; the carriers, Galois actions, and maps are unchanged.
-/

namespace Submission.CField.HNorm

open CategoryTheory CategoryTheory.Limits Representation
open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.CBrauer

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private noncomputable abbrev concreteIdeleAction :
    IAData (K := K) (L := L) :=
  concreteActionData

/-- The resized representation on global units used as the first term of
the idèle-class sequence. -/
noncomputable def resizedRepresentation (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation (Rep.ofAlgebraAutOnUnits K L)

/-- The resized representation on the literal idèle-class cokernel. -/
noncomputable def resizedIdeleRepresentation (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
  Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation
    (Submission.CField.NIndex.classCokernelRepresentation
      (K := K) (L := L))

/-- The literal idèle-class short complex after resizing the coefficient
ring. -/
noncomputable def resizedShortComplex (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ShortComplex (Rep (ULift.{u} ℤ) Gal(L/K)) := by
  let D := concreteIdeleAction (K := K) (L := L)
  exact ShortComplex.mk
    (uliftIntegralHom D.principalIdeleHom)
    (uliftIntegralHom (cokernel.π D.principalIdeleHom)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change (cokernel.π D.principalIdeleHom) (D.principalIdeleHom x) = 0
      exact congrArg (fun f => f x) (cokernel.condition D.principalIdeleHom))

/-- Resizing preserves exactness of the idèle-class sequence because it
does not change any underlying additive map. -/
theorem resized_short_exact (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (resizedShortComplex K L).ShortExact := by
  letI intRepModule (A : Rep.{u, 0, u} ℤ Gal(L/K)) : Module ℤ A := A.hV2
  letI uliftRepModule
      (A : Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K)) :
      Module (ULift.{u} ℤ) A := A.hV2
  let D := concreteIdeleAction (K := K) (L := L)
  let f := D.principalIdeleHom
  let X : ShortComplex (Rep.{u, 0, u} ℤ Gal(L/K)) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hX : X.ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.exact_cokernel f
    · apply (Rep.mono_iff_injective f).2
      intro x y hxy
      apply Additive.toMul.injective
      apply principalIdele_injective (NumberField.RingOfIntegers L) L
      exact congrArg Additive.toMul hxy
    · infer_instance
  let F : (Rep.{u, 0, u} ℤ Gal(L/K)) ⥤ ModuleCat.{u} ℤ :=
    forget₂ (Rep.{u, 0, u} ℤ Gal(L/K)) (ModuleCat.{u} ℤ)
  have hXF : (X.map F).ShortExact := hX.map_of_exact F
  apply ShortComplex.ShortExact.mk'
  · exact (forget₂ (Rep.{u, u, u} (ULift.{u} ℤ) Gal(L/K))
      (ModuleCat.{u} (ULift.{u} ℤ))).reflects_exact_of_faithful _ <|
      (ShortComplex.moduleCat_exact_iff _).2 (fun x hx => by
        have hx' : X.g x = 0 := hx
        obtain ⟨y, hy⟩ :=
          (ShortComplex.moduleCat_exact_iff (X.map F)).1
            hXF.exact x hx'
        exact ⟨y, hy⟩)
  · rw [Rep.mono_iff_injective]
    exact (Rep.mono_iff_injective X.f).1 hX.mono_f
  · rw [Rep.epi_iff_surjective]
    exact (Rep.epi_iff_surjective X.g).1 hX.epi_g

/-- The resized global-units representation is the direct multiplicative
presentation used by the norm-quotient comparison. -/
noncomputable def resizedIsoHasse (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    resizedRepresentation K L ≅
      hasseGlobalRepresentation K L := by
  apply Rep.mkIso
  refine
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ) (Additive Lˣ)
      isIntertwining' := ?_ }
  intro sigma
  rfl

/-- The third term agrees with the resized idèle-class representation used
in Theorem VII.5.1. -/
noncomputable def resizedIdeleIso (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    resizedIdeleRepresentation K L ≅
      Submission.CField.CIdeles.ideleCohomologyRepresentation
        K L :=
  intUIso K L

end

end Submission.CField.HNorm
