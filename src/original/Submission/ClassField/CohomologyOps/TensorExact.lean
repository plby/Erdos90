import Submission.ClassField.CohomologyOps.DimensionShiftModule
import Submission.ClassField.CohomologyOps.DimensionShiftingIso
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

namespace Submission.CField.COps.CPBuild

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct

noncomputable section

variable {G : Type} [Group G]

/-- Tensoring a short exact sequence on the left stays short exact when its
first map splits after forgetting the group action. -/
theorem tensor_underlying_retraction
    (M : Rep ℤ G) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (r : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) X.X₂ X.X₁ _ _
      X.X₂.hV2 X.X₁.hV2)
    (hr : Function.LeftInverse r X.f) :
    (X.map ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact := by
  letI repModule (A : Rep ℤ G) : Module ℤ A := A.hV2
  let F : Functor (Rep ℤ G) (ModuleCat ℤ) :=
    forget₂ (Rep ℤ G) (ModuleCat ℤ)
  let UX := X.map F
  have hUX : UX.ShortExact := hX.map_of_exact F
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact UX).mp
        hUX.exact
  have hsurj : Function.Surjective X.g.hom.toLinearMap := by
    exact (ModuleCat.epi_iff_surjective _).mp hUX.epi_g
  let T := X.map ((tensoringLeft (Rep ℤ G)).obj M)
  refine
    { exact := F.reflects_exact_of_faithful T ?_
      mono_f := (Rep.mono_iff_injective _).2 ?_
      epi_g := (Rep.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff (T.map F)).2
    intro x hx
    change LinearMap.lTensor M X.g.hom.toLinearMap x = 0 at hx
    obtain ⟨y, hy⟩ := (lTensor_exact M hexact hsurj x).mp hx
    refine ⟨y, ?_⟩
    change LinearMap.lTensor M X.f.hom.toLinearMap y = x
    exact hy
  · intro x y hxy
    change LinearMap.lTensor M X.f.hom.toLinearMap x =
      LinearMap.lTensor M X.f.hom.toLinearMap y at hxy
    have hcomp : r.comp X.f.hom.toLinearMap = LinearMap.id :=
      LinearMap.ext fun z ↦ hr z
    apply_fun LinearMap.lTensor M r at hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp,
      LinearMap.lTensor_id_apply] using hxy
  · exact LinearMap.lTensor_surjective M hsurj

/-- Right-handed version of split tensor exactness. -/
theorem short_underlying_retraction
    (N : Rep ℤ G) {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    (r : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) X.X₂ X.X₁ _ _
      X.X₂.hV2 X.X₁.hV2)
    (hr : Function.LeftInverse r X.f) :
    (X.map ((tensoringRight (Rep ℤ G)).obj N)).ShortExact := by
  letI repModule (A : Rep ℤ G) : Module ℤ A := A.hV2
  let F : Functor (Rep ℤ G) (ModuleCat ℤ) :=
    forget₂ (Rep ℤ G) (ModuleCat ℤ)
  let UX := X.map F
  have hUX : UX.ShortExact := hX.map_of_exact F
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact UX).mp
        hUX.exact
  have hsurj : Function.Surjective X.g.hom.toLinearMap := by
    exact (ModuleCat.epi_iff_surjective _).mp hUX.epi_g
  let T := X.map ((tensoringRight (Rep ℤ G)).obj N)
  refine
    { exact := F.reflects_exact_of_faithful T ?_
      mono_f := (Rep.mono_iff_injective _).2 ?_
      epi_g := (Rep.epi_iff_surjective _).2 ?_ }
  · apply (ShortComplex.moduleCat_exact_iff (T.map F)).2
    intro x hx
    change LinearMap.rTensor N X.g.hom.toLinearMap x = 0 at hx
    obtain ⟨y, hy⟩ := (rTensor_exact N hexact hsurj x).mp hx
    refine ⟨y, ?_⟩
    change LinearMap.rTensor N X.f.hom.toLinearMap y = x
    exact hy
  · intro x y hxy
    change LinearMap.rTensor N X.f.hom.toLinearMap x =
      LinearMap.rTensor N X.f.hom.toLinearMap y at hxy
    have hcomp : r.comp X.f.hom.toLinearMap = LinearMap.id :=
      LinearMap.ext fun z ↦ hr z
    apply_fun LinearMap.rTensor N r at hxy
    simpa only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp,
      LinearMap.rTensor_id_apply] using hxy
  · exact LinearMap.rTensor_surjective N hsurj

/-- Evaluation at the identity retracts the first map of Milne's canonical
dimension-shifting sequence after forgetting the action. -/
theorem shift_retraction_inverse (A : Rep ℤ G) :
    Function.LeftInverse (dimensionShiftRetraction A)
      (dimensionShiftSequence A).f := by
  intro a
  change (dimensionShiftRetraction A).hom
      ((dimensionShiftEmbedding A).hom a) = a
  have h := congrArg (fun q => q a)
    (dimension_shift_retraction A)
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h

/-- Milne's canonical dimension-shifting row remains exact after tensoring
on the left by any coefficient module. -/
theorem tensor_shift_short
    (M A : Rep ℤ G) :
    ((dimensionShiftSequence A).map
      ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact :=
  tensor_underlying_retraction M
    (shift_sequence_short A)
    (dimensionShiftRetraction A).hom
    (shift_retraction_inverse A)

/-- Milne's canonical dimension-shifting row remains exact after tensoring
on the right by any coefficient module. -/
theorem shift_short_exact
    (A N : Rep ℤ G) :
    ((dimensionShiftSequence A).map
      ((tensoringRight (Rep ℤ G)).obj N)).ShortExact :=
  short_underlying_retraction N
    (shift_sequence_short A)
    (dimensionShiftRetraction A).hom
    (shift_retraction_inverse A)

end

end Submission.CField.COps.CPBuild
