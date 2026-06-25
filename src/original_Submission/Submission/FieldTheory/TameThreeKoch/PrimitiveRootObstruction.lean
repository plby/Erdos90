import Submission.FieldTheory.TameThreeKoch.RootNormData


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

universe u v w

open NumberField
open Submission.CField.Ideles
open Submission.CField.LBrauer

attribute [local instance]
  part2FiniteGaloisIntermediateFieldFiniteDimensional
  part2FiniteGaloisIntermediateFieldIsGalois
  part2AlgebraicClosureAlgebraic
  part2AlgebraicClosureNormal
  algebraicClosureIsGalois

set_option synthInstance.maxHeartbeats 1000000 in
-- The tame obstruction theorem synthesizes the full local action and cohomology setup.
set_option maxHeartbeats 40000000 in
-- Isolating it gives the following Brauer transport a fresh heartbeat budget.
theorem pullback_obstruction_primitive
    {Q : Type v} {G : Type v} [Group Q] [Finite Q]
    [Group G] [Finite G]
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (P : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    [Fact (FinitePlace.mk P).val.IsNontrivial]
    [IsUltrametricDist (FinitePlace.mk P).val.Completion]
    (w : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := L) (FinitePlace.mk P).val)
    [Finite
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [Nonempty
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    [MulAction.IsPretransitive Gal(L/K)
      (Submission.CField.ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk P).val)]
    (I : Subgroup (placeCanonicalGal P w))
    [I.Normal]
    (n : ℕ) [NeZero n]
    (data : TamePrimitiveData
      q galoisEquiv kernelToUnits P w I n) :
    let v := (FinitePlace.mk P).val
    let f := placeCompletionGroup P w galoisEquiv
    letI : Algebra v.Completion w.1.Completion :=
      (Submission.NumberTheory.Milne.completionLies
        v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Submission.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      Submission.NumberTheory.Milne.placeCompletionGalois v w
    let p := extensionPullbackProjection q f
    let hp : Function.Surjective p :=
      central_pullback_projection q hq f
    let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
      extension_pullback_projection q f hcentral
    let e := centralExtensionPullback q f
    let phiLocal := placeCompletionUnits P w kernelToUnits
    let phiPull := phiLocal.comp e.toMonoidHom
    let hfixedPull := fun sigma z ↦
      completion_units_fixed v
        (fun x y ↦ (FinitePlace.mk P).add_le x y)
        w kernelToUnits hfixed sigma (e z)
    letI : CommGroup p.ker := centralExtensionComm p hpc
    letI : MulDistribMulAction (placeCanonicalGal P w) p.ker :=
      trivialDistribAction (placeCanonicalGal P w) p.ker
    Submission.CField.CProduca.MHTwo.mapCoefficientsHom
        phiPull (fun sigma z ↦ (hfixedPull sigma z).symm)
        (extensionObstructionClass p hp hpc) = 1 := by
  rcases data with
    ⟨hphi, eI, x, hx, horderX, y, r, hconj, zeta, hzeta, hzetaI,
      hzetaY, degree, hdegree, horder, hgen, ord, hord, hnorm⟩
  let v := (FinitePlace.mk P).val
  let f := placeCompletionGroup P w galoisEquiv
  letI : Algebra v.Completion w.1.Completion :=
    (Submission.NumberTheory.Milne.completionLies
      v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionGalois v w
  letI : Finite (placeCanonicalGal P w) := by
    infer_instance
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center
      (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  let phiLocal :=
    placeCompletionUnits P w kernelToUnits
  let phiPull : p.ker →* w.1.Completionˣ :=
    phiLocal.comp e.toMonoidHom
  have hvna : IsNonarchimedean v :=
    fun a b ↦ (FinitePlace.mk P).add_le a b
  let hfixedPull :
      ∀ sigma : placeCanonicalGal P w,
        ∀ z : p.ker, sigma • phiPull z = phiPull z :=
    fun sigma z ↦
      completion_units_fixed
        v hvna w kernelToUnits hfixed sigma (e z)
  letI : CommGroup p.ker :=
    centralExtensionComm p hpc
  letI : MulDistribMulAction
      (placeCanonicalGal P w) p.ker :=
    trivialDistribAction
      (placeCanonicalGal P w) p.ker
  have hphi' : Function.Injective phiPull := by
    exact hphi
  have H0 :=
    mapped_obstruction_primitive
      (q := p)
      (hq := hp)
      (hcentral := hpc)
      (phi := phiPull)
      (hphi := hphi')
      (hfixed := hfixedPull)
      (I := I)
      (n := n)
  have H1 :=
    H0 eI x hx horderX y r hconj
  have H2 :=
    H1 zeta hzeta hzetaI hzetaY
  have H3 :=
    H2 degree hdegree horder hgen
  exact H3 ord hord hnorm

end TBluepr
end Submission
