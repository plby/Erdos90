import Submission.ClassField.NormIndex.IdeleExtensionTower

/-! # Transitivity of finite-idèle extension in a tower -/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.CField.NIndex

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

private theorem place_cast_dependent
    {K : Type u} [Field K] [NumberField K]
    {P P' : HeightOneSpectrum (OK K)} (h : P = P')
    (x : (V : HeightOneSpectrum (OK K)) → V.adicCompletion K) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K) h
        (x P) = x P' := by
  subst P'
  rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Unfolding two nested restricted-product maps is elaboration-heavy.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/-- Transitivity of coordinatewise extension on finite idèles. -/
theorem extension_monoid_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    (ideleMonoidHom (K := E) (L := L)).comp
        (ideleMonoidHom (K := K) (L := E)) =
      ideleMonoidHom (K := K) (L := L) := by
  apply MonoidHom.ext
  intro x
  apply RestrictedProduct.ext
  intro R
  let Q := R.under (OK E)
  let P := R.under (OK K)
  let P₀ := Q.under (OK K)
  let hQP : P₀ = P := height_one_spectrum R
  simp only [MonoidHom.comp_apply, ideleMonoidHom]
  change extensionMonoidHom (K := E) (L := L) R
      (extensionMonoidHom (K := K) (L := E) Q
        (x.1 P₀)) =
    extensionMonoidHom (K := K) (L := L) R (x.1 P)
  apply Units.ext
  rw [extension_monoid_val,
    extension_monoid_val,
    extension_monoid_val]
  have htrans := extension_ring_trans
    (K := K) (E := E) (L := L) R
  have hcast : RingEquiv.cast hQP.symm
      ((x.1 P : P.adicCompletion K)) =
      (x.1 P₀ : P₀.adicCompletion K) :=
    place_cast_dependent hQP.symm
      (fun V ↦ (x.1 V : V.adicCompletion K))
  rw [← hcast]
  exact RingHom.congr_fun htrans (x.1 P : P.adicCompletion K)

end

end Submission.CField.KNIndex
