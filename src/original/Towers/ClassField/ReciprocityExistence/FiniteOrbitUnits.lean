import Towers.ClassField.ReciprocityExistence.FiniteOrbitDense

/-!
# Finite-orbit naturality on units

Transporting the equality of completion ring maps through units identifies
the literal finite-orbit coordinate with the canonical completion embedding.
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option maxHeartbeats 10000000 in
-- The ring-map equality is transported once through units and the target equivalence.
set_option maxRecDepth 100000 in
/-- The finite-orbit coordinate map is the canonical embedding of the base
local unit into the chosen upper completion. -/
theorem chosen_monoid_canonical
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (y : (P.adicCompletion K)ˣ) :
    chosenMonoidHom
        (K := K) (L := L) P w y =
      Units.map
        (completionLies
          (FinitePlace.mk P).val w.1 w.2).toMonoidHom
        (Units.map
          (placeCompletionAdic
            P).symm.toRingHom.toMonoidHom y) := by
  let Qw := placeUpperFactor
    (K := K) (L := L) P w
  let Q := upperPrime (K := K) (L := L) P Qw
  let hQ : Q.under (NumberField.RingOfIntegers K) = P :=
    upperPrime_under (K := K) (L := L) P Qw
  let eK := placeCompletionAdic P
  let eL := completionPlaceAdic (K := K) (L := L) P w
  let v := (FinitePlace.mk P).val
  change (placeUnitsAdic
      (K := K) (L := L) P w).symm
        (NIndex.extensionMonoidHom
          (K := K) (L := L) Q
          (Units.map
            ((RingEquiv.cast
              (R := fun R : HeightOneSpectrum
                (NumberField.RingOfIntegers K) => R.adicCompletion K)
              hQ.symm).toRingHom.toMonoidHom) y)) = _
  apply Units.ext
  change eL.symm
      ((NIndex.extensionMonoidHom
        (K := K) (L := L) Q
        (Units.map
          ((RingEquiv.cast
            (R := fun R : HeightOneSpectrum
              (NumberField.RingOfIntegers K) => R.adicCompletion K)
            hQ.symm).toRingHom.toMonoidHom) y) :
          (Q.adicCompletion L)ˣ) : Q.adicCompletion L) =
    completionLies v w.1 w.2 (eK.symm (y : P.adicCompletion K))
  rw [NIndex.extension_monoid_val]
  apply eL.injective
  rw [eL.apply_symm_apply]
  have hmap := DFunLike.congr_fun
    (base_chosen_adic
      (K := K) (L := L) P w)
    (eK.symm (y : P.adicCompletion K))
  unfold baseChosenAdic
    chosenAdicDirect at hmap
  dsimp only [RingHom.comp_apply] at hmap
  have heK : (placeCompletionAdic P)
      (eK.symm (y : P.adicCompletion K)) = y :=
    eK.apply_symm_apply _
  have heK' : (placeCompletionAdic P).toRingHom
      (eK.symm (y : P.adicCompletion K)) = y := heK
  rw [heK'] at hmap
  have hcast :
      ((Units.map
        ((RingEquiv.cast
          (R := fun R : HeightOneSpectrum
            (NumberField.RingOfIntegers K) => R.adicCompletion K)
          hQ.symm).toRingHom.toMonoidHom) y :
            ((Q.under (NumberField.RingOfIntegers K)).adicCompletion K)ˣ) :
        (Q.under (NumberField.RingOfIntegers K)).adicCompletion K) =
      RingEquiv.cast hQ.symm (y : P.adicCompletion K) := rfl
  rw [hcast]
  simpa only [Q, Qw, eL, v, eK] using hmap

end


end Towers.CField.RExist
