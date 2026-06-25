import Mathlib.RingTheory.Norm.Transitivity
import Towers.ClassField.NormIndex.FactorExtensionCompatibility

/-!
# Transitivity of canonical finite-completion norms

This file packages the dependent completion-algebra calculation behind one
opaque theorem.  Consumers of the finite idèle norm should not need to unfold
the three transported algebra structures simultaneously.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The algebra norm for the canonical embedding between literal prime-adic
completion coordinates. -/
noncomputable def finiteCanonicalNorm
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : HeightOneSpectrum (OK L)) :
    (Q.adicCompletion L)ˣ →*
      ((Q.under (OK K)).adicCompletion K)ˣ := by
  letI : Algebra ((Q.under (OK K)).adicCompletion K)
      (Q.adicCompletion L) :=
    (coordinateExtensionHom (K := K) (L := L) Q).toAlgebra
  exact Units.map (Algebra.norm ((Q.under (OK K)).adicCompletion K))

private theorem units_norm_base
    {A₀ A B : Type*} [CommRing A₀] [CommRing A] [Ring B]
    [Algebra A₀ B] [Algebra A B]
    (e : A₀ ≃+* A)
    (he : RingHom.comp (algebraMap A B) e.toRingHom = algebraMap A₀ B)
    (z : Bˣ) :
    Units.map e.toRingHom.toMonoidHom
        (Units.map (Algebra.norm A₀) z) =
      Units.map (Algebra.norm A) z := by
  apply Units.ext
  change e (Algebra.norm A₀ (z : B)) = Algebra.norm A (z : B)
  rw [Algebra.norm_eq_of_equiv_equiv e (RingEquiv.refl B) he,
    RingEquiv.apply_symm_apply]
  rfl

private theorem units_norm_trans
    {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Free A B] [Module.Free B C] [Module.Free A C]
    (z : Cˣ) :
    Units.map (Algebra.norm A) z =
      Units.map (Algebra.norm A) (Units.map (Algebra.norm B) z) := by
  apply Units.ext
  exact (Algebra.norm_norm (R := A) (S := B) (A := C)).symm

private theorem units_trans_equiv
    {A₀ A B C : Type*} [CommRing A₀] [CommRing A] [CommRing B] [Ring C]
    [Algebra A₀ B] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [Module.Free A₀ B] [Module.Free A B] [Module.Free B C] [Module.Free A C]
    (e : A₀ ≃+* A)
    (he : RingHom.comp (algebraMap A B) e.toRingHom = algebraMap A₀ B)
    (z : Cˣ) :
    Units.map e.toRingHom.toMonoidHom
        (Units.map (Algebra.norm A₀) (Units.map (Algebra.norm B) z)) =
      Units.map (Algebra.norm A) z := by
  calc
    _ = Units.map (Algebra.norm A) (Units.map (Algebra.norm B) z) :=
      units_norm_base e he _
    _ = Units.map (Algebra.norm A) z := (units_norm_trans z).symm

set_option maxHeartbeats 5000000 in
-- Synthesizing and comparing all three dependent completion modules is deep.
set_option synthInstance.maxHeartbeats 300000 in
set_option maxRecDepth 100000 in
/-- Canonical finite-completion norms are transitive in a number-field tower. -/
theorem finite_canonical_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L]
    (R : HeightOneSpectrum (OK L)) (z : (R.adicCompletion L)ˣ) :
    Units.map ((RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
        (height_one_spectrum (K := K) (E := E) (L := L) R)
          ).toRingHom.toMonoidHom)
      (finiteCanonicalNorm (K := K) (L := E) (R.under (OK E))
        (finiteCanonicalNorm (K := E) (L := L) R z)) =
      finiteCanonicalNorm (K := K) (L := L) R z := by
  let Q := R.under (OK E)
  let P := R.under (OK K)
  let P₀ := Q.under (OK K)
  let hQP : P₀ = P := height_one_spectrum R
  let eP : P₀.adicCompletion K ≃+* P.adicCompletion K := RingEquiv.cast hQP
  let fKE := coordinateExtensionHom (K := K) (L := E) Q
  let fEL := coordinateExtensionHom (K := E) (L := L) R
  let fKL := coordinateExtensionHom (K := K) (L := L) R
  letI : Algebra (P₀.adicCompletion K) (Q.adicCompletion E) := fKE.toAlgebra
  letI : Algebra (P.adicCompletion K) (Q.adicCompletion E) :=
    (fKE.comp eP.symm.toRingHom).toAlgebra
  letI : Algebra (Q.adicCompletion E) (R.adicCompletion L) := fEL.toAlgebra
  letI : Algebra (P.adicCompletion K) (R.adicCompletion L) := fKL.toAlgebra
  letI : Module.Free (P₀.adicCompletion K) (Q.adicCompletion E) :=
    Module.Free.of_divisionRing (P₀.adicCompletion K) (Q.adicCompletion E)
  letI : Module.Free (P.adicCompletion K) (Q.adicCompletion E) :=
    Module.Free.of_divisionRing (P.adicCompletion K) (Q.adicCompletion E)
  letI : Module.Free (Q.adicCompletion E) (R.adicCompletion L) :=
    Module.Free.of_divisionRing (Q.adicCompletion E) (R.adicCompletion L)
  letI : Module.Free (P.adicCompletion K) (R.adicCompletion L) :=
    Module.Free.of_divisionRing (P.adicCompletion K) (R.adicCompletion L)
  letI : IsScalarTower (P.adicCompletion K) (Q.adicCompletion E)
      (R.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa only [P, P₀, Q, fKE, fEL, fKL, eP, RingHom.comp_assoc] using
      (extension_ring_trans (K := K) (E := E) (L := L) R).symm
  have he : RingHom.comp (algebraMap (P.adicCompletion K) (Q.adicCompletion E))
        eP.toRingHom =
      algebraMap (P₀.adicCompletion K) (Q.adicCompletion E) := by
    apply DFunLike.ext _ _
    intro a
    change fKE (RingEquiv.cast hQP.symm (RingEquiv.cast hQP a)) = fKE a
    rw [place_cast_symm]
  change Units.map eP.toRingHom.toMonoidHom
      (Units.map (Algebra.norm (P₀.adicCompletion K))
        (Units.map (Algebra.norm (Q.adicCompletion E)) z)) =
    Units.map (Algebra.norm (P.adicCompletion K)) z
  exact units_trans_equiv eP he z

end

end Towers.CField.NIndex
