import Towers.NumberTheory.Locals.UnramifiedExtensions
import Towers.NumberTheory.Locals.LocalDegreeFormula
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedTower

/-!
# Ramification of the canonical unramified levels

This file records the two bridges needed to read ramification from the
Hensel-lifted integral model: unramifiedness at the maximal ideal forces
ramification index one, which in turn makes normalized adic order restrict
unchanged to the base field.
-/

namespace Towers.CField.LBrauer

noncomputable section

open IsDedekindDomain

universe u

/-- Ramification index one is exactly the condition under which normalized
adic order on an extension restricts to the normalized adic order downstairs. -/
theorem normalized_ramification_idx
    {A B K L : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.IsTorsionFree A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (p : HeightOneSpectrum A) (P : HeightOneSpectrum B)
    [P.asIdeal.LiesOver p.asIdeal]
    (h : p.asIdeal.ramificationIdx P.asIdeal = 1) (x : Kˣ) :
    Towers.NumberTheory.Milne.normalizedAdicOrder P
        (Units.map (algebraMap K L).toMonoidHom x) =
      Towers.NumberTheory.Milne.normalizedAdicOrder p x := by
  simpa [h] using
    Towers.NumberTheory.Milne.normalized_adic_ramification
      p P x

/-- In a finite local extension of DVRs, unramifiedness at the maximal ideal
forces the maximal-ideal ramification index to be one.  The local-hom
assumption constructs the required `LiesOver` instance. -/
theorem ramification_idx_unramified
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B)] :
    (IsLocalRing.maximalIdeal A).ramificationIdx
        (IsLocalRing.maximalIdeal B) = 1 := by
  letI : (IsLocalRing.maximalIdeal B).LiesOver
      (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  have h := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    (R := A) (S := B) (IsDiscreteValuationRing.not_a_field B)
  rw [← Ideal.LiesOver.over (p := IsLocalRing.maximalIdeal A)
    (P := IsLocalRing.maximalIdeal B)] at h
  exact h

end

end Towers.CField.LBrauer
