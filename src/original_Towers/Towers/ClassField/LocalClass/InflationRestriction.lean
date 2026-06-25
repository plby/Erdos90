import Towers.ClassField.CohomologyOps.ShortComplexMap
import Towers.ClassField.LocalClass.Cardinality
import Towers.ClassField.LocalReciprocity.SubgroupHilbert90

/-!
# The inflation--restriction estimate in Lemma III.2.6

This file combines the full higher inflation--restriction sequence of
Proposition II.1.34 with the finite-cardinality estimate used in Milne's
induction.  In degree two its only vanishing hypothesis is `H¹(H,A) = 0`.
-/

namespace Towers.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Towers.CField.COps

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The exact sequence

`0 → H²(G/H,Aʰ) → H²(G,A) → H²(H,A)`

gives the cardinality inequality used in Lemma III.2.6.  This is a direct
specialization of Proposition II.1.34; no surjectivity of restriction is
assumed. -/
theorem cohomology_h_1
    (A : Rep k G) (H : Subgroup G) [H.Normal]
    (hH1 : IsZero
      (groupCohomology (Rep.res H.subtype A) 1))
    [Finite (groupCohomology (A.quotientToInvariants H) 2)]
    [Finite (groupCohomology A 2)]
    [Finite (groupCohomology (Rep.res H.subtype A) 2)] :
    Nat.card (groupCohomology A 2) ≤
      Nat.card (groupCohomology (A.quotientToInvariants H) 2) *
        Nat.card (groupCohomology (Rep.res H.subtype A) 2) := by
  let hvanish : ∀ j : ℕ, 0 < j → j < 2 →
      IsZero (groupCohomology (Rep.res H.subtype A) j) := by
    intro j hj hj2
    interval_cases j
    exact hH1
  let X := restrictionCochainsComplex A H 2 (by omega) hvanish
  have hmono : Mono X.f := by
    dsimp only [X]
    exact inflation_mono A H 2 (by omega) hvanish
  have hinjective : Function.Injective X.f :=
    (ModuleCat.mono_iff_injective X.f).mp hmono
  have hexact : Function.Exact X.f X.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp <| by
      dsimp only [X]
      exact restrictionCochainsShort A H 2 (by omega) hvanish
  have hinjective' : Function.Injective X.f.hom.toAddMonoidHom := hinjective
  have hexact' :
      Function.Exact X.f.hom.toAddMonoidHom X.g.hom.toAddMonoidHom := hexact
  letI : Finite X.X₁ := by
    dsimp only [X, restrictionCochainsComplex]
    infer_instance
  letI : Finite X.X₂ := by
    dsimp only [X, restrictionCochainsComplex]
    infer_instance
  letI : Finite X.X₃ := by
    dsimp only [X, restrictionCochainsComplex]
    infer_instance
  have hcard := nat_middle_exact
    (f := X.f.hom.toAddMonoidHom) (g := X.g.hom.toAddMonoidHom)
    hinjective' hexact'
  simpa only [X, restrictionCochainsComplex] using hcard

end

section GaloisUnits

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The degree-two inflation--restriction estimate for field units.  Hilbert
90 discharges the only lower-degree vanishing hypothesis. -/
theorem nat_units_normal
    (H : Subgroup Gal(L/K)) [H.Normal]
    [Finite (groupCohomology
      ((Rep.ofMulDistribMulAction Gal(L/K) Lˣ).quotientToInvariants H) 2)]
    [Finite (groupCohomology
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2)]
    [Finite (groupCohomology
      (Rep.res H.subtype
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2)] :
    Nat.card (groupCohomology
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) ≤
      Nat.card (groupCohomology
          ((Rep.ofMulDistribMulAction Gal(L/K) Lˣ).quotientToInvariants H) 2) *
        Nat.card (groupCohomology
          (Rep.res H.subtype
            (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 2) := by
  apply cohomology_h_1
  exact LRecip.hilbert_90_zero H

end GaloisUnits

end Towers.CField.LClass
