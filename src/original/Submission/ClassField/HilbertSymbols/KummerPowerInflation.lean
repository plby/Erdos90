import Submission.ClassField.LocalClass.Inflation
import Submission.ClassField.LocalReciprocity.TateZeroQuotient
import Submission.ClassField.HilbertSymbols.NormCriterion
import Submission.ClassField.HilbertSymbols.KummerNormCriterion
import Submission.ClassField.KummerTheory.PowerClasses

/-!
# Milne, Class Field Theory, Section III.4, Step 2

This file packages the unconditional finite-level content of Step 2.  The
power-class quotient has exactly the expected vanishing criterion, and
inflation on multiplicative `H²` is injective, including for irreducible
Kummer extensions.

The source additionally identifies the inflated Step 1 cyclic class with the
absolute cup product `chi ∪ δ b`.  The repository has cup-product
naturality for categorical quotient-group inflation, but it does not yet
identify the crossed-product inflation used here with that categorical map,
nor identify the generator-dependent periodicity class from Step 1 with the
explicit `δ chi ∪ b` cocycle.  We isolate the unconditional ingredients
without adding either missing comparison as a hypothesis.
-/

namespace Submission.CField.HSymbol

open Polynomial
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.LClass
open Submission.CField.CProduca
open Submission.CField.KTheory

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

/-- The elementary Kummer identification at degree zero: the class of `b`
in `Kˣ / Kˣⁿ` is trivial exactly when `b` is an `n`th power. -/
theorem power_class_nth
    {K : Type*} [Field K] (n : ℕ) (b : Kˣ) :
    powerClass n b = 1 ↔ ∃ x : Kˣ, x ^ n = b := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff b).mp h
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    apply (QuotientGroup.eq_one_iff b).mpr
    exact ⟨x, hx⟩

section FiniteInflation

variable (K E L : Type)
  [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K E] [IsGalois K E]
  [FiniteDimensional K L] [IsGalois K L]

/-- Inflation on finite Galois multiplicative `H²` is injective.  Under
the crossed-product classification it is simply inclusion of relative
Brauer groups. -/
theorem h_inflation_injective :
    Function.Injective (galoisHInflation K E L) := by
  intro x y hxy
  apply (CProduc.hRelativeBrauer K E).injective
  apply Subtype.ext
  have h := congrArg
    (CProduc.hRelativeBrauer K L) hxy
  rw [h_brauer_inflation,
    h_brauer_inflation] at h
  have hv := congrArg
    (fun z : relativeBrauerGroup K L ↦ (z : BrauerGroup K)) h
  simpa only [tower_inclusion_coe] using hv

/-- Consequently a finite-level inflated `H²` class vanishes exactly when
the original class vanishes.  This is the injectivity step in Milne's boxed
norm criterion. -/
theorem galois_h_inflation
    (x : MHTwo Gal(E/K) Eˣ) :
    galoisHInflation K E L x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply h_inflation_injective K E L
    simpa using hx
  · rintro rfl
    exact map_one _

end FiniteInflation

section KummerInflation

variable {K E L : Type} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K L]
variable {n : ℕ} [NeZero n] {a ζ : K}
variable [IsSplittingField K E (X ^ n - C a)]

/-- **Step 2 for an irreducible Kummer field, finite inflation part.**  In
every finite Galois overfield, inflation out of the Kummer splitting field
detects the trivial `H²` class. -/
theorem inflated_kummer_h
    (hirr : Irreducible (X ^ n - C a))
    (hζ : IsPrimitiveRoot ζ n)
    (x :
      letI : FiniteDimensional K E :=
        Polynomial.IsSplittingField.finiteDimensional E (X ^ n - C a)
      letI : IsGalois K E :=
        (kummer_splitting_structure (L := E) hirr hζ).1
      MHTwo Gal(E/K) Eˣ) :
    letI : FiniteDimensional K E :=
      Polynomial.IsSplittingField.finiteDimensional E (X ^ n - C a)
    letI : IsGalois K E :=
      (kummer_splitting_structure (L := E) hirr hζ).1
    galoisHInflation K E L x = 1 ↔ x = 1 := by
  letI : FiniteDimensional K E :=
    Polynomial.IsSplittingField.finiteDimensional E (X ^ n - C a)
  letI : IsGalois K E :=
    (kummer_splitting_structure (L := E) hirr hζ).1
  exact galois_h_inflation K E L x

end KummerInflation

end

end Submission.CField.HSymbol
