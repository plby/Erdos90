import Towers.ClassField.Reciprocity.LocalFactorsQ
import Towers.ClassField.Reciprocity.UniversePlaceArtin
import Towers.ClassField.LocalReciprocity.DualityConclusion
import Towers.ClassField.ReciprocityExistence.PadicFactors

/-!
# The canonical/exlicit comparison at the conductor prime

This file puts the canonically normalized finite local Artin map and the
explicit inverse-unit map of Example VII.8.2 in exactly the same source and
target types.  Thus the remaining ramified normalization theorem is a single
equality of homomorphisms `Q_p^x -> Gal(L/Q)`, rather than an informal
comparison between different completion models.

The degree-one conductors `1` and `2` are discharged here.  Positive
nontrivial prime-power conductors retain the genuine arithmetic content of
Example I.3.13(b).
-/

namespace Towers.CField.RExist

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo
open scoped IsMulCommutative

noncomputable section

/-- The height-one prime of `𝓞 ℚ` represented by the rational prime `p`. -/
noncomputable def rationalHeightOne
    (p : ℕ) [Fact p.Prime] :
    HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, Fact.out⟩

/-- The adic completion of `ℚ` at its canonical height-one prime above `p`
is the standard field `ℚ_[p]`. -/
noncomputable def rationalCompletionEquiv
    (p : ℕ) [Fact p.Prime] :
    (rationalHeightOne p).adicCompletion ℚ ≃A[ℚ] ℚ_[p] := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    (rationalHeightOne p)
  have hp : Rat.HeightOneSpectrum.primesEquiv
      (rationalHeightOne p) = (⟨p, Fact.out⟩ : Nat.Primes) :=
    Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _
  rw [hp] at e
  exact e

/-- Multiplicative-group form of `rationalCompletionEquiv`. -/
noncomputable def rationalUnitsEquiv
    (p : ℕ) [Fact p.Prime] :
    ((rationalHeightOne p).adicCompletion ℚ)ˣ ≃* ℚ_[p]ˣ :=
  Units.mapEquiv (rationalCompletionEquiv p).toMulEquiv

/-- The Proposition III.3.6 local Artin map at the rational prime `p`,
transported from the height-one-prime completion to the standard field
`Q_p`. -/
noncomputable def canonicalPadicArtin
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    ℚ_[p]ˣ →* Gal(L/ℚ) := by
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p ^ r} ℚ L
  letI : IsMulCommutative Gal(L/ℚ) :=
    IsCyclotomicExtension.isMulCommutative {p ^ r} ℚ L
  exact (adicArtinUniverse ℚ L
    (rationalHeightOne p) w).comp
      (rationalUnitsEquiv p).symm.toMonoidHom

/-- The exact remaining ramified normalization assertion used by Example
VII.8.2.  No auxiliary kernel, surjectivity, or completion-identification
hypotheses occur in its statement. -/
def CanonicalPadicNormalization : Prop :=
  ∀ (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val),
    canonicalPadicArtin p r L w =
      padicCyclotomicArtin p r L

/-- The genuinely nontrivial part of the normalization assertion: positive
prime-power conductors other than `2`. -/
def PositivePadicNormalization : Prop :=
  ∀ (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val),
    0 < r → p ^ r ≠ 2 →
      canonicalPadicArtin p r L w =
        padicCyclotomicArtin p r L

/-- Scalar form of the remaining arithmetic calculation.  It asks that the
canonical Proposition III.3.6 cup invariant of a `p`-adic unit equal every
rational character evaluated on the explicit inverse-unit action. -/
def PositiveCupFormula : Prop :=
  ∀ (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val),
    letI : IsGalois ℚ L :=
      IsCyclotomicExtension.isGalois {p ^ r} ℚ L
    letI : IsMulCommutative Gal(L/ℚ) :=
      IsCyclotomicExtension.isMulCommutative {p ^ r} ℚ L
    0 < r → p ^ r ≠ 2 →
      ∀ (a : ℚ_[p]ˣ) (chi : CharacterModule (Additive Gal(L/ℚ))),
        (characterFormulaUniverse ℚ L
          (rationalHeightOne p) w).cupInvariant
            ((rationalUnitsEquiv p).symm a) chi =
          chi (Additive.ofMul
            (padicCyclotomicArtin p r L a))

/-- At conductor `p^0 = 1`, the canonical and explicit maps agree because
the target Galois group is trivial. -/
theorem canonical_artin_explicit
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ 0} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne p)).val) :
    canonicalPadicArtin p 0 L w =
      padicCyclotomicArtin p 0 L :=
  padic_cyclotomic_artin p L _

/-- At the exceptional conductor `2`, the comparison is again automatic
because `Q(zeta_2) = Q`. -/
theorem artin_explicit_two
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {2} ℚ L]
    (w : CompletionPlacesAbove (L := L)
      (FinitePlace.mk (rationalHeightOne 2)).val) :
    canonicalPadicArtin 2 1 L w =
      padicCyclotomicArtin 2 1 L := by
  letI : IsCyclotomicExtension {2 ^ 1} ℚ L := by simpa
  exact local_cyclotomic_artin L _

/-- Rational characters separate the finite abelian cyclotomic Galois group,
so the scalar cup formula proves the positive-conductor map equality. -/
theorem normalization_cup_formula
    (hcup : PositiveCupFormula) :
    PositivePadicNormalization := by
  intro p r _ _ L _ _ _ w hr htwo
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois {p ^ r} ℚ L
  letI : IsMulCommutative Gal(L/ℚ) :=
    IsCyclotomicExtension.isMulCommutative {p ^ r} ℚ L
  apply MonoidHom.ext
  intro a
  apply Towers.CField.LRecip.forall_rational_character
    (G := Gal(L/ℚ))
  intro chi
  change chi (Additive.ofMul
      ((characterFormulaUniverse ℚ L
        (rationalHeightOne p) w).artin
          ((rationalUnitsEquiv p).symm a))) =
    chi (Additive.ofMul (padicCyclotomicArtin p r L a))
  rw [(characterFormulaUniverse ℚ L
    (rationalHeightOne p) w).formula]
  exact hcup p r L w hr htwo a chi

/-- Conversely, equality of the canonical and explicit local maps gives the
scalar cup formula by Proposition III.3.6.  Thus the cup formulation does not
hide a weaker arithmetic target: rational characters merely re-express the
same orientation-sensitive local reciprocity comparison. -/
theorem cup_formula_normalization
    (hnormalization : PositivePadicNormalization) :
    PositiveCupFormula := by
  intro p r _ _ L _ _ _ w
  letI : IsGalois ℚ L :=
    IsCyclotomicExtension.isGalois {p ^ r} ℚ L
  letI : IsMulCommutative Gal(L/ℚ) :=
    IsCyclotomicExtension.isMulCommutative {p ^ r} ℚ L
  intro hr htwo a chi
  let D := characterFormulaUniverse ℚ L
    (rationalHeightOne p) w
  calc
    D.cupInvariant
        ((rationalUnitsEquiv p).symm a) chi =
        chi (Additive.ofMul
          (canonicalPadicArtin p r L w a)) := by
      exact (D.formula
        ((rationalUnitsEquiv p).symm a) chi).symm
    _ = chi (Additive.ofMul
          (padicCyclotomicArtin p r L a)) := by
      rw [hnormalization p r L w hr htwo]

/-- The two currently used statements of the positive prime-power gap are
logically equivalent.  The substantive missing input is therefore precisely
the canonical-versus-Lubin--Tate normalization, including its orientation. -/
theorem positive_formula_normalization :
    PositiveCupFormula ↔
      PositivePadicNormalization :=
  ⟨normalization_cup_formula,
    cup_formula_normalization⟩

/-- The positive nontrivial conductor calculation, together with the two
already-settled degenerate levels, proves the full normalization statement. -/
theorem canonical_normalization_positive
    (hpositive : PositivePadicNormalization) :
    CanonicalPadicNormalization := by
  intro p r _ _ L _ _ _ w
  by_cases hr : r = 0
  · subst r
    exact canonical_artin_explicit p L w
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  by_cases htwo : p ^ r = 2
  · have hpr := (Nat.Prime.pow_eq_iff Nat.prime_two).mp htwo
    rcases hpr with ⟨rfl, rfl⟩
    exact artin_explicit_two L w
  · exact hpositive p r L w hrpos htwo

/-- A proof of the scalar positive-conductor cup formula is the only input
needed for the full canonical/explicit normalization at every prime-power
level. -/
theorem canonical_normalization_formula
    (hcup : PositiveCupFormula) :
    CanonicalPadicNormalization :=
  canonical_normalization_positive
    (normalization_cup_formula hcup)

end

end Towers.CField.RExist
