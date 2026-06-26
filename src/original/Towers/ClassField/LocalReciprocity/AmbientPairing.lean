import Towers.ClassField.LocalReciprocity.RationalDoubleDual
import Towers.ClassField.LocalReciprocity.DualityConclusion
import Towers.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Towers.ClassField.ReciprocityExistence.FieldCup
import Towers.ClassField.ReciprocityExistence.CupAdditivity

/-!
# Proposition III.3.6 in the ambient universe

The canonical local invariant of the literal multiplicative cup class is
additive in both variables.  Finite rational-character double duality
therefore turns this pairing into a canonical homomorphism to the Galois
group.  By construction it satisfies the exact character formula of
Proposition III.3.6, without shrinking either field to `Type 0`.
-/

namespace Towers.CField.LRecip

open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.RExist
open scoped IsMulCommutative

noncomputable section

universe u

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsMulCommutative Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

/-- The canonical local invariant, restricted along the relative Brauer
class of a multiplicative degree-two cohomology class. -/
noncomputable def ambientMultiplicativeInvariant :
    MHTwo Gal(L/K) Lˣ →*
      Multiplicative LocalInvariant :=
  (carryBrauerInvariant K).toMonoidHom.comp
    ((relativeBrauerGroup K L).subtype.comp
      (CProduc.hRelativeBrauer K L).toMonoidHom)

omit [IsUltrametricDist K] [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The literal multiplicative cup class is additive in the character. -/
@[simp]
theorem global_multiplicative_add
    (a : Kˣ) (χ ψ : CharacterModule (Additive Gal(L/K))) :
    multiplicativeCupClass K L a (χ + ψ) =
      multiplicativeCupClass K L a χ *
        multiplicativeCupClass K L a ψ := by
  simp only [multiplicativeCupClass,
    invariant_cup_add]

omit [IsUltrametricDist K] [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsGalois K L] in
/-- The zero character gives the neutral literal cup class. -/
@[simp]
theorem global_multiplicative_zero (a : Kˣ) :
    multiplicativeCupClass K L a
      (0 : CharacterModule (Additive Gal(L/K))) = 1 := by
  simp only [multiplicativeCupClass,
    invariant_character_cup]

/-- The canonical invariant of the ambient-universe multiplicative cup. -/
noncomputable def ambientCupInvariant
    (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))) :
    LocalInvariant :=
  (ambientMultiplicativeInvariant K L
    (multiplicativeCupClass K L a χ)).toAdd

/-- For fixed `a`, the ambient cup invariant is a rational character of
the rational-character group. -/
noncomputable def ambientCupCharacter (a : Kˣ) :
    CharacterModule (CharacterModule (Additive Gal(L/K))) where
  toFun χ := ambientCupInvariant K L a χ
  map_zero' := by
    change (ambientMultiplicativeInvariant K L
      (multiplicativeCupClass K L a 0)).toAdd = 0
    have hzero : multiplicativeCupClass K L a
        (0 : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) = 1 :=
      global_multiplicative_zero K L a
    rw [hzero, map_one]
    rfl
  map_add' χ ψ := by
    change (ambientMultiplicativeInvariant K L
        (multiplicativeCupClass K L a (χ + ψ))).toAdd =
      (ambientMultiplicativeInvariant K L
          (multiplicativeCupClass K L a χ)).toAdd +
        (ambientMultiplicativeInvariant K L
          (multiplicativeCupClass K L a ψ)).toAdd
    have hadd : multiplicativeCupClass K L a (χ + ψ) =
        multiplicativeCupClass K L a χ *
          multiplicativeCupClass K L a ψ :=
      global_multiplicative_add K L a χ ψ
    rw [hadd, map_mul]
    rfl

/-- Transpose the ambient cup pairing: a base-field unit gives a character
of the Galois character group. -/
noncomputable def ambientPairingTranspose :
    Additive Kˣ →+
      CharacterModule (CharacterModule (Additive Gal(L/K))) where
  toFun a := ambientCupCharacter K L a.toMul
  map_zero' := by
    ext χ
    change ambientCupInvariant K L 1 χ = 0
    change (ambientMultiplicativeInvariant K L
      (multiplicativeCupClass K L 1 χ)).toAdd = 0
    rw [global_multiplicative_one, map_one]
    rfl
  map_add' a b := by
    ext χ
    change ambientCupInvariant K L (a.toMul * b.toMul) χ =
      ambientCupInvariant K L a.toMul χ +
        ambientCupInvariant K L b.toMul χ
    change (ambientMultiplicativeInvariant K L
        (multiplicativeCupClass K L (a.toMul * b.toMul) χ)).toAdd =
      (ambientMultiplicativeInvariant K L
          (multiplicativeCupClass K L a.toMul χ)).toAdd +
        (ambientMultiplicativeInvariant K L
          (multiplicativeCupClass K L b.toMul χ)).toAdd
    rw [global_multiplicative_mul, map_mul]
    rfl

/-- The ambient-universe finite local Artin homomorphism characterized by
the multiplicative cup pairing of Proposition III.3.6. -/
noncomputable def multiplicativeCupArtin : Kˣ →* Gal(L/K) :=
  ((rationalDoubleDual Gal(L/K)).toAddMonoidHom.comp
    (ambientPairingTranspose K L)).toMultiplicative

/-- **Proposition III.3.6, ambient multiplicative form.** The Artin element
defined by the ambient cup pairing has precisely the prescribed value under
every rational character. -/
theorem multiplicative_cup_character
    (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))) :
    χ (Additive.ofMul (multiplicativeCupArtin K L a)) =
      ambientCupInvariant K L a χ := by
  change χ (rationalDoubleDual Gal(L/K)
    (ambientCupCharacter K L a)) =
      ambientCupInvariant K L a χ
  rw [rational_double_dual]
  rfl

/-- The character formula uniquely determines the ambient local Artin
homomorphism. -/
theorem multiplicative_cup_unique
    (artin : Kˣ →* Gal(L/K))
    (h : ∀ (a : Kˣ) (χ : CharacterModule (Additive Gal(L/K))),
      χ (Additive.ofMul (artin a)) =
        ambientCupInvariant K L a χ) :
    artin = multiplicativeCupArtin K L := by
  apply MonoidHom.ext
  intro a
  apply forall_rational_character (G := Gal(L/K))
  intro χ
  rw [h, multiplicative_cup_character]

end

end Towers.CField.LRecip
