import Towers.ClassField.ArtinLSeries.SquareSumIdentity
import Towers.ClassField.GrunwaldWang.GrunwaldWangStatement

/-! # Chapter VIII, Section 10, Example 10.1: the Hecke character

The character is stated on the actual idèle class group of
`Q(ζ₃)`.  Prime evaluation uses an actual one-place idèle whose local
entry is a uniformizer.  The unavailable construction of the Eisenstein
prime, cubic residue symbol, and global Hecke character is isolated in two
narrow bridges; the integral normalization is supplied by `Example101.lean`.
-/

namespace Towers.CField.ALSeries

open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.GWang
open scoped WithZero

noncomputable section

/-- The Eisenstein number field `Q(ζ₃)` used in Example 10.1. -/
abbrev EisensteinField := CyclotomicField 3 ℚ

/-- The source's cube-free condition on the integer `D`. -/
def CubeFreeInteger (D : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ 3 ∣ D)

/-- The complex number denoted `√-3` in the Eisenstein normalization. -/
def eisensteinSqrtNeg : ℂ := (Real.sqrt 3 : ℂ) * Complex.I

/-- The already-proved integral part of the split-prime normalization. -/
def IntegralNormalization : Prop :=
  ∀ p : ℕ, p.Prime → p % 3 = 1 →
    ∃ A B : ℤ, 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2

theorem integralNormalization :
    IntegralNormalization := by
  intro p hp hmod
  letI : Fact p.Prime := ⟨hp⟩
  exact sq_twenty_seven p hmod

/-- A value of the cubic residue symbol `(D / denominator)`.  Indexing the
type by its denominator records that in the split case the denominator is
the conjugate primary factor `bar π`; its value is a cube root of unity. -/
structure CubicSymbolValue (D : ℤ) (denominator : ℂ) where
  value : Circle
  cube_eq_one : value ^ 3 = 1

/-- The local Eisenstein data needed to read the two formulas in Example
10.1.  The fields involving prime ideals, uniformizers, the primary factor,
and the cubic residue symbol are precisely the pieces not presently
constructed in the library. -/
structure ECData (D : ℤ) where
  primePlace : ℕ → HeightOneSpectrum (RingOfIntegers EisensteinField)
  liesAbove : ∀ p : ℕ, p.Prime →
    algebraMap ℤ (RingOfIntegers EisensteinField) (p : ℤ) ∈
      (primePlace p).asIdeal
  primeElement : ∀ p : ℕ, (primePlace p).adicCompletion EisensteinField
  prime_element_uniformizer : ∀ p : ℕ,
    (Valued.v : Valuation
      ((primePlace p).adicCompletion EisensteinField) ℤᵐ⁰).IsUniformizer
      (primeElement p)
  primaryFactor : ℕ → ℂ
  primaryFactor_shape : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    ∃ A B : ℤ,
      4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 ∧
      primaryFactor p =
        ((A : ℂ) + 3 * (B : ℂ) * eisensteinSqrtNeg) / 2
  primaryPhase : ℕ → Circle
  primaryPhase_coe : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    (primaryPhase p : ℂ) = primaryFactor p / (Real.sqrt p : ℂ)
  cubicResidue : ∀ p : ℕ,
    CubicSymbolValue D (starRingEnd ℂ (primaryFactor p))

/-- The class of the idèle having the chosen prime element in the selected
finite-place component and `1` in every other component. -/
def ECData.primeIdeleClass
    {D : ℤ} (data : ECData D) (p : ℕ) :
    IdeleClassGroup (RingOfIntegers EisensteinField) EisensteinField :=
  QuotientGroup.mk'
    (principalIdeles (RingOfIntegers EisensteinField) EisensteinField)
    (finitePlaceEmbedding (RingOfIntegers EisensteinField) EisensteinField
      (data.primePlace p)
      (Units.mk0 (data.primeElement p)
        (data.prime_element_uniformizer p).ne_zero))

/-- The literal prime-value clauses in Example 10.1.  Through
`primaryPhase_coe`, the second right-hand side is
`π / √p * (D / bar π)`. -/
def HasPrimeValues
    {D : ℤ} (data : ECData D)
    (psi : IdeleClassCharacter EisensteinField) : Prop :=
  (∀ p : ℕ, p.Prime → Odd p → p % 3 ≠ 1 →
    psi (data.primeIdeleClass p) = 1) ∧
  ∀ p : ℕ, p.Prime → p % 3 = 1 →
    psi (data.primeIdeleClass p) =
      data.primaryPhase p * (data.cubicResidue p).value

/-- Construction of the chosen Eisenstein primes, their primary complex
generators and cubic residue values.  The proved integral normalization is
passed in explicitly, so this bridge contains no hidden arithmetic
conclusion about `4p = A² + 27B²`. -/
def EisensteinDataBridge : Prop :=
  ∀ D : ℤ, CubeFreeInteger D → IntegralNormalization →
    Nonempty (ECData D)

/-- The remaining global class-field-theoretic step: the prescribed
Eisenstein local values are realized by a continuous idèle-class character. -/
def HeckeConstructionBridge : Prop :=
  ∀ D : ℤ, CubeFreeInteger D →
    ∀ data : ECData D,
      ∃ psi : IdeleClassCharacter EisensteinField,
        HasPrimeValues data psi

theorem hecke_character_bridges
    (hlocal : EisensteinDataBridge)
    (hcharacter : HeckeConstructionBridge) :
    ∀ D : ℤ, CubeFreeInteger D →
    ∃ data : ECData D,
      ∃ psi : IdeleClassCharacter EisensteinField,
        HasPrimeValues data psi
  := by
  intro D hD
  obtain ⟨data⟩ := hlocal D hD integralNormalization
  exact ⟨data, hcharacter D hD data⟩

end

end Towers.CField.ALSeries
