import Submission.ClassField.NormCorrespondence.LocalStatements
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Chapter I, Theorem 1.1: the Local Recip Law

This file gives a concrete statement of local reciprocity.  Unramifiedness
is expressed on the spectral valuation integers of a finite extension, and
arithmetic Frobenius is characterized by its residue-power action.  Thus the
statement does not depend on choosing identifications with a preferred tower
of unramified extensions.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u

open scoped NormedField

open LBrauer

private abbrev normInteger (F : Type u) [NormedField F]
    [IsUltrametricDist F] :=
  Valuation.integer (NormedField.valuation (K := F))

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- A finite subextension is unramified when its spectral valuation integers
are finite and formally unramified over the valuation integers of `K`.

For finite extensions of complete discretely valued fields this is the
standard intrinsic definition of an unramified extension. -/
def FASubext.IsUnramified
    (L : FASubext K) : Prop :=
  let E := L.finiteIntermediateField
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension K E
  Module.Finite (normInteger K) (normInteger E) ∧
    Algebra.FormallyUnramified (normInteger K) (normInteger E)

/-- The residue field cardinality of a nonarchimedean local field. -/
abbrev localResidueCardinality : ℕ :=
  Nat.card (IsLocalRing.ResidueField (normInteger K))

/-- A prime element of a nonarchimedean local field, expressed using the
canonical maximal value below one in its discrete value group. -/
def LocalPrimeElement (π : Kˣ) : Prop :=
  ValuativeRel.valuation K (π : K) = ValuativeRel.uniformizer K

/-- Intrinsic characterization of arithmetic Frobenius on an unramified
finite extension: on integral elements it is the `q`-power map modulo the
maximal ideal, where `q` is the cardinality of the base residue field. -/
def FASubext.IsArithmeticFrobenius
    (L : FASubext K)
    (σ : Gal(L.finiteIntermediateField/K)) : Prop :=
  let E := L.finiteIntermediateField
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  ∀ x : E, ‖x‖ ≤ 1 →
    ‖σ x - x ^ localResidueCardinality K‖ < 1

/-- The finite-level reciprocity clause for an abelian extension `L/K`.
It says that restriction of `φ` factors through the norm quotient and that
the resulting map is an isomorphism. -/
def InducesLocalReciprocity
    (φ : Kˣ →* AbsoluteAbelianGalois K)
    (L : FASubext K) : Prop :=
  ∃ e : (Kˣ ⧸ L.normGroup) ≃*
      Gal(L.finiteIntermediateField/K),
    ∀ x : Kˣ,
      e (QuotientGroup.mk' L.normGroup x) =
        localAbelianRestriction L (φ x)

/-- The two characterizing properties of the local Artin map in Theorem
I.1.1. -/
def IsReciprocityMap
    (φ : Kˣ →* AbsoluteAbelianGalois K) : Prop :=
  (∀ (π : Kˣ), LocalPrimeElement K π →
    ∀ L : FASubext K, L.IsUnramified K →
      L.IsArithmeticFrobenius K (localAbelianRestriction L (φ π))) ∧
  ∀ L : FASubext K,
    InducesLocalReciprocity K φ L

/-- **Theorem I.1.1 (Local Recip Law), statement.**

For every nonarchimedean local field there is a unique homomorphism from
`Kˣ` to the Galois group of its maximal abelian extension which sends every
prime element to arithmetic Frobenius on every finite unramified extension
and induces the norm-residue isomorphism on every finite abelian extension. -/
def LocalReciprocityLaw : Prop :=
  ∃! φ : Kˣ →* AbsoluteAbelianGalois K,
    IsReciprocityMap K φ

end

end Submission.CField.LFTheory
