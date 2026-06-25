import Submission.ClassField.BrauerLocalization.BrauerKernelLifting
import Submission.ClassField.LocalBrauer.InvariantBaseChange

/-!
# Local vanishing from the invariant base-change formula

This file isolates the elementary implication used in the tailored-extension
argument for Theorem VIII.4.2: if an integer kills the invariant of a local
Brauer class and divides the degree of a finite local extension, then scalar
extension kills the class.
-/

namespace Submission.CField.BLoc

open IsDedekindDomain NumberField
open Submission.CField.BGroups
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.RExist

noncomputable section

universe u

variable (k E : Type u)
  [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [NontriviallyNormedField E] [IsUltrametricDist E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E]
  [Valuation.Compatible (NormedField.valuation (K := E))]
  [Algebra k E]

/-- A degree divisible by an annihilator of the source invariant forces
scalar extension of the Brauer class to be trivial. -/
theorem brauer_change_finrank
    (hbaseChange : BCForm k E)
    (x : BrauerGroup k) (m : ℕ)
    (hx : (carryBrauerInvariant k x) ^ m = 1)
    (hdegree : m ∣ Module.finrank k E) :
    brauerBaseChange k E x = 1 := by
  apply (carryBrauerInvariant E).injective
  rw [hbaseChange x]
  obtain ⟨d, hd⟩ := hdegree
  rw [hd, pow_mul, hx, one_pow, map_one]

/-- Additive form of
`brauer_change_finrank`, matching
the local-invariant coordinates in the direct sum of Theorem VIII.4.2. -/
theorem brauer_change_nsmul
    (hbaseChange : BCForm k E)
    (x : Additive (BrauerGroup k)) (m : ℕ)
    (hx : m • (carryBrauerInvariant k x.toMul).toAdd = 0)
    (hdegree : m ∣ Module.finrank k E) :
    brauerBaseChange k E x.toMul = 1 := by
  apply brauer_change_finrank
    k E hbaseChange x.toMul m
  · exact hx
  · exact hdegree

/-- The reverse implication needed for the finite cyclic relative sequence:
if a class becomes trivial after scalar extension, the extension degree
annihilates its local invariant. -/
theorem nsmul_brauer_change
    (hbaseChange : BCForm k E)
    (x : Additive (BrauerGroup k))
    (hx : brauerBaseChange k E x.toMul = 1) :
    Module.finrank k E •
      (carryBrauerInvariant k x.toMul).toAdd = 0 := by
  have h := hbaseChange x.toMul
  rw [hx, map_one] at h
  exact (congrArg Multiplicative.toAdd h).symm

/-- Spectral-local-field form of the same vanishing criterion.  The target
field only needs to be a finite abstract extension; its canonical local-field
structure is installed internally by `SpectralChangeFormula`.
This is the convenient form for arbitrary chosen number-field completions. -/
theorem brauer_spectral_nsmul
    (F : Type u) [Field F] [Algebra k F] [FiniteDimensional k F]
    (hbaseChange : SpectralChangeFormula k F)
    (x : Additive (BrauerGroup k)) (m : ℕ)
    (hx : m • (carryBrauerInvariant k x.toMul).toAdd = 0)
    (hdegree : m ∣ Module.finrank k F) :
    brauerBaseChange k F x.toMul = 1 := by
  letI : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.of_finite k F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField k F
  letI : NormedAlgebra k F := spectralNorm.normedAlgebra k F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra k
  letI : ValuativeRel F := FLExt.valuativeRel k F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField k F
  apply brauer_change_nsmul
    k F
  · exact hbaseChange
  · exact hx
  · exact hdegree

/-- Spectral-local-field form of the reverse implication. -/
theorem nsmul_spectral_change
    (F : Type u) [Field F] [Algebra k F] [FiniteDimensional k F]
    (hbaseChange : SpectralChangeFormula k F)
    (x : Additive (BrauerGroup k))
    (hx : brauerBaseChange k F x.toMul = 1) :
    Module.finrank k F •
      (carryBrauerInvariant k x.toMul).toAdd = 0 := by
  letI : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.of_finite k F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField k F
  letI : NormedAlgebra k F := spectralNorm.normedAlgebra k F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra k
  letI : ValuativeRel F := FLExt.valuativeRel k F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField k F
  exact nsmul_brauer_change
    k F hbaseChange x hx

section NumberField

variable (K : Type u) [Field K] [NumberField K]

/-- The coordinatewise local invariants of a family in the local Brauer
direct sum. -/
noncomputable def localInvariantCoordinates
    (data : BData K)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))) :
    DirectSum (NumberFieldPlace K) (fun _ ↦ LocalInvariant) :=
  DirectSum.map data.placeInvariant.invariant x

/-- The canonical positive common annihilator of all local invariants in a
finite-support Brauer family. -/
noncomputable def localInvariantAnnihilator
    (data : BData K)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))) : ℕ :=
  directInvariantAnnihilator
    (localInvariantCoordinates K data x)

theorem invariant_annihilator_pos
    (data : BData K)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))) :
    0 < localInvariantAnnihilator K data x :=
  direct_annihilator_pos
    (localInvariantCoordinates K data x)

/-- The canonical annihilator kills the invariant of every coordinate,
including coordinates outside the support. -/
theorem local_annihilator_nsmul
    (data : BData K)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (v : NumberFieldPlace K) :
    localInvariantAnnihilator K data x •
        data.placeInvariant.invariant v (x v) = 0 := by
  simpa only [localInvariantAnnihilator,
    localInvariantCoordinates, DirectSum.map_apply] using
    direct_annihilator_nsmul
      (localInvariantCoordinates K data x) v

/-- At a finite place the preceding statement is literally the canonical
carry-normalized invariant used by the local base-change formula. -/
theorem invariant_annihilator_nsmul
    (data : BData K)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v))))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    localInvariantAnnihilator K data x •
        finitePlaceInvariant K P (x (.inl P)) = 0 := by
  rw [← data.placeInvariant.finite_eq P]
  exact local_annihilator_nsmul K data x (.inl P)

end NumberField

end

end Submission.CField.BLoc
