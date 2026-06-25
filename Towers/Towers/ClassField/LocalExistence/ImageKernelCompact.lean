import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.LocalExistence.NormFiberCompactness
import Towers.ClassField.LocalExistence.ClosedImagesKernels

/-!
# Milne, Class Field Theory, Section III.5, Step 1

For a finite Galois extension of a nonarchimedean local field, the canonical
spectral topology makes the norm on field units continuous, with closed image
and compact kernel.  The image is open because Theorem III.3.1 makes the norm
quotient finite; the kernel is the compact unit-kernel already constructed
from the valuation formula.

Milne states the result for every finite extension.  The present repository
proves continuity, the norm-order formula, and compactness of the norm kernel
only in the Galois case.  Passing to a Galois closure would require the general
case of the Norm Limitation Theorem III.3.5; only its Galois case is currently
formalized.  The theorem below therefore exposes the strongest unconditional
field-theoretic statement, without adding a substitute hypothesis.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.LBrauer

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance normImageValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance normImageValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The norm on field-unit groups is continuous for the canonical spectral
local-field structure on a finite Galois extension. -/
theorem galois_units_continuous :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    Continuous (normOnUnits K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  exact (FLExt.continuous_fieldNorm K L).units_map

set_option maxHeartbeats 1000000 in
-- The finite norm quotient and the compact integral-unit model are instance-heavy.
set_option synthInstance.maxHeartbeats 200000 in
/-- **Section III.5, Step 1, finite Galois case.**  The image of the norm
`Lˣ → Kˣ` is closed and its kernel is compact.  All topologies and
valuation relations on `L` are the canonical spectral ones. -/
theorem range_closed_compact :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    IsClosed ((normOnUnits K L).range : Set Kˣ) ∧
      IsCompact ((normOnUnits K L).ker : Set Lˣ) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : Finite (Kˣ ⧸ normSubgroup K L) :=
    Finite.of_injective (localArtinEquiv K L)
      (localArtinEquiv K L).injective
  letI : (normSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  constructor
  · exact (normSubgroup K L).isClosed_of_isOpen
      (norm_subgroup K L)
  · exact units_ker_compact K L

end

end Towers.CField.LExist
