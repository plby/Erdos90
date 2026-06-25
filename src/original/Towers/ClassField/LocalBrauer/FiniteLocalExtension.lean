import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Towers.ClassField.LocalBrauer.FieldNormExtension

/-!
# Chapter IV, Section 4: finite extensions of local fields

Every finite extension of a nonarchimedean local field is again a
nonarchimedean local field.  Since an abstract field extension carries no
preferred topology, the statement requires choosing the canonical spectral
norm topology.  This file packages all of the corresponding structures:

* the spectral nontrivially normed field and normed algebra structures;
* the valuative relation defined by the norm valuation;
* completeness and local compactness of the finite-dimensional extension;
* the resulting `IsNonarchimedeanLocalField` instance.

The structures are definitions rather than global instances, avoiding a
diamond with any topology already chosen on the extension field.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel
open scoped Topology

namespace FLExt

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The canonical spectral normed-field structure on a finite extension. -/
@[implicit_reducible]
def nontriviallyNormedField : NontriviallyNormedField L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  exact spectralNorm.nontriviallyNormedField K L

/-- The valuative relation on the extension defined by its spectral norm. -/
@[implicit_reducible]
def valuativeRel : ValuativeRel L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  exact ValuativeRel.ofValuation (NormedField.valuation (K := L))

/-- **Finite extensions of nonarchimedean local fields are local fields.**

This is unconditional after equipping the extension with the canonical
spectral norm and its norm-valuative relation. -/
@[implicit_reducible]
def nonarchimedeanLocalField :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    IsNonarchimedeanLocalField L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  haveI htop : IsValuativeTopology L := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : L) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := L)))ˣ,
          {x | (NormedField.valuation (K := L)).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := L)).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := L)).exists_setOf_restrict_le_iff 0 s
  letI : CompleteSpace L := spectralNorm.completeSpace K L
  letI : ProperSpace L := FiniteDimensional.proper K L
  haveI hcompact : LocallyCompactSpace L := inferInstance
  haveI hnontrivial : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := L))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }

/-- Under the canonical extension structures, the norm is literally the
spectral norm. -/
@[simp]
theorem norm_eq_spectral (x : L) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    ‖x‖ = spectralNorm K L x := by
  rfl

/-- The canonical extension norm restricts to the original norm on the base
field. -/
@[simp]
theorem norm_algebraMap (x : K) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    ‖algebraMap K L x‖ = ‖x‖ := by
  exact spectralNorm_extends x

end FLExt

end

end Towers.CField.LBrauer
