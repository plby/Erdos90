import Submission.ClassField.LocalClass.IntegralModelTotal
import Submission.ClassField.LocalBrauer.SpectralIntegerClosure

/-!
# Transporting total ramification from norm integers to valuative integers

The local-field API uses both the norm valuation ring and the valuation-
relation ring.  They are equal as subrings, but their types and inferred
algebra structures are not definitionally equal.  This file packages the
transport needed by the maximal-unramified argument.
-/

namespace Submission.CField.LClass

noncomputable section

open ValuativeRel IsLocalRing
open Submission.NumberTheory.Milne
open Submission.CField.LBrauer
open scoped NormedField Valued

attribute [local instance] NormedField.toValued

private abbrev vInteger (F : Type*) [NontriviallyNormedField F]
    [ValuativeRel F] :=
  Valuation.integer (ValuativeRel.valuation F)

private abbrev nInteger (F : Type*) [NontriviallyNormedField F]
    [IsUltrametricDist F] :=
  Valuation.integer (NormedField.valuation (K := F))

variable (C L : Type*)
  [NontriviallyNormedField C] [IsUltrametricDist C] [ValuativeRel C]
  [IsNonarchimedeanLocalField C]
  [Valuation.Compatible (NormedField.valuation (K := C))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [NormedAlgebra C L] [FiniteDimensional C L] [Algebra.IsSeparable C L]
  [(NormedField.valuation (K := C)).HasExtension
    (NormedField.valuation (K := L))]

/-- The extension relation between norm valuations transports to the
canonical valuation relations.  Its induced integer-ring algebra is the
desired algebra on `ℴ[C]` and `ℴ[L]`. -/
@[implicit_reducible]
noncomputable def valuativeValuationExtension :
    (ValuativeRel.valuation C).HasExtension
      (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  rw [valuative_integer_norm C,
    valuative_integer_norm L]
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff _ _ _

attribute [local instance] valuativeValuationExtension

omit [IsNonarchimedeanLocalField C] [IsNonarchimedeanLocalField L]
  [FiniteDimensional C L] [Algebra.IsSeparable C L] in
/-- The transported algebra of valuative integer rings is compatible with
the inclusions into the extension field. -/
theorem valuativeScalarTower :
    IsScalarTower (vInteger C) (vInteger L) L := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  rfl

omit [IsNonarchimedeanLocalField C] [IsNonarchimedeanLocalField L] in
/-- The extension of valuation-relation integer rings is torsion-free. -/
theorem valuative_torsion_extension :
    Module.IsTorsionFree (vInteger C) (vInteger L) := by
  infer_instance

end

end Submission.CField.LClass
