import Towers.ClassField.LocalBrauer.DivisionDegreeFormula
import Towers.ClassField.LocalBrauer.ResidueDegreeBound
import Towers.ClassField.LocalBrauer.UnramifiedMaximalSubfield

/-!
# Chapter IV, Section 4: structure of a local division algebra

The ramification-residue degree formula, together with the two degree bounds,
forces both the ramification index and residue degree to equal the degree of
the division algebra.  Consequently the lifted residue generator constructed
earlier is unconditionally a maximal unramified splitting subfield.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open CProduca

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Algebra K D] [Algebra.IsCentral K D] [Module.Finite K D]

local instance localDivisionAlgebraStructureUniformSpace : UniformSpace K :=
  IsTopologicalAddGroup.rightUniformSpace K
local instance localDivisionAlgebraStructureIsUniformAddGroup : IsUniformAddGroup K :=
  isUniformAddGroup_of_addCommGroup
local instance localDivisionAlgebraStructureValuationRankOne : Valuation.RankOne
    (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
  change Valuation.RankOne (valuation K)
  infer_instance
local instance localDivisionAlgebraStructureNontriviallyNormedField :
    NontriviallyNormedField K :=
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)

variable [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The ramification index and residue degree both equal the degree of the
central division algebra. -/
theorem ramification_sqrt_finrank :
    ramificationIndex K D = Nat.sqrt (Module.finrank K D) ∧
      residueDegree K D = Nat.sqrt (Module.finrank K D) := by
  let n := Nat.sqrt (Module.finrank K D)
  obtain ⟨m, hm⟩ :=
    BGroups.finrank_simple_square K D
  have hn : n = m := by
    simp [n, hm]
  have hsquare : Module.finrank K D = n ^ 2 := by
    rw [hm, hn]
  apply ramification_residue_sq
    (ramification_index_degree K D)
    (degree_sqrt_finrank K D)
  exact (ramification_residue_finrank K D).trans hsquare

/-- For a local central division algebra, the ramification index is its
degree. -/
theorem ramification_index_finrank :
    ramificationIndex K D = Nat.sqrt (Module.finrank K D) :=
  (ramification_sqrt_finrank K D).1

/-- For a local central division algebra, the residue degree is its degree. -/
theorem residue_sqrt_finrank :
    residueDegree K D = Nat.sqrt (Module.finrank K D) :=
  (ramification_sqrt_finrank K D).2

/-- A division algebra of degree greater than one is ramified: its
ramification index is greater than one. -/
theorem index_sqrt_finrank
    (hdegree : 1 < Nat.sqrt (Module.finrank K D)) :
    1 < ramificationIndex K D := by
  rw [ramification_index_finrank K D]
  exact hdegree

/-- Unconditionally, a local central division algebra contains an unramified
maximal commutative subfield which splits it. -/
theorem splitting_subfield_unconditional :
    ∃ alpha : divisionIntegerSubring K D,
      let E := Algebra.adjoin K ({(alpha : D)} : Set D)
      ∃ hcomm : ∀ x y : E, x * y = y * x,
        Module.finrank K E = Nat.sqrt (Module.finrank K D) ∧
          IsMaximalCommutative E ∧
          (letI : IsSimpleRing E :=
            commutative_subalgebra_simple K D E hcomm
           SplitSubalgebra K D E hcomm) ∧
          letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
          letI : Module.Finite K E :=
            Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
          letI : IsDomain E :=
            Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
          letI : Field E := fieldOfFiniteDimensional K E
          let OR := (valuation K).integer
          let g : OR →+* E := (algebraMap K E).comp OR.subtype
          letI : Algebra OR E := g.toAlgebra
          let e : E :=
            ⟨(alpha : D), Algebra.subset_adjoin
              (Set.mem_singleton (alpha : D))⟩
          let U := Algebra.adjoin OR ({e} : Set E)
          IsIntegral OR e ∧
            Algebra.FormallyUnramified OR U ∧
            ∃ hlocal : IsLocalRing U,
              letI := hlocal
              ∃ hdvr : IsDiscreteValuationRing U,
                letI := hdvr
                Algebra.IsUnramifiedAt OR (IsLocalRing.maximalIdeal U) :=
  maximal_splitting_subfield K D
    (residue_sqrt_finrank K D)

end

end Towers.CField.LBrauer
