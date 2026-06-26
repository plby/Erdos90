import Towers.ClassField.CrossedProducts.TensorEquivLeft
import Towers.ClassField.LocalBrauer.ResidueDegreeBound

/-!
# Chapter IV, Section 4: a subfield lifted from the residue field

A primitive element of the division residue field lifts to an integer whose
generated subfield has degree at least the residue degree.  If the residue
degree is the full degree of the division algebra, this subfield is maximal
and splits the division algebra.
-/

namespace Towers.CField.LBrauer

noncomputable section

open CProduca
open scoped Valued

universe u

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DivisionRing D]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra K D] [Algebra.IsCentral K D] [Module.Finite K D]

/-- Any lifted residue generator whose generated subfield realizes the
residue-degree lower bound is maximal and splitting when `f` is the full
degree of `D`. -/
theorem residue_maximal_split
    (alpha : divisionIntegerSubring K D)
    (hcomm : ∀ x y : Algebra.adjoin K ({(alpha : D)} : Set D),
      x * y = y * x)
    (hdegree : residueDegree K D ≤
      Module.finrank K (Algebra.adjoin K ({(alpha : D)} : Set D)))
    (hresidue : residueDegree K D = Nat.sqrt (Module.finrank K D)) :
    let E := Algebra.adjoin K ({(alpha : D)} : Set D)
    Module.finrank K E = Nat.sqrt (Module.finrank K D) ∧
      IsMaximalCommutative E ∧
        letI : IsSimpleRing E :=
          commutative_subalgebra_simple K D E hcomm
        SplitSubalgebra K D E hcomm := by
  let E := Algebra.adjoin K ({(alpha : D)} : Set D)
  change
    Module.finrank K E = Nat.sqrt (Module.finrank K D) ∧
      IsMaximalCommutative E ∧
        letI : IsSimpleRing E :=
          commutative_subalgebra_simple K D E hcomm
        SplitSubalgebra K D E hcomm
  have hlower : Nat.sqrt (Module.finrank K D) ≤ Module.finrank K E := by
    rw [← hresidue]
    exact hdegree
  have hupper : Module.finrank K E ≤ Nat.sqrt (Module.finrank K D) :=
    commutative_subalgebra_finrank K D E hcomm
  have heq : Module.finrank K E = Nat.sqrt (Module.finrank K D) :=
    Nat.le_antisymm hupper hlower
  have hmax : IsMaximalCommutative E :=
    (maximal_subfield_sqrt K D E hcomm).2 heq
  have hdim : Module.finrank K D = (Module.finrank K E) ^ 2 :=
    (maximal_subfield_sq K D E hcomm).1 hmax
  letI : IsSimpleRing E :=
    commutative_subalgebra_simple K D E hcomm
  exact ⟨heq, hmax, subfield_split_sq K D E hcomm hdim⟩

/-- If the residue degree equals the degree of `D`, a lift of a residue-field
primitive element generates a maximal subfield which splits `D`. -/
theorem residue_maximal_splitting
    (hresidue : residueDegree K D = Nat.sqrt (Module.finrank K D)) :
    ∃ alpha : divisionIntegerSubring K D,
      let E := Algebra.adjoin K ({(alpha : D)} : Set D)
      ∃ hcomm : ∀ x y : E, x * y = y * x,
        Module.finrank K E = Nat.sqrt (Module.finrank K D) ∧
          IsMaximalCommutative E ∧
            letI : IsSimpleRing E :=
              commutative_subalgebra_simple K D E hcomm
            SplitSubalgebra K D E hcomm := by
  obtain ⟨alpha, hcomm, hdegree⟩ := residue_generator_lift K D
  refine ⟨alpha, hcomm, ?_⟩
  exact residue_maximal_split K D alpha hcomm hdegree hresidue

end

end Towers.CField.LBrauer
