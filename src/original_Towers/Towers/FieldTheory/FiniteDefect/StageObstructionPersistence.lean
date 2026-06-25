import Towers.FieldTheory.FiniteDefect.StageObstructions


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open PRFact

namespace KRData

namespace DSObstru

variable
    (D : KRData)
    {n m : ℕ}
    (W : D.DSObstru n)

/--
If an actual Koch-kernel witness survives the canonical relator quotient at
depth `n`, then the same ambient witness survives every deeper canonical
relator quotient.
-/
def of_le
    (hnm : n ≤ m) :
    D.DSObstru m where
  witness := W.witness
  witness_initial_koch := W.witness_initial_koch
  witnessSurvivesFin := by
    intro hxm
    apply W.witnessSurvivesFin
    apply MonoidHom.mem_ker.mp
    apply D.three_relator_kernel hnm
    exact MonoidHom.mem_ker.mpr hxm

/--
The persistence operation keeps the ambient Koch-kernel witness itself, not
merely the existence of some unrelated deeper obstruction.
-/
@[simp]
lemma of_le_witness
    (hnm : n ≤ m) :
    (of_le D W hnm).witness = W.witness := rfl

include W
/--
A finite defect stage obstruction prevents its corrected finite defect stage
from factoring uniquely back to the original canonical relator quotient layer.
-/
lemma not_koch_defect :
    ¬ FactorsUniquelyThrough
      (D.canonicalDefectAmbient n)
      (D.ZassenhausRelatorQuotient n).map := by
  intro hfactor
  apply (nonempty_defect_bot
    D
    n).mp ⟨W⟩
  exact (koch_defect_relator
    D
    n).mpr hfactor

end DSObstru

/--
Once one canonical finite defect stage obstruction appears, canonical finite
defect stage obstructions occur at every deeper Zassenhaus depth.
-/
lemma nonempty_stage_obstruction
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m)
    (hnonempty : Nonempty (D.DSObstru n)) :
    Nonempty (D.DSObstru m) := by
  rcases hnonempty with ⟨W⟩
  exact ⟨DSObstru.of_le D W hnm⟩

/--
Failure of the desired finite quotient Koch theorem is equivalent to an
eventual tail of canonical finite defect stage obstructions.
-/
lemma eventually_stage_obstruction
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
        Nonempty (D.DSObstru m) := by
  constructor
  · intro hnot
    rcases (D.defect_stage_obstruction).mp
      hnot with ⟨n, hnonempty⟩
    exact ⟨n, fun m hnm =>
      D.nonempty_stage_obstruction hnm hnonempty⟩
  · rintro ⟨n, htail⟩
    exact (D.defect_stage_obstruction).mpr
      ⟨n, htail n le_rfl⟩

/--
Failure of the desired finite quotient Koch theorem is witnessed by one actual
Koch-kernel element that survives every sufficiently deep canonical relator
quotient layer.
-/
lemma stage_obstruction_witness
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧
          ∀ m : ℕ, n ≤ m →
            (D.ZassenhausRelatorQuotient m).map x ≠ 1 := by
  constructor
  · intro hnot
    rcases (D.defect_stage_obstruction).mp
      hnot with ⟨n, ⟨W⟩⟩
    exact ⟨n, W.witness, W.witness_initial_koch, fun m hnm =>
      (DSObstru.of_le D W hnm).witnessSurvivesFin⟩
  · rintro ⟨n, x, hxker, htail⟩
    apply (D.defect_stage_obstruction).mpr
    exact ⟨n, ⟨{
      witness := x
      witness_initial_koch := hxker
      witnessSurvivesFin := htail n le_rfl
    }⟩⟩

/--
Failure of the desired finite quotient Koch theorem is equivalent to an
eventual tail of corrected finite defect stages that cannot factor uniquely
back to their original canonical relator quotient layers.
-/
lemma not_eventually_relator
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
        ¬ FactorsUniquelyThrough
          (D.canonicalDefectAmbient m)
          (D.ZassenhausRelatorQuotient m).map := by
  constructor
  · intro hnot
    rcases (D.defect_stage_obstruction).mp
      hnot with ⟨n, ⟨W⟩⟩
    exact ⟨n, fun m hnm =>
      DSObstru.not_koch_defect
        D
        (DSObstru.of_le D W hnm)⟩
  · rintro ⟨n, htail⟩
    exact (D.not_ambient_relator).mpr
      ⟨n, htail n le_rfl⟩

end KRData
end TBluepr
end Towers
