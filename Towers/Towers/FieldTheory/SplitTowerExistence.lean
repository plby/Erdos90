import Towers.FieldTheory.TotallyRealTower
import Towers.FieldTheory.SplitRealTower

noncomputable section

namespace Towers

/--
The arithmetic input asserting the existence of a split totally real tower.

The HMR construction is carried out in `TBluepr.STBuild`;
this theorem packages its output for the arithmetic/geometric endgame.
-/
theorem input_totally_tower :
    Nonempty (SplitTotallyTower.{0}) := by
  classical
  refine ⟨{
    fields := fun j => (TBluepr.STBuild.towerField j : Type)
    instField := fun _ => inferInstance
    instNumberField := fun _ => inferInstance
    inclusions := fun j =>
      let f : TBluepr.STBuild.towerField j →ₐ[ℚ]
          TBluepr.STBuild.towerField (j + 1) :=
        Classical.choice (TBluepr.STBuild.towerField_nested j)
      { toFun := f
        inj' := f.injective }
    totallyReal := TBluepr.STBuild.tower_totally_real
    degree_tendsto_top := TBluepr.STBuild.tower_degree_tendsto
    rootDiscriminant_bounded :=
      TBluepr.STBuild.tower_discriminant_bounded
    splitPrimes := TBluepr.STBuild.splitPrimeSet
    splitPrimes_infinite := TBluepr.STBuild.split_set_infinite
    splitPrimes_spec := by
      intro p hp
      refine
        ⟨?_, TBluepr.STBuild.split_set_four hp, ?_⟩
      · rcases hp with ⟨i, rfl⟩
        exact TBluepr.STBuild.chosenPrime_prime i
      · intro j
        exact
          TBluepr.STBuild.splits_every_tower hp j
  }⟩

end Towers
