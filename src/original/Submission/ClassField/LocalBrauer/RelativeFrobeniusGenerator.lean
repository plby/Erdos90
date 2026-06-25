import Submission.ClassField.LocalBrauer.RelativeFrobeniusCoordinate

/-!
# Generator normalization for the relative Frobenius coordinate
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev relativeLowerLevel (f : ℕ) :=
  canonicalUnramifiedLevel K f

set_option maxHeartbeats 7000000 in
-- Normalizing the generator compares conjugation across two canonical levels.
set_option synthInstance.maxHeartbeats 500000 in
@[simp]
theorem relative_frobenius_z
    (m f : ℕ) [NeZero m] [NeZero f] :
    frobeniusZMod K m f
        (Multiplicative.ofAdd (1 : ZMod m)) =
      relativeArithmeticFrobenius K m f := by
  let F := relativeLowerLevel K f
  let e := canonicalUnramifiedRelative K m f
  change e.autCongr.symm
      (levelZMod F m
        (Multiplicative.ofAdd (1 : ZMod m))) = _
  rw [level_frobenius_z]
  exact e.autCongr.symm_apply_eq.mpr
    (arithmetic_aut_congr K m f e).symm

end

end Submission.CField.LBrauer
